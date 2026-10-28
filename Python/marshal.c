
/* Write Python objects to files and read them back.
   This is intended for writing and reading compiled Python code only;
   a true persistent storage facility would be much harder, since
   it would have to take circular links and sharing into account. */

#define PY_SSIZE_T_CLEAN

#include "Python.h"
#include "longintrepr.h"
#include "code.h"
#include "marshal.h"

#define ABS(x) ((x) < 0 ? -(x) : (x))

/* High water mark to determine when the marshalled object is dangerously deep
 * and risks coring the interpreter.  When the object stack gets this deep,
 * raise an exception instead of continuing.
 * On Windows debug builds, reduce this value.
 */
#if defined(MS_WINDOWS) && defined(_DEBUG)
#define MAX_MARSHAL_STACK_DEPTH 1000
#else
#define MAX_MARSHAL_STACK_DEPTH 2000
#endif

#define TYPE_NULL               '0'
#define TYPE_NONE               'N'
#define TYPE_FALSE              'F'
#define TYPE_TRUE               'T'
#define TYPE_STOPITER           'S'
#define TYPE_ELLIPSIS           '.'
#define TYPE_INT                'i'
#define TYPE_INT64              'I'
#define TYPE_FLOAT              'f'
#define TYPE_BINARY_FLOAT       'g'
#define TYPE_COMPLEX            'x'
#define TYPE_BINARY_COMPLEX     'y'
#define TYPE_LONG               'l'
#define TYPE_STRING             's'
#define TYPE_INTERNED           't'
#define TYPE_STRINGREF          'R'
#define TYPE_TUPLE              '('
#define TYPE_LIST               '['
#define TYPE_DICT               '{'
#define TYPE_CODE               'c'
#define TYPE_UNICODE            'u'
#define TYPE_UNKNOWN            '?'
#define TYPE_SET                '<'
#define TYPE_FROZENSET          '>'

/* NetEase Minecraft (.mcs) extensions.  Strings and unicode are stored with
   their bytes XORed with 0x8D, or encrypted with a fixed RC4 key; code
   objects use a reordered "o"/"M" layout and carry a magic number that
   selects one of three bytecode numbering schemes. */
#define TYPE_MCS_o                      'o'   /* reordered code object      */
#define TYPE_MCS_M                      'M'   /* reordered code object + tail */
#define TYPE_MCS_ENC_STRING             0x08  /* xor 0x8D string            */
#define TYPE_MCS_ENC_UNICODE            0x0E  /* xor 0x8D utf-8 unicode     */
#define TYPE_MCS_ENC_INTERNED           0x0F  /* xor 0x8D interned string   */
#define TYPE_MCS_RC4_STRING             'm'   /* rc4 string                 */
#define TYPE_MCS_RC4_INTERNED           'b'   /* rc4 interned string        */
#define TYPE_MCS_RC4_UNICODE            '1'   /* rc4 utf-8 unicode          */

#define MCS_XOR_KEY 0x8D
#define MCS_HAVE_ARGUMENT 0x5D          /* mcs opcodes >= this take a 16-bit arg */

#define WFERR_OK 0
#define WFERR_UNMARSHALLABLE 1
#define WFERR_NESTEDTOODEEP 2
#define WFERR_NOMEMORY 3

typedef struct {
    FILE *fp;
    int error;  /* see WFERR_* values */
    int depth;
    /* If fp == NULL, the following are valid: */
    PyObject *str;
    char *ptr;
    char *end;
    PyObject *strings; /* dict on marshal, list on unmarshal */
    int version;
    void *mcs_tail;    /* NEPy: 8-byte trailer copied into 'M' code objects */
} WFILE;

#define w_byte(c, p) if (((p)->fp)) putc((c), (p)->fp); \
                      else if ((p)->ptr != (p)->end) *(p)->ptr++ = (c); \
                           else w_more(c, p)

static void
w_more(int c, WFILE *p)
{
    Py_ssize_t size, newsize;
    if (p->str == NULL)
        return; /* An error already occurred */
    size = PyString_Size(p->str);
    newsize = size + size + 1024;
    if (newsize > 32*1024*1024) {
        newsize = size + (size >> 3);           /* 12.5% overallocation */
    }
    if (_PyString_Resize(&p->str, newsize) != 0) {
        p->ptr = p->end = NULL;
    }
    else {
        p->ptr = PyString_AS_STRING((PyStringObject *)p->str) + size;
        p->end =
            PyString_AS_STRING((PyStringObject *)p->str) + newsize;
        *p->ptr++ = Py_SAFE_DOWNCAST(c, int, char);
    }
}

static void
w_string(const char *s, Py_ssize_t n, WFILE *p)
{
    if (p->fp != NULL) {
        fwrite(s, 1, n, p->fp);
    }
    else {
        while (--n >= 0) {
            w_byte(*s, p);
            s++;
        }
    }
}

static void
w_short(int x, WFILE *p)
{
    w_byte((char)( x      & 0xff), p);
    w_byte((char)((x>> 8) & 0xff), p);
}

static void
w_long(long x, WFILE *p)
{
    w_byte((char)( x      & 0xff), p);
    w_byte((char)((x>> 8) & 0xff), p);
    w_byte((char)((x>>16) & 0xff), p);
    w_byte((char)((x>>24) & 0xff), p);
}

#if SIZEOF_LONG > 4
static void
w_long64(long x, WFILE *p)
{
    w_long(x, p);
    w_long(x>>32, p);
}
#endif

#define SIZE32_MAX  0x7FFFFFFF

#if SIZEOF_SIZE_T > 4
# define W_SIZE(n, p)  do {                     \
        if ((n) > SIZE32_MAX) {                 \
            (p)->depth--;                       \
            (p)->error = WFERR_UNMARSHALLABLE;  \
            return;                             \
        }                                       \
        w_long((long)(n), p);                   \
    } while(0)
#else
# define W_SIZE  w_long
#endif

static void
w_pstring(const char *s, Py_ssize_t n, WFILE *p)
{
        W_SIZE(n, p);
        w_string(s, n, p);
}

/* We assume that Python longs are stored internally in base some power of
   2**15; for the sake of portability we'll always read and write them in base
   exactly 2**15. */

#define PyLong_MARSHAL_SHIFT 15
#define PyLong_MARSHAL_BASE ((short)1 << PyLong_MARSHAL_SHIFT)
#define PyLong_MARSHAL_MASK (PyLong_MARSHAL_BASE - 1)
#if PyLong_SHIFT % PyLong_MARSHAL_SHIFT != 0
#error "PyLong_SHIFT must be a multiple of PyLong_MARSHAL_SHIFT"
#endif
#define PyLong_MARSHAL_RATIO (PyLong_SHIFT / PyLong_MARSHAL_SHIFT)

static void
w_PyLong(const PyLongObject *ob, WFILE *p)
{
    Py_ssize_t i, j, n, l;
    digit d;

    w_byte(TYPE_LONG, p);
    if (Py_SIZE(ob) == 0) {
        w_long((long)0, p);
        return;
    }

    /* set l to number of base PyLong_MARSHAL_BASE digits */
    n = ABS(Py_SIZE(ob));
    l = (n-1) * PyLong_MARSHAL_RATIO;
    d = ob->ob_digit[n-1];
    assert(d != 0); /* a PyLong is always normalized */
    do {
        d >>= PyLong_MARSHAL_SHIFT;
        l++;
    } while (d != 0);
    if (l > SIZE32_MAX) {
        p->depth--;
        p->error = WFERR_UNMARSHALLABLE;
        return;
    }
    w_long((long)(Py_SIZE(ob) > 0 ? l : -l), p);

    for (i=0; i < n-1; i++) {
        d = ob->ob_digit[i];
        for (j=0; j < PyLong_MARSHAL_RATIO; j++) {
            w_short(d & PyLong_MARSHAL_MASK, p);
            d >>= PyLong_MARSHAL_SHIFT;
        }
        assert (d == 0);
    }
    d = ob->ob_digit[n-1];
    do {
        w_short(d & PyLong_MARSHAL_MASK, p);
        d >>= PyLong_MARSHAL_SHIFT;
    } while (d != 0);
}

static void
w_object(PyObject *v, WFILE *p)
{
    Py_ssize_t i, n;

    p->depth++;

    if (p->depth > MAX_MARSHAL_STACK_DEPTH) {
        p->error = WFERR_NESTEDTOODEEP;
    }
    else if (v == NULL) {
        w_byte(TYPE_NULL, p);
    }
    else if (v == Py_None) {
        w_byte(TYPE_NONE, p);
    }
    else if (v == PyExc_StopIteration) {
        w_byte(TYPE_STOPITER, p);
    }
    else if (v == Py_Ellipsis) {
        w_byte(TYPE_ELLIPSIS, p);
    }
    else if (v == Py_False) {
        w_byte(TYPE_FALSE, p);
    }
    else if (v == Py_True) {
        w_byte(TYPE_TRUE, p);
    }
    else if (PyInt_CheckExact(v)) {
        long x = PyInt_AS_LONG((PyIntObject *)v);
#if SIZEOF_LONG > 4
        long y = Py_ARITHMETIC_RIGHT_SHIFT(long, x, 31);
        if (y && y != -1) {
            w_byte(TYPE_INT64, p);
            w_long64(x, p);
        }
        else
#endif
            {
            w_byte(TYPE_INT, p);
            w_long(x, p);
        }
    }
    else if (PyLong_CheckExact(v)) {
        PyLongObject *ob = (PyLongObject *)v;
        w_PyLong(ob, p);
    }
    else if (PyFloat_CheckExact(v)) {
        if (p->version > 1) {
            unsigned char buf[8];
            if (_PyFloat_Pack8(PyFloat_AsDouble(v),
                               buf, 1) < 0) {
                p->error = WFERR_UNMARSHALLABLE;
                return;
            }
            w_byte(TYPE_BINARY_FLOAT, p);
            w_string((char*)buf, 8, p);
        }
        else {
            char *buf = PyOS_double_to_string(PyFloat_AS_DOUBLE(v),
                                              'g', 17, 0, NULL);
            if (!buf) {
                p->error = WFERR_NOMEMORY;
                return;
            }
            n = strlen(buf);
            w_byte(TYPE_FLOAT, p);
            w_byte((int)n, p);
            w_string(buf, n, p);
            PyMem_Free(buf);
        }
    }
#ifndef WITHOUT_COMPLEX
    else if (PyComplex_CheckExact(v)) {
        if (p->version > 1) {
            unsigned char buf[8];
            if (_PyFloat_Pack8(PyComplex_RealAsDouble(v),
                               buf, 1) < 0) {
                p->error = WFERR_UNMARSHALLABLE;
                return;
            }
            w_byte(TYPE_BINARY_COMPLEX, p);
            w_string((char*)buf, 8, p);
            if (_PyFloat_Pack8(PyComplex_ImagAsDouble(v),
                               buf, 1) < 0) {
                p->error = WFERR_UNMARSHALLABLE;
                return;
            }
            w_string((char*)buf, 8, p);
        }
        else {
            char *buf;
            w_byte(TYPE_COMPLEX, p);
            buf = PyOS_double_to_string(PyComplex_RealAsDouble(v),
                                        'g', 17, 0, NULL);
            if (!buf) {
                p->error = WFERR_NOMEMORY;
                return;
            }
            n = strlen(buf);
            w_byte((int)n, p);
            w_string(buf, n, p);
            PyMem_Free(buf);
            buf = PyOS_double_to_string(PyComplex_ImagAsDouble(v),
                                        'g', 17, 0, NULL);
            if (!buf) {
                p->error = WFERR_NOMEMORY;
                return;
            }
            n = strlen(buf);
            w_byte((int)n, p);
            w_string(buf, n, p);
            PyMem_Free(buf);
        }
    }
#endif
    else if (PyString_CheckExact(v)) {
        if (p->strings && PyString_CHECK_INTERNED(v)) {
            PyObject *o = PyDict_GetItem(p->strings, v);
            if (o) {
                long w = PyInt_AsLong(o);
                w_byte(TYPE_STRINGREF, p);
                w_long(w, p);
                goto exit;
            }
            else {
                int ok;
                o = PyInt_FromSsize_t(PyDict_Size(p->strings));
                ok = o &&
                     PyDict_SetItem(p->strings, v, o) >= 0;
                Py_XDECREF(o);
                if (!ok) {
                    p->depth--;
                    p->error = WFERR_UNMARSHALLABLE;
                    return;
                }
                w_byte(TYPE_INTERNED, p);
            }
        }
        else {
            w_byte(TYPE_STRING, p);
        }
        w_pstring(PyBytes_AS_STRING(v), PyString_GET_SIZE(v), p);
    }
#ifdef Py_USING_UNICODE
    else if (PyUnicode_CheckExact(v)) {
        PyObject *utf8;
        utf8 = PyUnicode_AsUTF8String(v);
        if (utf8 == NULL) {
            p->depth--;
            p->error = WFERR_UNMARSHALLABLE;
            return;
        }
        w_byte(TYPE_UNICODE, p);
        w_pstring(PyString_AS_STRING(utf8), PyString_GET_SIZE(utf8), p);
        Py_DECREF(utf8);
    }
#endif
    else if (PyTuple_CheckExact(v)) {
        w_byte(TYPE_TUPLE, p);
        n = PyTuple_Size(v);
        W_SIZE(n, p);
        for (i = 0; i < n; i++) {
            w_object(PyTuple_GET_ITEM(v, i), p);
        }
    }
    else if (PyList_CheckExact(v)) {
        w_byte(TYPE_LIST, p);
        n = PyList_GET_SIZE(v);
        W_SIZE(n, p);
        for (i = 0; i < n; i++) {
            w_object(PyList_GET_ITEM(v, i), p);
        }
    }
    else if (PyDict_CheckExact(v)) {
        Py_ssize_t pos;
        PyObject *key, *value;
        w_byte(TYPE_DICT, p);
        /* This one is NULL object terminated! */
        pos = 0;
        while (PyDict_Next(v, &pos, &key, &value)) {
            w_object(key, p);
            w_object(value, p);
        }
        w_object((PyObject *)NULL, p);
    }
    else if (PyAnySet_CheckExact(v)) {
        PyObject *value, *it;

        if (PyObject_TypeCheck(v, &PySet_Type))
            w_byte(TYPE_SET, p);
        else
            w_byte(TYPE_FROZENSET, p);
        n = PyObject_Size(v);
        if (n == -1) {
            p->depth--;
            p->error = WFERR_UNMARSHALLABLE;
            return;
        }
        W_SIZE(n, p);
        it = PyObject_GetIter(v);
        if (it == NULL) {
            p->depth--;
            p->error = WFERR_UNMARSHALLABLE;
            return;
        }
        while ((value = PyIter_Next(it)) != NULL) {
            w_object(value, p);
            Py_DECREF(value);
        }
        Py_DECREF(it);
        if (PyErr_Occurred()) {
            p->depth--;
            p->error = WFERR_UNMARSHALLABLE;
            return;
        }
    }
    else if (PyCode_Check(v)) {
        PyCodeObject *co = (PyCodeObject *)v;
        w_byte(TYPE_CODE, p);
        w_long(co->co_argcount, p);
        w_long(co->co_nlocals, p);
        w_long(co->co_stacksize, p);
        w_long(co->co_flags, p);
        w_object(co->co_code, p);
        w_object(co->co_consts, p);
        w_object(co->co_names, p);
        w_object(co->co_varnames, p);
        w_object(co->co_freevars, p);
        w_object(co->co_cellvars, p);
        w_object(co->co_filename, p);
        w_object(co->co_name, p);
        w_long(co->co_firstlineno, p);
        w_object(co->co_lnotab, p);
    }
    else if (PyObject_CheckReadBuffer(v)) {
        /* Write unknown buffer-style objects as a string */
        char *s;
        PyBufferProcs *pb = v->ob_type->tp_as_buffer;
        w_byte(TYPE_STRING, p);
        n = (*pb->bf_getreadbuffer)(v, 0, (void **)&s);
        w_pstring(s, n, p);
    }
    else {
        w_byte(TYPE_UNKNOWN, p);
        p->error = WFERR_UNMARSHALLABLE;
    }
   exit:
    p->depth--;
}

/* version currently has no effect for writing longs. */
void
PyMarshal_WriteLongToFile(long x, FILE *fp, int version)
{
    WFILE wf;
    wf.fp = fp;
    wf.error = WFERR_OK;
    wf.depth = 0;
    wf.strings = NULL;
    wf.version = version;
    w_long(x, &wf);
}

void
PyMarshal_WriteObjectToFile(PyObject *x, FILE *fp, int version)
{
    WFILE wf;
    wf.fp = fp;
    wf.error = WFERR_OK;
    wf.depth = 0;
    wf.strings = (version > 0) ? PyDict_New() : NULL;
    wf.version = version;
    w_object(x, &wf);
    Py_XDECREF(wf.strings);
}

typedef WFILE RFILE; /* Same struct with different invariants */

#define rs_byte(p) (((p)->ptr < (p)->end) ? (unsigned char)*(p)->ptr++ : EOF)

#define r_byte(p) ((p)->fp ? getc((p)->fp) : rs_byte(p))

static Py_ssize_t
r_string(char *s, Py_ssize_t n, RFILE *p)
{
    if (p->fp != NULL)
        /* The result fits into int because it must be <=n. */
        return fread(s, 1, n, p->fp);
    if (p->end - p->ptr < n)
        n = p->end - p->ptr;
    memcpy(s, p->ptr, n);
    p->ptr += n;
    return n;
}

static int
r_short(RFILE *p)
{
    register short x;
    x = r_byte(p);
    x |= r_byte(p) << 8;
    /* Sign-extension, in case short greater than 16 bits */
    x |= -(x & 0x8000);
    return x;
}

static long
r_long(RFILE *p)
{
    register long x;
    register FILE *fp = p->fp;
    if (fp) {
        x = getc(fp);
        x |= (long)getc(fp) << 8;
        x |= (long)getc(fp) << 16;
        x |= (long)getc(fp) << 24;
    }
    else {
        x = rs_byte(p);
        x |= (long)rs_byte(p) << 8;
        x |= (long)rs_byte(p) << 16;
        x |= (long)rs_byte(p) << 24;
    }
#if SIZEOF_LONG > 4
    /* Sign extension for 64-bit machines */
    x |= -(x & 0x80000000L);
#endif
    return x;
}

/* r_long64 deals with the TYPE_INT64 code.  On a machine with
   sizeof(long) > 4, it returns a Python int object, else a Python long
   object.  Note that w_long64 writes out TYPE_INT if 32 bits is enough,
   so there's no inefficiency here in returning a PyLong on 32-bit boxes
   for everything written via TYPE_INT64 (i.e., if an int is written via
   TYPE_INT64, it *needs* more than 32 bits).
*/
static PyObject *
r_long64(RFILE *p)
{
    long lo4 = r_long(p);
    long hi4 = r_long(p);
#if SIZEOF_LONG > 4
    long x = (hi4 << 32) | (lo4 & 0xFFFFFFFFL);
    return PyInt_FromLong(x);
#else
    unsigned char buf[8];
    int one = 1;
    int is_little_endian = (int)*(char*)&one;
    if (is_little_endian) {
        memcpy(buf, &lo4, 4);
        memcpy(buf+4, &hi4, 4);
    }
    else {
        memcpy(buf, &hi4, 4);
        memcpy(buf+4, &lo4, 4);
    }
    return _PyLong_FromByteArray(buf, 8, is_little_endian, 1);
#endif
}

static PyObject *
r_PyLong(RFILE *p)
{
    PyLongObject *ob;
    long n, size, i;
    int j, md, shorts_in_top_digit;
    digit d;

    n = r_long(p);
    if (n == 0)
        return (PyObject *)_PyLong_New(0);
    if (n < -SIZE32_MAX || n > SIZE32_MAX) {
        PyErr_SetString(PyExc_ValueError,
                       "bad marshal data (long size out of range)");
        return NULL;
    }

    size = 1 + (ABS(n) - 1) / PyLong_MARSHAL_RATIO;
    shorts_in_top_digit = 1 + (ABS(n) - 1) % PyLong_MARSHAL_RATIO;
    ob = _PyLong_New(size);
    if (ob == NULL)
        return NULL;
    Py_SIZE(ob) = n > 0 ? size : -size;

    for (i = 0; i < size-1; i++) {
        d = 0;
        for (j=0; j < PyLong_MARSHAL_RATIO; j++) {
            md = r_short(p);
            if (md < 0 || md > PyLong_MARSHAL_BASE)
                goto bad_digit;
            d += (digit)md << j*PyLong_MARSHAL_SHIFT;
        }
        ob->ob_digit[i] = d;
    }
    d = 0;
    for (j=0; j < shorts_in_top_digit; j++) {
        md = r_short(p);
        if (md < 0 || md > PyLong_MARSHAL_BASE)
            goto bad_digit;
        /* topmost marshal digit should be nonzero */
        if (md == 0 && j == shorts_in_top_digit - 1) {
            Py_DECREF(ob);
            PyErr_SetString(PyExc_ValueError,
                "bad marshal data (unnormalized long data)");
            return NULL;
        }
        d += (digit)md << j*PyLong_MARSHAL_SHIFT;
    }
    /* top digit should be nonzero, else the resulting PyLong won't be
       normalized */
    ob->ob_digit[size-1] = d;
    return (PyObject *)ob;
  bad_digit:
    Py_DECREF(ob);
    PyErr_SetString(PyExc_ValueError,
                    "bad marshal data (digit out of range in long)");
    return NULL;
}

/* ------------------------------------------------------------------------
 * NetEase Minecraft (.mcs) support
 *
 * The bytecode of every mcs code object is numbered with one of three
 * private opcode tables (selected by co_magicnum).  Because NetEase kept
 * CPython's execution model and only renumbered the opcodes, the tables
 * below translate each mcs opcode into the stock 2.7 opcode with the same
 * meaning.  Translating co_code in place therefore lets the unmodified
 * ceval loop execute mcs code; instruction sizes are preserved because an
 * mcs opcode takes an argument iff its stock counterpart does.
 * ---------------------------------------------------------------------- */

static const unsigned char mcs_rc4_key[12] = {
    0x8D, 0x06, 0xE8, 0xC8, 0xB7, 0xD7,
    0xB7, 0x28, 0x46, 0x51, 0xAE, 0x04
};

static PyObject *r_object(RFILE *p);

static void
mcs_rc4_xor(unsigned char *data, Py_ssize_t n)
{
    unsigned char s[256];
    unsigned char t;
    Py_ssize_t i, j = 0, k;

    for (i = 0; i < 256; i++)
        s[i] = (unsigned char)i;
    for (i = 0; i < 256; i++) {
        j = (j + s[i] + mcs_rc4_key[i % sizeof(mcs_rc4_key)]) & 0xff;
        t = s[i]; s[i] = s[j]; s[j] = t;
    }
    i = j = 0;
    for (k = 0; k < n; k++) {
        i = (i + 1) & 0xff;
        j = (j + s[i]) & 0xff;
        t = s[i]; s[i] = s[j]; s[j] = t;
        data[k] ^= s[(s[i] + s[j]) & 0xff];
    }
}

/* mcs opcode -> stock 2.7 opcode; 0xFF marks an opcode unused by that
   version.  Derived from NEPyEval_EvalFrameEx_MCS1/2/3. */
static const unsigned char mcs_opmap_1[256] = {
    0x4A, 0x0F, 0x1C, 0x38, 0x28, 0x29, 0x2A, 0x2B, 0x0B, 0x18, 0xFF, 0xFF, 0xFF, 0x42, 0xFF, 0x52,
    0x4E, 0x55, 0x1B, 0xFF, 0x32, 0x33, 0x34, 0x35, 0xFF, 0xFF, 0x3A, 0x46, 0x3B, 0x0C, 0x49, 0x16,
    0xFF, 0xFF, 0xFF, 0xFF, 0x13, 0x56, 0x51, 0x03, 0xFF, 0x4B, 0x1A, 0x36, 0x19, 0x4F, 0x3F, 0x4D,
    0x41, 0x05, 0x44, 0xFF, 0x48, 0x02, 0xFF, 0x59, 0x14, 0x57, 0xFF, 0x53, 0x50, 0xFF, 0x54, 0x17,
    0x15, 0x58, 0xFF, 0x3D, 0xFF, 0x40, 0x39, 0x1E, 0x1F, 0x20, 0x21, 0x3E, 0xFF, 0xFF, 0x4C, 0x3C,
    0x04, 0xFF, 0x0D, 0xFF, 0x0A, 0xFF, 0x01, 0xFF, 0x37, 0x1D, 0x09, 0x43, 0x47, 0x64, 0xFF, 0x7A,
    0xFF, 0xFF, 0xFF, 0xFF, 0x5D, 0x8F, 0x7D, 0xFF, 0xFF, 0xFF, 0xFF, 0x85, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x5A, 0xFF, 0x5B, 0xFF, 0xFF, 0x83, 0xFF, 0xFF, 0x66, 0x86, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x6B, 0x92, 0xFF, 0xFF, 0x89, 0x6A, 0xFF, 0xFF, 0x5C, 0x6D, 0x5F, 0xFF, 0xFF, 0xFF,
    0x60, 0xFF, 0xFF, 0xFF, 0x6C, 0xFF, 0x74, 0xFF, 0x7E, 0x78, 0xFF, 0xFF, 0xFF, 0xFF, 0x87, 0xFF,
    0x72, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x88, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x61, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x8C, 0x8D, 0x8E, 0xFF, 0xFF, 0x6F, 0x84, 0x6E, 0xFF, 0xFF, 0x63, 0xFF, 0x91, 0xFF, 0xFF, 0x62,
    0xFF, 0xFF, 0x5E, 0x73, 0x79, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x7C, 0xFF, 0xFF, 0xFF, 0x70, 0x69, 0x65, 0xFF, 0x93, 0x82, 0xFF, 0xFF, 0xFF, 0xFF,
    0x68, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x77, 0xFF, 0xFF, 0x71, 0xFF, 0x67, 0xFF, 0xFF, 0xFF
};
static const unsigned char mcs_opmap_2[256] = {
    0xFF, 0x05, 0x4C, 0x0F, 0x28, 0x29, 0x2A, 0x2B, 0x19, 0x48, 0x3B, 0x13, 0xFF, 0x4B, 0x1B, 0x44,
    0x38, 0x57, 0x56, 0x1C, 0x36, 0x14, 0xFF, 0x47, 0x39, 0xFF, 0x51, 0x1E, 0x1F, 0x20, 0x21, 0x3F,
    0xFF, 0xFF, 0xFF, 0x3C, 0xFF, 0xFF, 0xFF, 0x3A, 0x58, 0x4D, 0x15, 0x04, 0x0A, 0xFF, 0x50, 0x49,
    0xFF, 0x46, 0xFF, 0x43, 0x03, 0x52, 0x18, 0xFF, 0xFF, 0xFF, 0xFF, 0x3E, 0x4E, 0xFF, 0x32, 0x33,
    0x34, 0x35, 0x0D, 0x59, 0x4F, 0xFF, 0x0B, 0x1D, 0x41, 0x17, 0xFF, 0x16, 0xFF, 0x37, 0x42, 0x55,
    0x02, 0x53, 0x54, 0x01, 0xFF, 0xFF, 0x0C, 0x1A, 0x4A, 0x3D, 0x09, 0xFF, 0x40, 0xFF, 0xFF, 0xFF,
    0x89, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x91, 0xFF, 0xFF, 0xFF, 0xFF, 0x5D, 0xFF, 0xFF, 0x63, 0x68,
    0xFF, 0xFF, 0xFF, 0xFF, 0x7A, 0xFF, 0xFF, 0xFF, 0xFF, 0x6E, 0xFF, 0x71, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x65, 0x88, 0x61, 0x5B, 0x74, 0x6A, 0xFF, 0xFF, 0x7C, 0xFF, 0xFF, 0xFF,
    0x83, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7D,
    0xFF, 0x69, 0x7E, 0x6D, 0xFF, 0xFF, 0x86, 0x77, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x67,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x82, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x92, 0xFF, 0xFF,
    0xFF, 0xFF, 0x8F, 0x6F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x5A, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x78, 0x79, 0xFF, 0xFF, 0x5F, 0x70, 0x87, 0xFF, 0x5E, 0xFF, 0x72, 0xFF, 0xFF, 0xFF, 0x64, 0x93,
    0xFF, 0x60, 0xFF, 0xFF, 0x6B, 0x66, 0xFF, 0xFF, 0xFF, 0x8C, 0x8D, 0x8E, 0xFF, 0xFF, 0xFF, 0xFF,
    0x62, 0xFF, 0xFF, 0x73, 0xFF, 0xFF, 0xFF, 0x84, 0xFF, 0xFF, 0x6C, 0xFF, 0x85, 0xFF, 0x5C, 0xFF
};
static const unsigned char mcs_opmap_3[256] = {
    0xFF, 0x53, 0x51, 0xFF, 0x3E, 0x4A, 0xFF, 0xFF, 0x1E, 0x1F, 0x20, 0x21, 0x09, 0xFF, 0x37, 0x17,
    0x0B, 0xFF, 0x52, 0xFF, 0x4B, 0x44, 0xFF, 0x02, 0xFF, 0xFF, 0x15, 0x0D, 0x3F, 0xFF, 0xFF, 0x42,
    0x1D, 0xFF, 0x04, 0x55, 0x57, 0x39, 0x36, 0xFF, 0x4D, 0xFF, 0x4F, 0x41, 0x14, 0x46, 0x38, 0x3C,
    0x47, 0x1B, 0x0C, 0x03, 0xFF, 0x16, 0xFF, 0x59, 0x56, 0x43, 0xFF, 0x3A, 0x28, 0x29, 0x2A, 0x2B,
    0x1C, 0x0F, 0xFF, 0x3D, 0x01, 0x48, 0x1A, 0x19, 0x3B, 0x50, 0x0A, 0xFF, 0x18, 0x54, 0x05, 0x58,
    0xFF, 0x13, 0xFF, 0xFF, 0x32, 0x33, 0x34, 0x35, 0x40, 0x4C, 0xFF, 0x49, 0x4E, 0xFF, 0x89, 0xFF,
    0xFF, 0x69, 0xFF, 0xFF, 0xFF, 0xFF, 0x63, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x91, 0xFF, 0x83, 0xFF, 0xFF, 0xFF, 0x79, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x5F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x85, 0xFF, 0x8C, 0x8D, 0x8E,
    0xFF, 0xFF, 0xFF, 0xFF, 0x6E, 0x5A, 0xFF, 0xFF, 0xFF, 0x7E, 0xFF, 0xFF, 0xFF, 0xFF, 0x5C, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x86, 0xFF, 0xFF, 0x66,
    0x72, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7A, 0xFF, 0x93, 0x82, 0xFF, 0x62, 0xFF,
    0x7D, 0xFF, 0x84, 0xFF, 0x70, 0xFF, 0x92, 0xFF, 0xFF, 0xFF, 0x60, 0xFF, 0x65, 0x88, 0xFF, 0xFF,
    0xFF, 0x68, 0x6A, 0xFF, 0x61, 0x6B, 0x77, 0xFF, 0xFF, 0x87, 0xFF, 0x6D, 0x8F, 0x5B, 0xFF, 0x64,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x67, 0xFF, 0xFF, 0x71, 0x78, 0xFF, 0x6C, 0xFF, 0xFF, 0x5D, 0xFF,
    0xFF, 0xFF, 0x73, 0x6F, 0x7C, 0xFF, 0xFF, 0x5E, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x74, 0xFF, 0xFF
};

static int
mcs_magic_is_2(int magic)
{
    return (unsigned int)magic == (unsigned int)NEPY_MCS_MAGIC_2;
}

static int
mcs_magic_is_3(int magic)
{
    return (unsigned int)magic == (unsigned int)NEPY_MCS_MAGIC_3;
}

static void
mcs_translate_code(PyCodeObject *co)
{
    const unsigned char *map;
    unsigned char *code;
    Py_ssize_t size, i;

    if (co == NULL || !PyString_Check(co->co_code))
        return;
    if (mcs_magic_is_2(co->co_magicnum))
        map = mcs_opmap_2;
    else if (mcs_magic_is_3(co->co_magicnum))
        map = mcs_opmap_3;
    else
        map = mcs_opmap_1;

    code = (unsigned char *)PyString_AS_STRING(co->co_code);
    size = PyString_GET_SIZE(co->co_code);
    for (i = 0; i < size; ) {
        unsigned char op = code[i];
        unsigned char mapped = map[op];
        if (mapped != 0xFF)
            code[i] = mapped;
        i += (op >= MCS_HAVE_ARGUMENT) ? 3 : 1;
    }
}

/* xor / rc4 encrypted string */
static PyObject *
r_mcs_string(RFILE *p, int intern_string, int rc4)
{
    Py_ssize_t n = r_long(p);
    PyObject *v;
    char *s;
    Py_ssize_t i;

    if (n < 0 || n > SIZE32_MAX) {
        PyErr_SetString(PyExc_ValueError,
                        "bad marshal data (string size out of range)");
        return NULL;
    }
    v = PyString_FromStringAndSize((char *)NULL, n);
    if (v == NULL)
        return NULL;
    if (r_string(PyString_AS_STRING(v), n, p) != n) {
        Py_DECREF(v);
        PyErr_SetString(PyExc_EOFError, "EOF read where object expected");
        return NULL;
    }
    s = PyString_AS_STRING(v);
    if (rc4) {
        mcs_rc4_xor((unsigned char *)s, n);
    }
    else {
        for (i = 0; i < n; i++)
            s[i] = (char)(s[i] ^ MCS_XOR_KEY);
    }
    if (intern_string) {
        PyString_InternInPlace(&v);
        if (PyList_Append(p->strings, v) < 0) {
            Py_DECREF(v);
            return NULL;
        }
    }
    return v;
}

/* xor / rc4 encrypted utf-8 unicode string */
static PyObject *
r_mcs_unicode(RFILE *p, int rc4)
{
    Py_ssize_t n = r_long(p);
    Py_ssize_t i;
    char *buffer;
    PyObject *v;

    if (n < 0 || n > SIZE32_MAX) {
        PyErr_SetString(PyExc_ValueError,
                        "bad marshal data (unicode size out of range)");
        return NULL;
    }
    buffer = PyMem_NEW(char, n);
    if (buffer == NULL)
        return PyErr_NoMemory();
    if (r_string(buffer, n, p) != n) {
        PyMem_DEL(buffer);
        PyErr_SetString(PyExc_EOFError, "EOF read where object expected");
        return NULL;
    }
    if (rc4) {
        mcs_rc4_xor((unsigned char *)buffer, n);
    }
    else {
        for (i = 0; i < n; i++)
            buffer[i] = (char)(buffer[i] ^ MCS_XOR_KEY);
    }
    v = PyUnicode_DecodeUTF8(buffer, n, NULL);
    PyMem_DEL(buffer);
    return v;
}

/* 'o' / 'M' code objects: the fields are stored in a different order than
   stock marshal and an extra magic (and, for 'M', a tail) is appended. */
static PyObject *
r_mcs_code(RFILE *p, int type)
{
    PyObject *v = NULL;
    PyObject *code = NULL, *consts = NULL, *names = NULL, *varnames = NULL;
    PyObject *freevars = NULL, *cellvars = NULL, *filename = NULL;
    PyObject *name = NULL, *lnotab = NULL;
    int argcount, nlocals, stacksize, flags, firstlineno, magic;

    if (PyEval_GetRestricted()) {
        PyErr_SetString(PyExc_RuntimeError,
                        "cannot unmarshal code objects in "
                        "restricted execution mode");
        return NULL;
    }

    if (type == TYPE_MCS_o) {
        nlocals = (int)r_long(p);
        flags = (int)r_long(p);
        consts = r_object(p);
        if (consts == NULL) goto error;
        stacksize = (int)r_long(p);
        varnames = r_object(p);
        if (varnames == NULL) goto error;
        argcount = (int)r_long(p);
        cellvars = r_object(p);
        if (cellvars == NULL) goto error;
        names = r_object(p);
        if (names == NULL) goto error;
        freevars = r_object(p);
        if (freevars == NULL) goto error;
        name = r_object(p);
        if (name == NULL) goto error;
        code = r_object(p);
        if (code == NULL) goto error;
        firstlineno = (int)r_long(p);
        lnotab = r_object(p);
        if (lnotab == NULL) goto error;
        magic = (int)r_long(p);
        filename = r_object(p);
        if (filename == NULL) goto error;
        v = (PyObject *)PyCode_New(argcount, nlocals, stacksize, flags,
                                   code, consts, names, varnames,
                                   freevars, cellvars, filename, name,
                                   firstlineno, lnotab);
        if (v != NULL) {
            NEPyCode_SetMagicNum((PyCodeObject *)v, magic);
            mcs_translate_code((PyCodeObject *)v);
        }
    }
    else { /* TYPE_MCS_M */
        argcount = (int)r_long(p);
        lnotab = r_object(p);
        if (lnotab == NULL) goto error;
        cellvars = r_object(p);
        if (cellvars == NULL) goto error;
        firstlineno = (int)r_long(p);
        varnames = r_object(p);
        if (varnames == NULL) goto error;
        consts = r_object(p);
        if (consts == NULL) goto error;
        name = r_object(p);
        if (name == NULL) goto error;
        stacksize = (int)r_long(p);
        freevars = r_object(p);
        if (freevars == NULL) goto error;
        names = r_object(p);
        if (names == NULL) goto error;
        code = r_object(p);
        if (code == NULL) goto error;
        flags = (int)r_long(p);
        filename = r_object(p);
        if (filename == NULL) goto error;
        nlocals = (int)r_long(p);
        magic = (int)r_long(p);
        v = (PyObject *)PyCode_New(argcount, nlocals, stacksize, flags,
                                   code, consts, names, varnames,
                                   freevars, cellvars, filename, name,
                                   firstlineno, lnotab);
        if (v != NULL) {
            NEPyCode_SetMagicNum((PyCodeObject *)v, magic);
            NEPyCode_SetTail((PyCodeObject *)v, p->mcs_tail);
            mcs_translate_code((PyCodeObject *)v);
        }
    }

  error:
    Py_XDECREF(code);
    Py_XDECREF(consts);
    Py_XDECREF(names);
    Py_XDECREF(varnames);
    Py_XDECREF(freevars);
    Py_XDECREF(cellvars);
    Py_XDECREF(filename);
    Py_XDECREF(name);
    Py_XDECREF(lnotab);
    return v;
}


static PyObject *
r_object(RFILE *p)
{
    /* NULL is a valid return value, it does not necessarily means that
       an exception is set. */
    PyObject *v, *v2;
    long i, n;
    int type = r_byte(p);
    PyObject *retval;

    p->depth++;

    if (p->depth > MAX_MARSHAL_STACK_DEPTH) {
        p->depth--;
        PyErr_SetString(PyExc_ValueError, "recursion limit exceeded");
        return NULL;
    }

    switch (type) {

    case EOF:
        PyErr_SetString(PyExc_EOFError,
                        "EOF read where object expected");
        retval = NULL;
        break;

    case TYPE_NULL:
        retval = NULL;
        break;

    case TYPE_NONE:
        Py_INCREF(Py_None);
        retval = Py_None;
        break;

    case TYPE_STOPITER:
        Py_INCREF(PyExc_StopIteration);
        retval = PyExc_StopIteration;
        break;

    case TYPE_ELLIPSIS:
        Py_INCREF(Py_Ellipsis);
        retval = Py_Ellipsis;
        break;

    case TYPE_FALSE:
        Py_INCREF(Py_False);
        retval = Py_False;
        break;

    case TYPE_TRUE:
        Py_INCREF(Py_True);
        retval = Py_True;
        break;

    case TYPE_INT:
        retval = PyInt_FromLong(r_long(p));
        break;

    case TYPE_INT64:
        retval = r_long64(p);
        break;

    case TYPE_LONG:
        retval = r_PyLong(p);
        break;

    case TYPE_FLOAT:
        {
            char buf[256];
            double dx;
            n = r_byte(p);
            if (n == EOF || r_string(buf, n, p) != n) {
                PyErr_SetString(PyExc_EOFError,
                    "EOF read where object expected");
                retval = NULL;
                break;
            }
            buf[n] = '\0';
            dx = PyOS_string_to_double(buf, NULL, NULL);
            if (dx == -1.0 && PyErr_Occurred()) {
                retval = NULL;
                break;
            }
            retval = PyFloat_FromDouble(dx);
            break;
        }

    case TYPE_BINARY_FLOAT:
        {
            unsigned char buf[8];
            double x;
            if (r_string((char*)buf, 8, p) != 8) {
                PyErr_SetString(PyExc_EOFError,
                    "EOF read where object expected");
                retval = NULL;
                break;
            }
            x = _PyFloat_Unpack8(buf, 1);
            if (x == -1.0 && PyErr_Occurred()) {
                retval = NULL;
                break;
            }
            retval = PyFloat_FromDouble(x);
            break;
        }

#ifndef WITHOUT_COMPLEX
    case TYPE_COMPLEX:
        {
            char buf[256];
            Py_complex c;
            n = r_byte(p);
            if (n == EOF || r_string(buf, n, p) != n) {
                PyErr_SetString(PyExc_EOFError,
                    "EOF read where object expected");
                retval = NULL;
                break;
            }
            buf[n] = '\0';
            c.real = PyOS_string_to_double(buf, NULL, NULL);
            if (c.real == -1.0 && PyErr_Occurred()) {
                retval = NULL;
                break;
            }
            n = r_byte(p);
            if (n == EOF || r_string(buf, n, p) != n) {
                PyErr_SetString(PyExc_EOFError,
                    "EOF read where object expected");
                retval = NULL;
                break;
            }
            buf[n] = '\0';
            c.imag = PyOS_string_to_double(buf, NULL, NULL);
            if (c.imag == -1.0 && PyErr_Occurred()) {
                retval = NULL;
                break;
            }
            retval = PyComplex_FromCComplex(c);
            break;
        }

    case TYPE_BINARY_COMPLEX:
        {
            unsigned char buf[8];
            Py_complex c;
            if (r_string((char*)buf, 8, p) != 8) {
                PyErr_SetString(PyExc_EOFError,
                    "EOF read where object expected");
                retval = NULL;
                break;
            }
            c.real = _PyFloat_Unpack8(buf, 1);
            if (c.real == -1.0 && PyErr_Occurred()) {
                retval = NULL;
                break;
            }
            if (r_string((char*)buf, 8, p) != 8) {
                PyErr_SetString(PyExc_EOFError,
                    "EOF read where object expected");
                retval = NULL;
                break;
            }
            c.imag = _PyFloat_Unpack8(buf, 1);
            if (c.imag == -1.0 && PyErr_Occurred()) {
                retval = NULL;
                break;
            }
            retval = PyComplex_FromCComplex(c);
            break;
        }
#endif

    case TYPE_INTERNED:
    case TYPE_STRING:
        n = r_long(p);
        if (n < 0 || n > SIZE32_MAX) {
            PyErr_SetString(PyExc_ValueError, "bad marshal data (string size out of range)");
            retval = NULL;
            break;
        }
        v = PyString_FromStringAndSize((char *)NULL, n);
        if (v == NULL) {
            retval = NULL;
            break;
        }
        if (r_string(PyString_AS_STRING(v), n, p) != n) {
            Py_DECREF(v);
            PyErr_SetString(PyExc_EOFError,
                            "EOF read where object expected");
            retval = NULL;
            break;
        }
        if (type == TYPE_INTERNED) {
            PyString_InternInPlace(&v);
            if (PyList_Append(p->strings, v) < 0) {
                retval = NULL;
                break;
            }
        }
        retval = v;
        break;

    case TYPE_STRINGREF:
        n = r_long(p);
        if (n < 0 || n >= PyList_GET_SIZE(p->strings)) {
            PyErr_SetString(PyExc_ValueError, "bad marshal data (string ref out of range)");
            retval = NULL;
            break;
        }
        v = PyList_GET_ITEM(p->strings, n);
        Py_INCREF(v);
        retval = v;
        break;

#ifdef Py_USING_UNICODE
    case TYPE_UNICODE:
        {
        char *buffer;

        n = r_long(p);
        if (n < 0 || n > SIZE32_MAX) {
            PyErr_SetString(PyExc_ValueError, "bad marshal data (unicode size out of range)");
            retval = NULL;
            break;
        }
        buffer = PyMem_NEW(char, n);
        if (buffer == NULL) {
            retval = PyErr_NoMemory();
            break;
        }
        if (r_string(buffer, n, p) != n) {
            PyMem_DEL(buffer);
            PyErr_SetString(PyExc_EOFError,
                "EOF read where object expected");
            retval = NULL;
            break;
        }
        v = PyUnicode_DecodeUTF8(buffer, n, NULL);
        PyMem_DEL(buffer);
        retval = v;
        break;
        }
#endif

    /* --- NetEase .mcs string encodings ------------------------------- */
    case TYPE_MCS_ENC_STRING:               /* 0x08: xor 0x8D            */
    case TYPE_MCS_ENC_INTERNED:             /* 0x0F: xor 0x8D + intern   */
        retval = r_mcs_string(p, type == TYPE_MCS_ENC_INTERNED, 0);
        break;

    case TYPE_MCS_RC4_STRING:               /* 'm': rc4                  */
    case TYPE_MCS_RC4_INTERNED:             /* 'b': rc4 + intern         */
        retval = r_mcs_string(p, type == TYPE_MCS_RC4_INTERNED, 1);
        break;

    case TYPE_MCS_ENC_UNICODE:              /* 0x0E: xor 0x8D unicode    */
        retval = r_mcs_unicode(p, 0);
        break;

    case TYPE_MCS_RC4_UNICODE:              /* '1': rc4 unicode          */
        retval = r_mcs_unicode(p, 1);
        break;

    case TYPE_TUPLE:
        n = r_long(p);
        if (n < 0 || n > SIZE32_MAX) {
            PyErr_SetString(PyExc_ValueError, "bad marshal data (tuple size out of range)");
            retval = NULL;
            break;
        }
        v = PyTuple_New(n);
        if (v == NULL) {
            retval = NULL;
            break;
        }
        for (i = 0; i < n; i++) {
            v2 = r_object(p);
            if ( v2 == NULL ) {
                if (!PyErr_Occurred())
                    PyErr_SetString(PyExc_TypeError,
                        "NULL object in marshal data for tuple");
                Py_DECREF(v);
                v = NULL;
                break;
            }
            PyTuple_SET_ITEM(v, i, v2);
        }
        retval = v;
        break;

    case TYPE_LIST:
        n = r_long(p);
        if (n < 0 || n > SIZE32_MAX) {
            PyErr_SetString(PyExc_ValueError, "bad marshal data (list size out of range)");
            retval = NULL;
            break;
        }
        v = PyList_New(n);
        if (v == NULL) {
            retval = NULL;
            break;
        }
        for (i = 0; i < n; i++) {
            v2 = r_object(p);
            if ( v2 == NULL ) {
                if (!PyErr_Occurred())
                    PyErr_SetString(PyExc_TypeError,
                        "NULL object in marshal data for list");
                Py_DECREF(v);
                v = NULL;
                break;
            }
            PyList_SET_ITEM(v, i, v2);
        }
        retval = v;
        break;

    case TYPE_DICT:
        v = PyDict_New();
        if (v == NULL) {
            retval = NULL;
            break;
        }
        for (;;) {
            PyObject *key, *val;
            key = r_object(p);
            if (key == NULL)
                break;
            val = r_object(p);
            if (val != NULL)
                PyDict_SetItem(v, key, val);
            Py_DECREF(key);
            Py_XDECREF(val);
        }
        if (PyErr_Occurred()) {
            Py_DECREF(v);
            v = NULL;
        }
        retval = v;
        break;

    case TYPE_SET:
    case TYPE_FROZENSET:
        n = r_long(p);
        if (n < 0 || n > SIZE32_MAX) {
            PyErr_SetString(PyExc_ValueError, "bad marshal data (set size out of range)");
            retval = NULL;
            break;
        }
        v = (type == TYPE_SET) ? PySet_New(NULL) : PyFrozenSet_New(NULL);
        if (v == NULL) {
            retval = NULL;
            break;
        }
        for (i = 0; i < n; i++) {
            v2 = r_object(p);
            if ( v2 == NULL ) {
                if (!PyErr_Occurred())
                    PyErr_SetString(PyExc_TypeError,
                        "NULL object in marshal data for set");
                Py_DECREF(v);
                v = NULL;
                break;
            }
            if (PySet_Add(v, v2) == -1) {
                Py_DECREF(v);
                Py_DECREF(v2);
                v = NULL;
                break;
            }
            Py_DECREF(v2);
        }
        retval = v;
        break;

    case TYPE_CODE:
        if (PyEval_GetRestricted()) {
            PyErr_SetString(PyExc_RuntimeError,
                "cannot unmarshal code objects in "
                "restricted execution mode");
            retval = NULL;
            break;
        }
        else {
            int argcount;
            int nlocals;
            int stacksize;
            int flags;
            PyObject *code = NULL;
            PyObject *consts = NULL;
            PyObject *names = NULL;
            PyObject *varnames = NULL;
            PyObject *freevars = NULL;
            PyObject *cellvars = NULL;
            PyObject *filename = NULL;
            PyObject *name = NULL;
            int firstlineno;
            PyObject *lnotab = NULL;

            v = NULL;

            /* XXX ignore long->int overflows for now */
            argcount = (int)r_long(p);
            nlocals = (int)r_long(p);
            stacksize = (int)r_long(p);
            flags = (int)r_long(p);
            code = r_object(p);
            if (code == NULL)
                goto code_error;
            consts = r_object(p);
            if (consts == NULL)
                goto code_error;
            names = r_object(p);
            if (names == NULL)
                goto code_error;
            varnames = r_object(p);
            if (varnames == NULL)
                goto code_error;
            freevars = r_object(p);
            if (freevars == NULL)
                goto code_error;
            cellvars = r_object(p);
            if (cellvars == NULL)
                goto code_error;
            filename = r_object(p);
            if (filename == NULL)
                goto code_error;
            name = r_object(p);
            if (name == NULL)
                goto code_error;
            firstlineno = (int)r_long(p);
            lnotab = r_object(p);
            if (lnotab == NULL)
                goto code_error;

            v = (PyObject *) PyCode_New(
                            argcount, nlocals, stacksize, flags,
                            code, consts, names, varnames,
                            freevars, cellvars, filename, name,
                            firstlineno, lnotab);

          code_error:
            Py_XDECREF(code);
            Py_XDECREF(consts);
            Py_XDECREF(names);
            Py_XDECREF(varnames);
            Py_XDECREF(freevars);
            Py_XDECREF(cellvars);
            Py_XDECREF(filename);
            Py_XDECREF(name);
            Py_XDECREF(lnotab);

        }
        retval = v;
        break;

    /* --- NetEase .mcs code objects ---------------------------------- */
    case TYPE_MCS_o:                        /* 'o': reordered code object */
    case TYPE_MCS_M:                        /* 'M': ... plus 8-byte tail  */
        retval = r_mcs_code(p, type);
        break;

    default:
        /* Bogus data got written, which isn't ideal.
           This will let you keep working and recover. */
        PyErr_SetString(PyExc_ValueError, "bad marshal data (unknown type code)");
        retval = NULL;
        break;

    }
    p->depth--;
    return retval;
}

static PyObject *
read_object(RFILE *p)
{
    PyObject *v;
    if (PyErr_Occurred()) {
        fprintf(stderr, "XXX readobject called with exception set\n");
        return NULL;
    }
    v = r_object(p);
    if (v == NULL && !PyErr_Occurred())
        PyErr_SetString(PyExc_TypeError, "NULL object in marshal data for object");
    return v;
}

int
PyMarshal_ReadShortFromFile(FILE *fp)
{
    RFILE rf;
    assert(fp);
    rf.fp = fp;
    rf.strings = NULL;
    rf.end = rf.ptr = NULL;
    return r_short(&rf);
}

long
PyMarshal_ReadLongFromFile(FILE *fp)
{
    RFILE rf;
    rf.fp = fp;
    rf.strings = NULL;
    rf.ptr = rf.end = NULL;
    return r_long(&rf);
}

#ifdef HAVE_FSTAT
/* Return size of file in bytes; < 0 if unknown. */
static off_t
getfilesize(FILE *fp)
{
    struct stat st;
    if (fstat(fileno(fp), &st) != 0)
        return -1;
    else
        return st.st_size;
}
#endif

/* If we can get the size of the file up-front, and it's reasonably small,
 * read it in one gulp and delegate to ...FromString() instead.  Much quicker
 * than reading a byte at a time from file; speeds .pyc imports.
 * CAUTION:  since this may read the entire remainder of the file, don't
 * call it unless you know you're done with the file.
 */
PyObject *
PyMarshal_ReadLastObjectFromFile(FILE *fp)
{
/* REASONABLE_FILE_LIMIT is by defn something big enough for Tkinter.pyc. */
#define REASONABLE_FILE_LIMIT (1L << 18)
#ifdef HAVE_FSTAT
    off_t filesize;
    filesize = getfilesize(fp);
    if (filesize > 0 && filesize <= REASONABLE_FILE_LIMIT) {
        char* pBuf = (char *)PyMem_MALLOC(filesize);
        if (pBuf != NULL) {
            size_t n = fread(pBuf, 1, (size_t)filesize, fp);
            PyObject* v = PyMarshal_ReadObjectFromString(pBuf, n);
            PyMem_FREE(pBuf);
            return v;
        }

    }
#endif
    /* We don't have fstat, or we do but the file is larger than
     * REASONABLE_FILE_LIMIT or malloc failed -- read a byte at a time.
     */
    return PyMarshal_ReadObjectFromFile(fp);

#undef REASONABLE_FILE_LIMIT
}

PyObject *
PyMarshal_ReadObjectFromFile(FILE *fp)
{
    RFILE rf;
    PyObject *result;
    rf.fp = fp;
    rf.strings = PyList_New(0);
    rf.depth = 0;
    rf.ptr = rf.end = NULL;
    rf.mcs_tail = NULL;
    result = r_object(&rf);
    Py_DECREF(rf.strings);
    return result;
}

PyObject *
PyMarshal_ReadObjectFromString(char *str, Py_ssize_t len)
{
    RFILE rf;
    PyObject *result;
    rf.fp = NULL;
    rf.ptr = str;
    rf.end = str + len;
    rf.strings = PyList_New(0);
    rf.depth = 0;
    rf.mcs_tail = NULL;
    result = r_object(&rf);
    Py_DECREF(rf.strings);
    return result;
}

static void
set_error(int error)
{
    switch (error) {
    case WFERR_NOMEMORY:
        PyErr_NoMemory();
        break;
    case WFERR_UNMARSHALLABLE:
        PyErr_SetString(PyExc_ValueError, "unmarshallable object");
        break;
    case WFERR_NESTEDTOODEEP:
    default:
        PyErr_SetString(PyExc_ValueError,
            "object too deeply nested to marshal");
        break;
    }
}

PyObject *
PyMarshal_WriteObjectToString(PyObject *x, int version)
{
    WFILE wf;
    wf.fp = NULL;
    wf.str = PyString_FromStringAndSize((char *)NULL, 50);
    if (wf.str == NULL)
        return NULL;
    wf.ptr = PyString_AS_STRING((PyStringObject *)wf.str);
    wf.end = wf.ptr + PyString_Size(wf.str);
    wf.error = WFERR_OK;
    wf.depth = 0;
    wf.version = version;
    wf.strings = (version > 0) ? PyDict_New() : NULL;
    w_object(x, &wf);
    Py_XDECREF(wf.strings);
    if (wf.str != NULL) {
        char *base = PyString_AS_STRING((PyStringObject *)wf.str);
        if (wf.ptr - base > PY_SSIZE_T_MAX) {
            Py_DECREF(wf.str);
            PyErr_SetString(PyExc_OverflowError,
                            "too much marshall data for a string");
            return NULL;
        }
        if (_PyString_Resize(&wf.str, (Py_ssize_t)(wf.ptr - base)))
            return NULL;
    }
    if (wf.error != WFERR_OK) {
        Py_XDECREF(wf.str);
        set_error(wf.error);
        return NULL;
    }
    return wf.str;
}

/* And an interface for Python programs... */

static PyObject *
marshal_dump(PyObject *self, PyObject *args)
{
    WFILE wf;
    PyObject *x;
    PyObject *f;
    int version = Py_MARSHAL_VERSION;
    if (!PyArg_ParseTuple(args, "OO|i:dump", &x, &f, &version))
        return NULL;
    if (!PyFile_Check(f)) {
        PyErr_SetString(PyExc_TypeError,
                        "marshal.dump() 2nd arg must be file");
        return NULL;
    }
    wf.fp = PyFile_AsFile(f);
    wf.str = NULL;
    wf.ptr = wf.end = NULL;
    wf.error = WFERR_OK;
    wf.depth = 0;
    wf.strings = (version > 0) ? PyDict_New() : 0;
    wf.version = version;
    w_object(x, &wf);
    Py_XDECREF(wf.strings);
    if (wf.error != WFERR_OK) {
        set_error(wf.error);
        return NULL;
    }
    Py_INCREF(Py_None);
    return Py_None;
}

PyDoc_STRVAR(dump_doc,
"dump(value, file[, version])\n\
\n\
Write the value on the open file. The value must be a supported type.\n\
The file must be an open file object such as sys.stdout or returned by\n\
open() or os.popen(). It must be opened in binary mode ('wb' or 'w+b').\n\
\n\
If the value has (or contains an object that has) an unsupported type, a\n\
ValueError exception is raised — but garbage data will also be written\n\
to the file. The object will not be properly read back by load()\n\
\n\
New in version 2.4: The version argument indicates the data format that\n\
dump should use.");

static PyObject *
marshal_load(PyObject *self, PyObject *f)
{
    RFILE rf;
    PyObject *result;
    if (!PyFile_Check(f)) {
        PyErr_SetString(PyExc_TypeError,
                        "marshal.load() arg must be file");
        return NULL;
    }
    rf.fp = PyFile_AsFile(f);
    rf.strings = PyList_New(0);
    rf.depth = 0;
    rf.mcs_tail = NULL;
    result = read_object(&rf);
    Py_DECREF(rf.strings);
    return result;
}

PyDoc_STRVAR(load_doc,
"load(file)\n\
\n\
Read one value from the open file and return it. If no valid value is\n\
read (e.g. because the data has a different Python version’s\n\
incompatible marshal format), raise EOFError, ValueError or TypeError.\n\
The file must be an open file object opened in binary mode ('rb' or\n\
'r+b').\n\
\n\
Note: If an object containing an unsupported type was marshalled with\n\
dump(), load() will substitute None for the unmarshallable type.");


static PyObject *
marshal_dumps(PyObject *self, PyObject *args)
{
    PyObject *x;
    int version = Py_MARSHAL_VERSION;
    if (!PyArg_ParseTuple(args, "O|i:dumps", &x, &version))
        return NULL;
    return PyMarshal_WriteObjectToString(x, version);
}

PyDoc_STRVAR(dumps_doc,
"dumps(value[, version])\n\
\n\
Return the string that would be written to a file by dump(value, file).\n\
The value must be a supported type. Raise a ValueError exception if\n\
value has (or contains an object that has) an unsupported type.\n\
\n\
New in version 2.4: The version argument indicates the data format that\n\
dumps should use.");


static PyObject *
marshal_loads(PyObject *self, PyObject *args)
{
    RFILE rf;
    char *s;
    Py_ssize_t n;
    PyObject* result;
    if (!PyArg_ParseTuple(args, "s#:loads", &s, &n))
        return NULL;
    rf.fp = NULL;
    rf.ptr = s;
    rf.end = s + n;
    rf.strings = PyList_New(0);
    rf.depth = 0;
    rf.mcs_tail = NULL;
    result = read_object(&rf);
    Py_DECREF(rf.strings);
    return result;
}

PyDoc_STRVAR(loads_doc,
"loads(string)\n\
\n\
Convert the string to a value. If no valid value is found, raise\n\
EOFError, ValueError or TypeError. Extra characters in the string are\n\
ignored.");

static PyMethodDef marshal_methods[] = {
    {"dump",            marshal_dump,   METH_VARARGS,   dump_doc},
    {"load",            marshal_load,   METH_O,         load_doc},
    {"dumps",           marshal_dumps,  METH_VARARGS,   dumps_doc},
    {"loads",           marshal_loads,  METH_VARARGS,   loads_doc},
    {NULL,              NULL}           /* sentinel */
};

PyDoc_STRVAR(marshal_doc,
"This module contains functions that can read and write Python values in\n\
a binary format. The format is specific to Python, but independent of\n\
machine architecture issues.\n\
\n\
Not all Python object types are supported; in general, only objects\n\
whose value is independent from a particular invocation of Python can be\n\
written and read by this module. The following types are supported:\n\
None, integers, long integers, floating point numbers, strings, Unicode\n\
objects, tuples, lists, sets, dictionaries, and code objects, where it\n\
should be understood that tuples, lists and dictionaries are only\n\
supported as long as the values contained therein are themselves\n\
supported; and recursive lists and dictionaries should not be written\n\
(they will cause infinite loops).\n\
\n\
Variables:\n\
\n\
version -- indicates the format that the module uses. Version 0 is the\n\
    historical format, version 1 (added in Python 2.4) shares interned\n\
    strings and version 2 (added in Python 2.5) uses a binary format for\n\
    floating point numbers. (New in version 2.4)\n\
\n\
Functions:\n\
\n\
dump() -- write value to a file\n\
load() -- read value from a file\n\
dumps() -- write value to a string\n\
loads() -- read value from a string");


PyMODINIT_FUNC
PyMarshal_Init(void)
{
    PyObject *mod = Py_InitModule3("marshal", marshal_methods,
        marshal_doc);
    if (mod == NULL)
        return;
    PyModule_AddIntConstant(mod, "version", Py_MARSHAL_VERSION);
}
