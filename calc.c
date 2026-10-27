// Ali Aliyev 251ADB254
// https://github.com/ALIEV772/calc-lab-home
// Compile with: gcc -O2 -Wall -Wextra -std=c17 -o calc calc.c -lm
// Resources used: GEMINI (AI) :  Prompt "what to do" with lab instructions to get a project roadmap and structural skeleton
// Claude (AI) : used for fixing logical and unsual errors in the code, and for code review and suggestions

#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <errno.h>
#include <dirent.h>
#include <sys/stat.h>


#define STU_NAME     "ali"
#define STU_LASTNAME "aliyev"
#define STU_ID       "251ADB254"

static char *buf, *end, *p;   /* whole file, its end, current parse position */
static int failed;            /* set once the first error is found */
static long err_pos;          /* 1-based position of that first error */

/* Stack used to evaluate ** chains: value, start of operand, position of the ** before it */
static long long *pv;
static long *ps, *po;
static size_t psp, pcap;
/*Output text collected in memory; only written to disk if there was no error*/
static char *out;
static size_t out_len, out_cap;

#define POS(q) ((long)((q) - buf + 1)) /*pointer -> 1-based file position */
#define IS_DIGIT(c) ((c) >= '0' && (c) <= '9')

/* realloc that exits cleanly when memory runs out */
static void *xrealloc(void *q, size_t n) {
    void *r = realloc(q, n ? n : 1);
    if (!r) {
        fprintf(stderr, "calc:Out of memory\n");
        exit(1);
    }
    return r;
}

/* Remember only the FIRST error; later ones are ignored */
static void fail(long pos) {
    if (!failed) {
        failed = 1;
        err_pos = pos;
    }
}

static void skipws(void) {
    while (*p == ' ' || *p == '\t') p++;
}

static void push(long long v, long start, long op)
{
    if (psp == pcap) {
        pcap = pcap ? pcap * 2 : 64;
        pv = xrealloc(pv, pcap * sizeof *pv);
        ps = xrealloc(ps, pcap * sizeof *ps);
        po = xrealloc(po, pcap * sizeof *po);
    }
    pv[psp] = v;
    ps[psp] = start;
    po[psp] = op;
    psp++;
}

static void out_append(const char *s, size_t n)
{
    if (out_len + n + 1 > out_cap)
{
    while (out_len + n + 1 > out_cap) out_cap = out_cap ? out_cap * 2 : 4096;
    out = xrealloc(out, out_cap);

}
memcpy(out + out_len, s, n);
    out_len += n;
}

/* ---------- Arithmetic ---------- */
/* + - * /  on integers. rstart = start of the right operand (for division by zero).
   Unsigned math avoids undefined behaviour on overflow. */
    static long long arith(char op, long long a, long long b, long rstart) {
    unsigned long long x = (unsigned long long)a, y = (unsigned long long)b;
    
    switch (op) {
        case '+': return (long long)(x + y);
        case '-': return (long long)(x - y);
        case '*': return (long long)(x * y);
        default: 
            if (b == 0) {
                fail(rstart);
                return 0;
            }
            if (b == -1) return (long long)(0ULL - x); /* avoids LLONG_MIN / -1 crash */
            return a / b; /* C truncates toward zero */
        }
    }    
/* a ** b by repeated squaring. Negative exponent is an error at the exponent's start. */
static long long powll(long long a, long long b, long exstart) {
    if (b < 0) {
        fail(exstart);
        return 0;
    }
    unsigned long long r = 1, base = (unsigned long long)a;
    long long e = b;
    while (e > 0) {
        if (e & 1) r *= base;
        base *= base;
        e >>= 1;
    }
    return (long long) r;  /* x ** 0 gives 1, also for 0 ** 0 */
}
/* ---------- Parser (evaluates while parsing) ----------
   expr    := term  { (+|-) term }
   term    := power { (*|/) power }
   power   := primary { ** primary }   (right-assoc, solved with a stack)
   primary := number | ( expr )
   Lower rules call higher-precedence rules, which gives the right precedence.
   Every error is reported at the token the parser was looking at. */
   static long long parse_expr(void);
static long long parse_number(void)
{
    unsigned long long n = 0;
    while (IS_DIGIT(*p)) {
        n = n * 10 + (*p - '0');
        p++;
    }
    return (long long)n;
}

static long long parse_primary(void) {
    skipws();
     if (IS_DIGIT(*p)) return parse_number();
    if (*p == '(') {
        p++;
        long long v = parse_expr();
        if (failed) return v;
        skipws();
        if (*p == ')') 
        { p++;return v; } 
    fail(POS(p));
    return 0;
    }
    fail(POS(p));
    return 0;
}

/* Collect a ** b ** c ... on the stack, then fold from the right.
   Using a stack instead of recursion keeps long chains from overflowing the C stack. */
static long long parse_power(void)
{
    size_t base = psp;
    skipws();
    long st = POS(p);
    long long v = parse_primary();
    if (failed) return v;
    push(v, st, 0);
    for (;;) {
        skipws();
        if (p[0] == '*' && p[1] == '*') {
            long op = POS(p);
            p += 2;
            skipws();
            st = POS(p);
            v = parse_primary();
            if (failed) return v;
            push(v, st, op);
        } else {
            break;  
    }
}
long long res = pv[psp - 1];
for (size_t i = psp - 1; i > base; i--) {
    res = powll(pv[i - 1], res, ps[i]);
if (failed) break;
}
psp = base;
return res;
}
/* * and / , left-associative */
static long long parse_term(void){
    long long v = parse_power();
    if (failed) return v;
    for (;;) {
        skipws();
        char c = *p;
        if (c != '*' && c != '/') break;
        p++;
        skipws();
        long rstart = POS(p);
        long long r = parse_power();
        if (failed) return v;
        v = arith(c, v, r, rstart);
        if (failed) return v;
}
return v;
}

/* + and - , left-associative */
static long long parse_expr(void) {
    long long v = parse_term();
    if (failed) return v;
    for (;;) {
        skipws();
        char c = *p;
        if (c != '+' && c != '-') break;
        p++;
        long long r = parse_term();
        if (failed) return v;
        v = arith(c, v, r, POS(p));
        if (failed) return v;
    }
    return v;
}
/* Go through the file line by line. Returns 0, or the position of the first error.
   Blank lines and # comments are skipped (their characters still count for positions). */
   static long process(void)
{
    p=buf;
    while (p < end) {
        skipws();
        if (p>=end) break;
        if (*p == '\n') { p++; continue; }
        if (*p == '#'){
            while (p < end && *p != '\n') p++;
            continue;
        }
        long long v = parse_expr();
        if (failed) return err_pos;
        skipws();
        if(!(p>=end || *p == '\n')) {  /* leftover text: extra ) or bad character */
            fail(POS(p));
            return err_pos;
        }
        char tmb[64];
        int n = snprintf(tmb, sizeof tmb, "%lld\n", v);
        out_append(tmb,(size_t)n);
        if (p<end) p++;
    }
    return 0;
}

// FILES AND FOLDERS
static char *copy_str(const char *s, size_t n) {
    char *r = xrealloc(NULL, n + 1);
    memcpy(r, s, n);
    r[n] = '\0';
    return r;
}
/* a + "/" + b (no double slash) */
static char *join(const char *a, const char *b) {
    size_t la = strlen(a), lb = strlen(b);
    int slash = (la>0 && a[la - 1] != '/');
    char *r = xrealloc(NULL, la + lb + 2);
    memcpy(r, a, la);
    if (slash) r[la++] = '/';
    memcpy(r + la, b, lb);
    r[la + lb] = '\0';
    return r;
}
/* Last part of a path, ignoring trailing slashes ("labs/task1.txt" -> "task1.txt") */
static char* last_component(const char *path) 
{
    size_t len = strlen(path), start;
    while (len > 1 && path[len - 1] == '/') len--;
    start = len;
    while (start > 0 && path[start - 1] != '/') start--;
    return copy_str(path + start, len - start);
}
static void strip_txt(char *name){
    size_t n = strlen(name);
    if (n >= 4 && strcmp(name + n - 4, ".txt") == 0) name[n - 4] = '\0';
}
/* Read a whole file into memory (any size), NUL-terminated so the parser can't run past the end */
static char *read_file(const char *path, size_t *plen)
{
    struct stat st;
    if (stat(path, &st) != 0) {
        fprintf(stderr, "calc: cannot open '%s': %s\n", path, strerror(errno));
        return NULL;
    }
    if (!S_ISREG(st.st_mode)) {
        fprintf(stderr, "calc: '%s' is not a regular file\n", path);
        return NULL;
    }
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "calc: cannot open '%s': %s\n", path, strerror(errno));
        return NULL;
    }
    size_t cap = 65536, len = 0;
    char *b = xrealloc(NULL, cap + 1);
    for (;;) {
        len += fread(b + len, 1, cap - len, f);
        if (len < cap) break;
        cap *= 2;
        b = xrealloc(b, cap + 1);
    }
    if (ferror(f)) {
        fprintf(stderr, "calc: error reading '%s'\n", path);
        free(b);
        fclose(f);
        return NULL;
    }
    fclose(f);
    b[len] = '\0';
    *plen = len;
    return b;
}
/* Create the folder if missing; fine if it already exists */
static int ensure_dir(const char *path) {
       struct stat st;
       if (stat(path, &st) == 0) {
           if (S_ISDIR(st.st_mode)) return 0;
           fprintf(stderr, "calc: '%s' exists and is not a directory\n", path);
           return 1;
       }
       if (mkdir(path, 0777) != 0) {
           fprintf(stderr, "calc: cannot create directory '%s': %s\n", path, strerror(errno));
           return 1;
       }
       return 0;
   }
/* Evaluate one file; write <outdir>/<base>_<name>_<lastname>_<id>.txt.
   On any error the file contains only "ERROR:<pos>". */
     static int run_file(const char *inpath, const char *outdir, const char *base)
{
    size_t len  =  0;
    char *data = read_file(inpath, &len);
    if (!data) return 1;
    if (ensure_dir(outdir) != 0) { free(data); return 1; }

    buf = data;
    end = buf + len;
    failed = 0;
    err_pos = 0;
    psp = 0;
    out_len = 0;
    long e = process();

    char errtxt[64];
    const char *content =out;
    size_t clen = out_len;
    if (e){
        int n = snprintf(errtxt, sizeof errtxt, "ERROR:%ld\n", e);
        content = errtxt;
        clen = (size_t)n;
    }
    free(data);
    buf = end = p = NULL;

    size_t nl = strlen(base) + sizeof("_" STU_NAME "_" STU_LASTNAME "_" STU_ID ".txt");
    char *fname = xrealloc(NULL, nl);
    snprintf(fname, nl, "%s_%s_%s_%s.txt", base, STU_NAME, STU_LASTNAME, STU_ID);
    char *outpath = join(outdir, fname);
    free(fname);
     int rc = 0;
    FILE *f = fopen(outpath, "wb");
    if (!f) {
        fprintf(stderr, "calc: error writing '%s': %s\n", outpath, strerror(errno));
        rc = 1;
    } else {
        if (clen > 0 && fwrite(content, 1, clen, f) != clen) rc = 1;
        if (fclose(f) != 0) rc = 1;
        if (rc) fprintf(stderr, "calc: error writing '%s'\n", outpath);
    }
    free(outpath);
    return rc;  
        }
        static int cmp_names(const void *a, const void *b) 
        {
            return strcmp(*(char * const *)a, *(char * const *)b);
        }
/* Process every *.txt directly inside dir (subfolders and other files are ignored) */
static int run_dir(const char *dir, const char *outdir)
{
    DIR *d = opendir(dir);
    if (!d) {
        fprintf(stderr, "calc: cannot open directory '%s': %s\n", dir, strerror(errno));
        return 1;
    }
    char **names = NULL;
    size_t count = 0, cap = 0;
    struct dirent *e;
    while ((e = readdir(d)) != NULL) {
        const char *nm = e->d_name;
        size_t n = strlen(nm);
        if (n < 4 || strcmp(nm + n - 4, ".txt") != 0) continue;
        char *full = join(dir, nm);
        struct stat st;
        int ok = stat(full, &st) == 0 && S_ISREG(st.st_mode);
        free(full);
        if (!ok) continue;
        if (count == cap) {
            cap = cap ? cap * 2 : 16;
            names = xrealloc(names, cap * sizeof *names);
        }
        names[count++] = copy_str(nm, n);
    }
    closedir(d);
    if (count > 1) qsort(names, count, sizeof *names, cmp_names);   // sorted order

    int rc = ensure_dir(outdir);
    for (size_t i = 0; i < count && rc == 0; i++) {
        char *full = join(dir, names[i]);
        char *base = copy_str(names[i], strlen(names[i]));  
        strip_txt(base);
        if (run_file(full, outdir,base) != 0) rc = 1;
        free(base);
        free(full);
    }
    for (size_t i = 0; i < count; i++) free(names[i]);
    free(names);
    return rc;
}

static void usage(void) {
    fprintf(stderr, "usage: calc [-d DIR | --dir DIR] [-o OUTDIR | --output-dir OUTDIR] [input.txt]\n");
}

int main(int argc, char **argv)
{
     const char *dir = NULL, *outdir = NULL, *input = NULL;

for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
   if (strcmp(a, "-d") == 0 || strcmp(a, "--dir") == 0) {
            if (i + 1 >= argc || dir) { usage(); return 2; }
            dir = argv[++i];
        } else if (strcmp(a, "-o") == 0 || strcmp(a, "--output-dir") == 0) {
            if (i + 1 >= argc || outdir) { usage(); return 2; }
            outdir = argv[++i];
    } else if (a[0] == '-' && a[1] != '\0') {
            fprintf(stderr, "calc: unknown option '%s'\n", a);
            usage();
            return 2;
    } else{
        if (input) { usage(); return 2; }
            input = a;
    }
}
/* need exactly one of: input file, or -d folder */
if ((!input && !dir) || (input && dir)) {
    usage();
    return 2;
}

int rc;
char *base = last_component(dir ? dir : input);
if (!dir) strip_txt(base);

/* default output folder: <base>_<name>_<studentid> */
char *defout = NULL;
    if (!outdir) {
        size_t n = strlen(base) + sizeof("_" STU_NAME "_" STU_ID);
        defout = xrealloc(NULL, n);
        snprintf(defout, n, "%s_%s_%s", base, STU_NAME, STU_ID);
        outdir = defout;
    }

    if (dir) rc = run_dir(dir, outdir);
    else rc = run_file(input, outdir, base);


    free(defout);
    free(base);
    free(out);
    free(pv);
    free(ps);
    free(po);
    return rc ? 1 : 0;
}
