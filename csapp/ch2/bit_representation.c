#include <stdio.h>
#include <stdbool.h>
#include <limits.h>
#include <assert.h>
#include <math.h>
#include <assert.h>
#include "../utils/utils.h"



// 2.27
bool uadd_ok(unsigned int x, unsigned int y) {
    unsigned int sum = x + y;
    return sum >= x;
}

// 2.30
bool tadd_ok(int x, int y) {
    int sum = x + y;
    if (x > 0 && y > 0) {
        return sum > 0;
    }
    if (x < 0 && y < 0) {
        return sum < 0;
    }
    /**
     * If x and y have different sign, never overflow
     *  say:
     *      x ranges: [-2^(w - 1), 0)
     *      y ranges: (0, 2^(w - 1) - 1]
     *      x + y ranges: [-2^(w - 1) + 1, 2^(w - 1) - 2]
     *      which locate inside normal range: [-2^(w - 1), 2^(w - 1) - 1]
     */
    return true;
}

// 2.32
bool tsub_ok(int x, int y) {
    int _y = -y;
    if (_y == y) {
        // 0 or TMin
        if (y == 0) {
            return true;
        }
        // TMin situation
        /**
         * x - TMin
         *   => x - (- TMax - 1)
         *   => x + TMax + 1
         *   => x must less than 0 to avoid positive overflow
         */
        return x < 0;
    }
    return tadd_ok(x, _y);
}

// 2.35
// TODO don't know how
bool tmult_ok(void) {
    // pass
    return true;
}


// 2.42
// Implement div16 without divide operation and conditional
int div16(int x) {
    int bias = (x >> 31) & 0xF;
    return (x + bias) >> 4;
}


// 2.55
void show_bytes(unsigned char* ptr, size_t size) {
    for(size_t i = 0; i < size; i++) {
        printf("%.2x ", *(ptr + i));
        if ((i + 1) % 4 == 0) {
            printf("\n");
        }
    }
}

// 2.57
void show_float(float v) {
    show_bytes((unsigned char *)&v, sizeof(v));
}

// 2.58
bool is_little_endian(void) {
    char ch[2] = { 1, 0 };
    return *(short *)ch == 1;
}

// 2.59
// yield a word consisting lsb of x and remain bytes of y
int merge_bits(int x, int y) {
    return (x & 0xff) | (y & (~0xff));
}


// 2.60
// replace `i`-st lsb of `x` with `b`
unsigned replace_bytes(unsigned x, unsigned char b, int i) {
    size_t shift = i % sizeof(x) * CHAR_BIT;
    unsigned mask = ~(((unsigned)0xff) << shift);
    unsigned keep = ((unsigned)b) << shift;
//    printf("mask is %#.8x\n", mask);
//    printf("keep is %#.8x\n",keep);
    return (x & mask) | keep;
}

// 2.61
/* return 1 in the following cases:
 * A. every bit is 1
 * B. every bit is 0
 * C. every bit in msb is 1
 * D. every bit in lsb is 0
 */
bool is_all_1(int x) {
    return !(x ^ (~0)) /* A */;
}
bool is_all_0(int x) {
    return !(x & ~0) /* B */;
}
bool is_msb_all_1(int x) {
    return is_all_1(x >> (sizeof(x) - 1) * CHAR_BIT);
}
bool is_lsb_all_0(int x) {
    return is_all_0(x << (sizeof(x) - 1) * CHAR_BIT);
}

bool exec_2_61(int x) {
    return is_all_0(x) || is_all_1(x) || is_msb_all_1(x) || is_lsb_all_0(x);
}

// 2.62
bool int_shifts_are_logical(void) {
    // bit representation of(-1 >> 1)
    //  logical right shifts: 01111...111
    //  arithmatic right shifts: 1111111, every bit is 1
    return !is_all_1(-1 >> 1);
}

void test_int_shifts_are_logical(void) {
    printf("int shifts are %slogical\n", int_shifts_are_logical() ? "" : "not " );
}

// 2.63
// TODO: incorrect when k equals 0
unsigned srl(unsigned x, int k) {
    unsigned xsra = (int)x >> k;
    return xsra & ~(-1 << (sizeof(x) * CHAR_BIT - k));
}

int sra(int x, int k) {
    size_t w = sizeof(x) * CHAR_BIT;
    int xsrl =  (unsigned)x >> k;
    int sign_bit = (1 << (w - k - 1)) & xsrl;
    // >=0: mask is 0b000..0000
    //  <0: mask is 0b111..0000
    int mask = (!sign_bit - 1) << (w - k);
    return xsrl | mask;
}

int test_srl_sra(void) {
    int x = 0x00f12345;
    int y = 0xff123456;
    for(int k = 0; k < 32; k++) {
        assert(sra(x, k) == (signed)x >> k);
        assert(srl(x, k) == (unsigned)x >> k);
        assert(sra(y, k) == (signed)y >> k);
        assert(srl(y, k) == (unsigned)y >> k);
    }
    printf("Test passed\n");
    return 0;
}

// 2.64
int any_even_one(unsigned x) {
    // Given int is assumed 32-bit, we can specify this mask
    unsigned mask = 0xAAAAAAAA;
    return !!(x & mask);
}

// 2.65
// We can prove this rule:
//   Given w-bit value x and y
//   if bit representation of `(x << w) + y` has even 1s
//   then x ^ y must also have even 1s;
//   1 ^ 1 == 0 // clear two 1s in the same bit position, keep even-odd attribute
//   1 ^ 0 == 1 // keep origin 1 count
// thus we can reduce 32 bits to 16 bits, 16 bits to 8 bits, and so on.
// until only 1 bit, just return xor result
int even_ones(unsigned x) {
    x = (x >> 16) ^ (x & 0xffff);
    x = (x >> 8) ^ (x & 0xff);
    x = (x >> 4) ^ (x & 0xf);
    x = (x >> 2) ^ (x & 0x3);
    return !(signed)((x >> 1) ^ (x & 1));
}

void test_even_ones(void) {
    assert(even_ones(0xAAFF) == 1);
    assert(even_ones(0x7AAFF) == 0);
    printf("All test cases passed\n");
}

// 2.66
int leftmost_one(unsigned x) {
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    return (int)(x ^ (x >> 1));
}

void test_leftmost_one(void) {
    assert(leftmost_one(0U) == 0);
    assert(leftmost_one(1U) == 1);
    assert(leftmost_one(3U) == 2);
    assert(leftmost_one(0x7bcd) == 0x4000);
    assert(leftmost_one((unsigned)-1) == 0x80000000);
    printf("leftmost_one: all test cases passed\n");
}

// 2.67
// should works on any machine for which `int` is at least 16 bits
int int_size_is_32(void) {
    return (1U << 15) << 1 == ((unsigned)INT_MIN >> 15);
}

void test_int_size_is_32(void) {
    assert(int_size_is_32() == 1);
    printf("int_size_is_32: test passed.\n");
}

// 2.68
// TODO: incorrect when n is 32
int lower_bits(int x, int n) {
    return (~(-1 << n)) | x;
}

void test_lower_bits(void) {
    int x = 0x6789abcd;
    for(int i = 0; i <= 32; i++) {
        char *bin_str = to_binary((unsigned)lower_bits(x, i));
        printf("%2d -> %s\n", i, bin_str);
        free(bin_str);
    }
}

// 2.69
unsigned rotate_right(unsigned x, int n) {
    int w = sizeof(x) * CHAR_BIT;
    unsigned tail = ~(-1 << n) & x;
    unsigned head = x >> n;
    return (tail << (w - n)) | head;
}

void test_rotate_right(void) {
    int x = 0x12345678;
    assert(rotate_right(x, 4) == 0x81234567);
    assert(rotate_right(x, 20) == 0x45678123);
    printf("rotate_right: all test cases passed\n");
}

// 2.70
int fits_bits(int x, int n) {
    return !((-1 << n) & x);
}

void test_fits_bits(void) {
    int x = 0x23456;
    assert(fits_bits(x, 3) == 0);
    assert(fits_bits(x, 4) == 0);
    assert(fits_bits(x, 5) == 0);
    assert(fits_bits(x, 17) == 0);
    assert(fits_bits(x, 18) == 1);
    assert(fits_bits(x, 19) == 1);
    assert(fits_bits(x, 20) == 1);
    printf("All test passed\n");
}

// 2.71
int xbyte(unsigned word, int n) {
    int leftshift = (sizeof(word) - n - 1) * CHAR_BIT;
    int rightshift = (sizeof(word) - 1) * CHAR_BIT;
    // not sure if type conversion is allowed here
    return (int)(word <<leftshift) >> rightshift;
}

void test_xbyte(void) {
    unsigned word = 0xfe339876;
    printf("%#.8x\n", word);
    for(int i = 0; i <= 3; i++) {
        printf("extract No.%d byte: %#.8x\n", i, xbyte(word, i));
    }
}

// 2.73
// Too ugly, find way to optimize
/**
 k: k = !(sx ^ sy) && (sy ^ sz)
 sx: if positive overflow sx == 0 else if negative overflow sx == -1 (bit: 0b1111...111)
 |-------------------|--------|---|---------|--------|-----------------|-------------------|
 | Var               | Target | k | m = k-1 | t1=m&z | t2=t1^(sx & ~m) | t3=t2^(Tmax & ~m) |
 | Normal            | z      | 0 | -1      | z      | z               | z                 |
 | Positive Overflow | Tmax   | 1 | 0       | 0      | 0               | Tmax              |
 | Negative Overflow | Tmin   | 1 | 0       | 0      | -1              | Tmin (==-1^Tmax)  |
 |-------------------|--------|---|---------|--------|-----------------|-------------------|
 */
int saturating_add(int x, int y) {
    int z = x + y;
    int sx = x >> 31;
    int sy = y >> 31;
    int sz = z >> 31;
    int k = !(sx ^ sy) && (sy ^ sz); // indicate if overflow
    int m = k - 1;
    return (m & z) ^ (sx & ~m) ^ (INT_MAX & ~m);
}

void test_saturating_add(void) {
    // test positive overflow
    int test_pos_over = INT_MAX / 2 + 1;
    assert(saturating_add(test_pos_over, test_pos_over + 1) == INT_MAX);
    assert(test_pos_over + test_pos_over + 1 != INT_MAX);
    // test negative overflow
    int test_neg_over = INT_MIN / 2 - 1;
    assert(saturating_add(test_neg_over, test_neg_over - 1) == INT_MIN);
    assert(test_neg_over + test_neg_over - 1 != INT_MIN);
    // test normal case
    assert(saturating_add(123, 234) == 357);
    assert(saturating_add(-123, -234) == -357);
    assert(saturating_add(123, -234) == -111);
    
    // some online test cases https://dreamanddead.github.io/CSAPP-3e-Solutions/chapter2/2.73/
    assert(INT_MAX == saturating_add(INT_MAX, 0x1234));
    assert(INT_MIN == saturating_add(INT_MIN, -0x1234));
    assert(0x11 + 0x22 == saturating_add(0x11, 0x22));
    printf("saturating_add: all test cases passed\n");
}

// 2.74
// Like tsub_ok but only limited operations are allowed
int tsub_ovf(int x, int y) {
    int z = x - y;
    int sx = x >> 31;
    int sy = y >> 31;
    int sz = z >> 31;
    return ((sx ^ sy) && !(sy ^ sz)) || (y == -y /* Tmin case */ && !sx && y);
}

void test_tsub_ovf_assert(int x, int y, int expected) {
    int is_overflow = tsub_ovf(x, y);
    assert(is_overflow == expected);
    assert(is_overflow == !tsub_ok(x, y));
}

void test_tsub_ovf(void) {
    test_tsub_ovf_assert(INT_MIN + 10, 20, 1);
    test_tsub_ovf_assert(INT_MAX - 10, -20, 1);
    test_tsub_ovf_assert(1, INT_MIN, 1);
    test_tsub_ovf_assert(-1, INT_MIN, 0);
    test_tsub_ovf_assert(4, -5, 0);
    test_tsub_ovf_assert(-10, 9, 0);
    test_tsub_ovf_assert(INT_MAX, 0, 0);
    test_tsub_ovf_assert(INT_MIN, 0, 0);
    printf("tsub_ovf: all case passed\n");
}

// 2.76
void test_2_76(void) {
    for(int i = 0; i < 100; i+= 10) {
        assert(((i << 2) + i) == i * 5);
        assert(((i << 3) + i) == i * 9);
        assert((i << 5) - (i << 1) == i * 30);
        assert((i << 3) - (i << 6) == i * -56);
    }
    printf("2.76: all test passed\n");
}


// 2.77
// k ranges: [0, w - 1)
int divide_power2(int x, int k) {
    int w = sizeof(x) * CHAR_BIT;
    int mask = x >> (w - 1);
    int bias = ~(-1 << k) & mask;
    return (x + bias) >> k;
}

void test_divide_power2(void) {
    int x = -12345;
    for(int k = 0; k < 14; k++) {
        assert(divide_power2(x, k) == x / (1<<k));
    }
    printf("divide_power2: all test passed\n");
}

// 2.78
int mul5div8(int x) {
    x = (x << 2) + x; // x*5
    return divide_power2(x, 3);
}

void test_mul5div8(void) {
    int n = INT_MAX / 4;
    assert(mul5div8(n) == (n * 5) / 8); // test overflow
    assert(mul5div8(110) == (110 * 5) / 8);
    assert(mul5div8(-1) == (-1 * 5) / 8);
    printf("mul5div8: test cases passed\n");
}


// 2.80
void exer_2_80(int m, int n) {
//    int a = -1 << n;
//    int b = ~(-1 << n) << m;
    char *bin_str_a = to_binary(-1 << n);
    char *bin_str_b = to_binary(~(-1 << n) << m);
    printf("m = %d, n = %d\n[%s, %s]\n", m, n, bin_str_a, bin_str_b);
    free(bin_str_a);
    free(bin_str_b);
}

void test_2_80(void) {
    for(int m = 0; m < 5; m++) {
        for(int n = 0; n < 10; n++) {
            exer_2_80(m, n);
        }
    }
    
}

// 2.83
/**
 * There are four cases when x >= y
 * 1. both zero(=)
 * 2. exactly same value(=)
 * 3. diff sign: then must x >=0 and y < 0
 * 4. same sign: abs(x) > abs(y) and both > 0, or abs(x) < abs(y), and both < 0
 *    we compare abs(x) and abs(y) by checking the overflow bit of the subtract result(first bit of msb, vz >> 31)
 */
int float_ge(float x, float y) {
    unsigned ux = f2u(x);
    unsigned uy = f2u(y);
    
    unsigned sx = ux >> 31;
    unsigned sy = uy >> 31;
    unsigned mask = 0x7fffffff;
    unsigned vx = ux & mask;
    unsigned vy = uy & mask;
    unsigned vz = vx - vy;
    int is_both_zero = !(vx | vy);
    int is_equal = ux == uy;
    int is_diff_sign_bigger = !sx && sy;
    int is_same_sign_bigger = vz >> 31 == sx && sx == sy;
    // too too too ugly, any better exp?
    return is_both_zero || is_equal || is_diff_sign_bigger || is_same_sign_bigger;
}

void test_float_ge(void) {
    float cases[][2] = {
        { +0.0f, -0.0f },
        { 1.5f, 2.5f },
        { 4.0f, 2.1f },
        { -10.5f, -9.0f },
        { -99.0f, -100.0f },
        { 9.0f,-10.1f },
        { -100.0f, 101.5f },
    };
    int length = sizeof(cases) / sizeof(cases[0]);
    for(int i = 0; i < length; i++ ) {
        float x = cases[i][0];
        float y = cases[i][1];
        int va = float_ge(x, y);
        int vb = x >= y;
        printf("check if %f >= %f: result: %d / %d\n", x, y, va, vb);
        assert(va == vb);
    }
}

// 2.91
typedef unsigned float_bits;
// Shared testing function
void float_bits_tester(char *fnname, float_bits fn(float_bits), float native_fn(float)) {
    printf("%s testing start: \n", fnname);
    float cases[] = {
        NAN,
        1.0f,
        1.5f,
        -1.5f,
        0.0f,
        INFINITY,
        -INFINITY,
        MAXFLOAT,
//        (float)0x7f7fffff,
    };
    int length = sizeof(cases) / sizeof(cases[0]);
    for(int i = 0; i < length; i++) {
        float v = cases[i];
        float nf = native_fn(v);
        float tf = u2f(fn(f2u(v)));
        printf("  %f -> %f, %f\n", v, nf, tf);
        if (nf == nf) {
            // both non-nan
            assert(nf == tf);
        } else {
            // both nan
            assert(tf != tf);
        }
    }
    printf("%s: all test cases passed\n", fnname);
}

float_bits float_absval(float_bits f) {
    unsigned exp = f << 1 >> 24;
    unsigned frac = f << 9 >> 9;
    if (exp == 0xff && frac > 0) {
        return f;
    }
    return (exp << 23 ) | frac;
}

float native_float_absval(float f) {
    if (f == f) {
        return f >= 0.0f ? f : -f;
    }
    // NaN
    return f;
}

void test_float_absval(void) {
    float_bits_tester("float_absval", float_absval, native_float_absval);
}

// 2.92
float_bits float_negate(float_bits f) {
    unsigned exp = f << 1 >> 24;
    unsigned frac = f & 0x7fffff;
    if (exp == 0xff && frac > 0) {
        // NAN
        return f;
    }
    return (1U << 31) ^ f;
}

float native_float_negate(float x) {
    return x == x ? -x : x;
}

void test_float_negate(void) {
    float_bits_tester("float_negate", float_negate, native_float_negate);
}

// 2.93
float_bits float_half(float_bits f) {
    unsigned sign = f >> 31;
    unsigned exp = f << 1 >> 24;
    unsigned frac = f & 0x7fffff;
    if (exp == 0xff) {
        if (frac > 0) {
            // NAN
            return f;
        }
        // just for explanation: inf and -inf case
        return f;
    }
    if (exp == 0) return 0U;
    exp = exp - 1;
    return (sign << 31) | (exp << 23) | frac;
}

float native_float_half(float x) {
    return x == x ? 0.5f * x : x;
}

void test_float_half(void) {
    float_bits_tester("float_half", float_half, native_float_half);
}

// 2.94
float_bits float_twice(float_bits f) {
    unsigned exp = f << 1 >> 24;
    unsigned frac = f & 0x7fffff;
    if (exp == 0xff) {
        return f;
    }
    // max exp is 254
    if (exp == 254) {
        exp = 255;
        frac = 0;
    } else if (exp == 0) {
        if (frac & 0x400000) {
            exp += 1;
        }
        frac = (frac & 0x3fffff) << 1;
    } else {
        exp += 1;
    }
    return (f >> 31 << 31) | (exp << 23) | frac;
}

float native_float_twice(float f) {
    return f == f ? 2.0f * f : f;
}

void test_float_twice(void) {
    float_bits_tester("float_twice", float_twice, native_float_twice);
}

// 2.95
/**
 *    0...0 1 XX...XX X...X
 *    ----- - ------- -----
 *      A        B      C
 *
 *   `shift` denote the continue `0` length(A part), after which is the most significant bit `1`
 *
 *   1. extract sign bit
 *   2. get the absolute value
 *   3. run `while` to get `shift`, thus check how many tail bits need to be rounded, may need to add a
 *      compensation conditionally(when `shift` < 8).
 *   4. adding compensation may cause the most significant bit `1` move to previous one, thus `shift--`
 *   5. after all above actions,
 *      `exp` will be B part length(as more length as possible, ranges 0 to 23) plus C part length(ranges 0 to 8) plus bias(127)
 *      `frac` is kept B part bits
 *      C part is ignored
 */
float_bits flaoat_i2f(int x) {
    if (x == 0) return 0U;
    // mask be normalize value
    unsigned sign = x >> 31; // 1 or 0
    unsigned value = x > 0 ? x : -x; // or (value ^ (-sign)) + sign
    unsigned mask = 0x80000000;
    unsigned shift = 0;
    while(mask) {
        if (mask & value) {
            break;
        }
        shift++;
        mask >>= 1;
    }
    if (shift < 8) {
        // 8 - shift bits need to be rounded up
        unsigned compensation = 1 << (7 - shift);
        unsigned ignore_value = ~(-1 << (8 -shift)) & value;
        if (ignore_value > compensation) {
            // round up
            value += compensation;
        } else if (ignore_value == compensation) {
            // round to even
            if ((compensation << 1) & value) {
                value += compensation;
            }
        }
        // compensation caused `shift` change
        if (((1 << (32 - shift - 1)) & value) == 0) {
            shift -= 1;
        }
    }
    unsigned exp = 32 - shift - 1 + 127;
    unsigned frac = value << (shift + 1);
    return (sign << 31) | (exp << 23) | (frac >> 9);
}

void test_i2f(void) {
    int cases[] = {
        0,
        1,
        -1,
        100,
        -100,
        INT_MIN,
        INT_MIN + 10,
        INT_MIN / 2,
        INT_MAX - 10,
        INT_MAX / 2,
        INT_MAX,
    };
    int length = sizeof(cases) / sizeof(cases[0]);
    for(int i = 0; i < length; i++) {
        int v = cases[i];
        float_bits nv = f2u((float)v);
        float_bits tv = flaoat_i2f(v);
        printf("convert %d to float: \n expected: %s\n      got: %s\n", v, to_binary(nv), to_binary(tv));
        assert(nv == tv);
    }
    printf("i2f: all cases passed\n");
}

// 2.95
int float_f2i(float_bits f) {
    unsigned sign = f >> 31;
    unsigned exp = ((f << 1) >> 24); // before subtract bias
    // round to zero, don't care frac part
    if (exp < 127) return 0;
    if (exp >= 158) return 0x80000000;
    exp = exp - 127;
    unsigned result = (1 << exp) + ((f << 9) >> (32 - exp));
    return (int)((result ^ (-sign)) + sign);
}

void test_float_f2i(void) {
    float cases[] = {
        0.0f,
        -0.0f,
        -10.9f,
        -12345.56f,
        99.99f,
        19.0f,
        // according to textbook, this MAXFLOAT case should return 0x80000000
        // but is different from c bahavior ((int),dontknow what to do
        // MAXFLOAT,
    };
    int length = sizeof(cases) / sizeof(cases[0]);
    for(int i = 0; i < length; i++) {
        float v = cases[i];
        float_bits fv = f2u(v);
        int result = float_f2i(fv);
        int expect = (int)v;
        printf("Convert %f to int: \nexpect: %d\nresult: %d\n", v, expect, result);
        assert(expect == result);
    }
    printf("float_f2i: ass cases passed\n");
}

int ch2_main(void) {
//    test_float_absval();
//    test_float_negate();
//    test_float_half();
//    test_float_twice();
    
    test_float_f2i();
    return 0;
}
