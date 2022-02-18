#include <stdio.h>
#include <stdbool.h>
#include <limits.h>
#include <assert.h>
#include <math.h>
#include <assert.h>


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

// 2.68
// TODO: incorrect when n is 32
int lower_bits(int x, int n) {
    return ~(-1 << n) | x;
}

void test_lower_bits(void) {
    int x = 0x6789abcd;
    for(int i = 0; i < 32; i++) {
        printf("%d -> %#.8x\n", i, lower_bits(x, i));
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

int ch2_main(void) {
    test_rotate_right();
    return 0;
}
