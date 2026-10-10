/*
 * autoform kernel shim: the smallest set of kernel types, macros and helper
 * declarations needed to compile individual kernel library files outside Kbuild.
 *
 * It provides declarations and obvious one-line helpers only. It never supplies a
 * function whose behaviour is being compared: every function under test is the
 * kernel's own source at the commit being analysed. Helpers are written from their
 * documented meaning (for example fls64(x) is the 1-based index of the most
 * significant set bit, 0 for x == 0), not copied from the kernel.
 */
#ifndef AUTOFORM_KERNEL_SHIM_H
#define AUTOFORM_KERNEL_SHIM_H

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef signed char s8;
typedef short s16;
typedef int s32;
typedef long long s64;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
#if defined(__SIZEOF_INT128__)
typedef unsigned __int128 u128;
typedef __int128 s128;
#endif
#ifndef __cplusplus
typedef _Bool bool;
#define true 1
#define false 0
#endif

#define BITS_PER_LONG (__SIZEOF_LONG__ * 8)
#define ULONG_MAX (~0UL)
#define U64_MAX (~0ULL)

#define EXPORT_SYMBOL(sym)
#define EXPORT_SYMBOL_GPL(sym)
#define __attribute_const__ __attribute__((__const__))
#define __always_inline inline __attribute__((__always_inline__))
#define noinline __attribute__((__noinline__))
#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

#define swap(a, b) \
	do { __typeof__(a) __autoform_tmp = (a); (a) = (b); (b) = __autoform_tmp; } while (0)

/* 1-based index of the most significant set bit; 0 when no bit is set. */
static inline int fls(unsigned int x) { return x ? 32 - __builtin_clz(x) : 0; }
static inline int fls64(u64 x) { return x ? 64 - __builtin_clzll(x) : 0; }
/* 0-based index of the most significant set bit; undefined for 0. */
static inline unsigned long __fls(unsigned long word)
{
	return BITS_PER_LONG - 1 - __builtin_clzl(word);
}
/* floor(log2(n)) for n > 0. */
#define ilog2(n) (fls64((u64)(n)) - 1)

/* Repeated-subtraction division, for small quotients. */
static inline u32 __iter_div_u64_rem(u64 dividend, u32 divisor, u64 *remainder)
{
	u32 ret = 0;
	while (dividend >= divisor) {
		dividend -= divisor;
		ret++;
	}
	*remainder = dividend;
	return ret;
}

#if BITS_PER_LONG == 64
/* On 64-bit targets these are plain C division (the kernel's own lib files only
 * define them for 32-bit targets). */
static inline u64 div_u64_rem(u64 dividend, u32 divisor, u32 *remainder)
{ *remainder = dividend % divisor; return dividend / divisor; }
static inline s64 div_s64_rem(s64 dividend, s32 divisor, s32 *remainder)
{ *remainder = dividend % divisor; return dividend / divisor; }
static inline u64 div64_u64_rem(u64 dividend, u64 divisor, u64 *remainder)
{ *remainder = dividend % divisor; return dividend / divisor; }
static inline u64 div64_u64(u64 dividend, u64 divisor) { return dividend / divisor; }
static inline s64 div64_s64(s64 dividend, s64 divisor) { return dividend / divisor; }
#else
u64 div64_u64_rem(u64 dividend, u64 divisor, u64 *remainder);
u64 div64_u64(u64 dividend, u64 divisor);
s64 div64_s64(s64 dividend, s64 divisor);
s64 div_s64_rem(s64 dividend, s32 divisor, s32 *remainder);
#endif

unsigned long gcd(unsigned long a, unsigned long b) __attribute_const__;
unsigned long lcm(unsigned long a, unsigned long b) __attribute_const__;
unsigned long lcm_not_zero(unsigned long a, unsigned long b) __attribute_const__;
unsigned long int_sqrt(unsigned long x);
#if BITS_PER_LONG < 64
u32 int_sqrt64(u64 x);
#else
static inline u32 int_sqrt64(u64 x) { return (u32)int_sqrt(x); }
#endif
u64 mul_u64_u64_div_u64(u64 a, u64 b, u64 c);

#endif
