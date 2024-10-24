/*----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------*/
#ifndef ARITH64_DEF
#define ARITH64_DEF

#define arith64_u64 unsigned long long int
#define arith64_s64 signed long long int
#define arith64_u32 unsigned int
#define arith64_s32 int

typedef union
{
    arith64_u64 u64;
    arith64_s64 s64;
    struct
    {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
        arith64_u32 hi; arith64_u32 lo;
#else
        arith64_u32 lo; arith64_u32 hi;
#endif
    } u32;
    struct
    {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
        arith64_s32 hi; arith64_s32 lo;
#else
        arith64_s32 lo; arith64_s32 hi;
#endif
    } s32;
} arith64_word;

// extract hi and lo 32-bit words from 64-bit value
#define arith64_hi(n) (arith64_word){.u64=n}.u32.hi
#define arith64_lo(n) (arith64_word){.u64=n}.u32.lo

// Negate a if b is negative, via invert and increment.
#define arith64_neg(a, b) (((a) ^ ((((arith64_s64)(b)) >= 0) - 1)) + (((arith64_s64)(b)) < 0))
#define arith64_abs(a) arith64_neg(a, a)

/*
 */
arith64_s64 __moddi3(arith64_s64 a, arith64_s64 b);

/*
 */
arith64_s64 __divdi3(arith64_s64 a, arith64_s64 b);


#endif
