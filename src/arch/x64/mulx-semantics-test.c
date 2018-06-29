#include <stdint.h>
#include <stdio.h> 
#include <x86intrin.h>
#include "immintrin.h"

int main(int argc, char* argv[])
{
    // Using Intel's intrinsic:
    uint64_t a = 0x0fffffffffffffff; 
    uint64_t b = 0xf0000000; 
    uint64_t c, d; 
    d = _mulx_u64(a, b, &c); 
    printf("%llx * %llx = %llx %llx\n", a, b, c, d); 

    // Manually specifying the registers to use
    uint64_t w = 0x0fffffffffffffff; 
    uint64_t x = 0xf0000000; 
    uint64_t y, z; 
    asm ("mulxq %%rcx, %%rbx, %%rax"
            : "=a" (y), "=b" (z)
            : "c" (w),  "d" (x)
        );

    printf("%llx * %llx = %llx %llx\n", w, x, y, z); 

    uint64_t myarray[10];
    myarray[0] = 0xaaaaaaaaa;

    // Making src2 a memory location
    asm ("mulxq (%%rcx), %%rbx, %%rax"
            : "=a" (y), "=b" (z)
            : "c" (myarray),  "d" (x)
        );

    printf("%llx * %llx = %llx %llx\n", myarray[0], x, y, z); 

    // Making src2 collide with dest1: multiplying another_array[0] * X = hi: 0, lo:&myarray. 
    // If src2 is read twice, then the second access of src2 should be to myarray, instead of another_array
    // In that case, the high value in y should be non-zero
    uint64_t another_array[10];
    another_array[0] = 1;
    x = (uint64_t)&myarray;
    
    asm ("mulxq (%%rcx), %%rcx, %%rax"
            : "=a" (y), "=c" (z)
            : "c" (another_array),  "d" (x)
        );

    printf("%llx * %llx = %llx %llx\n", another_array[0], x, y, z); 

    return 0;
}
