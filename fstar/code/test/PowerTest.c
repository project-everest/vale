#include <stdio.h>
#include <stdint.h>

void Copy16(unsigned long long *src, unsigned long long *dst);
unsigned long long MulIf(unsigned long long src);
unsigned long long AddLoop(unsigned long long src, unsigned long long count);
unsigned long long VecXor(unsigned long long src1, unsigned long long src2);

int fail(char *s)
{
    printf("Vale PowerTest failed: %s\n", s);
    return 1;
}

int main()
{
    unsigned long long src[] = {5, 5};
    unsigned long long dst[] = {0, 0};
    Copy16(src, dst);
    if (dst[0] != 5 || dst[1] != 5) {return fail("Copy16");}
    if (MulIf(8) != 40) {return fail("MulIf");}
    if (MulIf(15) != 5) {return fail("MulIf");}
    if (AddLoop(0, 10) != 50) {return fail("AddLoop");}
    if (VecXor(8, 7) != 15) {return fail("VecXor");}
    printf("Vale PowerTest Done\n");
    return 0;
}
