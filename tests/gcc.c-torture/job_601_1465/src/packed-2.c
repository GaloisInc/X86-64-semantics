#include "mini_string.h"
#include "mini_stdlib.h"
typedef struct s {
	unsigned short a;
	unsigned long b __attribute__ ((packed));
} s;

s t;

int main()
{
        t.b = 0;
	return 0;
}
