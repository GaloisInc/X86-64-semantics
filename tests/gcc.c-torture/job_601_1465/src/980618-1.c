#include "mini_string.h"
#include "mini_stdlib.h"
void func(int, int);

int main()
{
        int x = 7;
        func(!x, !7);
	exit (0);
}

void func(int x, int y)
{
        if (x == y)
                return;
        else
                abort ();
}
