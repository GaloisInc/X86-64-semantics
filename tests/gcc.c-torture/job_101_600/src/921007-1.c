#include "mini_string.h"
#include "mini_stdlib.h"
//static int strcmp(){return-1;}
//#define strcmp __builtin_strcmp
main()
{
if(strcmp("X","X\376")>=0)abort();
exit(0);
}
