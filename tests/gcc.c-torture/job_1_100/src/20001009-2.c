#include "mini_string.h"
#include "mini_stdlib.h"
int foo()
{
int b=1;
  int a;
  int c;
  a=0xff;
  for (;b;b--)
  {
    c=1;
    asm(""::"r"(c));
    c=(signed char)a;
  }
  if (c!=-1)
    abort();
  return c;
}
int main()
{
  foo();
  return 0;
}
