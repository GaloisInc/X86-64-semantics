#include "mini_string.h"
#include "mini_stdlib.h"

int
f1 ()
{
  unsigned long x, y = 1;

  x = ((y * 8192) - 216) % 16;
  return x;
}

int
main ()
{
  if (f1 () != 8)
    abort ();
  exit (0);
}
