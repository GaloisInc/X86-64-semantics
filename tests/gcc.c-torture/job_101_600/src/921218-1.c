#include "mini_string.h"
#include "mini_stdlib.h"
f()
{
  return (unsigned char)("\377"[0]);
}

main()
{
  if (f() != (unsigned char)(0377))
    abort();
  exit (0);
}
