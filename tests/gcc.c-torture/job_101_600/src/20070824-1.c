#include "mini_string.h"
#include "mini_stdlib.h"
/* PR tree-optimization/33136 */
/* { dg-require-effective-target alloca } */

extern void abort (void);

struct S
{
  struct S *a;
  int b;
};

int
main (void)
{
  struct S *s = (struct S *) 0, **p, *n;
  for (p = &s; *p; p = &(*p)->a);
  n = (struct S *) __builtin_alloca (sizeof (*n));
  n->a = *p;
  n->b = 1;
  *p = n;

  if (!s)
    abort ();
  return 0;
}
