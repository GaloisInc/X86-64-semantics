#include "mini_string.h"
#include "mini_stdlib.h"
/* Copyright (C) 2000  Free Software Foundation  */
/* by Alexandre Oliva <aoliva@redhat.com> */

#include <stdlib.h>

void bar (int);
void foo (int *);

int main () {
  int a[] = { 0, 1, 2 };
  //int *i = &a[sizeof(a)/sizeof(*a)];
  int *i = &a[3];
  
  while (i-- > a)
    foo (i);

  exit (0);
}

void baz (int, int);

void bar (int i) { baz (i, i); }
void foo (int *i) { bar (*i); }

void baz (int i, int j) {
  if (i != j)
    abort ();
}
