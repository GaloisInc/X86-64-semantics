#include "mini_string.h"
#include "mini_stdlib.h"
extern void abort ();
extern void exit (int);

int f (int a) {
	if (a < 12) {
	  if (a > -15) {
		a = a > 0 ? a : -a;
		if (a == 2)
		  return 0;
		return 1;
	  }
	}
	return 1;
}

int main (int argc, char *argv[]) {
	if (f (-2))
		abort ();
	exit (0);
}

