#include "mini_string.h"
#include "mini_stdlib.h"
#include <stdio.h>
#include <stdarg.h>

struct spurious
{
    int anumber;
};

int first(char *buf, char *fmt, ...)
{
  int pos, number;
  va_list args;
  int dummy;
  char *bp = buf;

  va_start(args, fmt);
  for (pos = 0; fmt[pos]; pos++)
    if (fmt[pos] == 'i')
      {
	number = va_arg(args, int);
	//sprintf(bp, "%d", number);
	bp += strlen(bp);
      }
    else
      *bp++ = fmt[pos];

  va_end(args);
  *bp = 0;
  return dummy;
}

struct spurious second(char *buf,char *fmt, ...)
{
  int pos, number;
  va_list args;
  struct spurious dummy;
  char *bp = buf;

  va_start(args, fmt);
  for (pos = 0; fmt[pos]; pos++)
    if (fmt[pos] == 'i')
      {
	number = va_arg(args, int);
	//sprintf(bp, "%d", number);
	bp += strlen(bp);
      }
    else
      *bp++ = fmt[pos];

  va_end(args);
  *bp = 0;
  return dummy;
}

main()
{
  char buf1[100], buf2[100];
  first(buf1, "i i ", 5, 20);
  second(buf2, "i i ", 5, 20);
  if (strcmp ("5 20 ", buf1) || strcmp ("5 20 ", buf2))
    abort();
  exit(0);
}
