#include "mini_string.h"
#include "mini_stdlib.h"
/* { dg-require-effective-target untyped_assembly } */
int s[2];
x(){if(!s[0]){s[1+s[1]]=s[1];return 1;}}
main(){s[0]=s[1]=0;if(x(0)!=1)abort();exit(0);}
