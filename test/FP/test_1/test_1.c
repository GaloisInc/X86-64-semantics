extern int printf(const char *str, ...);

void testfunc(short s, float X, char C, long long LL, int I, double D) {
	printf("%d, %f, %d, %lld, %d, %f\n", s, X, C, LL, I, D);
}

int main() {
	testfunc(12, 1.245f, 'x', 123456677890LL, -10, 4.5);
        return 0;
}
