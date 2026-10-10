long add(long a, long b) { return a + b; }
unsigned int wrap(unsigned int a, unsigned int b) { return a + b; }
int mixed(int a, unsigned int b) { return a < b; }
unsigned int right(unsigned int a, unsigned int b) { return a >> b; }
unsigned char bump(unsigned char a) { a++; return a; }
long nested(long a, long b) { return (a + b) * b; }
long literal(void) { return 2147483648 + 1; }
long mixedwidth(long a, unsigned int b) { return a + b; }
int promote(unsigned char a, int b) { return a + b; }
unsigned int hexliteral(void) { return 0xffffffff | 0; }
unsigned long long wideshift(void) { return 1ULL << 40; }
int octalcompare(void) { return 037777777777 < 0; }
