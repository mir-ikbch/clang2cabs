int x;

int test(int x, int y) {
    int z;
    int w = x + y;
    z = x * y;
    return z;
}

void test2() {
    int i, a = 0;
    for (i = 0; i < 10; i = i + 1) {
        a = a + i;
    }
    i = 0;
    goto foo;
    while (i < 10) {
        a = a + i;
        i = i + 1;
        continue;
    }
    foo:
    if (!(a > 20)) {
        a = 0;
        if (i != 10) a = 99;
    } else {
        a = 42;
    }
    return;
}

int main(void) {
    int a, b, c;
    c = -101;
    a = 2 * (3 + 1) - 1;
    b = 10 % 6 / 4;
    c = test(a, b);
    return 0;
}
