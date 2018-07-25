
int a(int x);
int b();
int c();
int d();
int e();


int lookup(int i) {
    switch (i) {
    case 0:
	return a(1);
    case 1:
	return b();
    case 2:
	return c();
    case 3:
	return d();
    case 4:
	return e();
    case 5:
	return 5;
    case 6:
	return 1123213;
    case 7:
	return 191286;
    case 8:
	return 921312;
    default:
	return 0;
    }
}
