// Output:
// Result: 51

class Main {

    int foo(int a) {
	return bar(a*10);
    }
    

    int bar(int b) {
	b = b + 1;
	return b;
    }

    int main() {
	int c = foo(5);
	return c;

    }
}
