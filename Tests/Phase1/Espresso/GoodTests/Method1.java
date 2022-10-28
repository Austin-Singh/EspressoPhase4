// Output:
// Result: 5

class Main {
    int foo(int a, int b) {
	return (a+b)/2;
    }
    
    int main() {
	int a,b,c;

	a = 4;
	b = 6;
	c = foo(a,b);
	return c;

    }
}
