// Output:
// Result: 16512

class A {
    int a;
    A() {
	a = 89;
    }
    int foo() {
	return -a;
    }
    void add(int a) {
        this.a = this.a + a;
    }
}


class Main {
    int b;
    int main() {
	A a = new A();
	a.add(6);
	a.add(34);
	b=a.a;
	return a.foo()+a.a*b;
    }
}
