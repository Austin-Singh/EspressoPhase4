// Output:
// Result: -129

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
    int main() {
	A a = new A();
	a.add(6);
	a.add(34);
	return a.foo();
    }
}
