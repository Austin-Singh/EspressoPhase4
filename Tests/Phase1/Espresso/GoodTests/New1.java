// Output:
// Result: 25


class A {
    int a;
    A() {
	a = 9;
    }
}

class B {
    int b;
}

class C {
    int c;
    C(int c) {
	this.c = c;
    }
}


class Main {
    int main() {
	A a = new A();
	B b = new B();
	C c = new C(7);
	b.b = 9;;
	return a.a+b.b+c.c;
    }
}
