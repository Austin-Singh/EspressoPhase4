// Output:
// Result: 89

class A {
    int a;
    A() {
	a = 89;
    }
    int foo() {
	return a;
    }

}


class Main {
    int main() {
	A a = new A();
	return a.foo();
    }
}
