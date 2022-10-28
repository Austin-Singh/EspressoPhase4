// BinaryExpr9.java
// ----------------
// Error msg:  "BinaryExpr9.java:23: Left hand side of instanceof needs expression of class type"

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
	int B;
        A a = new A();
	if (B instanceof A) B=1;  // this is not ok
	a.add(6);
        a.add(34);
        return a.foo();
    }
}
