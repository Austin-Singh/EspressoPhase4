// BinaryExpr8.java
// ----------------
// Error msg:  "BinaryExpr8.java:23: 'B' is not a class name."

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
	if (A instanceof B) B=1;  // this is not ok
	a.add(6);
        a.add(34);
        return a.foo();
    }
}
