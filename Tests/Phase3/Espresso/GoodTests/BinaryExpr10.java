// BinaryExpr10.java
// ----------------
// Error msg:  "BinaryExpr10.java:32: Left hand side of instanceof cannot be a class."

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

class AA {
    int b;
    
    AA() {
	b = 1;
    }
    
    int foo() { return b*b; }
}

class Main {
    int main() {
	int B;
        A a = new A();
	if (AA instanceof A) B=1;  // this is not ok
	a.add(6);
        a.add(34);
        return a.foo();
    }
}
