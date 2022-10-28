// CastExpr1.java
// ----------------
// Error msg:  "CastExpr1.java: Illegal type cast. Cannot cast type 'double' to type 'boolean'."

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
	B = (boolean) 1.5;  // this is not ok
	a.add(6);
        a.add(34);
        return a.foo();
    }
}
