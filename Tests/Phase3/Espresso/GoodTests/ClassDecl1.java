// ClassDecl1.java
// ---------------
// Error msg:  "CInvocation2.java:28: cannot inherit from final A"

final class A {  // A was declared final
    int a;
    A() {
        a = 89;
    }

    int foo() {
        return -a;
    }
}

class AA {
    int b;
    
    AA() {
	b = 1;
    }
    
    int foo() { return 1; }
}

class Main extends A {
    int main() {
	int B;
        A a = new A(); // the problem is here
	a.add(6);
        a.add(34);
        return a.foo();
    }
}
