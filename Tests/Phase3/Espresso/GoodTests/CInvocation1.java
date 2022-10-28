// CInvocation1.java
// -----------------
// Error msg:  "No constructor A( double ) found.
//              Candidates are:
//              A( )"

class A {
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

class Main {
    int main() {
	int B;
        A a = new A(4.5); // the problem is here
	a.add(6);
        a.add(34);
        return a.foo();
    }
}
