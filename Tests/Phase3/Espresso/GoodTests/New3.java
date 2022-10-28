// New3.java
// ---------
// Error msg:  "New3.java:36: A( ) has private access in 'A'. "

class A {
    int a;
    private A() {
	a = 1;
    }

    A(int bb) {
	bb = 21;
    }
    int add(int b) {
	return a-b;
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
        A a = new A();  // the problem is here

        return a.foo();
    }
}
