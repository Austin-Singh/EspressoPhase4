// New2.java
// ---------
// Error msg:  "New2.java:34: Default constructor for class 'A' must be implemented. "

class A {
    int a;

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
