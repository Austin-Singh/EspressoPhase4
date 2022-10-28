// New1.java
// ---------
// Error msg:  "No constructor A( int ) found.
//              Candidates are:"

class A {
    int a;

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
        A a = new A(12);  // the problem is here

        return a.foo();
    }
}
