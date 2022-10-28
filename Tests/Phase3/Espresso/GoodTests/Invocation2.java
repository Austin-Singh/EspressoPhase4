// Invocation2.java
// ----------------
// Error msg:  "Invocation2.java: No method food( int ) found.
//              Candiates are:"

class A {
    int a;
    A() {
        a = 89;
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
        A a = new A();
	A.food(6);      // the problem is here
        return a.foo();
    }
}
