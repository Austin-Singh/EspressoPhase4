// Invocation1.java
// ----------------
// Error msg:  "Invocation1.java:36: Attempt to invoke method 'add' in something not of class type."

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
	B.add(6);      // the problem is here
        return a.foo();
    }
}
