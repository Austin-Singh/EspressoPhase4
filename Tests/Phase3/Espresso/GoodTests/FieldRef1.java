// FieldRef1.java
// --------------
// Error msg:  "FieldRef1.java:34: Field 'b' not found in class 'A'."

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

class Main extends A {
    int main() {
	int B;
        A a1 = new A(); 

	B = a1.b + 12;   // the problem is here
	
        return a1.foo();
    }
}
