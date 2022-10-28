//(2)
//
//8
//8
import System;

class A {
    B b;
    A a;
    int value;
}

class B {
    A a;
    B b;
    int value;
}

class Main {
    public static void main(String args[]) {
	A a = new A();
	B b = new B();

	a.b = b.b = b;
	b.a = a.a = a;

	a.b.a.b.a.b = b.a.b.a.b.a.b.a.b;
	a.b.a.b.a.value = 8;
	b.a.b.a.b.value = a.b.a.b.a.b.a.b.a.value;
	System.out.println(a.value);
	System.out.println(b.value);
    }
}
