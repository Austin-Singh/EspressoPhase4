//(1)
//
//89
import System;

class A {
    int a;
    A() {
	a = 89;
    }
    int foo() {
	return a;
    }

}


class Main {
    public static void main(String args[]) {
	A a = new A();
	System.out.println(a.foo());
    }
}
