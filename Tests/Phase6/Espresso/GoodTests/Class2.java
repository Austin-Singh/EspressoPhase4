//(1)
//
//-129
import System;

class A {
    int a;
    A() {
	a = 89;
    }
    int foo() {
	return -a;
    }
    void add(int a) {
        this.a = this.a + a;
    }
}


class Main {
    public static void main(String args[]) {
	A a = new A();
	a.add(6);
	a.add(34);
	System.out.println(a.foo());
    }
}
