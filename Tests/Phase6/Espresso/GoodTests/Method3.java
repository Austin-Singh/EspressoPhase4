//(1)
//
//51
import System;

class Main {

    int foo(int a) {
	return bar(a*10);
    }
    

    int bar(int b) {
	b = b + 1;
	return b;
    }

    public static void main(String args[]) {
	Main m = new Main();
	int c = m.foo(5);
	System.out.println(c);
    }
}
