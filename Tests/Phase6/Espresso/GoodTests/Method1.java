//(1)
//
//5
import System;

class Main {
    int foo(int a, int b) {
	return (a+b)/2;
    }
    
    public static void main(String args[]) {
	int a,b,c;

	a = 4;
	b = 6;
	c = new Main().foo(a,b);
	System.out.println(c);

    }
}
