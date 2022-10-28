//(3)
//
//7
//9
//11
import System;

class test {
    int a = 7;
    test () {}
    int t1() { return a; }
}
class test2 {
    int b = 9;
    int t1() { return b; }
}

class test3 {
    int c;
    int t1() { c=11; return c; }
}

class Main {
    public static void main(String args[]) {
	System.out.println(new test().t1());
	System.out.println(new test2().t1());
	System.out.println(new test3().t1());
    }
}
