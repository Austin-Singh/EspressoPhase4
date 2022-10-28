//(4)
//
//From A:
//15
//From AA:
//20
import System;

class A {
    A() {}

    int a;
    A(int a) {
	this.a = a;
    }

    public void bar() {
	System.out.println("From A:");
	System.out.println(a);
    }
} 

class AA extends A {
    int b;
    public AA() {
	b = 89;
    }

    AA(int a) {
	super(a+10);
	b = a;
    }

    public void bar() {
	int a;
	super.bar();

	a = b + this.a; 
	System.out.println("From AA:");
	System.out.println(a);
    }

    private AA(String s) {
    }
    void foo() {
	AA aa = new AA();
	AA aaa = new AA(5);
	A a = new A();

	AA a2 = new AA("Hello");
	aaa.bar();
    }
    public static void main(String args[]) {
	new AA().foo();
    }

}


 
