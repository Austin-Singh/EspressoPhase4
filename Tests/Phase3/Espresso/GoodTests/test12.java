class A {
} 

class AA extends A {
    AA() {}

    AA(int a) {
    }

    private AA(String s) {
    }
    void foo() {
	AA aa = new AA();
	AA aaa = new AA(5);
	A a = new A();

	AA a2 = new AA("Hello");
    }
}
 
