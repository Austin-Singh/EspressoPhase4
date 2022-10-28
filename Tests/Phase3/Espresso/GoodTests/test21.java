 class A {
    final void foo() { }
}

 class B extends A {
    static final void foo() { }
}

 class C extends B {
    void foo() { }
    void bar() {
	foo();
    }	
}

