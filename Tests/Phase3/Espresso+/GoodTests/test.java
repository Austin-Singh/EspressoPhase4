class blah {
}

interface fu {
    int field = 90;

    void foo () ;
}

public final class test extends blah implements fu {
    int fi = bar();
    
    int bar() {
	return 1;
    }

    /*    public final static int a = 9;

    private test() { }

    
    public void bar() {
	foo();
	test2.baz();
    }

    public static void foo() {
	new test2().bar();
	test2.baz();
	int a;

	a = test2.aa;
	a = new test2().aa;
	a = new test2().bb;
        a = test.a;       

	a = (a<=7) ? a=b : (a)b;
    */
    public void foo() {}
    
    int val;
    int       key;
        
    public test(int val, int key) {
	this.val   = val;
	this.key   = key;
    }

    public test(int val) {
	this.val = val;
    }
    

    String Complicate(test t, boolean b, int in, int out, float fl) {
	return Complicate(t, "Hello");
    }
    
    String Complicate(test t, String s) {
	return "Hello";
    }

    public void run() {
	fi = field;
	String s;
	test t=null;
	int i;
	s = Complicate(t, true, 0x0df9, 9, 12.29f);
	//t = (blah) t;

	switch (t.val) {
	case 1: i=0; break;
	case 2:
	case 3: { i=89; break;}
	default: i = 8;
	}
	
    }
    
    
    
}


