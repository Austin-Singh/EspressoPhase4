// Output:
// Result: 0
// we are testing that you don't get a stack overflow here !

class test {
    int t1() {
	return 6;
    }

    void t2() {
	return ;
    }
}

class Main {
    public static void main() {
	int i;
	for (i=0;i<10000;i++) {
	    new test().t1();
	}

	for (i=0;i<10000;i++) {
	    new test().t2();
	}
	test t = new test();

	for (i=0;i<10000;i++) {
	    t.t1();
	}

	for (i=0;i<10000;i++) {
	    t.t2();
	}

	for (i=0;i<10000;i++) {
	    new test();
	}


    }

}
