interface test {
    int foo(int b);
}

class test3 {
    public int foo(int c) {
	return 1;
    }
}

class test2 extends test3 implements test{
}

