//(1)
//#9: Switch labels must be constants.
class test {
    public int f() { return 6; }
    public static void main() {
	test t;
	int a;
	switch(a) {
	case t.f(): a = 9;
	}
    }
}