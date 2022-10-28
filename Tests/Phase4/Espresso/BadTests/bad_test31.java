//(1)
//#7: Attempt to invoke method 'f' in something not of class type.
class test {
    public void f() { }
    public static void main() {
	int a;
	a.f();
    }
}