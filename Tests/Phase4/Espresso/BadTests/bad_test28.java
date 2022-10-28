//(1)
//#7: Attempt to access field 'a' in something not of class type.
class test {
    public int a;
    public static void main() {
	int a;
	a.a = 10;
    }
}
