//(1)
//#5: Class name 'test' cannot appear as parameter to operator '!='.
class test {
    public static void main() {
	if (test != test)
	    test = null;
    }
}