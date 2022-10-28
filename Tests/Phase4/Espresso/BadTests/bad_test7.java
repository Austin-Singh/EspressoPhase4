//(1)
//#6: Operator '>' requires operands of numeric type.
class test {
    public static void main() {
	test t;
	if (t > t) 
	    t = null;
    }
}

