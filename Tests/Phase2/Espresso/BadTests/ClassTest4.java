//(4)
//#18: Syntax error:
//
//public class ClassTest4  extends A extends
//                                   ^
class A {
    int a;
    public int getA() {
	a++;
	return ++a;
    }
}

class B {
    int b;
}

public class ClassTest4  extends A extends B {   
}
