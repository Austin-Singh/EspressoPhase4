//(4)
//#17: Syntax error:
//
//public class ClassTest3  extends A,
//                                  ^
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
public class ClassTest3  extends A, B {   
}
