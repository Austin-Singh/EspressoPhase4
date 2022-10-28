//(4)
//#18: Syntax error:
//
//public class ClassTest5  implements B1 extends
//                                       ^
class A1 {
    int a;
    public int getA() {
        a++;
        return ++a;
    }
}

interface B1 {
    int b;
}

public class ClassTest5  implements B1 extends A1{
}
