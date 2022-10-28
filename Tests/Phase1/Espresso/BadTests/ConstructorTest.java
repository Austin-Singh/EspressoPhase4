//(4)
//#15: Syntax error:
//
//    a.
//     ^
class A {
    B b;
}

class B {
    A a;
}
public class ConstructorTest {
    A a = new A();
    a.a = 10;
}
