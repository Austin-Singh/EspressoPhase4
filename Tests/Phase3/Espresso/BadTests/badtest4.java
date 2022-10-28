//(3)
//# Method 'f' has been declared with two different return types:
//#10:  boolean f( int )
//#6:  int f( int )
public class A {
    int f(int a) { }
}

public class B extends A {
    boolean f(int a) { }
}
