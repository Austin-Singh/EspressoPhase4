//(1)
//
//42
import System;
public class Foo {
    static int fubar = 42;

    Foo getFoo() {
        return null;    
    }

    public static void main(String args[]) {
        Foo foo = new Foo();
        System.out.println(foo.getFoo().fubar);
    }
}
