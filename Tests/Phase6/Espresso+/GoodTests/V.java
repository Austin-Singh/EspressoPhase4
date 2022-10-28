//(1)
//
//3
import System;
interface VV{
    public static  int i = 9;
    public int foo(int j);
}

public class V implements VV{
    
    public V(int i){}
    public int foo(int j){
	return j;
    }
    public static void main(String args[]){
	V a = new V(4);
	System.out.println(a.foo(3));
    }
}

