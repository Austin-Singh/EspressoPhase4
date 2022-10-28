//(8)
//
//Hello World 
//Hej Verden 
//Hallo Welt 
//Hola Mundo 
//Hello World 
//Hej Verden 
//Hallo Welt 
//Hola Mundo 
import System;

public class A {
    private String s;
    public A(String s) {
	this.s = s;
    }
    public void print() {
	System.out.print(s + " ");
    }
    String get() {
	return s;
    }
}

	

public class test34 {
    public static void main(String args[]) {
	A[][] a = new A[][] { { new A("Hello"), new A("World") }, 
			      { new A("Hej"),   new A("Verden")},
			      { new A("Hallo"), new A("Welt")}, 
			      { new A("Hola"),  new A("Mundo")} };
	for (int i=0;i<a.length;i++) {
	    for (int j=0;j<a[i].length;j++) 
		a[i][j].print();
	    System.out.println("");
	}
	for (int i=0;i<a.length;i++) {
	    for (int j=0;j<a[i].length;j++) 
		System.out.print(a[i][j].get() + " ");
	    System.out.println("");
	}
    }
}
