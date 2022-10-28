//(3)
//
//Hello
//We are running witout a main!
//Not really the right main
import System;

public class LookNoMain {
    public static void main(String args[]) { }
    
    public void fakeMain() { 
	System.out.println("Not really the right main");
    }

    public static void notMain() {
	System.out.println("We are running witout a main!");
	new LookNoMain().fakeMain();
	System.exit();
    }


    static {
	System.out.println("Hello");
	notMain();
    }
}