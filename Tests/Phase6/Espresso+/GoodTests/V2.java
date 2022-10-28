//(1)
//
//Hello 
import System;

public class Main {
    public static void main(String args[]) {
	int i=0;
	while (i<=5) {
	    switch (i) {
	    case 0: System.out.print('H'); break;
	    case 1: System.out.print('e'); break;
	    case 2:
	    case 3: System.out.print('l'); break;
	    case 4: System.out.print('o'); break;
	    default: System.out.println(' ');
	    }
	    i++;
	}
    }
}