//(1)
//
//12
import System;

public class GoodSwitch {
    
    public static void main(String args[]) {
	int a = 1;
	
	switch (a) {
	case 1: 
	    a++;
	    for (int i =0; i < 10; i++)
		a++;
	    break;
	case 3:   
	    a--;  
	    break;
	case 4:   
	    a++;  
	    break;
	}
        System.out.println(a);
    }
}
