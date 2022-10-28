//(4)
//
//256
//3125
//10000000
//10003381   
import System;

class Power {
    // power 1
    int p1(int m, int n) {
	if (n==0) {
	    return 1;
	} else {
	    return m * p1(m,n-1);
	}
    }
    

    // power 2
    int p2_h(int m, int n, int acc) {
	if (n==0) {
	    return acc;
	} else {
	    return p2_h(m,n-1,m*acc);
	}
    }
    
    int p2(int m, int n) {
	return p2_h(m,n,1);
    }

    // power 3
    int square(int n) {
	return n*n;
    }
    
    boolean even(int n) {
	return (n%2 == 0);
    }

    int p3(int m, int n) {

	if (n==0){
	    return 1;
	}
	else {
	    if (even(n)) {
		return square(p3(m,n/2));
	    } else {

		return m*square(p3(m,(n-1)/2));
		
	    }
	}
    }
}

class Main {
    Main() {
    }

    public static void main(String args[]) {
	Power p = new Power();
	int p1,p2,p3;
	p1 = p.p1(2,8);
	System.out.println(p1);
	p2 = p.p2(5,5);
	System.out.println(p2);
	p3 = p.p3(10,7);
	System.out.println(p3);
	
	System.out.println(p1+p2+p3);
    }
}
