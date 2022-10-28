// WhileStat1.java
// ---------------
// Error msg:  "WhileStat1.java:15: Non boolean Expression found as test in while-statement."

public class WhileStat1 {
    void mm() {
	int aa;
	aa++;
    }

    void main() {
	int a;
	boolean b;
	
	while ("1+2") {   // the problem is here
	    a++;
	}
    }
}
