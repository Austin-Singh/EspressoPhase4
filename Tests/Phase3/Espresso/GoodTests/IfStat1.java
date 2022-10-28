// IfStat1.java
// ------------
// Error msg:  "IfStat1.java:10: Non boolean Expression found as test in if-statement."

public class ForStat1 {
    void main() {
	int a;
	int b;
	
	if (a+b)  // the problem is here
        {
	    b++;
	}
    }
}
