// ForStat1.java
// ----------------
// Error msg:  "ForStat1.java:10: Non boolean Expression found in for-statement."

public class ForStat1 {
    void main() {
	int a;
	int b;
	
	for (a=1; a+1; a++)  // the problem is here
        {
	    b++;
	}
    }
}
