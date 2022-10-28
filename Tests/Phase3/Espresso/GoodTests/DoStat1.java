// DoStat1.java
// ------------
// Error msg:  "DoStat1.java:13: Non boolean Expression found as test in do-statement. "

public class DoStat1 {
    
    void main() {
	int a;
	byte b;
	
	do {
	    a = 2+1;
	} while (2*9);
    }
}
