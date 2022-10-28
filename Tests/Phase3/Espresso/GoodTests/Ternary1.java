// Ternary1.java
// -------------
// Error msg:  "Ternary1.java:15: Non boolean Expression found as test in ternary expression. "

public class Assignment1 {
    void mm() {
	int aa;
	aa++;
    }

    void main() {
	int a;
	byte b;
	
	a = (2+3) ?  1 : 2;  // the problem is here
    }
}
