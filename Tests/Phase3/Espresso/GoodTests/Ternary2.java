// Ternary2.java
// -------------
// Error msg:  "Ternary2.java:15: Both branches of a ternary expression must be of the same type."

public class Assignment1 {
    void mm() {
	int aa;
	aa++;
    }

    void main() {
	int a;
	int b=5;
	
	a = (b != 3) ?  1 : "2";  // the problem is here
    }
}
