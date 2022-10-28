// Var1.java
// ---------
// Error msg:  "Var1.java:15: Cannot assing value of type double to variable of type int."

public class Var1 {
    void mm() {
	int aa;
	aa++;
    }

    void main() {
	int a;
	boolean b;
	
	a = 2.5;   // the problem is here
    }
}
