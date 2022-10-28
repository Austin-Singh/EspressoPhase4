// BinaryExpr4.java
// ----------------
// Error msg:  "BinaryExpr4.java:11: Operator '^' requires both operands of either integral or boolean type."

public class BinaryExpr4 {
    void main() {
	int a;
	double b=2.1;
	
	a = 21; // this assignment is ok
        a = 1 ^ b;  // this assignment is not ok
    }

    void foo()
    {
	int ab;
	ab = 2;
    }
}
