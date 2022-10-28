// BinaryExpr1.java
// ----------------
// Error msg:  "BinaryExpr1.java:11: Operator '>=' requires operands of numeric type."

public class BinaryExpr1 {
    void main() {
	int a;
	boolean b;
	
	a = 21; // this assignment is ok
	a = (1 >= b);  // this assignment is not ok
    }
}
