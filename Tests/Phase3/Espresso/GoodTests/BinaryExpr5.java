// BinaryExpr5.java
// ----------------
// Error msg:  "BinaryExpr5.java:11: Operator '%' requires operands of numeric type. "

public class BinaryExpr5 {
    void main() {
	int a;
	float b;
	
	a = 21;           // this assignment is ok
	a = (100 % "c");  // this assignment is not ok
    }

    void foo()
    {
	int ab;
	ab = 2;
    }
}
