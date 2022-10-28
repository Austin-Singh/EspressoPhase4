// Assignment1.java
// ----------------
// Error msg:  "Assignment1.java:11: Cannot assing value of type int to variable of type byte."

public class Assignment1 {
    void main() {
	int a;
	byte b;
	
	a = b; // this assignment is ok
	b = a; // this assignment is not ok
    }
}
