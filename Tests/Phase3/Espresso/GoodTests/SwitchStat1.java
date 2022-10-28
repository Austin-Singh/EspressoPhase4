// SwitchStat1.java
// ----------------
// Error msg:  "SwitchStat1.java:15: Expression type does not match type of  label in line 16."

public class Assignment1 {
    void mm() {
	int aa;
	aa++;
    }

    void main() {
	int a;
	byte b;
	
	switch (a) {
	case "1": a++;  // "1" is a string and a is integer
	}
    }
}
