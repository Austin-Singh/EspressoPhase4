//(1)
//#8: Duplicate case label.
class test {
    public static void main() {
	int a;
	switch(a) {
	case 4: a=9;
	case 4: a=10;
	}
    }
}
