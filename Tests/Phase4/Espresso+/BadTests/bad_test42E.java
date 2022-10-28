//(1)
//#0: Duplicate default label.
class test {
    public static void main() {
	int a;
	switch(a) {
	default: a=0;
	default: a=9;
	}
    }
}