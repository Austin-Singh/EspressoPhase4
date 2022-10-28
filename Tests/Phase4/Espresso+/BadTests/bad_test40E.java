//(1)
//#7: Switch labels must be of type int.
class test {
    public static void main() {
	int a;
	switch(a) {
	case 4.4: a = 9;
	}
    }
}
