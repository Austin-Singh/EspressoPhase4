// Output:
// Result: 65

class Main {
    int main() {
	int a,b,c;
	a = 10;
	b = 0;
	c = 0;
	while (a>0) {
	    b = b + a;
	    c++;
	    a--;
	}
	return a+b+c;
    }
}
