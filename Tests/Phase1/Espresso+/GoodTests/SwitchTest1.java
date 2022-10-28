
public abstract class SwitchTest1 {
	abstract void f(int a);
	
	int g(int a) {
		switch(a) {
			case 3: return a+1;
			case 4: return 0;
			default: return -1;
		}
	}
}
