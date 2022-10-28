//(1)
//#10: Cannot instantiate abstract class 'BB'.
public abstract class BB {
    public BB() {
    }
}

public class CC {
    public void foo() {
	BB bb = new BB();
    }
}
