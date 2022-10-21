package AST;

public abstract class Statement extends AST {

	public Statement(Token t) {
		super(t);
	}

	public Statement(AST a) {
		super(a);
	}
}
