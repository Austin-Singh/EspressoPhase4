package AST;
import Utilities.Visitor;

public class Modifier extends AST {

	private int modifier = -1;

	public final static int Public    = 1;
	public final static int Private   = 2;
	public final static int Static    = 3;
	public final static int Final     = 4;
	public final static int Abstract  = 5;

	public Modifier(Token t, int modifier) {
		super(t);
		this.modifier = modifier;
	}

	public Modifier(int modifier) {
		super((AST)null);
		this.modifier = modifier;
	}
	
	public int getModifier() {
		return this.modifier;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitModifier(this);
	}
}
