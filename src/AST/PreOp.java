package AST;
import Utilities.Visitor;

public class PreOp extends AST {

	public static final int PLUSPLUS   = 1; // ++
	public static final int MINUSMINUS = 2; // --
	public static final int PLUS       = 3; // +
	public static final int MINUS      = 4; // -
	public static final int COMP       = 5; // ~
	public static final int NOT        = 6; // !

	private int kind;
	private static final String [] opSyms = { "" , "++", "--", "+", "-", "~", "!" };

	public PreOp(Token t, int kind) {
		super(t);
		this.kind = kind;
	}

	public String operator() { return opSyms[kind]; }

	public int getKind() {
		return this.kind;
	}
	
	public String toString() { return opSyms[kind]; }

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitPreOp(this);
	}


}
