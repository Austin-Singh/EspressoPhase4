package AST;
import Utilities.Visitor;

public class PostOp extends AST {

	public static final int PLUSPLUS   = 1; // ++
	public static final int MINUSMINUS = 2; // --

	private int kind;

	public PostOp(Token t, int kind) {
		super(t);
		this.kind = kind;
	}

	public static final String [] opSyms = { "", "++", "--" };

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
		return v.visitPostOp(this);
	}


}
