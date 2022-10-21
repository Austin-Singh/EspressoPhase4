package AST;
import Utilities.Visitor;

public class AssignmentOp extends AST {

	public int kind;

	public static final int EQ        = 1;
	public static final int MULTEQ    = 2;
	public static final int DIVEQ     = 3;
	public static final int MODEQ     = 4;
	public static final int PLUSEQ    = 5;
	public static final int MINUSEQ   = 6;
	public static final int LSHIFTEQ  = 7;
	public static final int RSHIFTEQ  = 8;
	public static final int RRSHIFTEQ = 9;
	public static final int ANDEQ     = 10;
	public static final int OREQ      = 11;
	public static final int XOREQ     = 12;

	public static final String [] opSyms = {
		"", "=", "*=", "/=", "%=", "+=", "-=", "<<=", 
		">>=", ">>>=", "&=", "|=", "^="  };

	public AssignmentOp(Token t, int kind) {
		super(t);
		this.kind = kind;
	}

	public AssignmentOp(int kind) {
		super(0,0);
		this.kind = kind;
	}

	public String operator() { return opSyms[kind]; }

	public String toString() { return opSyms[kind]; }

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitAssignmentOp(this);
	}


}
