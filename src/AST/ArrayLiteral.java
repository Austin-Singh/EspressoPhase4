package AST;

import Utilities.Visitor;

public class ArrayLiteral extends Expression {

	public ArrayLiteral(Sequence seq) {
		super(seq);
		nchildren = 1;
		children = new AST[] { seq };
	}

	public Sequence elements() {
		return (Sequence)children[0];
	}

	public String toString() {
		return "{.,.,.,.,.}";
	}


	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitArrayLiteral(this);
	}
}
