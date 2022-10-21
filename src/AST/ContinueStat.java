package AST;
import Utilities.Visitor;

public class ContinueStat extends Statement {

	public ContinueStat(Token c) {
		super(c);
		nchildren = 0;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */


	public Object visit(Visitor v) {
		return v.visitContinueStat(this);
	}


}
