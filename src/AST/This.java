package AST;
import Utilities.Visitor;

public class This extends Expression {

	public This(Token p_t) {
		super(p_t);
		nchildren = 0;
	}

	public ClassType type() { return (ClassType)type; }

	public boolean isConstant() {
		return true;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitThis(this);
	}


}

