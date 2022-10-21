package AST;
import Utilities.Visitor;

public class Super extends Expression {
    //public ClassType type;

	public Super(Token p_t) {
		super(p_t);
		nchildren = 0;
	}

    public ClassType type() { return (ClassType)type; }

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitSuper(this);
	}
}

