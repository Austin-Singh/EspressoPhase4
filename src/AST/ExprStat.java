package AST;
import Utilities.Visitor;

public class ExprStat extends Statement {

	public ExprStat(Expression expression) {
		super(expression);
		nchildren = 1;
		children = new AST[] { expression };
	}

	public Expression expression() { return (Expression)children[0]; }

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */


	public Object visit(Visitor v) {
		return v.visitExprStat(this);
	}
}
