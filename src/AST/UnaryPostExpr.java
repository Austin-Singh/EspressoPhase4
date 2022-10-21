package AST;
import Utilities.Visitor;

public class UnaryPostExpr extends Expression {

	public UnaryPostExpr(Expression expr, PostOp op) {
		super(expr);
		nchildren = 2;
		children = new AST[] { expr, op };
	}

	public Expression expr() { return (Expression)children[0]; }
	public PostOp op()       { return (PostOp)children[1];     }


	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitUnaryPostExpr(this);
	}
}
