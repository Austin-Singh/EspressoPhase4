package AST;

import Utilities.Visitor;

import java.math.*;

public class UnaryPreExpr extends Expression {

	public UnaryPreExpr(Expression expr, PreOp op) {
		super(expr);
		nchildren = 2;
		children = new AST[] { expr, op };
	}

	public Expression expr() {
		return (Expression) children[0];
	}

	public PreOp op() {
		return (PreOp) children[1];
	}

	public boolean isConstant() {
		if (op().getKind() != PreOp.PLUSPLUS && op().getKind() != PreOp.MINUSMINUS)
			return expr().isConstant();
		return false;
	}

	public Object constantValue() {
		Object o = expr().constantValue();
		if (o instanceof Boolean)
			return new Boolean(!((Boolean) o).booleanValue());

		BigDecimal val = (BigDecimal) o;
		switch (op().getKind()) {
		case PreOp.PLUS:
			return val;
		case PreOp.MINUS:
			return val.negate();
		case PreOp.COMP:
			return new BigDecimal(Integer.toString(~val.intValue()));
		}
		return null;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitUnaryPreExpr(this);
	}

}
