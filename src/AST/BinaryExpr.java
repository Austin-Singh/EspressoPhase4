package AST;
import Utilities.Visitor;

import java.math.*;

public class BinaryExpr extends Expression {

	public BinaryExpr(Expression left, Expression right, BinOp op) {
		super(left);
		nchildren = 3;
		children = new AST[] { left, right, op };
	}

	public Expression left()  { return (Expression)children[0]; }
	public Expression right() { return (Expression)children[1]; }
	public BinOp op()         { return (BinOp)children[2]; }

	public boolean isConstant() {
		return left().isConstant() && right().isConstant();
	}

	public Object constantValue() {
		BigDecimal lval = (BigDecimal) left().constantValue();
		BigDecimal rval = (BigDecimal) right().constantValue();

		switch(op().kind) {
		case BinOp.PLUS:  return lval.add(rval); 
		case BinOp.MINUS: return lval.subtract(rval); 
		case BinOp.MULT:  return lval.multiply(rval); 
		case BinOp.DIV:   
			if (left().type.isIntegralType() && right().type.isIntegralType()) 
				return new BigDecimal(lval.toBigInteger().divide(rval.toBigInteger()));
			new BigDecimal(lval.doubleValue()/rval.doubleValue());
		case BinOp.MOD: 
		case BinOp.LSHIFT:
		case BinOp.RSHIFT:
		case BinOp.RRSHIFT:
		case BinOp.AND:
		case BinOp.OR:
		case BinOp.XOR:
			int lint = lval.intValue();
			int rint = rval.intValue();
			switch(op().kind) {
			case BinOp.MOD:    return new BigDecimal(Integer.toString(lint % rint)); 
			case BinOp.LSHIFT: return new BigDecimal(Integer.toString(lint << rint));
			case BinOp.RSHIFT: return new BigDecimal(Integer.toString(lint >> rint));
			case BinOp.RRSHIFT: return new BigDecimal(Integer.toString(lint >>> rint));
			case BinOp.AND:    return new BigDecimal(Integer.toString(lint & rint)); 
			case BinOp.OR:     return new BigDecimal(Integer.toString(lint | rint)); 
			case BinOp.XOR:    return new BigDecimal(Integer.toString(lint ^ rint)); 
			}
		}
		return null;
	} 


	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitBinaryExpr(this);
	}

}

