package AST;
import Utilities.Visitor;

public class DoStat extends Statement {

	public DoStat(Statement stat, Expression expr) {
		super(expr);
		nchildren = 2;
		children = new AST[] { stat, expr };
	}

	public Statement  stat() { return (Statement)children[0];  }
	public Expression expr() { return (Expression)children[1]; }


	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitDoStat(this);
	}
}
