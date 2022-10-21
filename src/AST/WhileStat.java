package AST;
import Utilities.Visitor;

public class WhileStat extends Statement {

	public WhileStat(Expression expr, Statement stat) {
		super(expr);
		nchildren = 2;
		children = new AST[] { expr, stat };
	}

	public Expression expr() { return (Expression)children[0]; }
	public Statement  stat() { return (Statement)children[1];  }


	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitWhileStat(this);
	}


}
