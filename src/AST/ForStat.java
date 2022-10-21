package AST;
import Utilities.Visitor;

public class ForStat extends Statement {

	/* Note that init() and incr() can be null */

	public ForStat(Token t, Sequence /* of Statements*/ init, 
			Expression expr, 
			Sequence /* of Expressions */ incr , 
			Statement stat) {
		super(t);
		nchildren = 4;
		children = new AST[] { init, expr, incr, stat };
	}

	public Sequence   init()  { return (Sequence)children[0];   }
	public Expression expr()  { return (Expression)children[1]; }
	public Sequence   incr()  { return (Sequence)children[2];   }
	public Statement  stats() { return (Statement)children[3];  }

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitForStat(this);
	}
}
