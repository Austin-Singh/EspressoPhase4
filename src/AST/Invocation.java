package AST;
import Utilities.Visitor;

public class Invocation extends Expression {

	/** Note target() can return null */

	public MethodDecl targetMethod; // This one is needed in the code generation phase
	public Type targetType; // This one is needed in the code generation phase 

	public Invocation(Expression target, Name name, 
			Sequence /* of Expressions*/ params) {
		super(target);
		nchildren = 3;
		children = new AST[] { target, name, params };
	}

	public Invocation(Name name , Sequence /* of  Expressions */ params) {
		super(name);
		nchildren = 3;
		children = new AST[] { null, name, params };
	}

	public Expression target()     { return (Expression)children[0]; }
	public Name       methodName() { return (Name)children[1];       }
	public Sequence   params()     { return (Sequence)children[2];   }

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitInvocation(this);
	}
}
