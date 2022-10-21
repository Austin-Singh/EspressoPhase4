package AST;
import Utilities.Visitor;

public class ConstructorDecl extends ClassBodyDecl  {

	private Modifiers modifiers;

	public ConstructorDecl(Sequence /* of Modifiers */ modifiers, Name name, 
			Sequence /* of ParamDecl */ params, 
			CInvocation cInvocation,
			Sequence /* of Statement */ body) {
		super(name);
		nchildren = 5;
		this.modifiers = new Modifiers();
		this.modifiers.set(false, true, modifiers);
		children = new AST[] { modifiers, name, params, cInvocation, body };
	}

	public Sequence modifiers()  { return (Sequence)children[0]; }
	public Name name()           { return (Name)children[1];     }
	public Sequence params()     { return (Sequence)children[2]; }
	public CInvocation cinvocation() { return (CInvocation)children[3]; }
	public Sequence body()       { return (Sequence)children[4];    }

	public String getname() {
		return name().getname();
	}   

	public String paramSignature() {
		String s = "";
		Sequence params = params();

		for (int i=0;i<params.nchildren;i++)
			s = s + ((ParamDecl)params.children[i]).type().signature();
		return s;
	}

	public boolean isStatic() {
		return modifiers.isStatic();
	}

	public Modifiers getModifiers() {
		return this.modifiers;
	}

	/* *********************************************************** */
	/* **                                                       ** */
	/* ** Generic Visitor Stuff                                 ** */
	/* **                                                       ** */
	/* *********************************************************** */

	public Object visit(Visitor v) {
		return v.visitConstructorDecl(this);
	}
}

