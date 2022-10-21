package AST;
import Utilities.Visitor;

public class MethodDecl extends ClassBodyDecl  {

	/**
	 * The class to which this method belongs.<br>
	 * This is set in the visitMethodDecl() in ClassAndMemberFinder.java
	 */

    public static final boolean IS_INTERFACE_MEMBER = true;
    public static final boolean IS_NOT_INTERFACE_MEMBER = false;

	private ClassDecl myClass; 
	private Modifiers modifiers;
	private boolean interfaceMember = false;

	public MethodDecl(Sequence /* of Modifier */ modifiers,
			Type returnType, Name name, 
			Sequence /* of ParamDecl */ params, 
			Block body,
			boolean interfaceMember) {
		super(name);
		nchildren = 5;
		this.modifiers = new Modifiers();
		this.modifiers.set(false, false, modifiers);
		children = new AST[] { modifiers, returnType, name, params, body };
		this.interfaceMember = interfaceMember;
	}

	public Sequence modifiers() { return (Sequence)children[0]; }
	public Type returnType()    { return (Type)children[1];     }
	public Name name()          { return (Name)children[2];     }
	public Sequence params()    { return (Sequence)children[3]; }
	public Block block()        { return (Block)children[4];    }

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
	public boolean isInterfaceMember() {
		return interfaceMember;
	}
	public void setMyClass(ClassDecl cd) {
		this.myClass = cd;
	}
	public ClassDecl getMyClass() {
		return this.myClass;
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
		return v.visitMethodDecl(this);
	}


}

