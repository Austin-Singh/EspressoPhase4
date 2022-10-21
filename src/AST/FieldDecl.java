package AST;
import Utilities.Visitor;

public class FieldDecl extends ClassBodyDecl implements VarDecl  {

	public Modifiers modifiers;
	public boolean interfaceMember = false;
    public int fieldNumber; // this field it the 'fieldNumber'th field in th class. Needed for initializer checking
	
	public FieldDecl(Sequence /* of Modifier */ modifiers,
			Type type, Var var, boolean interfaceMember) {
		super(type);
		nchildren = 3;
		this.modifiers = new Modifiers();
		this.modifiers.set(false, false, modifiers);
		children = new AST[] { modifiers, type, var };
		this.interfaceMember = interfaceMember;
	}

	public Sequence modifiers() { return (Sequence)children[0]; }
	public Type type()          { return (Type)children[1];     } 
	public Var  var()           { return (Var)children[2];      }

	public String name() {
		return var().name().getname();
	}

	public String getname() {
		return var().name().getname();
	}

	public String toString() {
		return "FieldDecl>(Type:" + type() + " " + "Name:" + var() + ")";
	}

	public boolean isClassType() {
		return (type() instanceof ClassType);
	}

        public int address() {
		return 0;
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
		return v.visitFieldDecl(this);
	}
}
