package AST;

import Utilities.SymbolTable;
import Utilities.Visitor;

public class ClassDecl extends AST {
	//<--
	public Modifiers modifiers;
	// Symbol Table methods and data    
	public SymbolTable methodTable = new SymbolTable();
	public SymbolTable fieldTable  = new SymbolTable();
	
	private boolean generateCode = true; // imported files need not generate code cause their
	// respective class files are located in the Include/Library folder.
	

	// Methods in the class hierarchy
	// These are set in NameChecker.java: checkImplementationOfAbstractClasses
	public Sequence abstractMethods = new Sequence(); // all abstract methods in the class hierarchy
	public Sequence concreteMethods = new Sequence(); // all concrete methods in the class hierarchy
	public Sequence allMethods      = new Sequence(); // all concrete and abstract methods in the class hierarchy
	public Sequence constructors    = new Sequence(); // all constructors for this class.

	public static final boolean IS_INTERFACE = true;
	public static final boolean IS_NOT_INTERFACE = false;
	public boolean m_class = false, 
			m_interface = false;

	public ClassDecl(Sequence /* of Modifier */ modifiers,
			Name name, 
			ClassType superclass,
			Sequence /* ClassType */ interfaces,
			Sequence /* of ClassBodyDecl */ body,
			boolean isInterface) {
		super(name);
		nchildren = 5;
		this.modifiers = new Modifiers();
		this.modifiers.set(true, false, modifiers);
		children = new AST[] { modifiers, name, superclass, interfaces, body };
		m_interface = isInterface;
		m_class = !isInterface;
	}

	public Sequence  modifiers()  { return (Sequence)children[0];  }
	public Name      className()  { return (Name)children[1];      }
	public ClassType superClass() { return (ClassType)children[2]; }
	public Sequence  interfaces() { return (Sequence)children[3];  } 
	public Sequence  body()       { return (Sequence)children[4];  }

	public String name() {
		return className().toString();
	}

	public boolean isInterface() {
		return m_interface;
	}

	public boolean isClass() {
		return m_class;
	}

	public String toString() {
		return "ClassDecl>(Name:" + name() + ")";
	}

	public void doNotGenerateCode() {
		generateCode = false;
	}
	
	public boolean generateCode() {
		return this.generateCode;
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
		return v.visitClassDecl(this);
	}

	//-->
}
