package NameChecker;

import AST.*;
import Utilities.Error;
import Utilities.SymbolTable;
import Utilities.Visitor;
import Parser.*;
import Phases.Phase2;

/** A visitor class which visits classes, and their members and enters  
    them into the appropriate tables */
public class ClassAndMemberFinder extends Visitor {
	
	private void addMethod(ClassDecl cd, ClassBodyDecl md, String name, String sig) {
		SymbolTable st = (SymbolTable)cd.methodTable.get(name);

		// Are there methods defined in this class' symbol table with the right name?
		if (st != null) {
			// Are there any methods with the same parameter signature?
			Object m = st.get(sig);
			if (m != null) 		
				Error.error(md,"Method " + name + "(" + Type.parseSignature(sig) + " ) already defined.");
		}

		// If we are inserting a constructor just insert in now - don't
		// go looking in the super classes.
		if (name.equals("<init>")) {
			if (st == null) {
				//A constructor with this name has never been inserted before
				// Create a new symbol table to hold all constructors.
				SymbolTable mt = new SymbolTable();
				// Insert the signature with the method decl.
				mt.put(sig, md);
				// Insert this symbol table into the method table.
				cd.methodTable.put(name, mt);		
			} else 
				st.put(sig, md);
			return ;
		}

		// Static initializers
		if (name.equals("<clinit>")) {
			// We can only have one static initializer, so it doesn't exist in the table.
			SymbolTable mt = new SymbolTable();
			mt.put(sig, md);
			cd.methodTable.put(name, mt);
			return;
		}

		// Ok, we have dealt with constructors and static initializers, now deal with methods.

		// We will not search the hierarchy now - we do that later
		// when the entire class hierarchy has been defined. That
		// means we might be violating certain things now, but that is
		// ok, we will catch it later.

		// It's all good - just insert it.
		if (st == null) {
			// A method of this name has never been inserted before.
			// Create a new symbol table to hold all methods of name 'name'
			SymbolTable mt = new SymbolTable();
			// Insert the signature with the method decl.
			mt.put(sig, md);
			// Insert this symbol table into the method table.
			cd.methodTable.put(name, mt);
		} else 
			// Methods with this name have been defined before, so just use that entry.
			st.put(sig, md);
	}

	private void addField(ClassDecl cd, FieldDecl f, String name) {
		// We will not search the hierarchy now - we do that later when the 
		// entire class hierarchy has been defined.
		cd.fieldTable.put(name,f);
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



	/** 
	 * Contains references to all class declarations.<br>
	 * This is set in the constructor
	 */
	private SymbolTable classTable;
	/** 
	 * Holds a reference to the current class.<br>
	 * This is set in visitClassDecl()
	 */
	private ClassDecl currentClass;

	/* We need to give fields numbers in the order they were defined so we can later
	 * 	catch issues like this:
	 *   public int f = g+1;
     *   public int g = 9;
     * We cannot refer to g before it has been given a value.
     */
	private int fieldCounter = 0; 

	public ClassAndMemberFinder(SymbolTable classTable, boolean debug) { 
		this.classTable = classTable; 
		this.debug = debug;
	}


	/** CLASS DECLARATION */
	public Object visitClassDecl(ClassDecl cd) {
		println("ClassDecl:\t Inserting class '" + cd.name() +"' into global class table.");

		// Enter this class into the class table 
		classTable.put(cd.name(), cd);

		// 01/17/2012 added for allowing for common superclass 'Object'
		// For espresso it is simiilar to java/lang/Object for Java
		// see Phases/Phases2.java for the class 'Object'
		if (cd.superClass() == null && !cd.name().equals("Object")) {
			cd.children[2] = new ClassType(new Name(new Token(sym.IDENTIFIER,"Object",cd.line,0,0)));
			((ClassType)cd.children[2]).myDecl = Phase2.Objects_myDecl;
		}		
		// Update the current class 
		currentClass = cd;
		// Reset fieldCounter
		fieldCounter = 0;

		// Visit the children
		super.visitClassDecl(cd);

		// If there are not constructors at all - insert the default -
		// don't actually make any parse tree stuff - just generate
		// the code automatically in the code generation phase.
		if (cd.methodTable.get("<init>") == null && !cd.isInterface()) { 
			Token t = new Token(sym.IDENTIFIER, cd.name(), 0, 0, 0);
			Modifier m = new Modifier(Modifier.Public);

			ConstructorDecl c = new ConstructorDecl(new Sequence(m),
					new Name(t),
					new Sequence(),
					null,
					new Sequence());
			addMethod(cd, c, "<init>", "");
			cd.body().append(c);
			println("ClassDecl:\t Generating default construction <init>() for class '" + cd.name() + "'");
		}

		return null;
	}
	//<--
	/** CONSTRUCTOR DECL */
	public Object visitConstructorDecl(ConstructorDecl cd) {
		String methodName = cd.name().getname();
		String s = cd.paramSignature();

		if (!methodName.equals(currentClass.name())) 
			Error.error(cd,"Constructor must be named the same as the class.");
		else {
			println("ConstructorDecl: Inserting constructor '<init>' with signature '" + s + 
					"' into method table for class '" + 
					currentClass.name() + "'.");
			addMethod(currentClass, cd, "<init>", s);
		}
		return null;
	}

	/** FIELD DECLARATION - Insert all fields into the FieldTable of the class.
        Note, we will only be visiting field declarations. */
	public Object visitFieldDecl(FieldDecl fd) {
		println("FieldDecl:\t Inserting field '" + fd.name() + 
				"' into field table of class '" + currentClass.name() + "'.");
		// Set var's myDecl to point to this FieldDecl so we can type check its initializer later.
		fd.var().myDecl = fd;
		fd.fieldNumber = fieldCounter;
		fieldCounter++;
		addField(currentClass, fd, fd.name());
		return null;
	}

	/** METHOD - Insert all methods of a class into the ClassTable of the class. */
	public Object visitMethodDecl(MethodDecl md) {
		String methodName = md.name().getname();
		String s = md.paramSignature();
		md.setMyClass(currentClass);

		println("MethodDecl:\t Inserting method '" + methodName + 
				"' with signature '" + s + "' into method table for class '" + 
				currentClass.name() + "'.");
		addMethod(currentClass, md, methodName, s);
		return null;
	}
	//-->

	/** STATIC INITIALIZER - insert static initializer with name <clinit> */
	public Object visitStaticInitDecl(StaticInitDecl si) {
		println("StaticInitDecl:\t Inserting <clinit> into method table for class '" + 
				currentClass.name() + "'.");

		addMethod(currentClass, si, "<clinit>", "");
		return null;
	}
}

