package NameChecker;

import AST.*;
import Utilities.Error;
import Utilities.SymbolTable;
import Utilities.Visitor;
import Utilities.Rewrite;

import java.util.*;
import Parser.*;;

public class NameChecker extends Visitor {

	/* getMethod traverses the class hierarchy to look for a method of
       name 'methodName'. We return #t if we find any method with the
       correct name. Since we don't have types yet we cannot look at
       the signature of the method, so all we do for now is look if
       any method is defined. The search is as follows:

       1) look in the current class
       2) look in its super class
       3) look in all the interfaces

       Remember that the an entry in the methodTable is a symbol table
       it self. It holds all entries of the same name, but with
       different signatures. (See Documentation)
	 */    
	public static SymbolTable getMethod(String methodName, ClassDecl cd) {

		//<--
		// Look in the class' methodTable
		SymbolTable lookup = (SymbolTable)cd.methodTable.get(methodName);
		if (lookup != null)
			return lookup;

		// No method found, if there is a super class look there.
		if (cd.superClass() != null) 
			lookup = getMethod(methodName, cd.superClass().myDecl);

		if (lookup != null)
			return lookup;

		// no method found, if there are interfaces look there.
		Sequence interfaces = cd.interfaces();
		if (interfaces.nchildren > 0) {
			for (int i=0; i<interfaces.nchildren; i++) {
				lookup = getMethod(methodName, ((ClassType)interfaces.children[i]).myDecl);
				if (lookup != null)
					// We found one
					return lookup;
			}
		}
		// no method found in the class/interface hierarchy, so return null.
		//-->
		return null;
	}

	/* Same as getMethod just for fields instead 
	 */
	public static AST getField(String fieldName, ClassDecl cd) {

		//<--
		// Look in the class' fieldTable
		AST lookup = (AST)cd.fieldTable.get(fieldName);
		if (lookup != null)
			return lookup;

		// No field found, if there is a super class look there.
		if (cd.superClass() != null) 
			lookup = getField(fieldName, cd.superClass().myDecl);

		if (lookup != null)
			return lookup;

		// no field found, if there are interfaces look there.
		Sequence interfaces = cd.interfaces();
		if (interfaces.nchildren > 0) {
			for (int i=0; i<interfaces.nchildren; i++) {
				lookup = getField(fieldName, ((ClassType)interfaces.children[i]).myDecl);
				if (lookup != null)
					// We found it.
					return lookup;
			}
		}
		// no field found in the class/interface hierarchy, so return null.
		//-->
		return null;
	}

	/* Traverses all the classes and interfaces and builds a sequence
	   of the methods and constructors of the class hierarchy.
	 */
    public void getClassHierarchyMethods(ClassDecl cd, Sequence lst, Hashtable<String, Object> seenClasses) {
		//<--
	String className = cd.name();

	// if we reach object the just skip it - there is nothing there to look up!
	if (className.equals("Object"))
	    return;
	// have we visited this class or interface before?
	if (seenClasses.get(className) != null)
	    Error.error(cd,"Cyclic inheritance involving " + className);
	else 
	    seenClasses.put(className, cd);
	
	
	
	for (int i=0 ;i< cd.body().nchildren; i++) 
	    if (cd.body().children[i] instanceof MethodDecl)
		lst.append(cd.body().children[i]);
	
	if (cd.superClass() != null)
	    getClassHierarchyMethods(cd.superClass().myDecl, lst, seenClasses);
	if (cd.interfaces().nchildren > 0) 
	    for (int i=0; i<cd.interfaces().nchildren; i++) 
		getClassHierarchyMethods(((ClassType)cd.interfaces().children[i]).myDecl, lst, seenClasses);
	seenClasses.remove(className);
	//-->
    }

	/* For each method (not constructors) in this list, check that if
       it exists more than once with the same parameter signature that
       they all return something of the same type. 
	*/
    public void checkReturnTypesOfIdenticalMethods(Sequence lst) {
	//<--
	MethodDecl md, md2;
	
	for (int i=0; i<lst.nchildren; i++) {
	    md = (MethodDecl)lst.children[i];
	    for (int j=i+1; j<lst.nchildren; j++) {
		md2 = (MethodDecl)lst.children[j];
		if (md.getname().equals(md2.getname()) &&
		    md.paramSignature().equals(md2.paramSignature()) &&
		    //!(md.returnType().signature().equals(md2.returnType().signature())))
		    !md.returnType().identical(md2.returnType())) {
		    Error.error("Method '" + md.getname() + "' has been declared with two different return types:", false);
		    Error.error(md, Type.parseSignature(md.returnType().signature()) + " " + md.getname() + "(" + Type.parseSignature(md.paramSignature()) + " )", false);
		    Error.error(md2,Type.parseSignature(md2.returnType().signature()) + " " + md2.getname() + "(" + Type.parseSignature(md2.paramSignature()) + " )");
		}
	    }
	}
	//-->
    }
    
    /* Divides all the methods into two sequences: one for all the
       abstract ones, and one for all the concrete ones and check that
       all the methods that were delcared abstract were indeed
       implemented somewhere in the class hierarchy.  */
    

    // sup is the class in which the abstract method lives,
    // sub is the class in which the concrete method lives.
    public static boolean isSuper(ClassDecl sup, ClassDecl sub) {
	if (sup.name().equals(sub.name()))
	    return true;
		
	if (sub.superClass() != null && isSuper(sup, sub.superClass().myDecl))
	    return true;

	for (int i=0; i<sub.interfaces().nchildren; i++) 
	    if (isSuper(sup, ((ClassType)sub.interfaces().children[i]).myDecl))
		return true;

	return false;
    }


       public void checkImplementationOfAbstractClasses(ClassDecl cd, Sequence methods) {
	   //<--
	   for (int i=0; i<methods.nchildren; i++) {
	       MethodDecl md = (MethodDecl)methods.children[i];
	       if (md.block() == null) {
		   // now find a concrete in the rance [0..i-1]
		   boolean found = false;
		   for (int j=0; j<i; j++) {
		       MethodDecl md2 = (MethodDecl)methods.children[j];
		       if (md2.block() != null) 
			   found = (md.getname().equals(md2.getname()) && md.paramSignature().equals(md2.paramSignature())) || found;
		   }
		   if (!found)
		       Error.error(md,"Class '" + cd.name() + "' should be declared abstract; it does not implement\n" +
				   Type.parseSignature(md.returnType().signature()) +
				   " " + md.getname() + "(" + Type.parseSignature(md.paramSignature()) + " )");
	       }
	   }
	   //-->
       }
    
	public  void checkUniqueFields(Sequence fields, ClassDecl cd) {
		//<--	
		// All fields may only be defined once!
	    for (int j=0; j<cd.body().nchildren; j++) {
		if (cd.body().children[j] instanceof FieldDecl) {
		    FieldDecl fd = (FieldDecl)cd.body().children[j];
		    for (int i=0; i<fields.nchildren; i++) {
			if (((FieldDecl)fields.children[i]).name().equals(fd.name()))
			    // test23.java
			    Error.error((fields.children[i]),"Field '" + fd.name() +"' already defined.");
		    }
		    // field wasn't already defined, so insert it.
		    fields.append(fd);
		}
	    }
	    if (cd.superClass() != null)
		checkUniqueFields(fields, cd.superClass().myDecl);
	    for (int j=0; j<cd.interfaces().nchildren; j++) {
		checkUniqueFields(fields, ((ClassType)cd.interfaces().children[j]).myDecl);
	    }
	    //-->
	}

	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

	/**
	 * Points to the current scope.
	 */
	private SymbolTable currentScope;
	/**
	 * The class table<br>
	 * This is set in the constructor.
	 */
	private SymbolTable classTable;
	/**
	 * The current class in which we are working.<br>
	 * This is set in visitClassDecl().
	 */
	private ClassDecl   currentClass;
	
	public NameChecker(SymbolTable classTable, boolean debug) { 
		this.classTable = classTable; 
		this.debug = debug;
	}

	/** BLOCK */
	public Object visitBlock(Block bl) {
		println("Block:\t\t Creating new scope for Block.");
		currentScope = currentScope.newScope();
		super.visitBlock(bl);
		currentScope = currentScope.closeScope(); 
		return null;
	}


	/** CLASS DECLARATION */
	public Object visitClassDecl(ClassDecl cd) {
		println("ClassDecl:\t Visiting class '"+cd.name()+"'");

		// If we use the field table here as the top scope, then we do not
		// need to look in the field table when we resolve NameExpr. Note,
		// at this time we have not yet rewritten NameExprs which are really
		// FieldRefs with a null target as we have not resolved anything yet.
		currentScope = cd.fieldTable;
		currentClass = cd;

		Hashtable<String, Object> seenClasses = new Hashtable<String, Object>();

		// Check that the superclass is a class.
		if (cd.superClass() != null) 
			if (cd.superClass().myDecl.isInterface())
				Error.error(cd,"Class '" + cd.name() + "' cannot inherit from interface '" +
						cd.superClass().myDecl.name() + "'.");



		if (cd.superClass() != null) {
			if (cd.name().equals(cd.superClass().typeName()))
				Error.error(cd, "Class '" + cd.name() + "' cannot extend itself.");
			// If a superclass has a private default constructor, the 
			// class cannot be extended.
			ClassDecl superClass = (ClassDecl)classTable.get(cd.superClass().typeName());
			SymbolTable st = (SymbolTable)superClass.methodTable.get("<init>");
			ConstructorDecl ccd = (ConstructorDecl)st.get("");
			if (ccd != null && ccd.getModifiers().isPrivate())
			    Error.error(cd, "Class '" + superClass.className().getname() + "' cannot be extended because it has a private default constructor.");
		}
		
		// Visit the children
		super.visitClassDecl(cd);
			
		currentScope = null;

		// Check that the interfaces implemented are interfaces.
		for (int i=0; i<cd.interfaces().nchildren; i++) {
			ClassType ct = (ClassType)cd.interfaces().children[i];
			if (ct.myDecl.isClass())
				Error.error(cd,"Class '" + cd.name() + "' cannot implement class '" + ct.name() + "'.");
		}

		Sequence methods = new Sequence();
		
		getClassHierarchyMethods(cd, methods, seenClasses);

		checkReturnTypesOfIdenticalMethods(methods);

		// If the class is not abstract and not an interface it must implement all
		// the abstract functions of its superclass(es) and its interfaces.
		if (!cd.isInterface() && !cd.modifiers.isAbstract()) {
			checkImplementationOfAbstractClasses(cd, methods);
			// checkImplementationOfAbstractClasses(cd, new Sequence());
		}
		// All field names can only be used once in a class hierarchy
		checkUniqueFields(new Sequence(), cd);

		cd.allMethods = methods; // now contains only MethodDecls

		// Fill cd.constructors.
		SymbolTable st = (SymbolTable)cd.methodTable.get("<init>");
		ConstructorDecl cod;
		if (st != null) {
			for (Enumeration<Object> e = st.entries.elements() ; 
					e.hasMoreElements(); ) {
				cod = (ConstructorDecl)e.nextElement();
				cd.constructors.append(cod);
			}
		}

		// needed for rewriting the tree to replace field references
		// represented by NameExpr.
		println("ClassDecl:\t Performing tree Rewrite on " + cd.name());
		new Rewrite().go(cd, cd);

		return null;
	}
	//<--
	/** CLASS TYPE */
	public Object visitClassType(ClassType ct) {
		String n = ct.name().getname();
		println("ClassType:\t Looking up class/interface '" + n + "' in class table.");
		ClassDecl cl = (ClassDecl)classTable.get(n);
		if (cl == null) 
			Error.error(ct," Class '" + n + "' not found."); 
		ct.myDecl = cl;
		return null;
	}

	/** FIELD REFERENCE */
	public Object visitFieldRef(FieldRef fr) {
		if (fr.target() instanceof This) {
			String n = fr.fieldName().getname();

			println("FieldRef:\t Looking up field '" + n + "'.");
			AST lookup = getField(n, currentClass);
			if (lookup == null) 
				Error.error(fr,"Field '" + n + "' not found.");
			else 
				if (!(lookup instanceof FieldDecl)) 
					Error.error(fr,"'" + n + "' is not a field.");
		}
		else 
			println("FieldRef:\t Target too complicated for now!");

		return super.visitFieldRef(fr);
	}

	/** FOR STATEMENT */
	public Object visitForStat(ForStat fs) {
		println("ForStat:\t Creating new scope for For Statement.");
		currentScope = currentScope.newScope();
		super.visitForStat(fs);
		currentScope = currentScope.closeScope(); 
		return null;
	}

	/** LOCAL VARIABLE DECLARATION */
	public Object visitLocalDecl(LocalDecl ld) {
		println("LocalDecl:\t Declaring local symbol '" + 
				ld.name() + "'.");
		// Set var's myDecl to point to this LocalDecl so we can type check its initializer.
		ld.var().myDecl = ld;
		super.visitLocalDecl(ld);
		currentScope.put(ld.name(), ld);
		return null;    
	}

	/** METHOD DECLARATION */
	public Object visitMethodDecl(MethodDecl md) {
		println("MethodDecl:\t Creating new scope for Method '" + md.getname() + "' with signature '" +
				md.paramSignature() + "' (Parameters and Locals).");
		currentScope = currentScope.newScope();
		super.visitMethodDecl(md);
		currentScope = currentScope.closeScope();
		return null;
	}

	/** CONSTRUCTOR DECLARATION */
	public Object visitConstructorDecl(ConstructorDecl cd) {
		println("ConstructorDecl: Creating new scope for constructor <init> with signature '" + 
				cd.paramSignature()+ "' (Parameters and Locals).");
		currentScope = currentScope.newScope();

		if (currentClass.superClass() != null && 
			cd.cinvocation() == null &&
			!currentClass.superClass().myDecl.isInterface()) {
			cd.children[3] = new CInvocation(new Token(sym.SUPER, "super", 0, 0 ,0), new Sequence());
		}

		cd.params().visit(this);
		currentScope = currentScope.newScope();
		if (cd.cinvocation() != null) 
			cd.cinvocation().visit(this);
		cd.body().visit(this);

		currentScope = currentScope.closeScope();
		currentScope = currentScope.closeScope();
		return null;
	}

	/** NAME EXPRESSION */
	public Object visitNameExpr(NameExpr ne) {
		println("NameExpr:\t Looking up symbol '" + ne.name() + "'.");

		// Look to see if it is in the current scope?
		AST lookup = (AST)currentScope.get(ne.name().getname());    
		if (lookup == null)
			// now look to see if it is a field in the class hierarchy
			lookup = getField(ne.name().getname(), currentClass);

		if (lookup == null) {
			// could be a class name ?
			lookup = (AST)classTable.get(ne.name().getname());
			if (lookup == null)
				Error.error(ne,"Symbol '" + ne.name().getname() + "' not declared.");
		} 
		if (lookup instanceof ClassDecl) 
			println(" Found Class");
		else if (lookup instanceof LocalDecl)
			println(" Found Local Variable");
		else if (lookup instanceof ParamDecl)
			println(" Found Parameter");
		else if (lookup instanceof FieldDecl)
			println(" Found Field");
		ne.myDecl = lookup;
		return null;
	}

	/** INVOCATION */
	public Object visitInvocation(Invocation in) {
		String n = in.methodName().getname();

		/* We will only do checking if target is null or This */
		/** NULL or THIS */
		if (in.target() == null || (in.target() instanceof This)) {
			println("Invocation:\t Looking up method '" + n + "'.");

			// Search through the class/interface hierarchy for a method 
			// with the correct name.
			if (getMethod(n, currentClass) == null)
				Error.error(in,"Method '" + n + "' not found.");

			// Some method was found, but we don't know if the signatures match.
			// This check will be left until type checking
		} else if (in.target() instanceof Super) {
		    // added 10/13/14 
		    if (currentClass.superClass() != null)
			if (getMethod(n, currentClass.superClass().myDecl) == null)
			    Error.error(in,"Method '" + n + "' not found.");
			else
			    ;
		    else
			Error.error(in,"No super class.");
		} else
		    println("Invocation:\t Target too complicated for now!");
		return super.visitInvocation(in);
	}

	/** PARAMETER DECLARATION */
	public Object visitParamDecl(ParamDecl pd) {
		println("ParamDecl:\t Declaring local symbol '" + 
				pd.name() + "'.");
		super.visitParamDecl(pd);
		currentScope.put(pd.name(), pd);
		return null;
	}
	//-->

	/** THIS */
	public Object visitThis(This th) {
		ClassType ct = new ClassType(new Name(new Token(16,currentClass.name(),0,0,0)));
		ct.myDecl = currentClass;
		th.type = ct;
		return null;
	}

}

