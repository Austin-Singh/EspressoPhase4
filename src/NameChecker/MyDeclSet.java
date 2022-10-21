package NameChecker;

import AST.*;
import Utilities.Error;
import Utilities.SymbolTable;
import Utilities.Visitor;

// This visitor is not needed if classes and interfaces are defined in
// the order of inheritence, i.e., superclasses and superinterfaces
// are defined first and so on. if you want the freedom to put it in
// any order you need this traversal. If you don't care then make sure
// you have an implementation of visitClassType in
// ClassAndMemberFinder.


public class MyDeclSet extends Visitor {

	private SymbolTable classTable;

	public MyDeclSet(SymbolTable classTable, boolean debug) { 
		this.classTable = classTable; 
		this.debug = debug;
	}

	public Object visitClassType(ClassType ct) {
		ClassDecl cd = (ClassDecl) classTable.get(ct.typeName());

		println("ClassType:\t Setting myDecl for '" + ct.typeName() + "'");

		if (cd == null) 
			Error.error(ct,"Class '" + ct.typeName() + "' not found.");
		ct.myDecl = cd;
		return null;
	}
}

