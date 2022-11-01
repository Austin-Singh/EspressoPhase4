package TypeChecker;

import AST.*;
import Utilities.Error;
import Utilities.SymbolTable;
import Utilities.Visitor;
import java.util.*;
import java.math.*;

public class TypeChecker extends Visitor {

    private SymbolTable   classTable;
    private ClassDecl     currentClass;
    private ClassBodyDecl currentContext;
    private FieldDecl currentFieldDecl; // keep track of the currentFieldDecl 
    private boolean inFieldInit;        // 
	
    public TypeChecker(SymbolTable classTable, boolean debug) { 
		this.classTable = classTable; 
		this.debug = debug;
    }

    public static ClassBodyDecl findMethod(Sequence candidateMethods, String name, Sequence actualParams, boolean lookingForMethods) {
		if (lookingForMethods) {
			println("+------------- findMethod (Method) ------------");
			println("| Looking for method: " + name);
		} else {
			println("+---------- findMethod (Constructor) ----------");
			println("| Looking for constructor: " + name);
		}
		println("| With parameters:");
		for (int i=0; i<actualParams.nchildren; i++){
			println("|   " + i + ". " + ((actualParams.children[i] instanceof ParamDecl)?(((ParamDecl)actualParams.children[i]).type()):((Expression)actualParams.children[i]).type));
		}
		// The number of actual parameters in the invocation.
		int count = 0;
		
		// Make an array big enough to hold all the methods if needed
		ClassBodyDecl cds[] = new ClassBodyDecl[candidateMethods.nchildren];
		
		// Initialize the array to point to null
		for(int i=0;i<candidateMethods.nchildren;i++) 
			cds[i] = null;
		
		Sequence args = actualParams;
		Sequence params;
		
		// Insert all the methods from the symbol table that:
		// 1.) has the right number of parameters
		// 2.) each formal parameter can be assigned its corresponding
		//     actual parameter.
		if (lookingForMethods)
			println("| Finding methods with the right number of parameters and types");
		else
			println("| Finding constructors with the right number of parameters and types");
		for (int cnt=0; cnt<candidateMethods.nchildren; cnt++) {
			ClassBodyDecl cbd = (ClassBodyDecl)candidateMethods.children[cnt];
			
			// if the method doesn't have the right name, move on!
			if (!(cbd.getname().equals(name)))
			continue;
			
			// Fill params with the formal parameters.
			if (cbd instanceof ConstructorDecl) 
			params = ((ConstructorDecl)cbd).params();
			else if (cbd instanceof MethodDecl)
			params = ((MethodDecl)cbd).params();
			else
			// we have a static initializer, don't do anything - just skip it.
			continue;
			
			print("|   " + name + "(");
			if (cbd instanceof ConstructorDecl) 
			print(Type.parseSignature(((ConstructorDecl)cbd).paramSignature()));
			else 
			print(Type.parseSignature(((MethodDecl)cbd).paramSignature()));
			print(" )  ");
			
			if (args.nchildren == params.nchildren) {
			// The have the same number of parameters
			// now check that the formal parameters are
			// assignmentcompatible with respect to the 
			// types of the actual parameters.
			// OBS this assumes the type field of the actual
			// parameters has been set (in Expression.java),
			// so make sure to call visit on the parameters first.
			boolean candidate = true;
			
			for (int i=0;i<args.nchildren; i++) {
				candidate = candidate &&
				Type.assignmentCompatible(((ParamDecl)params.children[i]).type(),
							(args.children[i] instanceof Expression) ?
							((Expression)args.children[i]).type :
							((ParamDecl)args.children[i]).type());
				
				if (!candidate) {
				println(" discarded");
				break;
				}
			}
			if (candidate) {
				println(" kept");
				cds[count++] = cbd;
			}
			}
			else {
			println(" discarded");
			}
			
		}
		// now count == the number of candidates, and cds is the array with them.
		// if there is only one just return it!
		println("| " + count + " candidate(s) were found:");
		for ( int i=0;i<count;i++) {
			ClassBodyDecl cbd = cds[i];
			print("|   " + name + "(");
			if (cbd instanceof ConstructorDecl) 
			print(Type.parseSignature(((ConstructorDecl)cbd).paramSignature()));
			else 
			print(Type.parseSignature(((MethodDecl)cbd).paramSignature()));
			println(" )");
		}
		
		if (count == 0) {
			println("| No candidates were found.");
			println("+------------- End of findMethod --------------");
			return null;
		}
		
		if (count == 1) {
			println("| Only one candidate - thats the one we will call then ;-)");
			println("+------------- End of findMethod --------------");
			return cds[0];
		}
		println("| Oh no, more than one candidate, now we must eliminate some >:-}");
		// there were more than one candidate.
		ClassBodyDecl x,y;
		int noCandidates = count;
		
		for (int i=0; i<count; i++) {
			// take out a candidate
			x = cds[i];
			
			if (x == null)
			continue;		    
			cds[i] = null; // this way we won't find x in the next loop;
			
			// compare to all other candidates y. If any of these
			// are less specialised, i.e. all types of x are 
			// assignment compatible with those of y, y can be removed.
			for (int j=0; j<count; j++) {
			y = cds[j];
			if (y == null) 
				continue;
			
			boolean candidate = true;
			
			// Grab the parameters out of x and y
			Sequence xParams, yParams;
			if (x instanceof ConstructorDecl) {
				xParams = ((ConstructorDecl)x).params();
				yParams = ((ConstructorDecl)y).params();
			} else {
				xParams = ((MethodDecl)x).params();
				yParams = ((MethodDecl)y).params();
			}
			
			// now check is y[k] <: x[k] for all k. If it does remove y.
			// i.e. check if y[k] is a superclass of x[k] for all k.
			for (int k=0; k<xParams.nchildren; k++) {
				candidate = candidate &&
				Type.assignmentCompatible(((ParamDecl)yParams.children[k]).type(),
							((ParamDecl)xParams.children[k]).type());
				
				if (!candidate)
				break;
			}
			if (candidate) {
				// x is more specialized than y, so throw y away.
				print("|   " + name + "(");
				if (y instanceof ConstructorDecl) 
				print(Type.parseSignature(((ConstructorDecl)y).paramSignature()));
				else 
				print(Type.parseSignature(((MethodDecl)y).paramSignature()));
				print(" ) is less specialized than " + name + "(");
				if (x instanceof ConstructorDecl) 
				print(Type.parseSignature(((ConstructorDecl)x).paramSignature()));
				else 
				print(Type.parseSignature(((MethodDecl)x).paramSignature()));
				println(" ) and is thus thrown away!");
				
				cds[j] = null;
				noCandidates--;
			}
			}
			// now put x back in to cds
			cds[i] = x;
		}
		if (noCandidates != 1) {
			// illegal function call
			println("| There is more than one candidate left!");
			println("+------------- End of findMethod --------------");
			return null;
		}
		
		// just find it and return it.
		println("| We were left with exactly one candidate to call!");
		println("+------------- End of findMethod --------------");
		for (int i=0; i<count; i++)
			if (cds[i] != null)
			return cds[i];
		
		return null;
    }
    
    public void listCandidates(ClassDecl cd, Sequence candidateMethods, String name) {
		for (int cnt=0; cnt<candidateMethods.nchildren; cnt++) {
			ClassBodyDecl cbd = (ClassBodyDecl)(candidateMethods.children[cnt]);

			if (cbd.getname().equals(name)) {
			if (cbd instanceof MethodDecl)
				System.out.println("  " + name + "(" + Type.parseSignature(((MethodDecl)cbd).paramSignature()) + " )");
			else
				System.out.println("  " + cd.name() + "(" + Type.parseSignature(((ConstructorDecl)cbd).paramSignature()) + " )");
			}
		}
    }

    /** ArrayType */
    public Object visitArrayType(ArrayType at) {
		println(at.line + ": Visiting an ArrayType");
		println(at.line + ": ArrayType type is " + at);
		return at;
    }

    // TODO: Espresso doesn't allow 'int[][] a = new int[]{ f(), f() }} where f returns an array
    public boolean arrayAssignmentCompatible(Type t, Expression e) {
		if (t instanceof ArrayType && (e instanceof ArrayLiteral)) {
			ArrayType at = (ArrayType)t;
			e.type = at; //  we don't know that this is the type - but if we make it through it will be!
			ArrayLiteral al = (ArrayLiteral)e;
			
			// t is an array type i.e. XXXXXX[ ]
			// e is an array literal, i.e., { }
			if (al.elements().nchildren == 0) // the array literal is { }
			return true;   // any array variable can hold an empty array
			// Now check that XXXXXX can hold value of the elements of al
			// we have to make a new type: either the base type if |dims| = 1
			boolean b = true;
			for (int i=0; i<al.elements().nchildren; i++) {
			if (at.getDepth() == 1) 
				b = b && arrayAssignmentCompatible(at.baseType(), (Expression)al.elements().children[i]);
			else { 
				ArrayType at1 = new ArrayType(at.baseType(), at.getDepth()-1);
				b = b  && arrayAssignmentCompatible(at1, (Expression)al.elements().children[i]);
			}
			}
			return b;
		} else if (t instanceof ArrayType && !(e instanceof ArrayLiteral)) {
			Type t1 = (Type)e.visit(this);
			if (t1 instanceof ArrayType)
			if (!Type.assignmentCompatible(t,t1))
				Error.error("Incompatible type in array assignment");
			else
				return true;
			Error.error(t, "Error: cannot assign non array to array type " + t.typeName());	    
		}
		else if (!(t instanceof ArrayType) && (e instanceof ArrayLiteral)) {
			Error.error(t, "Error: cannot assign value " + ((ArrayLiteral)e).toString() + " to type " + t.typeName());
		}
		return Type.assignmentCompatible(t,(Type)e.visit(this));
		}
		
		public Object visitArrayLiteral(ArrayLiteral al) {
		// Espresso does not allow array literals without the 'new <type>' part.
		Error.error(al, "Array literal must be preceeded by a 'new <type>'");
		return null;
    }
    
    /** ClassType */
    public Object visitClassType(ClassType ct) {
		println(ct.line + ": Visiting a class type");

		println(ct.line + ": Class Type has type: " + ct);
		return ct;
    }

    /** FIELD DECLARATION */
    public Object visitFieldDecl(FieldDecl fd) {
		println(fd.line + ": Visiting a field declaration");

		// Update the current context
		currentContext = fd;
		inFieldInit = true;
		currentFieldDecl = fd;
		if (fd.var().init() != null)
			fd.var().visit(this);
		currentFieldDecl = null;
		inFieldInit = false;
		return fd.type();
    }

    /** FIELD REFERENCE */
    public Object visitFieldRef(FieldRef fr) {
		println(fr.line + ": Visiting a field reference" + fr.target());

		Type targetType = (Type) fr.target().visit(this);
		String field    = fr.fieldName().getname();

		// Changed June 22 2012 ARRAY
		if (fr.fieldName().getname().equals("length")) {
			if (targetType.isArrayType()) {
			fr.type = new PrimitiveType(PrimitiveType.IntKind);
			println(fr.line + ": Field Reference was a an Array.length reference, and it has type: " + fr.type);
			fr.targetType = targetType;
			return fr.type;
			}
		}

		if (targetType.isClassType()) {
			ClassType c = (ClassType)targetType;
			ClassDecl cd = c.myDecl;
			fr.targetType = targetType;

			println(fr.line + ": FieldRef: Looking up symbol '" + field + "' in fieldTable of class '" + 
				c.typeName() + "'.");

			// Lookup field in the field table of the class associated with the target.
			FieldDecl lookup = (FieldDecl) NameChecker.NameChecker.getField(field, cd);

			// Field not found in class.
			if (lookup == null)
			Error.error(fr,"Field '" + field + "' not found in class '" + cd.name() + "'.");
			else {
			fr.myDecl = lookup;
			fr.type = lookup.type();
			}
		} else 
			Error.error(fr,"Attempt to access field '" + field + "' in something not of class type.");
		println(fr.line + ": Field Reference has type: " + fr.type);

		if (inFieldInit && currentFieldDecl.fieldNumber <= fr.myDecl.fieldNumber && currentClass.name().equals(   (((ClassType)fr.targetType).myDecl).name()))
			Error.error(fr,"Illegal forward reference of non-initialized field.");

		return fr.type;
    }

    /** RETURN STATEMENT */
    public Object visitReturnStat(ReturnStat rs) {
		println(rs.line + ": Visiting a return statement");
		Type returnType;

		if (currentContext instanceof MethodDecl)
			returnType = ((MethodDecl)currentContext).returnType();
		else
			returnType = null;

		// Check is there is a return in a Static Initializer
		if (currentContext instanceof StaticInitDecl) 
			Error.error(rs,"return outside method");

		// Check if a void method is returning something.
		if (returnType == null || returnType.isVoidType()) {
			if (rs.expr() != null)
			Error.error(rs, "Return statement of a void function cannot return a value.");
			return null;
		}

		// Check if a non void method is returning without a proper value.
		if (rs.expr() == null)
			Error.error(rs, "Non void function must return a value.");

		Type returnValueType = (Type) rs.expr().visit(this);	
		if (rs.expr().isConstant()) {
			if (returnType.isShortType() && Literal.isShortValue(((BigDecimal)rs.expr().constantValue()).longValue()))
			;// is ok break;                                                                                                    
			else if (returnType.isByteType() && Literal.isByteValue(((BigDecimal)rs.expr().constantValue()).longValue()))
			; // is ok break;                                                                                                   
			else if (returnType.isCharType() && Literal.isCharValue(((BigDecimal)rs.expr().constantValue()).longValue()))
			; // break;
			else if (!Type.assignmentCompatible(returnType,returnValueType))
			Error.error(rs, "Illegal value of type " + returnValueType.typeName() + 
					" in method expecting value of type " + returnType.typeName() + ".");
		} else if (!Type.assignmentCompatible(returnType,returnValueType))
			Error.error(rs, "Illegal value of type " + returnValueType.typeName() + 
				" in method expecting value of type " + returnType.typeName() + ".");
			
		rs.setType(returnType);
		return null;
    }

    /** THIS */
    public Object visitThis(This th) {
		println(th.line + ": Visiting a this statement");

		th.type = th.type();

		println(th.line + ": This has type: " + th.type);
		return th.type;
    }

    /** ArrayAccessExpr - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitArrayAccessExpr(ArrayAccessExpr ae) {
		println(ae.line + ": Visiting ArrayAccessExpr");
		// INSERT CODE HERE
		/**
			Example)
			array[0]

			We can check the ArrayAccessExpr.java file and find two paramters (Expression target, Expression index)
			target[index]
			- target must be an arrayType
			- index must be integralType (int, long)

			array's type:
				if depth == 1	--> base type
				else 			--> new array type w/ base type of target, but depth ONE less
		 */
		return ae.type;
    }

    /** NewArray - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitNewArray(NewArray ne) {
		println(ne.line + ": Visiting a NewArray " + ne.dimsExpr().nchildren + " " + ne.dims().nchildren);
		// INSERT CODE HERE
		/**
			Example)

		 */
		println(ne.line + ": NewArray type is " + ne.type);
		return ne.type;
    }

    /** ASSIGNMENT - OUR CODE HERE (FINISHED) */
    public Object visitAssignment(Assignment as) {
		println(as.line + ": Visiting an assignment");

		Type vType = (Type) as.left().visit(this);
		Type eType = (Type) as.right().visit(this);

		/** Note: as.left() should be of NameExpr or FieldRef class! */

		if (!vType.assignable())          
			Error.error(as,"Left hand side of assignment not assignable.");

		switch (as.op().kind) {
		case AssignmentOp.EQ : {
			// Check if the right hand side is a constant.	    
			// if we don't do this the following is illegal: byte b; b = 4; because 4 is an it!
			if (as.right().isConstant()) {
			if (vType.isShortType() && Literal.isShortValue(((BigDecimal)as.right().constantValue()).longValue()))
				break;
			if (vType.isByteType() && Literal.isByteValue(((BigDecimal)as.right().constantValue()).longValue()))
				break;		
			if (vType.isCharType() && Literal.isCharValue(((BigDecimal)as.right().constantValue()).longValue()))
				break;
			}
				
			if (!Type.assignmentCompatible(vType,eType))
			Error.error(as,"Cannot assign value of type " + eType.typeName() + " to variable of type " + vType.typeName() + ".");
			break;
		}

		// INSERT CODE HERE
		case AssignmentOp.PLUSEQ:
		case AssignmentOp.MINUSEQ:
		case AssignmentOp.MULTEQ:
		case AssignmentOp.DIVEQ:
		case AssignmentOp.MODEQ:

		case AssignmentOp.RSHIFTEQ:
		case AssignmentOp.LSHIFTEQ:
		case AssignmentOp.RRSHIFTEQ:{
			if(!vType.isIntegralType()) {
				Error.error(as, "Left hand side must be integer.");
			}
			if(!eType.isIntegralType()) {
				Error.error(as, "Right hand side must be integer.");
			}
			break;			
		}

		case AssignmentOp.ANDEQ:
		case AssignmentOp.OREQ:
		case AssignmentOp.XOREQ:{
			if(!eType.isIntegralType() || !vType.isIntegerType()) {
				if(!eType.isBooleanType() || !vType.isBooleanType()) {
					Error.error(as, "Both sides must be either integer or boolean.");
				}
			}
			break;			
		}
		// - END -

		}

		as.type = vType;
		println(as.line + ": Assignment has type: " + as.type);

		return vType;
    }

    /** BINARY EXPRESSION - OUR CODE HERE (COMPLETE) */
    public Object visitBinaryExpr(BinaryExpr be) {
		println(be.line + ": Visiting a Binary Expression");

		// INSERT CODE HERE
		Type lType = (Type)be.left().visit(this);
		Type rType = (Type)be.right().visit(this);
		
		switch(be.op().kind) {
		case BinOp.LT:
		case BinOp.GT:
		case BinOp.LTEQ:
		case BinOp.GTEQ: {
			if(lType.isNumericType() && rType.isNumericType()) {
				be.type = new PrimitiveType(PrimitiveType.BooleanKind);
			}
			else {
				Error.error(be, "Operands for " + be.op().operator() + " must be numeric.");
			}
			break;
		}
		case BinOp.EQEQ:
		case BinOp.NOTEQ: {
			if(be.left() instanceof NameExpr) {
				if(((NameExpr)be.left()).myDecl instanceof ClassDecl) {
					Error.error(be, "Left hand side of " + be.op().operator() + " cannot be class name.");
				}
			}
			
			if(be.right() instanceof NameExpr) {
				if(((NameExpr)be.right()).myDecl instanceof ClassDecl) {
					Error.error(be, "Right hand side of " + be.op().operator() + " cannot be class name.");
				}
			}
			
			if(lType.identical(rType)) {
				if(!lType.isVoidType()) {
					be.type = new PrimitiveType(PrimitiveType.BooleanKind);
				}
				else {
					Error.error(be, "Operands for " + be.op().operator() + " cannot be void.");
				}
			}
			else if (lType.isNumericType() && rType.isNumericType()) {
				be.type = new PrimitiveType(PrimitiveType.BooleanKind);
			}
			else {
				Error.error(be, "Operands for " + be.op().operator() + " must be identical or numeric.");
			}
			break;
		}
		case BinOp.ANDAND:
		case BinOp.OROR: {
			if(lType.isBooleanType() && rType.isBooleanType()) {
				be.type = new PrimitiveType(PrimitiveType.BooleanKind);
			}
			else {
				Error.error(be, "Operands for " + be.op().operator() + " must both be boolean.");
			}
			break;
		}
		case BinOp.AND:
		case BinOp.OR:
		case BinOp.XOR: {
			if(lType.isBooleanType() && rType.isBooleanType()) {
				be.type = new PrimitiveType(PrimitiveType.BooleanKind);
			}
			else if (lType.isIntegralType() && rType.isIntegralType()) {
				be.type = new PrimitiveType(PrimitiveType.ceiling((PrimitiveType)lType, (PrimitiveType)rType));
			}
			else {
				Error.error(be, "Operands for " + be.op().operator() + " must be either boolean or integrals.");
			}
			break;
		}
		case BinOp.PLUS:
		case BinOp.MINUS:
		case BinOp.MOD:
		case BinOp.MULT:
		case BinOp.DIV: {
			if(lType.isNumericType() && rType.isNumericType()) {
				be.type = new PrimitiveType(PrimitiveType.ceiling((PrimitiveType)lType, (PrimitiveType)rType));
			}
			else if (be.op().kind == BinOp.PLUS) {
				if(lType.isStringType() || rType.isStringType()) {
					be.type = new PrimitiveType(PrimitiveType.StringKind);
				}
			}
			else {
				Error.error(be, "Operands for " + be.op().operator() + " must be numeric.");
			}
			break;
		}
		case BinOp.LSHIFT:
		case BinOp.RSHIFT:
		case BinOp.RRSHIFT: {
			if(lType.isIntegralType() && rType.isIntegralType()) {
				be.type = lType;
			}
			else {
				Error.error(be, "Operands for " + be.op().operator() + " must be integrals.");
			}
			//if lType == byte, short, or char => change it to int? Nothing tests this? Unsure what he means. Be aware for testing phase.
			break;
		}
		case BinOp.INSTANCEOF: {
			if(classTable.get(((NameExpr)be.right()).name().getname()) == null) {
				Error.error(be, "Right side of " + be.op().operator() + " must be a class name.");
			}
			
			if(!lType.isClassType()) {
				Error.error(be, "Left side of " + be.op().operator() + " must be a class type.");
			}
			
			be.type = new PrimitiveType(PrimitiveType.BooleanKind);
			break;
			}
		}
		// - END -

		println(be.line + ": Binary Expression has type: " + be.type);
		return be.type;
    }

    /** CAST EXPRESSION - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitCastExpr(CastExpr ce) {
		println(ce.line + ": Visiting a cast expression");

		// INSERT CODE HERE

		println(ce.line + ": Cast Expression has type: " + ce.type);
		return ce.type;
    }

    /** CONSTRUCTOR (EXPLICIT) INVOCATION - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitCInvocation(CInvocation ci) {
		println(ci.line + ": Visiting an explicit constructor invocation");

		// INSERT CODE HERE

		return null;
    }

    /** CLASS DECLARATION - OUR CODE HERE (FINISHED?) */
    public Object visitClassDecl(ClassDecl cd) {
		println(cd.line + ": Visiting a class declaration");

		// INSERT CODE HERE
		super.visitClassDecl(cd);
		// - END -

		return null;
    }

    /** CONSTRUCTOR DECLARATION - OUR CODE HERE (FINISHED) */
    public Object visitConstructorDecl(ConstructorDecl cd) {
		println(cd.line + ": Visiting a constructor declaration");

		// INSERT CODE HERE
		currentContext = cd;
		super.visitConstructorDecl(cd);
		// - END -

		return null;
    }

    /** DO STATEMENT - OUR CODE HERE (FINISHED) */
    public Object visitDoStat(DoStat ds) {
		println(ds.line + ": Visiting a do statement");

		// INSERT CODE HERE
		Type exprType = (Type)ds.expr().visit(this);
		
		if(!exprType.isBooleanType()) {
			Error.error(ds, "Do statement must have boolean expression.");
		}
		
		ds.stat().visit(this);
		// - END -

		return null;
    }

    /** FOR STATEMENT - OUR CODE HERE (COMPLETE) */
    public Object visitForStat(ForStat fs) {
		println(fs.line + ": Visiting a for statement");

		// INSERT CODE HERE
		if(fs.init() != null) {
			fs.init().visit(this);
		}
		
		if(fs.expr() != null) {
			Type exprType = (Type)fs.expr().visit(this);
			if(!exprType.isBooleanType()) {
				Error.error(fs, "For statement must have boolean expression.");
			}
		}
		
		if(fs.incr() != null) {
			fs.incr().visit(this);
		}
		
		if(fs.stats() != null) {
			fs.stats().visit(this);
		}

		return null;
    }

    /** IF STATEMENT - OUR CODE HERE (COMPLETE) */
    public Object visitIfStat(IfStat is) {
		println(is.line + ": Visiting a if statement");

		// INSERT CODE HERE
		Type exprType = (Type)is.expr().visit(this);
		if(!exprType.isBooleanType()) {
			Error.error(is, "If statement must have boolean expression.");
		}
		
		if(is.thenpart() != null) {
			is.thenpart().visit(this);
		}
		
		if(is.elsepart() != null) {
			is.elsepart().visit(this);
		}

		return null;
    }

    /** INVOCATION - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitInvocation(Invocation in) {
		println(in.line + ": Visiting an Invocation");

		// INSERT CODE HERE

		println(in.line + ": Invocation has type: " + in.type);
		return in.type;
    }

    /** LITERAL - OUR CODE HERE (COMPLETE) */
    public Object visitLiteral(Literal li) {
		println(li.line + ": Visiting a literal");

		// INSERT CODE HERE
		if(li.getKind() == Literal.NullKind) {
			li.type = new NullType(li);
		}
		else {
			li.type = new PrimitiveType(li.getKind());
		}
		// - END -

		println(li.line + ": Literal has type: " + li.type);
		return li.type;
    }

    /** METHOD DECLARATION - OUR CODE HERE (FINISHED) */
    public Object visitMethodDecl(MethodDecl md) {
		println(md.line + ": Visiting a method declaration");
		currentContext = md;

		// INSERT CODE HERE
		super.visitMethodDecl(md);
		// - END -

		return null;
    }

    /** NAME EXPRESSION - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitNameExpr(NameExpr ne) {
		println(ne.line + ": Visiting a Name Expression");

		// INSERT CODE HERE

		println(ne.line + ": Name Expression has type: " + ne.type);
		return ne.type;
    }

    /** NEW - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitNew(New ne) {
		println(ne.line + ": Visiting a new");

		// INSERT CODE HERE

		println(ne.line + ": New has type: " + ne.type);
		return ne.type;
    }

    /** STATIC INITIALIZER - OUR CODE HERE (COMPLETE) */
    public Object visitStaticInitDecl(StaticInitDecl si) {
		println(si.line + ": Visiting a static initializer");

		// INSERT CODE HERE
		currentContext = si;
		super.visitStaticInitDecl(si);
		// - END -

		return null;
    }

    /** SUPER - OUR CODE HERE (COMPLETE) */
    public Object visitSuper(Super su) {
		println(su.line + ": Visiting a super");

		// INSERT CODE HERE
		if(currentClass.superClass() == null) {
			Error.error(su, "Super called on class with no super class.");
		}
		else {
			su.type = currentClass.superClass();
		}
		// - END -

		return su.type;
    }

    /** SWITCH STATEMENT - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitSwitchStat(SwitchStat ss) {
		println(ss.line + ": Visiting a Switch statement");

		// INSERT CODE HERE

		return null;
    }

    /** TERNARY EXPRESSION - OUR CODE HERE (COMPLETE) */
    public Object visitTernary(Ternary te) {
		println(te.line + ": Visiting a ternary expression");

		// INSERT CODE HERE
		Type exprType = (Type)te.expr().visit(this);
		Type trueExprType = (Type)te.trueBranch().visit(this);
		Type falseExprType = (Type)te.falseBranch().visit(this);
		
		if(!exprType.isBooleanType()) {
			Error.error(te, "Ternary expression must have boolean expression.");
		}
		else if(!falseExprType.identical(trueExprType)) {
			Error.error(te, "Ternary expression must have identical return types.");
		}
		
		te.type = falseExprType;
		// - END -

		println(te.line + ": Ternary has type: " + te.type);
		return te.type;
    }

    /** UNARY POST EXPRESSION - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitUnaryPostExpr(UnaryPostExpr up) {
		println(up.line + ": Visiting a unary post expression");
		Type eType = null;

		// INSERT CODE HERE

		println(up.line + ": Unary Post Expression has type: " + up.type);
		return eType;
    }

    /** UNARY PRE EXPRESSION - OUR CODE HERE (STILL TO COMPLETE) */
    public Object visitUnaryPreExpr(UnaryPreExpr up) {
		println(up.line + ": Visiting a unary pre expression");

		// INSERT CODE HERE

		println(up.line + ": Unary Pre Expression has type: " + up.type);
		return up.type;
    }

    /** VAR - OUR CODE HERE (COMPLETE) */
    public Object visitVar(Var va) {
		println(va.line + ": Visiting a var");

		// INSERT CODE HERE
		if(va.init() != null) {
			Type varType = (Type)va.myDecl.type();
			Type initType = (Type)va.init().visit(this);
			if(!Type.assignmentCompatible(varType, initType)) {
				Error.error(va, "This type cannot be assigned to this variable.");
			}
		}
		// - END -

		return null;
    }

    /** WHILE STATEMENT - OUR CODE HERE (COMPLETE) */
    public Object visitWhileStat(WhileStat ws) {
		println(ws.line + ": Visiting a while statement"); 

		// INSERT CODE HERE
		Type exprType = (Type)ws.expr().visit(this);
		
		if(!exprType.isBooleanType()) {
			Error.error(ws, "While statement must have boolean expression.");
		}
		
		ws.stat().visit(this);
		// - END -

		return null;
    }

}
