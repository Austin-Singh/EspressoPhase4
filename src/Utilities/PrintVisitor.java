package Utilities;

import AST.*;
import Utilities.Visitor;
import Phases.*;

/** Prints the parse tree
 * 
 * @author Matt Pedersen
 *
 */
public class PrintVisitor extends Visitor {

	private int indent = 0;

	private String indent(int line) {
		String s = "" + line + ": ";
		int l = 4-s.length();
		for (int i=0; i<indent+l; i++) {
			s = s + " ";
		}
		return s;
	}

	/** ARRAY ACCESS EXPRESSION */
	public Object visitArrayAccessExpr(ArrayAccessExpr ae) {
		System.out.println(indent(ae.line) + "Array Access Expression:");
		indent += 2;
		super.visitArrayAccessExpr(ae);
		indent -=2;
		return null;
	}

	//** ARRAY LITERAL */
	public Object visitArrayLiteral(ArrayLiteral al) {
		System.out.println(indent(al.line) + "Array Literal:");
		indent += 2;
		super.visitArrayLiteral(al);
		indent -= 2;
		return null;
	}

	//** ARRAY TYPE */
	public Object visitArrayType(ArrayType at) {
	    System.out.print(indent(at.line) + "Array Type: ");
		for (int i=0;i<at.getDepth();i++)
		    System.out.print("[]");
	    System.out.println();
	    indent += 2;
	    super.visitArrayType(at);
	    indent -= 2;
	    return null;
	}
	
	/** ASSIGNMENT */
	public Object visitAssignment(Assignment as) {
		System.out.println(indent(as.line) + "Assignment:");
		indent += 2;
		super.visitAssignment(as);
		indent -= 2;
		return null;
	}

	/** ASSIGNMENT OP */
	public Object visitAssignmentOp(AssignmentOp ao) {
		System.out.println(indent(ao.line) + "AssignmentOp = " + ao.operator());
		return null;
	}

	/** BINARY EXPRESSION */
	public Object visitBinaryExpr(BinaryExpr be) {
		System.out.println(indent(be.line) + "BinaryExpr:");
		indent += 2;
		super.visitBinaryExpr(be);
		indent -= 2;
		return null;
	}              

	/** BINARY OPERATOR */
	public Object visitBinOp(BinOp bo) {
		System.out.println(indent(bo.line) + "BinOp = " + bo.operator());
		return null;
	}

	/** BLOCK */
	public Object visitBlock(Block bl) {
		System.out.println(indent(bl.line) + "Block:");
		indent += 2;
		super.visitBlock(bl);
		indent -= 2;
		return null;
	}

	/** BREAK STATEMENT */
	public Object visitBreakStat(BreakStat bs) {
		System.out.println(indent(bs.line) + "BreakStat");
		return null;
	}

	/** CAST EXPRESSION */
	public Object visitCastExpr(CastExpr ce) {
		System.out.println(indent(ce.line) + "CastExpr:");
		indent += 2;
		super.visitCastExpr(ce);
		indent -= 2;
		return null;
	}

	/** CONSTRUCTOR INVOCATION (EXPLICIT) */
	public Object visitCInvocation(CInvocation ci) {
		if (ci.superConstructorCall())
			System.out.println(indent(ci.line) + "CInvocation (super):");
		else
		indent += 2;
		super.visitCInvocation(ci);
		indent -= 2;
		return null;
	}

	/** CLASS DECLARATION */
	public Object visitClassDecl(ClassDecl cd) {
		if (cd.isClass())
			System.out.println(indent(cd.line) + "ClassDecl: (Class)");
		else
			System.out.println(indent(cd.line) + "ClassDecl: (Interface)");
		System.out.println(indent(cd.line) + "  [Name       :: " + cd.className() + " ]");
		System.out.println(indent(cd.line) + "  [MethodTable:: " + cd.methodTable + " ]");
		System.out.println(indent(cd.line) + "  [FieldTable :: " + cd.fieldTable + " ]");
		System.out.println(indent(cd.line) + "  [Modifiers  :: " + cd.modifiers + "]");
		if (cd.isClass()) 
			if (cd.superClass() != null)
				System.out.println(indent(cd.line) + "  [Extends     :: " + cd.superClass().typeName() + "]"); 

		if (cd.interfaces() != null) {
			if (cd.isClass())	
				System.out.print(indent(cd.line) + "  [Implements :: ");
			else
				System.out.print(indent(cd.line) + "  [Extends  :: ");
			for (int i=0; i<cd.interfaces().nchildren; i++) 
				System.out.print(((ClassType)cd.interfaces().children[i]).typeName() + " ");
			System.out.println("]");
		}
		indent += 2;
		cd.body().visit(this);
		indent -= 2;
		return null;
	}      

	/** CLASS TYPE */
	public Object visitClassType(ClassType ct) {
		System.out.println(indent(ct.line) + "ClassType:");
		indent += 2;
		super.visitClassType(ct);
		indent -= 2;
		return null;
	}

	/** COMPILATION UNIT */
	public Object visitCompilation(Compilation co) {
		System.out.println(indent(co.line) + "Compilation:");
		System.out.println(indent(co.line) + "  [ClassTable:: " + Phase.classTable + " ]");
		indent += 2;
		super.visitCompilation(co);
		indent -= 2;
		return null;
	}

	/** CONSTRUCTOR DECLARATION */
	public Object visitConstructorDecl(ConstructorDecl cd) {
		System.out.println(indent(cd.line) + "ConstructorDecl: (Constructor)");
		System.out.println(indent(cd.line) + "  [Name      :: " + cd.name() + "]");
		System.out.println(indent(cd.line) + "  [Modifiers :: " + cd.getModifiers() + "]");
		indent += 2; 
		if (cd.params() != null)
			cd.params().visit(this);
		if (cd.cinvocation() != null)
			cd.cinvocation().visit(this);
		if (cd.body() != null)
			cd.body().visit(this);
		indent -= 2;
		return null;
	}

	/** CONTINUE STATEMENT */
	public Object visitContinueStat(ContinueStat cs) {
		System.out.println(indent(cs.line) + "Continue");
		return null;
	} 

	/** DO STATEMENT */
	public Object visitDoStat(DoStat ds) {
		System.out.println(indent(ds.line) + "DoStat:");
		indent += 2;
		super.visitDoStat(ds);
		indent -= 2;
		return null;
	}

	/** EXPRESSION STATEMENT */
	public Object visitExprStat(ExprStat es) {
		System.out.println(indent(es.line) + "ExprStat:");
		indent += 2;
		super.visitExprStat(es);
		indent -= 2;
		return null;
	}

	/** FIELD DECLARATION */
	public Object visitFieldDecl(FieldDecl fd) {
		System.out.println(indent(fd.line) + "FieldDecl:");
		System.out.println(indent(fd.line) + "  [Modifiers: " + fd.modifiers + "]");
		indent += 2;
		super.visitFieldDecl(fd);
		indent -= 2;
		return null;
	}      

	/** FIELD REFERENCE */
	public Object visitFieldRef(FieldRef fr) {
		System.out.println(indent(fr.line) + "FieldRef:");
		indent +=2;
		super.visitFieldRef(fr);
		indent -=2;
		return null;
	}

	/** FOR STATEMENT */
	public Object visitForStat(ForStat fs) {
		System.out.println(indent(fs.line) + "ForStat:");
		indent += 2;
		super.visitForStat(fs);
		indent -= 2;
		return null;
	}

	/** IF STATEMENT */
	public Object visitIfStat(IfStat is) {
		System.out.println(indent(is.line) + "IfStat:");
		indent += 2;
		super.visitIfStat(is);
		indent -= 2;
		return null;
	}

	/** INVOCATION */
	public Object visitInvocation(Invocation in) {
		System.out.println(indent(in.line) + "Invocation:");
		indent += 2;
		super.visitInvocation(in);
		indent -= 2;
		return null;
	}

	/** LITERAL */
	public Object visitLiteral(Literal li) {
		System.out.println(indent(li.line) + "Literal = " + li);
		indent += 2;
		super.visitLiteral(li);
		indent -= 2;
		return null;
	}

	/** VARIABLE LOCAL DECLARATION */
	public Object visitLocalDecl(LocalDecl ld) {
		System.out.println(indent(ld.line) + "LocalDecl:");
		indent += 2;
		super.visitLocalDecl(ld);
		indent -= 2;
		return null;
	}      

	/** METHOD DECLARATION*/
	public Object visitMethodDecl(MethodDecl md) {
		System.out.println(indent(md.line) + "MethodDecl: (Method)");
		System.out.println(indent(md.line) + "  [Name        :: " + md.name() + "]");
		System.out.println(indent(md.line) + "  [Modifiers   :: " + md.getModifiers() + "]");
		System.out.println(indent(md.line) + "  [Return type :: " + md.returnType().typeName() + " ]");
		indent += 2;
		md.params().visit(this);
		if (md.block() != null)
			md.block().visit(this);
		indent -= 2;
		return null;
	}

	/** NAME */
	public Object visitName(Name na) {
		System.out.println(indent(na.line) + "Name = " + na);
		return null;
	}

	/** NAME EXPRESSION */
	public Object visitNameExpr(NameExpr ne) {
		System.out.println(indent(ne.line) + "NameExpr:");
		indent += 2;
		super.visitNameExpr(ne);
		indent -= 2;
		return null;
	}

	/** NEW EXPRESSION */
	public Object visitNew(New ne) {
		System.out.println(indent(ne.line) + "New:");
		indent += 2;
		super.visitNew(ne);
		indent -= 2;
		return null;
	}

	/** NEW ARRAY */
	public Object visitNewArray(NewArray ne) {
		System.out.println(indent(ne.line) + "New Array");
		indent += 2;
		super.visitNewArray(ne);
		indent -= 2;
		return null;
	}

	
	/** VARIABLE PARAMETER DECLARATION */
	public Object visitParamDecl(ParamDecl pd) {
		System.out.println(indent(pd.line) + "ParamDecl: ");
		indent += 2;
		super.visitParamDecl(pd);
		indent -= 2;
		return null;
	}      

	/** POSTFIX OPERATOR */
	public Object visitPostOp(PostOp po) {
		System.out.println(indent(po.line) + "PostOp = " + po.operator());
		return null;
	}

	/** PREFIX OPERATOR */
	public Object visitPreOp(PreOp po) {
		System.out.println(indent(po.line) + "PreOp = " + po.operator());
		return null;
	}

	/** PRIMITIVE TYPE */
	public Object visitPrimitiveType(PrimitiveType pt) {
		System.out.println(indent(pt.line) + "PrimitiveType = " + pt);
		return null;
	}

	/** RETURN STATEMENT */
	public Object visitReturnStat(ReturnStat rs) {
		if (rs.expr() == null)
			System.out.println(indent(rs.line) + "Return");
		else
			System.out.println(indent(rs.line) + "Return:");
		indent += 2;
		super.visitReturnStat(rs);
		indent -= 2;
		return null;
	}

	/** SEQUENCE */
	public Object visitSequence(Sequence se) {
		System.out.println(indent(se.line) + "Sequence:[" + se.nchildren + " nodes]");
		for (int i=0; i<se.nchildren; i++) {
			if (se.children[i] != null) {
				System.out.println(indent(se.children[i].line) + "Sequence[" + i + "]:");
				indent += 2;
				se.children[i].visit(this);
				indent -= 2;
			}
		}
		return null;
	}

	/** STATIC INITIALIZER **/
	public Object visitStaticInitDecl(StaticInitDecl si) {
		System.out.println(indent(si.line) + "Static Initializer:");
		indent += 2;
		super.visitStaticInitDecl(si);
		indent -= 2;
		return null;
	}

	/** SUPER **/
	public Object visitSuper(Super su) {
		System.out.println(indent(su.line) + "Super");
		return null;
	}

	/** SWITCH GROUP */
	public Object visitSwitchGroup(SwitchGroup sg) {	
		System.out.println(indent(sg.line) + "Switch Group:");
		indent += 2;
		super.visitSwitchGroup(sg);
		indent -= 2;
		return null;
	}

	/** SWITCH LABEL */
	public Object visitSwitchLabel(SwitchLabel sl) {
		System.out.println(indent(sl.line) + "Switch Label:");
		indent += 2;
		super.visitSwitchLabel(sl);
		indent -= 2;
		return null;
	}

	/** SWITCH STAT */
	public Object visitSwitchStat(SwitchStat st) {
		System.out.println(indent(st.line) + "Switch Stat:");
		indent += 2;
		super.visitSwitchStat(st);
		indent -= 2;
		return null;
	}

	/** TERNARY EXPRESSION */
	public Object visitTernary(Ternary te) {
		System.out.println(indent(te.line) + "Ternary:");
		indent += 2;
		super.visitTernary(te);
		indent -= 2;
		return null;
	}

	/** THIS STATEMENT */
	public Object visitThis(This th) {
		System.out.println(indent(th.line) + "This");
		return null;
	}

	/** UNARY POST EXPRESSION */
	public Object visitUnaryPostExpr(UnaryPostExpr up) {
		System.out.println(indent(up.line) + "UnaryPostExpr:");
		indent += 2;
		super.visitUnaryPostExpr(up);
		indent -= 2;
		return null;
	}

	/** UNARY PRE EXPRESSION */
	public Object visitUnaryPreExpr(UnaryPreExpr up) {
		System.out.println(indent(up.line) + "UnaryPreExpr:");
		indent += 2;
		super.visitUnaryPreExpr(up);
		indent -= 2;
		return null;
	}

	/** VAR(IABLE) */
	public Object visitVar(Var va) {
		System.out.println(indent(va.line) + "Var:"); 
		indent += 2;
		super.visitVar(va);
		indent -= 2;
		return null;
	}

	/** WHILE STATEMENT */
	public Object visitWhileStat(WhileStat ws) {
		System.out.println(indent(ws.line) + "WhileStat:");
		indent += 2;
		super.visitWhileStat(ws);
		indent -= 2;
		return null;
	}

}
