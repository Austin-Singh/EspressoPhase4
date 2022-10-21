package Utilities;

import AST.*;
import Parser.sym;

/** Rewrites all NameExpr whose myDecl is a FieldDecl to a FieldRef with a null
 * target to 
 * <className>.field for static fields
 * this.field for non-static fields
 * 
 * @author Matt Pedersen
 *
 */
public class Rewrite {
    public void go(AST a, ClassDecl cd) {
	for (int i=0; i<a.nchildren; i++) {
	    if (a.children[i] != null) {
		if (a.children[i] instanceof NameExpr) {  // if a.children[i] id a Name Expression
		    NameExpr ne = (NameExpr)a.children[i];
		    if (ne.myDecl instanceof FieldDecl) {   // and its myDecl is a Field Declaration (i.e., the name referred to a field)
			FieldDecl fd = (FieldDecl)ne.myDecl;
			FieldRef fr;
			// Add the class name as the target
			if (fd.isStatic()) {
			    NameExpr na = new NameExpr(new Name(new Token(sym.IDENTIFIER, cd.name(), ne.line, ne.charBegin, ne.charBegin + cd.name().length())));
			    na.myDecl = cd;
			    fr = new FieldRef(na, ne.name());
			    fr.rewritten = true;
			    a.children[i] = fr;
			} else {
			    // Add 'this' as target
			    This th = new This(new Token(sym.THIS, "this", ne.line, ne.charBegin, ne.charBegin + 4));
			    ClassType ct = new ClassType(new Name(new Token(sym.IDENTIFIER, cd.name(), ne.line, ne.charBegin, ne.charBegin + cd.name().length())));
			    ct.myDecl = cd;
			    th.type = ct;
			    fr = new FieldRef(th, ne.name());
			    fr.rewritten = true;
			    fr.myDecl = (FieldDecl)ne.myDecl;
			    a.children[i] = fr;
			}
		    }
		} else 
		    go(a.children[i], cd);
	    }
	}
    }
}
