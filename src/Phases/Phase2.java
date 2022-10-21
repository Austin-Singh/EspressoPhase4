package Phases;

import AST.*;
import Utilities.*;
import Parser.*;

public class Phase2 extends Phase1 {
    public static ClassDecl Objects_myDecl = null;

	public void execute(Object arg, int debugLevel, int runLevel) {
		super.execute(arg, debugLevel, runLevel);
		if ((runLevel & 0x0002) == 0x0002) {
			// Add a shared superclass named 'Object' to the parse tree
			ClassDecl cd =  new ClassDecl(new Sequence(new Modifier(Modifier.Public)),
					new Name(new Token(sym.IDENTIFIER, "Object", 0, 0, 0)),
					null,
					new Sequence(),
					new Sequence(),
					false);
			cd.doNotGenerateCode();
			Objects_myDecl = cd;
			((Compilation)root).types().append(cd);
		}
		if ((debugLevel & 0x0002) == 0x0002) {
			((Compilation)root).visit(new PrintVisitor()); 
		}
	}
}