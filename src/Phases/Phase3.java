package Phases;

import AST.*;
import NameChecker.*;

public class Phase3 extends Phase2 {
	public void execute(Object arg, int debugLevel, int runLevel) {
		boolean traceNameChecker = ((debugLevel & 0x0004) == 0x0004);
		super.execute(arg, debugLevel, runLevel);

		if (traceNameChecker) 
			System.out.println("** Defining Classes, Members and Fields. **");
		if ((runLevel & 0x0004) == 0x0004) {
			((Compilation)root).visit(new ClassAndMemberFinder(Phase.classTable,traceNameChecker));
		}
		if (traceNameChecker) 
			System.out.println("** Defining Classes, Members and Fields. ** DONE!");

		if (traceNameChecker) {
			System.out.println("---------------------------------------------------------");
			System.out.println("** Resolving symbols and defining locals. **");
		}
		if ((runLevel & 0x0004) == 0x0004) {
			((Compilation)root).visit(new MyDeclSet(Phase.classTable, traceNameChecker));   
			((Compilation)root).visit(new NameChecker(Phase.classTable,traceNameChecker));
		}
		if (traceNameChecker) {
			System.out.println("** Resolving symbols and defining locals. ** DONE!");
			System.out.println("Phase 3 successfully terminated.");
		}
	}
}