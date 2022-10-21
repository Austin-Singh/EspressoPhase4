package Phases;

import TypeChecker.*;


public class Phase4 extends Phase3 {
	public void execute(Object arg, int debugLevel, int runLevel) {
		boolean traceTypeChecker = ((debugLevel & 0x0008) == 0x0008);
		super.execute(arg, debugLevel, runLevel);

		if (traceTypeChecker)
			System.out.println("** Checking types **");
		if ((runLevel & 0x0008) == 0x0008) {
			root.visit(new TypeChecker(classTable,traceTypeChecker));
		}
		if (traceTypeChecker) {
			System.out.println("** Checking types ** DONE!");
			System.out.println("Phase 4 successfully terminated.");
		}
	}
}