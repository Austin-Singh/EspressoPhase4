package Phases;

import ModifierChecker.*;
import Utilities.*;

public class Phase5 extends Phase4 {
	public void execute(Object arg, int debugLevel, int runLevel) {
		boolean traceModifierChecker = ((debugLevel & 0x0010) == 0x0010);
		super.execute(arg, debugLevel, runLevel);

		if (traceModifierChecker)
			System.out.println("** Checking Modifiers **");
		if ((runLevel & 0x0010) == 0x0010) {
		    root.visit(new ModifierChecker(classTable, traceModifierChecker));
		}
		if (traceModifierChecker) {
			System.out.println("** Checking Modifiers ** DONE!");
			System.out.println("Phase 5 successfully terminated");
		}       	
	}
}