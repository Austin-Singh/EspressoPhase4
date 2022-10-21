package Phases;

import AST.*;
import CodeGenerator.*;

public class Phase6 extends Phase5 {
	public void execute(Object arg, int debugLevel, int runLevel) {

		boolean traceCodeGenerator  = ((debugLevel & 0x00020) == 0x0020);
		super.execute(arg, debugLevel, runLevel);
		if ((runLevel & 0x0020) == 0x0020) {
			// If we are not generating code for the EVM, so rename Object to /java/lang/Object etc.
			if (!Utilities.Settings.generateEVMCode)
				((Compilation)root).visit(new Java());

			new CodeGenerator().generate((Compilation)root, traceCodeGenerator);	
			// generate( ) writes the files by calling WriteFiles.
		}       	
	}
}