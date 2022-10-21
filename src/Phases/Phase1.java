package Phases;

import AST.*;
import Scanner.*;
import Parser.*;

public class Phase1 extends Phase {

	public void execute(Object arg, int debugLevel, int runLevel) {
		if ((debugLevel & 0x0001) == 0x0001)
			Scanner.debug = true; //((parser)arg).lexer.debug = true;
		try {
			if ((runLevel & 0x0001) == 0x0001) {
				java_cup.runtime.Symbol r = ((parser)arg).parse();
				root = (AST)r.value;
			}
		} catch (java.io.IOException e) {
			System.out.println("An I/O error occured while scanning :");
			System.out.println(e);
			System.exit(1);
		} catch (Exception e) {
			e.printStackTrace();
			System.exit(1);
		}
	}
}