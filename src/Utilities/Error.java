package Utilities;

import AST.*;

public class Error {
	public static String fileName = "";

	public static void setFileName(String name) {
		fileName = name;
	}

	public static void error(AST e, String msg) {
		System.out.println(fileName + ":" + e.line + ": " + msg);
		System.exit(1);
	}   

	public static void error(String msg) {
		System.out.println(fileName + ": " + msg);
		System.exit(1);
	}

	public static void error(AST e, String msg, boolean terminate) {
		System.out.println(fileName + ":" + e.line + ": " + msg);
		if (terminate)
			System.exit(1);
	}   

	public static void error(String msg, boolean terminate) {
		System.out.println(fileName + ": " + msg);
		if (terminate)
			System.exit(1);
	}
}
