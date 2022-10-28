//(1)
//#7: Left hand side of instanceof needs expression of class type
class test {
      public static void main() {
	  test a;
	  int c;
	  boolean b = (c instanceof test);
      }
}
