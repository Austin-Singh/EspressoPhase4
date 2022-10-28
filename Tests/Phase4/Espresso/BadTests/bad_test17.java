//(1)
//#6: Left hand side of instanceof cannot be a class.
class test {
      public static void main() {
	  test a;
	  boolean b = (test instanceof test);
      }
}