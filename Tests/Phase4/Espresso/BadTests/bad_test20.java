//(1)
//#6: Illegal type cast. Cannot cast type 'test' to type 'int'.
class test {
      public static void main() {
	  test a;
	  a = (int)a;
      }
}