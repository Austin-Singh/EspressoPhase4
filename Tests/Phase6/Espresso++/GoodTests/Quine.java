//(35)
//
//import System;
//public class Quine
//{
//public static void main( String[] args )
//{
//char q = 34;
//String[] l = new String[] {
//"import System;",
//"public class Quine",
//"{",
//"public static void main( String[] args )",
//"{",
//"char q = 34;",
//"String[] l = new String[] {",
// "",
//"};",
//"for( int i = 0; i < 7; i++ )",
//"System.out.println( l[i] );",
//"for( int i = 0; i < l.length-1; i++ )",
//"System.out.println( l[7] + q + l[i] + q + ',');",
//"System.out.println( l[7] + q + l[l.length-1] + q);",
//"for( int i = 8; i < l.length; i++ )",
//"System.out.println( l[i] );",
//"}",
//"}"
//};
//for( int i = 0; i < 7; i++ )
//System.out.println( l[i] );
//for( int i = 0; i < l.length-1; i++ )
//System.out.println( l[7] + q + l[i] + q + ',');
//System.out.println( l[7] + q + l[l.length-1] + q);
//for( int i = 8; i < l.length; i++ )
//System.out.println( l[i] );
//}
//}
import System;
public class Quine
{
public static void main( String[] args )
{
char q = 34;
String[] l = new String[] {
"import System;",
"public class Quine",
"{",
"public static void main( String[] args )",
"{",
"char q = 34;",
"String[] l = new String[] {",
"",
"};",
"for( int i = 0; i < 7; i++ )",
"System.out.println( l[i] );",
"for( int i = 0; i < l.length-1; i++ )",
"System.out.println( l[7] + q + l[i] + q + ',');",
"System.out.println( l[7] + q + l[l.length-1] + q);",
"for( int i = 8; i < l.length; i++ )",
"System.out.println( l[i] );",
"}",
"}"
};
for( int i = 0; i < 7; i++ )
System.out.println( l[i] );
for( int i = 0; i < l.length-1; i++ )
System.out.println( l[7] + q + l[i] + q + ',');
System.out.println( l[7] + q + l[l.length-1] + q);
for( int i = 8; i < l.length; i++ )
System.out.println( l[i] );
}
}
