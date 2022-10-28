//(1)
//#MCMLXXXIV
//MCMLXXXIV = 1984
import System;

public class Roman {
    public static void main(String args[]) {
	int a[] = new int[] {100,500,0,0,0,0,1,0,0,50,1000,0,0,0,0,0,0,0,0,5,0,10}, sum=0, i;
	for (i=0;i<args[0].length()-1;i++)
            sum += ((a[args[0].charAt(i)-67] < a[args[0].charAt(i+1)-67]) ? -1 : 1)*a[args[0].charAt(i)-67];
        System.out.println(args[0] + " = " + (sum + a[args[0].charAt(i)-67]));
    }
}
