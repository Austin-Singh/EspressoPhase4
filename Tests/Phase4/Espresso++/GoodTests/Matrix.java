//(3)
//
//|   14   32   50 |
//|   32   77  122 |
//|   50  122  194 |
import System;

public class Matrix {
    public static int numDigits(int number) {
	int digits = 0;
	if (number < 0) digits = 1; // remove this line if '-' counts as a digit
	while (number>0) {
	    number /= 10;
	    digits++;
	}
	return digits;
    }


    public static void print(int n) {
	System.out.print(" ");
	int d = numDigits(n);
	for (int i=0;i<4-d;i++)
	    System.out.print(" ");
	System.out.print(n);
    }

    public static void print(int[][] m) {
	for (int i=0;i<m.length;i++) {
	    System.out.print("|");
	    for (int j=0;j<m[i].length;j++)
		print(m[i][j]);
	    System.out.println(" |");
	}
    }

    public static void main(String args[]) {
	int[][] A = new int[][]{{1,2,3},{4,5,6},{7,8,9}};
	int[][] B = new int[][]{{1,4,7},{2,5,8},{3,6,9}};
	int[][] C = new int[3][3];
	for (int i=0; i<A.length; i++) {
	    for (int j=0; j<A[i].length; j++) {
		int sum=0;
		for (int k=0; k<A[i].length; k++)
		    sum += A[i][k]*B[k][j];
		C[i][j] = sum;
	    }
	}
	print(C);
    }
    
  
}