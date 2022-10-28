//(32)
//
//fib(0) = 0
//fib(1) = 1
//fib(2) = 1
//fib(3) = 2
//fib(4) = 3
//fib(5) = 5
//fib(6) = 8
//fib(7) = 13
//fib(8) = 21
//fib(9) = 34
//fib(10) = 55
//fib(11) = 89
//fib(12) = 144
//fib(13) = 233
//fib(14) = 377
//There are 25 primes less than 100 and they are {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}
//true
//Here is 123 right justified 7: ' 123'
//|       1       2       3       4       5 |
//|       6       7       8       9      10 |
//|      11      33      55      77      99 |
//|     100     300     600     877     899 |
//| -866769      54      12      56    3425 |
//F:
//| 1 0 |
//| 0 1 |
//F^25:
//| 121393  75025 |
//|  75025  46368 |
//Fib(25) = 75025
//| 19 22 |
//| 43 50 |
import System;

public class Assignment5 {

    public static int fib(int n) {
	int[][] F = new int[][]{ {1, 1}, {1, 0}};
	int[][] M = new int[][]{ {1, 0}, {0, 1}};

	for (int i=0; i<n; i++) {
	    int[][] temp = new int[][]{{0,0}, {0,0}};
	    // calculate M = M * F;
	    temp[0][0] = M[0][0]*F[0][0]+M[0][1]*F[1][0];
	    temp[0][1] = M[0][0]*F[0][1]+M[0][1]*F[1][1];
	    temp[1][0] = M[1][0]*F[0][0]+M[1][1]*F[1][0];
	    temp[1][1] = M[1][0]*F[0][1]+M[1][1]*F[1][1];
	    M = temp;
	    
	}
	return M[1][0];
    }

    public static int[] sieve(int n) {
	int[] numbers = new int[n];
	for (int i=0; i<n ; i++) 
	    numbers[i] = i+1;
	numbers[0] = 0;	
	for (int i=1;i<n;i++) {
	    if (numbers[i] != 0) {
		int j = numbers[i]*2;
		while (j<=n) {
		    numbers[j-1] = 0;
		    j = j + numbers[i];
		}
	    }
	}
	int count = 0;
	for (int i=0; i<n;i++)
	    if (numbers[i] != 0)
		count++;
	int primes[] = new int[count];
	int index = 0;
	for (int i=0; i<n; i++) 
	    if (numbers[i] != 0) {

		primes[index] = numbers[i];
		index++;
	    }
	return primes;
    }
				
	  
    public static boolean checkMatrixDim(int[][] M, int n) {
	if (M.length != n)
	    return false;
	for (int i=0; i<n; i++)
	    if (M[i].length != n)
		return false;
	return true;
    }


    public static String rjustify(int val, int n) {
	String result = "" + val;
	while (result.length() < n)
	    result = " " + result;
	return result;
    }
	       
    
    public static void printMatrix(int[][] M, int n) {
	if (checkMatrixDim(M,n)) {
	    int max = 0;
	    int min = 0;
	    for (int i=0; i<n; i++)
		for (int j=0;j<n;j++) {
		    if (M[i][j] < min) min = M[i][j];
		    if (M[i][j] > max) max = M[i][j];
		}
	    int l1 = ("" + min).length();
	    int l2 = ("" + max).length();
	    int just = ((l1>l2) ? l1 : l2) + 1;

	    for (int i=0;i<n;i++) {
		System.out.print("|");
		for (int j=0;j<n;j++)
		    System.out.print(rjustify(M[i][j],just));
		System.out.println(" |");
	    }
	}
    }


    public static int[][] matrixMult(int[][] A, int[][] B, int n) {
	if (!checkMatrixDim(A,n) || !checkMatrixDim(B,n))
	    return null;
	else {
	    int[][] C = new int[n][n];
	    for (int i=0;i<n;i++)
		for (int j=0;j<n;j++)
		    C[i][j] = 0;
	    for (int i=0;i<n;i++)
		for (int j=0;j<n;j++)
		    for (int k=0;k<n;k++)
			C[i][j] += A[i][k]*B[k][j];
	    return C;
	}
    }
    

    public static void main(String[] args) {	
	
	for (int i=0;i<15;i++) {
	    System.out.println("fib(" + i + ") = " +fib(i));
	}
	
	int[] primes = sieve(100);
	System.out.print("There are " + primes.length + " primes less than 100 and they are {");
	for(int i=0;i<primes.length;i++) {
	    System.out.print(primes[i]);
	    if (i<primes.length-1)
		System.out.print(", ");
	}
	System.out.println("}");
	
	System.out.println(checkMatrixDim(new int[][] { {1,2,3,4,5},
							{6,7,8,9,10},
							{11,33,55,77,99},
							{100,300,600,877,899},
							{-866769,54,12,56,3425}}, 5));
	
	
	
	System.out.println("Here is 123 right justified 7: '" + rjustify(123,4) + "'");
	
	
	printMatrix(new int[][] { {1,2,3,4,5},
				  {6,7,8,9,10},
				  {11,33,55,77,99},
				  {100,300,600,877,899},
				  {-866769,54,12,56,3425}}, 5);
	
	
	int[][] A,B,C;
	A = new int[][]{{1,1},{1,0}};
	C = new int[][]{{1,0},{0,1}};
	System.out.println("F:");	
	printMatrix(C,2);
	for (int i=1;i<=25;i++) {
	    C = matrixMult(C,A,2);
	}
	System.out.println("F^25:");	
	printMatrix(C,2);
	System.out.println("Fib(25) = " + C[1][0]);
	
	printMatrix(matrixMult(new int[][]{{1,2},{3,4}},
			       new int[][]{{5,6},{7,8}},2),2);
    }
    
}