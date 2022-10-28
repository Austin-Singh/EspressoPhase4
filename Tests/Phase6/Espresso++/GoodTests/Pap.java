//(62)
//
//+-----+
//| 54  |
//|    3|
//| 56 5|
//|025 5|
//|     |
//+-----+
//+-----+
//|     |
//|     |
//|     |
//|     |
//|     |
//+-----+
//Missing = 19
//+-----+
//|     |
//|XXX  |
//|  XX |
//|  XX |
//|   X |
//+-----+
//Missing = 10
//+-----+
//|     |
//|XXX X|
//|  XXX|
//|  XXX|
//|   X |
//+-----+
//Missing = 5
//+-----+
//|     |
//|XXX X|
//|  XXX|
//|  XXX|
//|   X |
//+-----+
//Missing = 3
//+-----+
//| XX  |
//|XXX X|
//|  XXX|
//|  XXX|
//|   X |
//+-----+
//Missing = 1
//+-----+
//| XX  |
//|XXX X|
//|  XXX|
//|  XXX|
//|   X |
//+-----+
//Missing = 0
//+-----+
//| XX  |
//|XXX X|
//|  XXX|
//|  XXX|
//|   X |
//+-----+
import System;

public class Pap {

    public static int board[][] = new int[][]{
	{-2, -2, -2, -2, -2, -2 ,-2}, 
	decode(" 54  "),
	decode("    3"),
	decode(" 56 5"),
	decode("025 5"),
	decode("     "),
	{-2, -2, -2, -2, -2, -2 ,-2}};

    public static int[] decode(String s) {
	int[] a = new int[s.length()+2];
	a[0] = -2;
	a[s.length()+1] = -2;
	for (int i=0;i<s.length(); i++) {
	    if (s.charAt(i) == ' ')
		a[i+1] = -1;
	    else
		a[i+1] = s.charAt(i)-'0';
	}
	return a;
    }
	


    public static int board2[][] = new int[board.length][board[0].length];

    public static void printBoard(int[][] b, boolean numberBoard, boolean fin) {
	System.out.print("+");
	for (int i=1; i<b[0].length-1; i++) 
	    System.out.print("-");
	System.out.println("+");
	for (int i=1; i<b.length-1; i++) {
	    System.out.print("|");
	    for (int j=1; j<b[i].length-1; j++) {
		if (numberBoard) {
		    System.out.print(b[i][j]>=0 ? b[i][j]+"" : " ");
		} else {
		
		    if (b[i][j] == 1) // it is black
			System.out.print("X");
		    else if (b[i][j] == 0 && !fin)
			System.out.print(" ");
		    else
			System.out.print(" ");
		}
	    }
	    System.out.println("|");
	}
	System.out.print("+");
	for (int i=1; i<b[0].length-1; i++) 
	    System.out.print("-");
	System.out.println("+");
    }

    // count the number of squares in b that have value 'value' 
    public static int getSquareCount(int[][] b, int x, int y, int  value) {
	int sum = 0;
	for (int i=x-1;i<=x+1;i++)
	    for(int j=y-1; j<=y+1; j++)
		if (b[i][j] != -2 && b[i][j] == value) {		   
		    sum++;
		}
	return sum;
    }

    public static int color(int b[][], int x, int y, int from, int to) {
	int count = 0;
	for (int i=x-1;i<=x+1;i++)
	    for(int j=y-1; j<=y+1; j++)
		if (b[i][j] == from) {
		    b[i][j] = to;
		    count++;
		}
	return count;
    }

    public static int color2(int b[][], int x, int y, int direction) {
	int count = 0;
	// E S S F 
	// E 2 5 F 
	// E S S F 
	// 
	//b[x][y] == 5 if direction = -1, otherwise b[x][y] == 2
	//System.out.println(x + " " + y + " " + direction);
	// TODO: this is a silly hack -- same in color3


	if (x-1<0) x++;
	if (direction == 1) {
	    for (int i=x-1;i<=x+1;i++)
                if (b[i][y-2] == -1) {
                    b[i][y-2] = 1;
                    count++;
                }
	    for (int i=x-1;i<=x+1;i++)
                if (b[i][y-2] == -1) {
                    b[i][y-2] = 0;
                    count++;
                }
	}
	if (direction == -1) {
	    for (int i=x-1;i<=x+1;i++)
		if (b[i][y+1] == -1) {
		    b[i][y+1] = 0;
		    count++;
		}
	    for (int i=x-1;i<=x+1;i++)
		if (b[i][y+1] == -1) {
		    b[i][y+1] = 1;
		    count++;
		}
	} 
	return count;
    }



    public static int color3(int b[][], int x, int y, int direction) {
	int count = 0;
	// E E E
	// S 2 S
	// S 5 S
	// F F F
	// 
	//b[x][y] == 5 if direction = -1, otherwise b[x][y] == 1
	if (y-1<0) y++;
	if (direction == -1) {
	    for (int j=y-1;j<=y+1;j++)
		if (b[x-2][j] == -1) {
		    b[x-2][j] = 0;
		    count++;
		}
	    for (int j=y-1;j<=y+1;j++)
		if (b[x+1][j] == -1) {
		    b[x+1][j] = 1;
		    count++;
		}
	} else if (direction == 1) {
	    for (int j=y-1;j<=y+1;j++)
                if (b[x-2][j] == -1) {
                    b[x-2][j] = 1;
                    count++;
                }
	    for (int j=y-1;j<=y+1;j++)
                if (b[x+1][j] == -1) {
                    b[x+1][j] = 0;
                    count++;
                }
	}
	return count;
    }

    
    public static void main(String args[]) {
	for (int i=0; i<board.length;i++) {
	    for (int j=0; j<board[0].length; j++) {
		if (i==0 || i==board.length-1 || j==0 || j==board[0].length-1)
		    board2[i][j] = -2;
		else
		    board2[i][j] = -1;  // 0 white, 1 black, -2 edge, -1 unknown
	    }
	}
	//printBoard(board2, false, false);
	printBoard(board, true, false);

	int missing = (board.length-2)*(board[0].length-2);
	int oldMissing = missing;
	while (missing > 0) {
	    for (int i=1; i<board.length-1;i++) {
		for (int j=1; j<board[0].length-1; j++) { 
		    // if the number of neighbors that are black plus 
		    // the number of neighbors that are blank is the 
		    // same as board[i][j] then color the blank ones black	    	    
		    if (getSquareCount(board2, i, j, 1) + getSquareCount(board2, i, j, -1) == board[i][j]) 
			missing -= color(board2, i, j, -1, 1);
		    // if the number of neighbors that are black is 
		    // the correct number, then color the rest white.
		    if (getSquareCount(board2, i, j, 1) == board[i][j])
			missing -= color(board2, i, j, -1, 0);
		    if (board[i][j] == 0)
			missing -= color(board2, i, j, -1, 0);
		    if (board[i][j] == 9)
			missing -= color(board2, i, j, -1, 1);
		    if (board[i][j] < 9 && i>2 && board[i][j] == board[i][j-1]-3)    // 5 2 
			missing -= color2(board2, i, j, -1);
		    if (board[i][j] < 9 && i>2 && board[i][j] == board[i][j-1]+3)    // 2 5
			missing -= color2(board2, i, j, 1);
		    if (board[i][j] < 9 && j>2 && board[i][j] == board[i-1][j]-3)    // 5 above 2
			missing -= color3(board2, i, j, -1);
		    if (board[i][j] < 9 && j>2 && board[i][j] == board[i-1][j]+3)    // 5 below 2
			missing -= color3(board2, i, j, 1);		   
		}
	    }
	    printBoard(board2, false, false);
	    //printBoard(board, true, false);
	    System.out.println("Missing = " + missing);
	    if (missing == oldMissing) {
		System.out.println("Stuck!");
		return;//System.exit(1);
	    }

	    oldMissing = missing;
	}
	printBoard(board2, false, true);
   }

}
