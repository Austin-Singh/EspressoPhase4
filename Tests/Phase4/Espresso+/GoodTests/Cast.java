class Dessert {}

class Cake extends Dessert {}

class Scone extends Dessert {}

class ChocolateCake extends Cake {}

class ButteredScone extends Scone {}

public class test1 {

    void moorge(Dessert d, Scone s) {}
    void moorge(Dessert d, Scone s, int j) {}

    void moorge(Cake c, Dessert d) {}
    
    void moorge(ChocolateCake cc, Scone s) {}

    void main() {
	Dessert dessertRef;
	Cake cakeRef;
	Scone sconeRef;
	ChocolateCake chocolateCakeRef;
	ButteredScone butteredSconeRef;
	int i;
	float f;
	String s;

       	moorge(dessertRef, sconeRef);
	
	moorge(chocolateCakeRef, dessertRef);

	moorge(chocolateCakeRef, butteredSconeRef);

	//moorge(cakeRef, sconeRef);

	sconeRef = (Scone)butteredSconeRef; 
	//butteredSconeRef = (ButteredScone) chocolateCakeRef;

	f = (float)i;
	i = (int)f;
	//i = (int)s;
    }
}

