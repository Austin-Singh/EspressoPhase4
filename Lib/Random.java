public class Random {
    private java.util.Random r;
    public Random() {
	this.r = new java.util.Random();
    }
    public Random(long seed) {
	this.r = new java.util.Random(seed);
    }
 
    // Returns the next pseudorandom, uniformly distributed boolean value from this random number generator's sequence. 
    public boolean nextBoolean() {
	return r.nextBoolean();
    }

    // Generates random bytes and places them into a user-supplied byte array.
    public void nextBytes(byte[] bytes) {
	r.nextBytes(bytes);
    }

    // Returns the next pseudorandom, uniformly distributed double value between 0.0 and 1.0 from this random number generator's sequence.
    public double nextDouble() {
	return r.nextDouble();
    }
     
    // Returns the next pseudorandom, uniformly distributed float value between 0.0 and 1.0 from this random number generator's sequence. 
    public float nextFloat() {
	return r.nextFloat();
    }

    // Returns the next pseudorandom, Gaussian ("normally") distributed double value with mean 0.0 
    // and standard deviation 1.0 from this random number generator's sequence.
    public double nextGaussian() {
	return r.nextGaussian();
    }
    
    // Returns the next pseudorandom, uniformly distributed int value from this random number generator's sequence.
    public int nextInt() {
	return r.nextInt();
    }

    // Returns a pseudorandom, uniformly distributed int value between 0 (inclusive) and the specified value 
    // (exclusive), drawn from this random number generator's sequence.
    public int nextInt(int n) {
	return r.nextInt(n);
    }
    
    // Returns the next pseudorandom, uniformly distributed long value from this random number generator's sequence.
    public long nextLong() {
	return r.nextLong();
    }

    // Sets the seed of this random number generator using a single long seed.
    public void setSeed(long seed) {
	r.setSeed(seed);
    }
}
         
    