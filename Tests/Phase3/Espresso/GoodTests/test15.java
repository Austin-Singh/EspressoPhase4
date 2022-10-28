class Reuse {

    Reuse() {
    }
    
    Reuse Reuse(Reuse Reuse) {
        for (;;) {
            if (Reuse.Reuse(Reuse) == Reuse)
                break;
        }
        return Reuse;
    }

    void foo() {
	Reuse r;
	r = new Reuse();
	r = new Reuse(r);
    }

}
