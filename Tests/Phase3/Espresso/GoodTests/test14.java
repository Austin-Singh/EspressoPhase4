class Reuse {
    Reuse NotReuse(Reuse reuse) {
	Reuse.NotReuse(reuse);
	return reuse;
    }
}

