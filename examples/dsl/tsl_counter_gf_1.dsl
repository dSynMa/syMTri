// Adapted from the "counters" example in 
// Bernd Finkbeiner, Felix Klein, Ruzica Piskac, Mark Santolucito,
// Temporal Stream Logic: Synthesis beyond the Bools.
// https://arxiv.org/pdf/1712.00246.pdf


int MIN0 := 0;
int MAX0 := 1;

int count0 := 0;
bool canDecr0 := false; 
bool canIncr0 := true;

bool initStage := true;

method extern incrMax () {
    assume(initStage);
    MAX0++;
}

method extern doneInit () {
    assume(initStage);
    initStage := false;
}

method extern decr0 () {
    assume(!initStage && canDecr0);
    assert(count0-1 >= MIN0);
    count0--;
}

method extern incr0 () {
    assume(!initStage && canIncr0);
    assert(count0+1 <= MAX0);
    count0++;
}

// Controller actions
method GF intern toggleDecr0 () { assert(!initStage); canDecr0 := !canDecr0; }
method GF intern toggleIncr0 () { assert(!initStage); canIncr0 := !canIncr0; }
method intern stutter () {}