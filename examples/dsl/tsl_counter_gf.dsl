// Adapted from the "counters" example in 
// Bernd Finkbeiner, Felix Klein, Ruzica Piskac, Mark Santolucito,
// Temporal Stream Logic: Synthesis beyond the Bools.
// https://arxiv.org/pdf/1712.00246.pdf


int MIN0 := 0;
int MAX0 := 5;

int count0 := 0;
bool canDecr0 := false; 
bool canIncr0 := true;


method extern decr0 () {
    assume(canDecr0);           //If violated, environment loses
    assert(count0-1 >= MIN0);   //If violated, environment wins
    count0--;
}

method extern incr0 () {
    assume(canIncr0);
    assert(count0+1 <= MAX0);
    count0++;
}

// Controller actions (basic)
method GF intern toggleDecr0 () { canDecr0 := !canDecr0; }
method GF intern toggleIncr0 () { canIncr0 := !canIncr0; }
