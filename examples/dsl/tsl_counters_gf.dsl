// Adapted from the "counters" example in 
// Bernd Finkbeiner, Felix Klein, Ruzica Piskac, Mark Santolucito,
// Temporal Stream Logic: Synthesis beyond the Bools.
// https://arxiv.org/pdf/1712.00246.pdf


int MIN0 := 0;
int MAX0 := 3;
int MIN1 := 0;
int MAX1 := 3;

int count0 := 0;
int count1 := 0;
bool canDecr0 := false; 
bool canDecr1 := false;
bool canIncr0 := true;
bool canIncr1 := true;


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
method extern decr1 () {
    assume(canDecr1);           //If violated, environment loses
    assert(count1-1 >= MIN1);   //If violated, environment wins
    count1--;
}
method extern incr1 () {
    assume(canIncr1);
    assert(count1+1 <= MAX1);
    count1++;
}

// Controller actions (basic)
method GF intern toggleDecr0 () { canDecr0 := !canDecr0; }
method GF intern toggleIncr0 () { canIncr0 := !canIncr0; }
method GF intern toggleDecr1 () { canDecr1 := !canDecr1; }
method GF intern toggleIncr1 () { canIncr1 := !canIncr1; }
method intern stutter () {}


// Controller actions (limited)
// method intern toggleDecr0 () { assert(!canIncr0 || count0 == MIN0); canDecr0 := !canDecr0; }
// method intern toggleIncr0 () { assert(!canIncr0 || count0 == MAX0); canIncr0 := !canIncr0; }
// method intern toggleDecr1 () { assert(!canIncr1 || count1 == MIN1); canDecr1 := !canDecr1; }
// method intern toggleIncr1 () { assert(!canIncr1 || count1 == MAX1); canIncr1 := !canIncr1; }
