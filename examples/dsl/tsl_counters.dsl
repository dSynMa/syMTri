// Adapted from the "counters" example in 
// Bernd Finkbeiner, Felix Klein, Ruzica Piskac, Mark Santolucito,
// Temporal Stream Logic: Synthesis beyond the Bools.
// https://arxiv.org/pdf/1712.00246.pdf


int MIN0, MAX0, MIN1, MAX1; // Parameters

int count0 = MIN0, count1 = MIN1;
bool canDecr0 = false, canDecr1 = false;
bool canIncr0 = false, canIncr1 = false;


method extern decr0 () {
    assume(canDecr0);       //If violated, environment loses
    count0--;
    assert(count0 >= MIN0); //If violated, environment wins
}

method extern incr0 () {
    assume(canIncr0);
    count0++;
    assert(count0 <= MAX0);
}
method extern decr1 () {
    assume(canDecr1);       //If violated, environment loses
    count1--;
    assert(count1 >= MIN0); //If violated, environment wins
}
method extern incr1 () {
    assume(canIncr1);
    count1++;
    assert(count1 <= MAX1);
}

// Controller actions
method intern toggleDecr0 () { canDecr0 = !canDecr0; }
method intern toggleIncr0 () { canIncr0 = !canIncr0; }
method intern toggleDecr1 () { canDecr1 = !canDecr1; } 
method intern toggleIncr1 () { canDecr1 = !canDecr1; } 


// Extra guarantees: liveness of increase/decrease buttons
// GF(canDecr0), GF(canIncr0), GF(canDecr1), GF(canIncr1)
// But this gives a tad too much power to the controller

// //Alternative toggle that limits the controller's power
// method intern toggleIncr0limited () {
//     assert(!canIncr0 || count0 == MAX0);
//     canIncr0 = !canIncr0;
// }