// The game of Nim
// https://en.wikipedia.org/wiki/Nim

// In this version the player taking the last item wins,
// we can easily switch that by changing some assumes to asserts and vice versa.

int row0 := 1;
int row1 := 3;
int row2 := 5;
int row3 := 7;

// TODO use an enum
int chosenRow := 0;

// Whose turn is it?
bool envTurn := true;

// Has the current player chosen a row already?
bool hasChosen := false;


// First, choose a non-empty row and remove 1 item.
method extern envChoose (bool c0, bool c1) {
    assume(envTurn && !hasChosen);
    assume((!c0 && !c1) -> row0 > 0);
    assume((!c0 &&  c1) -> row1 > 0);
    assume(( c0 && !c1) -> row2 > 0);
    assume(( c0 &&  c1) -> row3 > 0);
    // If the board is cleared, controller loses
    assert(row0 + row1 + row2 + row3 > 1);
    if (!c0 && !c1) { chosenRow := 0; row0--; }
    if (!c0 &&  c1) { chosenRow := 1; row1--; }
    if ( c0 && !c1) { chosenRow := 2; row2--; }
    if ( c0 &&  c1) { chosenRow := 3; row3--; }
    hasChosen := true;

}

// After a row has been chosen, environment can keep removing items
method extern envRemoveNext () {
    assume(envTurn && hasChosen);
    assume(chosenRow == 0 -> row0 > 0);
    assume(chosenRow == 1 -> row1 > 0);
    assume(chosenRow == 2 -> row2 > 0);
    assume(chosenRow == 3 -> row3 > 0);
    // If the board is cleared, environment wins
    assert(row0 + row1 + row2 + row3 > 1);

    if (chosenRow == 0) { row0--; }
    if (chosenRow == 1) { row1--; }
    if (chosenRow == 2) { row2--; }
    if (chosenRow == 3) { row3--; }    
}

// ... or pass
method extern envPass() {
    assume(envTurn && hasChosen);
    envTurn := false;
    hasChosen := false;
}

// Same for the controller, more or less
method intern conChoose (bool c0, bool c1) {
    assert(!envTurn && !hasChosen);
    assert((!c0 && !c1) -> row0 > 0);
    assert((!c0 &&  c1) -> row1 > 0);
    assert(( c0 && !c1) -> row2 > 0);
    assert(( c0 &&  c1) -> row3 > 0);
    // If the board is cleared, controller wins
    assume(row0 + row1 + row2 + row3 > 1);
    if (!c0 && !c1) { chosenRow := 0; row0--; }
    if (!c0 &&  c1) { chosenRow := 1; row1--; }
    if ( c0 && !c1) { chosenRow := 2; row2--; }
    if ( c0 &&  c1) { chosenRow := 3; row3--; }
    hasChosen := true;
}

// After a row has been chosen, controller can keep removing items...
method intern conRemoveNext () {
    assert(!envTurn && hasChosen);
    assert(chosenRow == 0 -> row0 > 0);
    assert(chosenRow == 1 -> row1 > 0);
    assert(chosenRow == 2 -> row2 > 0);
    assert(chosenRow == 3 -> row3 > 0);
    // If the board is cleared, controller wins
    assume(row0 + row1 + row2 + row3 > 1);

    if (chosenRow == 0) { row0--; }
    if (chosenRow == 1) { row1--; }
    if (chosenRow == 2) { row2--; }
    if (chosenRow == 3) { row3--; }
}

// ... or pass
method intern conPass() {
    assert(!envTurn && hasChosen);
    envTurn := true;
    hasChosen := false;
}
