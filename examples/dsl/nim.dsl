// The game of Nim
// https://en.wikipedia.org/wiki/Nim

// In this version the player taking the last item wins,
// we can easily switch that by changing some assumes to assert and vice versa.

int row0 = 1, row1 = 3, row2 = 5, row3 = 7;

int chosenRow = 0;

// Whose turn is it?
bool envTurn = true;

// Has the current player chosen a row already?
bool hasChosen = false;


// First, choose a non-empty row and remove 1 item.
method extern envChoose (bool c0, bool c1, bool c2, bool c3) {
    assume(envTurn && !hasChosen);
    assume(c0 => !c1 && !c2 && !c3 && row0 > 0);
    assume(c1 => !c0 && !c2 && !c3 && row1 > 0);
    assume(c2 => !c0 && !c1 && !c3 && row2 > 0);
    assume(c3 => !c0 && !c1 && !c2 && row3 > 0);
    if (c0) { chosenRow = 0; row0--; }
    if (c1) { chosenRow = 1; row1--; }
    if (c2) { chosenRow = 2; row2--; }
    if (c3) { chosenRow = 3; row3--; }
    hasChosen = true;

    // If the board is cleared, controller loses
    assert(row0 + row1 + row2 + row3 > 0);
}

// After a row has been chosen, environment can keep removing items
method extern envRemoveNext () {
    assume(envTurn && hasChosen);
    if (chosenRow == 0) { assume(row0 > 0); row0--; }
    if (chosenRow == 1) { assume(row1 > 0); row1--; }
    if (chosenRow == 2) { assume(row2 > 0); row2--; }
    if (chosenRow == 3) { assume(row3 > 0); row3--; }
    // If the board is cleared, environment wins
    assert(row0 + row1 + row2 + row3 > 0);
}

// ... or pass
method extern envPass() {
    assume(envTurn && hasChosen);
    envTurn = false;
    hasChosen = false;
}

// Same for the controller, more or less
method intern conChoose (bool cc0, bool cc1, bool cc2, bool cc3) {
    assert(!envTurn && !hasChosen);
    // Cardinality
    assert(cc0 || cc1 || cc2 || cc3);
    assert(cc0 => !cc1 && !cc2 && !cc3 && row0 > 0);
    assert(cc1 => !cc0 && !cc2 && !cc3 && row1 > 0);
    assert(cc2 => !cc0 && !cc1 && !cc3 && row2 > 0);
    assert(cc3 => !cc0 && !cc1 && !cc2 && row3 > 0);
    if (cc0) { chosenRow = 0; row0--; }
    if (cc1) { chosenRow = 1; row1--; }
    if (cc2) { chosenRow = 2; row2--; }
    if (cc3) { chosenRow = 3; row3--; }
    hasChosen = true;

    // If the board is cleared, controller wins
    assume(row0 + row1 + row2 + row3 > 0);
}

// After a row has been chosen, controller can keep removing items...
method intern conRemoveNext () {
    assert(!envTurn && hasChosen);
    if (chosenRow == 0) { assume(row0 > 0); row0--; }
    if (chosenRow == 1) { assume(row1 > 0); row1--; }
    if (chosenRow == 2) { assume(row2 > 0); row2--; }
    if (chosenRow == 3) { assume(row3 > 0); row3--; }
    
    // If the board is cleared, controller wins
    assume(row0 + row1 + row2 + row3 > 0);
}

// ... or pass
method intern conPass() {
    assert(!envTurn && hasChosen);
    envTurn = true;
    hasChosen = false;
}