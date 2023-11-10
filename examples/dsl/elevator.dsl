int maxFloor := 0;
int curFloor := 0;
int target := 0;

bool doneInit := false;
bool targetSet := false;

method extern incrMaxFloor () {
    assume(!doneInit);
    maxFloor++;
}

method F extern done () {
    assume(!doneInit);
    doneInit := true;
}

method extern changeTarget(bool incr) {
    assume(doneInit && !targetSet);
    assume(incr -> target < maxFloor);
    assume(!incr -> target > 1);
    if (incr) target++;
    else target--;
}

method GF extern setTarget () {
    assume(doneInit && !targetSet);
    targetSet := true;
}

method intern changeFloor (bool incr) {
    assert(doneInit && targetSet);
    assert(incr -> curFloor < maxFloor);
    assert(!incr -> curFloor > 1);
    if (incr) curFloor++;
    else curFloor--;
}

//method intern stutter () {}

method intern reachTarget() {
    assert(doneInit && targetSet);
    assert(target == curFloor);
    targetSet := false;
}


guarantee {
    G (setTarget -> F reachTarget)
}
