

int maxFloor := 0;
int curFloor := 0;
int target := 0;

bool doneInit := false;
bool targetSet := false;

method extern incrMaxFloor () {
    assume(!doneInit);
    maxFloor++;
}

method extern done () {
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

method extern setTarget () {
    assume(doneInit && !targetSet);
    targetSet := true;
}

// TODO we should scope parameter names to their methods
method intern changeFloor (bool incrFloor) {
    assert(doneInit && targetSet);
    assert(incrFloor -> curFloor < maxFloor);
    assert(!incrFloor -> curFloor > 1);
    if (incrFloor) curFloor++;
    else curFloor--;
}

method intern targetReached() {
    assert(doneInit && targetSet);
    assert(target == curFloor);
    targetSet := false;
}

