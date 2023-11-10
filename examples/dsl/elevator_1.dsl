

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

method extern incrTarget() {
    assume(doneInit && !targetSet);
    if (target < maxFloor) target++;
    else target := maxFloor;
}

method extern targetReached () {
    assume(doneInit && targetSet && target == curFloor);
    target := 0;
    targetSet := false;
}

method GF extern setTarget () {
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


guarantee {
    G (setTarget -> F targetReached);
}




