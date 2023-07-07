int x := 0;
bool done := false;
output bool goal := false;

method extern incr_env(bool _done) {
    assume(!done);
    x++;
    done := _done;
}

method intern decr() {
    assume(done);
    x--;
}

method intern incr() {
    assume(done);
    x++;
}

method extern check() {
    assert(x == 0);
    goal := true;
}