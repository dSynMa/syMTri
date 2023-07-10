int x := 0;
bool init_done := false;
output bool goal := false;

method extern incr_env() {
    assume(!init_done);
    x++;
}

method extern start() {
    assume(!init_done);
    init_done := true;
}

method intern decr() {
    assume(init_done);
    x--;
}

method intern incr() {
    assume(init_done);
    x++;
}

method extern check() {
    assert(init_done);
    assert(x == 0);
    goal := true;
}