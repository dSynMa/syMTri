int x := 1;
bool init_done := false;
output bool goal := false;

method intern decr() {
    x--;
}

method intern incr() {
    x++;
}

method extern check() {
    //assert(init_done);
    //assert(x == 0);
    goal := (x == 0);
}