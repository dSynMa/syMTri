int x := 0;

method intern decr() {
    x--;
}

method intern incr() {
    x++;
}

method extern check() {
    assert(x < 0);
}