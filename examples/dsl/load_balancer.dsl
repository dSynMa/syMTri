int LOAD := 3;
int CPU0 := 0;
int CPU1 := 0;
bool mustEnqueue := false;


method extern cpu0IsLighter () { assume(CPU0 < CPU1); }
method extern cpu1IsLighter () { assume(CPU1 < CPU0); }
method GF extern askEnqueue () { mustEnqueue := true; }

method intern enqueue (bool tocpu0) {
    assert(mustEnqueue);
    if (tocpu0) { CPU0 := CPU0 + LOAD; }
    else        { CPU1 := CPU1 + LOAD; }
    mustEnqueue := false;
}

// The CONTROLLER loses if the ENVIRONMENT is able to call either method forever
// At the moment these need to be passed to symtri via cli, but we can extend
// the language. e.g.:
//guarantee {
//    !(G (cpu0IsLighter | askEnqueue));
//    !(G cpu1IsLighter);
//}


// A load-balancing CPU scheduling algorithm that determines which CPU to allocate tasks to. It will always apply tasks to a CPU with a lighter load.
//#LIA#
//always guarantee {
//    enqueue && gt cpu0 cpu1 -> [cpu0 <- add cpu0 c1()];
//    enqueue && gt cpu1 cpu0 -> [cpu1 <- add cpu1 c1()];
//
//    (!(enqueue) && gt cpu0 cpu1) -> [cpu0 <- add cpu0 c1()] && [cpu1 <- sub cpu1 c0()];
//    (!(enqueue) && gt cpu1 cpu0) -> [cpu1 <- add cpu1 c1()] && [cpu0 <- sub cpu0 c0()];
//
//    !(G gt cpu0 cpu1);
//    !(G gt cpu1 cpu0);
//}