int cnt := 0;
bool done_requests := false;

method extern request(){
    assume(!done_requests);
    cnt++;
}
method extern service(){
    assume(!done_requests);
    done_requests := true;
}

method intern grant(){
    assert(done_requests);
    // ... code to handle job ...
    cnt--;
}
method intern finish(){
    assert(done_requests);
    assert(cnt == 0);
    done_requests := false;
}