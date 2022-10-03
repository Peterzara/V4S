function while0() {
    var x = 0; 
    var y = 1;
    while (true) {
        invariant(y>=0);
        x = y;
        y = y + 1;
    }
    assert(x>=0);
}
