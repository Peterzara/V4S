function twoloops() {
    var i = 0;
    while (i <= 8) {
        pred(i >= 0);
        i = i + 1;
    }
    while (i <= 7) {
        pred(i >= 8);
        pred(i <= 9);
        i = i + 1;
    }
    assert (i == 8);
}
