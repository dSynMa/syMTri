

bool lm := false;
bool rm := false;

method GF extern isLeftmost () {
    assume(!rm);
    lm := true;
}
method GF extern isRightmost () {
    assume(!lm);
    rm := true;
}


method intern moveLeft () {
    assert(!lm);
    rm := false;
}

method intern moveRight () {
    assert(!rm);
    lm := false;
}
method intern stutter () {}


guarantee {
    G (isLeftmost -> F moveRight);
    G (isRightmost -> F moveLeft);
    G (moveRight -> ((moveRight U isRightmost) || G moveRight));
    G (moveLeft -> ((moveLeft U isLeftmost) || G moveLeft));
}


//https://github.com/Barnard-PL-Labs/tsltools/blob/master/src/test/res/specs/Ball.tsl
//always assume {
//  [ball <- moveLeft ball] -> X (! rightmost ball);
//  [ball <- moveRight ball] -> X (! leftmost ball);
//  ! (leftmost ball && rightmost ball);
//}

//always guarantee {
//
//  rightmost ball -> F [ball <- moveLeft ball ];
//  leftmost ball -> F [ball <- moveRight ball ];
//  (! leftmost ball && ! rightmost ball ) -> F ([ball <- moveLeft ball ] || [ball <- moveRight ball ]);
//  (leftmost ball && X (!leftmost ball)) -> ((! [ball <- moveLeft ball]) W rightmost ball);
//  (rightmost ball && X (!rightmost ball)) -> ((! [ball <- moveRight ball]) W leftmost ball);
// }