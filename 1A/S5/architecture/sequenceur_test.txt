// Test du module sequenceur(rst, clk, ir[31..16], N, Z, V, C : fetch, decode, pcplus1, ..., areg[3..0], breg[3..0], dreg[3..0], ualCmd[3..0], dbusIn[1..0], write, setFlags)


// Initialisations
set rst 1
set rst 0
set clk 0

// Vérification état de départ
check fetch 1
check decode 0
check pcplus1 0

///////////////////////
// TEST INSRUCTION add
///////////////////////

// fetch => decode : IR <- [PC]
check areg[3..0] 1110
check breg[3..0] 0000
check dreg[3..0] 1111
check ualCmd[3..0] 0000
check dbusIn[1..0] 10
check write 0

set clk 1
set clk 0
// add %r1, %r0, %r2
set ir[31..16] 0000001000010000

// decode
check fetch 0
check decode 1
check pcplus1 0
check setFlags 1

// decode => pcplus1 : r2 <- r1 + r0
check areg[3..0] 0001
check breg[3..0] 0000
check dreg[3..0] 0010
check ualCmd[3..0] 0000
check dbusIn[1..0] 01
check write 0

set clk 1
set clk 0

// pcplus1
check fetch 0
check decode 0
check pcplus1 1
check setFlags 0

// pcplus1 => fetch : PC <- PC + r1
check areg[3..0] 1110
check breg[3..0] 0001
check dreg[3..0] 1110
check ualCmd[3..0] 0000
check dbusIn[1..0] 01
check write 0

set clk 1
set clk 0

// fetch
check fetch 1
check decode 0
check pcplus1 0

///////////////////////
// TEST INSRUCTION sub
///////////////////////

// fetch => decode : IR <- [PC]
check areg[3..0] 1110
check breg[3..0] 0000
check dreg[3..0] 1111
check ualCmd[3..0] 0000
check dbusIn[1..0] 10
check write 0

set clk 1
set clk 0
// sub %r2, %r1, *r2
set ir[31..16] 0001001000100001

// decode
check fetch 0
check decode 1
check pcplus1 0
check setFlags 1

// decode => pcplus1 : r2 <- r2 - r1
check areg[3..0] 0010
check breg[3..0] 0001
check dreg[3..0] 0010
check ualCmd[3..0] 0001
check dbusIn[1..0] 01
check write 0

set clk 1
set clk 0

// pcplus1
check fetch 0
check decode 0
check pcplus1 1
check setFlags 0

// pcplus1 => fetch : PC <- PC + r1
check areg[3..0] 1110
check breg[3..0] 0001
check dreg[3..0] 1110
check ualCmd[3..0] 0000
check dbusIn[1..0] 01
check write 0

set clk 1
set clk 0

// fetch
check fetch 1
check decode 0
check pcplus1 0


///////////////////////
// TEST INSRUCTION set
///////////////////////
// à faire

///////////////////////
// TEST INSRUCTION load
///////////////////////
// à faire

///////////////////////
// TEST INSRUCTION store
///////////////////////
// à faire

///////////////////////
// TEST INSRUCTION bcond
///////////////////////
// à faire


