// module minicraps(rst, clk, on, bregin[3..0], adin[7..0] : 
//	abus[31..0], bbus[31..0], rambus[31..0], dbus[31..0], pc[31..0], ir[31..0], flags[3..0], etats[4..0])
  
// avec le prgramme :
//    "00000000" : "0x02100000"		// add %r1, %r0, %r2
//    "00000001" : "0x03110008"		// add %r1, %r1, %r3
//    "00000010" : "0x14320000"		// sub %r3, %r2, %r4

// Initialisations
set rst 1
set clk 0
set rst 0
set bregin[3..0] 0000
set adin[7..0] 00000000

// Vérification départ
check etats[4..2] 100
check pc[31..0] 00000000000000000000000000000000

// Instruction add %r1, %r0, %r2 : 3 cycles
set on 1
set clk 1
set clk 0
set clk 1
set clk 0
set clk 1
set clk 0

// Vérification des états et du PC
check etats[4..2] 100
check pc[31..0] 00000000000000000000000000000001

// Vérification du résultat
set on 0
set bregin[3..0] 0010
check bbus[31..0] 00000000000000000000000000000001

// Instruction add %r1, %r1, %r3 : 3 cycles
set on 1
set clk 1
set clk 0
set clk 1
set clk 0
set clk 1
set clk 0

// Vérification des états et du PC
check etats[4..2] 100
check pc[31..0] 00000000000000000000000000000010

// Vérification du résultat
set on 0
set bregin[3..0] 0011
check bbus[31..0] 00000000000000000000000000000010

//// sub %r3, %r2, %r4 : 3 cycles
set on 1
set clk 1
set clk 0
set clk 1
set clk 0
set clk 1
set clk 0

// Vérification des états et du PC
check etats[4..2] 100
check pc[31..0] 00000000000000000000000000000011

// Vérification du résultat
set on 0
set bregin[3..0] 0100
check bbus[31..0] 00000000000000000000000000000001






