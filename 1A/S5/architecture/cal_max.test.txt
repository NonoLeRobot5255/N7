// Test du module cal_max(rst, clk, cal, ad1[7..0], ad2[7..0], elemCour[31..0] : 
// adCour[7..0], max[31..0], adMax[7..0], INITAD, INITMAX, MAJMAX, FINI)
// Attention : il faut que le module testé ait exactement les mêmes signaux
// d'entrée et de sortie, en respectant la casse.

set rst 1
set rst 0
set cal 0
set clk 0

// Initialisation
check INITAD 1
check INITMAX 0
check MAJMAX 0
check FINI 0
check adCour[7..0] 00000000
check adMax[7..0] 00000000
check max[31..0] 00000000000000000000000000000000

set ad1[7..0] 00000001
set ad2[7..0] 00000100
set elemCour[31..0] 00000000000000000000000000000001

set clk 1
// cal = 0 => rien ne se passe
check INITAD 1
check INITMAX 0
check MAJMAX 0
check FINI 0
//check adCour[7..0] 00000001
check adMax[7..0] 00000000
check max[31..0] 00000000000000000000000000000000

// cal=1 : Verif INITAD -> INITMAX
set cal 1
set clk 0
set clk 1

check INITAD 0
check INITMAX 1
check MAJMAX 0
check FINI 0
check adCour[7..0] 00000001
check adMax[7..0] 00000000
check max[31..0] 00000000000000000000000000000000

// Verif INITMAX -> MAJMAX
set clk 0
set elemCour[31..0] 00000000000000000000000000000010
set clk 1

check INITAD 0
check INITMAX 0
check MAJMAX 1
check FINI 0
check adCour[7..0] 00000010
check adMax[7..0] 00000001
check max[31..0] 00000000000000000000000000000010

// Verif MAJMAX -> MAJMAX sans maj du max
set clk 0
set elemCour[31..0] 00000000000000000000000000000001
set clk 1

check INITAD 0
check INITMAX 0
check MAJMAX 1
check FINI 0
check adCour[7..0] 00000011
check adMax[7..0] 00000001
check max[31..0] 00000000000000000000000000000010

// Verif MAJMAX -> MAJMAX avec maj du max
set clk 0
set elemCour[31..0] 00000000000000000000000000000011
set clk 1

check INITAD 0
check INITMAX 0
check MAJMAX 1
check FINI 0
check adCour[7..0] 00000100
check adMax[7..0] 00000011
check max[31..0] 00000000000000000000000000000011

// Verif dernière maj du max
set clk 0
set elemCour[31..0] 00000000000000000000000000000101
set clk 1

check INITAD 0
check INITMAX 0
//check MAJMAX 0
//check FINI 1
//check adCour[7..0] 00000100 
check adMax[7..0] 00000100
check max[31..0] 00000000000000000000000000000101

set clk 0
set clk 1

// Verif FINI -> FINI si cal=1
set clk 0
set clk 1

check INITAD 0
check INITMAX 0
check MAJMAX 0
check FINI 1
//check adCour[7..0] 00000100
check adMax[7..0] 00000100
check max[31..0] 00000000000000000000000000000101

// Verif FINI -> INITAD si cal=0
set cal 0
set clk 0
set clk 1

check INITAD 1
check INITMAX 0
check MAJMAX 0
check FINI 0


