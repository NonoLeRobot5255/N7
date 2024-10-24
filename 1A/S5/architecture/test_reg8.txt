set rst 1
set rst 0

set e[7..0] 01010101
set en 0
set clk 1
set clk 0
check sr[7..0] 00000000
set clk 1
set clk 0
check sr[7..0] 00000000

set en 1
set e[7..0] 00000000
set clk 1
set clk 0
check sr[7..0] 00000000

set e[7..0] 01010101
set clk 1
set clk 0
check sr[7..0] 01010101

set e[7..0] 10101010
set clk 1
set clk 0
check sr[7..0] 10101010

set e[7..0] 01010111
set clk 1
set clk 0
check sr[7..0] 01010111

set e[7..0] 01011101
set clk 1
set clk 0
check sr[7..0] 01011101

set e[7..0] 01110101
set clk 1
set clk 0
check sr[7..0] 01110101

set e[7..0] 11010101
set clk 1
set clk 0
check sr[7..0] 11010101

set e[7..0] 11110101
set clk 1
set clk 0
check sr[7..0] 11110101

set e[7..0] 11111101
set clk 1
set clk 0
check sr[7..0] 11111101

set e[7..0] 11111111
set clk 1
set clk 0
check sr[7..0] 11111111

set en 0
set e[7..0] 00000000
set clk 1
set clk 0
check sr[7..0] 11111111

set en 1
set e[7..0] 00000000
set clk 1
set clk 0
check sr[7..0] 00000000