target remote :1234
break *0x7e00
break *0x20000
dir noyau
dir lib
dir boot
dir usr
dir sf
file noyau/noyaumb.elf
