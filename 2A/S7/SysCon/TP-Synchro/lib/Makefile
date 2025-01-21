.SUFFIXES: .nasm .bin .obj .c

include ../make.commons

include ../make.conf

ASM_BIN_OPT = -f bin

OBJETS      = string.o 
OBJETS     += $(if $(MANUX_CONSOLE), console.o)
OBJETS     += $(if $(MANUX_PRINTK), printk.o)
OBJETS     += $(if $(MANUX_JOURNAL), journal.o)
OBJETS     += $(if $(MANUX_RAMDISK), ramdisk.o)
OBJETS     += $(if $(MANUX_JOURNAL), journal.o)
OBJETS     += $(if $(MANUX_CLAVIER), clavier.o)
OBJETS     += $(if $(MANUX_STDLIB), stdlib.o)
#OBJETS     += $(if $(MANUX_GESTION_MEMOIRE), malloc.o)

libmanux.a : $(MANUX_FICHIER_CONFIG) $(OBJETS)
	ar rf libmanux.a $(OBJETS)

.$(ASM_EXT).bin :
	$(ASM) $(ASM_BIN_OPT) $< -o $@

.c.o :
	gcc $(CFLAGS) -c $<

clean :
	rm -f bochs.out *.bin *.obj *.o *.a

