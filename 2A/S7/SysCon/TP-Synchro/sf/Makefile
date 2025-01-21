.SUFFIXES: .nasm .bin .obj .c

#CFLAGS   = -fno-pie -m32 -march=i686 -Wall -I../include -O2 -nostdinc -fno-builtin -fomit-frame-pointer -fno-toplevel-reorder
ASM_EXT  = nasm

ASM         = nasm
ASM_BIN_OPT = -f elf

OBJETS      = fichier.o
OBJETS     +=   $(if $(MANUX_INOEUDS), inoeud.o)
OBJETS     +=   $(if $(MANUX_TUBES), tubes.o)


include ../make.conf

libsf.a : $(OBJETS) 
	ar rf libsf.a	$(OBJETS)

.$(ASM_EXT).bin :
	$(ASM) -D MANUX_KERNEL_TASK_TSS_IND=$(MANUX_KERNEL_TASK_TSS_IND) $(ASM_BIN_OPT) $< -o $@

.c.o :
	gcc $(CFLAGS) -c $<


clean :
	rm -f bochs.out *.bin *.obj *.o *.a

