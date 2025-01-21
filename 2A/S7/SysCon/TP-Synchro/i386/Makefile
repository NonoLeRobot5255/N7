.SUFFIXES: .nasm .bin .obj .c

ASM_EXT  = nasm

ASM         = nasm

include ../make.conf
include ../make.commons

# Les objects compilés (éventuellement sous condition d'une variable)
OBJETS      = interruptions.o \
              horloge.o \
              intel-8259a.o \
              arith64.o \
              interBasNiveau.bin \
#              gestionGDT.bin

OBJETS     +=   $(if $(MANUX_GESTION_MEMOIRE), segment.o)

ASM_DEF	    += -D MANUX_KERNEL_TASK_TSS_IND=$(MANUX_KERNEL_TASK_TSS_IND)
ASM_DEF     += -D MANUX_HANDLER_IRQ=$(MANUX_HANDLER_IRQ)
ASM_DEF     += $(if $(MANUX_APPELS_SYSTEME), -D MANUX_APPELS_SYSTEME)
ASM_DEF     += $(if $(MANUX_CLAVIER), -D MANUX_CLAVIER)

libi386.a : $(OBJETS)
	ar rf libi386.a	$(OBJETS)

.$(ASM_EXT).bin :
	$(ASM) $(ASM_DEF) $(ASM_ELF_OPT) $< -o $@

.c.o :
	gcc $(CFLAGS) -c $<

clean :
	rm -f bochs.out *.bin *.obj *.o *.a

