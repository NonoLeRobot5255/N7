.SUFFIXES: .nasm .bin .obj .c .elf

#KERN_SRC = noyau.$(ASM_EXT)

include ../make.conf
include ../make.commons
include ../make.rules

# Le fichier décrivant la taille du noyau
sinclude $(wildcard $(TAILLE_CONF))

all : floppyboot grubinit

# L'image disquette nécessite un certain nombre de fichiers
floppyboot : $(TAILLE_CONF)
	(make floppyboot2)

floppybootelf : $(TAILLE_CONF)
	(make floppybootelf2)

floppyboot2 : $(BSEC_BIN) $(INIT_BIN) 

floppybootelf2 : $(BSEC_BIN) $(INIT_ELF) 

# Calcul de la taille du noyau et du bourrage nécessaire
$(TAILLE_CONF) :  $(OUTILS) $(NOYAU_BIN)
	../outils/taillenoyau $(NOYAU_BIN) > $@

grubinit :  $(MB_MANUX_ELF)

clean :
	rm -f bochs.out *.bin *.obj *.o bourrage *.elf *.img $(TAILLE_CONF)
