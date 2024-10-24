.PHONY: FORCE clean
.SUFFIXES: .nasm .bin .obj .c

# Les principales valeurs globales
ROOTDIR := $(shell pwd)

# Le fichier de configuration est généré par make en fonction du
# contenu de include/manux/config.h
-include make.conf
include make.commons
include make.rules

DEMARAGE    = outils boot
RAMDISK     = ./boot/ramdisk.ram
OUTILS      = ./outils/taillenoyau ./outils/makeconfig

# Les includes de usr/include/manux qui sont des copies de include/manux
# ils sont édités dans l'arborescence du noyau et doivent donc être
# mis à jour dans la partie usr
USR_INC_D   = usr/include/manux
USR_INC_F   = appelsystemenum.h types.h string.h i386.h errno.h
USR_INC     = $(USR_INC_F:%.h=$(USR_INC_D)/%.h)

# Quels sont les composants d'un noyau fonctionnel (hors processus de boot)
MANUX_PARTS  = lib noyau  

MANUX_PARTS += $(if $(MANUX_LIBI386), i386)
MANUX_PARTS += $(if $(MANUX_USR), usr)
MANUX_PARTS += $(if $(MANUX_FICHIER), sf)

# Les sous-répertoires (pour le nettoyage par exemple)
SOUS_REP  = $(MANUX_PARTS) $(DEMARAGE) 

export CFLAGS ROOTDIR

#    Les cibles voulues, ce sera probablement des images finales
# WARNING : sont-ce bien les bonnes cibles ?
default : manux

all : manux iso

#-------------------------------------------------------------------------------
#    Première phase : la configuration générale
#-------------------------------------------------------------------------------
configuration : usrinc make.conf

#    Mise à jour des include du monde utilisateur
usr/include/manux/%.h : include/manux/%.h
	cp $< $@

# Le fichier config.h de usr, malheureusement nécessaire, est généré
usrconf :   $(MANUX_FICHIER_CONFIG) $(CONFIG_FILES)
	cpp -I$(ROOTDIR)/include -nostdinc -fno-builtin  -dM $(MANUX_FICHIER_CONFIG)   | awk '/^#define MANUX_/' > usr/include/manux/config.h

usrinc : $(USR_INC) usrconf

#...............................................................................
#    Le fichier de configuration (une des premières choses à faire !)
#...............................................................................
make.conf :  $(MANUX_FICHIER_CONFIG) $(CONFIG_FILES)
	cpp -I$(ROOTDIR)/include -nostdinc -fno-builtin  -dM $(MANUX_FICHIER_CONFIG)  | awk '/^#define MANUX_/ {if (length($$3)){val=$$3}else{val="True"};print $$2"="val}' > make.conf


FORCE:

#-------------------------------------------------------------------------------
#    Deuxième phase : les composants de ManuX
#-------------------------------------------------------------------------------
composants :
	(for r in $(MANUX_PARTS) ; do (cd $$r ; make ) ; done)

$(LIBI386) :
	(cd i386 ; make)

$(LIBSF) :
	(cd sf ; make)

$(LIBMANUX) :
	(cd lib ; make)

$(NOYAU_ELF) : configuration  composants 
	(cd noyau ; make noyau.elf)

#-------------------------------------------------------------------------------
#    Troisième phase : le code d'initialisation (dépend de l'image)
# bootfloppyelf est une nouvelle tentative d'avoir une image utilisable avec qemu !
#-------------------------------------------------------------------------------
bootfloppy : outillage $(NOYAU_ELF)
	(cd boot ; make floppyboot)

bootfloppyelf : outillage $(NOYAU_ELF)
	(cd boot ; make floppybootelf)

# L'image bootgrub nécessite un code d'initialisation spécifique
grubinit :
	(cd boot ; make grubinit)

# Attention, pas top 
outillage :
	(cd outils ; make)

#-------------------------------------------------------------------------------
#    Dernière phase : les images utilisables directement
#-------------------------------------------------------------------------------
manux : $(NOYAU_ELF)

#...............................................................................
# L'image sur disquette est obtenue en concaténant les fichiers de boot, d'init,
# et le noyau, puis en plaçant le tout en début d'un fichier de 1.44 Mo
#...............................................................................
floppy : $(FLOPPYELF_IMG)

$(FLOPPYELF_IMG) : bootfloppyelf $(NOYAU_ELF)
	ld -Ttext=0x7e00 -melf_i386 $(INIT_ELF) -o init.elf
	objcopy  -O binary init.elf $(INIT_BIN)
	cat $(BSEC_BIN) $(INIT_BIN) $(NOYAU_BIN)  > floppy.bin
	dd if=/dev/zero of=$@ bs=1024 count=1440
	dd if=floppy.bin of=$@ bs=512 conv=notrunc

$(FLOPPY_IMG) : bootfloppy $(NOYAU_ELF)
	cat $(BSEC_BIN) $(INIT_BIN) $(NOYAU_BIN)  > floppy.bin
	dd if=/dev/zero of=$@ bs=1024 count=1440
	dd if=floppy.bin of=$@ bs=512 conv=notrunc
#	rm -f floppy.bin



#...............................................................................
#  L'image bootgrub est en fait un noyau linké avec le code pour
# la compatibilité bootgrub
#...............................................................................
$(NOYAUMB_ELF) : configuration  grubinit  composants 
	(cd noyau ; make noyaumb.elf)

# Une image ISO
iso : $(NOYAUMB_ELF)
	$(CREER_ISO) $(ISO_REP_BASE) $(ISO_FICHIER) $(NOYAUMB_ELF)

$(ISO_FICHIER) : iso

#...............................................................................
#    Création d'une image iso intégrant un noyau pour chaque fichier de config
# du répertoire multiconf
#...............................................................................
multiso :
	(rm -rf noyaux/* $(ISO_REP_BASE)/* | true)
	(for c in $(ROOTDIR)/multiconf/*.h ; do (echo "\033[0;34m*****" ; echo "*****  Construction de $$c *****" ;echo "*****\033[0m" ;  make clean ; make MANUX_FICHIER_CONFIG="$$c" $(NOYAUMB_ELF) ; cp noyau/noyaumb.elf noyaux/`basename $$c .h` ) ; done )
	$(CREER_ISO) $(ISO_REP_BASE) $(ISO_FICHIER) noyaux/*

#-------------------------------------------------------------------------------
#    Lancement du noyau
#-------------------------------------------------------------------------------
run : $(NOYAUMB_ELF)
	$(RUN_MANUXMB_ELF)

rundbg : $(NOYAUMB_ELF)
	$(RUN_MANUXMB_ELF_DBG)

runfloppy : manux.img
	$(RUN_MANUX_FLOPPY)

runiso : #$(ISO_FICHIER)
	$(RUN_MANUX_ISO) $(ISO_FICHIER)

runisodbg : #$(ISO_FICHIER)
	$(RUN_MANUX_ISO_DBG) $(ISO_FICHIER)

runmultiso : multiso
	$(RUN_MANUX_ISO) $(ISO_FICHIER)

vbrun : iso
	$(RUN_MANUX_VBOX)

#-------------------------------------------------------------------------------
#
#-------------------------------------------------------------------------------
unifdef.conf :
	cpp -I$(ROOTDIR)/include -nostdinc -fno-builtin  -dM $(ROOTDIR)/include/manux/config.h  | awk '/^#define MANUX_/ {print "#undef "$$2;}' > unifdef.conf
	cpp -I$(ROOTDIR)/include -nostdinc -fno-builtin  -dM $(MANUX_FICHIER_CONFIG)  | awk '/^#define MANUX_/ {if (length($$3)){val=$$3}else{val="True"};print "#define " $$2"="val}' >> unifdef.conf

canevas : unifdef.conf 
	/usr/bin/unifdef -x 2 -f unifdef.conf noyau/main.c -o multiconf/main-$(CFG).c

#-------------------------------------------------------------------------------
#    Quelques cibles complémentaires en vrac
#-------------------------------------------------------------------------------
dump : $(NOYAU_ELF)
	ndisasm $(NOYAU_ELF) -u > dump

clean :
	(for r in $(SOUS_REP) doc ; do (cd $$r ; make clean) ; done)
	rm -f bochs.out *.bin manux *.obj *.o dump $(TAILLE_CONF) *~ __bfe.log__ $(ISO_FICHIER) dump.dat make.conf *.img unifdef.conf

distclean :
	(for r in $(SOUS_REP) ; do (cd $$r ; make clean) ; done)
	rm -f bochs.out *.bin *.obj *.o dump $(TAILLE_CONF) *~

tar : clean
	(cd .. ; tar cvf -  ManuX-32 | $(COMPRESS) > manux-32-`date +"%Y-%m-%d"`.tgz ; echo Archive dans manux-32-`date +"%Y-%m-%d"`.tgz )

