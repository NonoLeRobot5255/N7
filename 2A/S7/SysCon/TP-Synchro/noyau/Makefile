.SUFFIXES: .nasm .bin .obj .c .ld .lds

include ../make.conf     # La configuration générale
include ../make.commons  # Les principales valeurs globales
include ../make.rules    # Les règles les plus génériques

LIBRAIRIES_MANUX = $(LIBI386) $(LIBMANUX) $(LIBUSR)
LIBRAIRIES_MANUX += $(if  $(MANUX_FICHIER), $(LIBSF))

OBJETS      = 	$(MANUX_FICHIER_MAIN).o
OBJETS     +=   $(if $(MANUX_BOOTLOADER), bootloader.o)
OBJETS     +=   $(if $(MANUX_TACHES), listetaches.o tache.o)
OBJETS     +=   $(if $(MANUX_TACHES), scheduler.o)
OBJETS     +=   $(if $(MANUX_GESTION_MEMOIRE), memoire.o)
OBJETS     +=   $(if $(MANUX_PAGINATION), pagination.o)
OBJETS     +=   $(if $(MANUX_OUTILS_SYNCHRO), semaphore.o)
OBJETS     +=   $(if $(MANUX_APPELS_SYSTEME), appelsysteme.o)
OBJETS     +=   $(if $(MANUX_PCI), pci.o)
OBJETS     +=   $(if $(MANUX_ATOMIQUE), atomique.o)
OBJETS     +=   $(if $(MANUX_VIRTIO), virtio.o)
OBJETS     +=   $(if $(MANUX_VIRTIO_NET), virtio-net.o)
OBJETS     +=   $(if $(MANUX_VIRTIO_CONSOLE), virtio-console.o)
OBJETS     +=   $(if $(MANUX_KMALLOC), $(MANUX_KMALLOC).o)

# Une cible pour compiler les binaires, mais sans édition de liens
binaries :  $(OBJETS)

all : binaries noyau.elf noyaumb.elf 

#----------------------------------------------------------------------------------
# Une fois qu'on a tout compilé, il est temps de construire les noyaux
#----------------------------------------------------------------------------------
# Création d'un noyau "elf"
noyau.elf  : $(LD_SCRIPT) $(OBJETS) $(LIBRAIRIES_MANUX)
	ld -m elf_i386 --section-start=.text=$(MANUX_KERNEL_START_ADDRESS) -nmagic -T $(LD_SCRIPT) $(OBJETS) $(LIBRAIRIES_MANUX) -o $@
	nm noyau.elf | sort > symbols
	objcopy  -O binary $(NOYAU_ELF) $(NOYAU_BIN)

# Le même avec un entête multiboot (pas top !)
noyaumb.elf  : $(LD_SCRIPT) $(MB_MANUX_ELF) $(OBJETS) $(LIBRAIRIES_MANUX)
	ld -m elf_i386 -nmagic -T $(LD_SCRIPT) $(MB_MANUX_ELF) $(OBJETS) $(LIBRAIRIES_MANUX) -o $@
	nm noyaumb.elf | sort > symbolsmb


#----------------------------------------------------------------------------------

clean :
	rm -f bochs.out *.bin *.obj *.o *.elf *.a symbols* $(LD_SCRIPT)
