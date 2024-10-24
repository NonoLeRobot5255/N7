#include <manux/config.h>

ENTRY(_startManuX)                  /* Nom du point d'entrée */

SECTIONS {
    . = MANUX_KERNEL_START_ADDRESS; /* C'est ici que tout commence */
    .boot :                         /* On commence par le multiboot */
    {
        *(.multiboot)
    }

    _adresseDebutManuX = .;         /* C'est ici que le noyau commence */
    .text : {
       *(.text)
    }        
    .rodata : {
       *(.rodata)
    }
    .data : {
       *(.data)
    }
    .bss : {
       *(.bss)
    }
    _adresseFinManuX = .;           /* Repérage de la fin */
    . = ALIGN(4096);
    _adressePileManuX = . ; 
    .stack (NOLOAD) :
    {
        . = . + MANUX_TAILLE_PILE;
    }
    _adresseLimitePileManuX = . ; 
}

