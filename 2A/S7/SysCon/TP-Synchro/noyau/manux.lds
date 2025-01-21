ENTRY(_startManuX)
SECTIONS {
    . = 0x20000;
    .boot :
    {
        *(.multiboot)
    }
    _adresseDebutManuX = .;
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
    _adresseFinManuX = .;
    . = ALIGN(4096);
    _adressePileManuX = . ;
    .stack (NOLOAD) :
    {
        . = . + 16384;
    }
    _adresseLimitePileManuX = . ;
}
