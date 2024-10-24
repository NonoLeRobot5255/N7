;-------------------------------------------------------------------------------
;                                                      (C) Manu Chaput 2000-2021
;
; Obsolète : codé directement dans segment.c
; si je dois le réutiliser, attention à définir
;MANUX_CODE_SEG_SEL 0x08
;MANUX_DATA_SEG_SEL 0x10
;-------------------------------------------------------------------------------
;   // http://www.osdever.net/bkerndev/Docs/gdt.htm
;   // https://stackoverflow.com/questions/23978486/far-jump-in-gdt-in-bootloader~


global _chargerGDT

bits 32

gdtr   :
     dw 0 ; For limit storage
     dd 0 ; For base storage

; Chargement effectif de la GDT
;    _chargerGDT(uint32_t adresseGDT, uint16_t taille)
;
;   Cette fonction charge la GDT (avec lgdt) puis réinitialise les
; registres de segment en conséquence. Voir
;   http://www.osdever.net/bkerndev/Docs/gdt.htm
;   https://stackoverflow.com/questions/23978486/far-jump-in-gdt-in-bootloader~

_chargerGDT :
    mov   eax, [esp + 4]
    mov   [gdtr + 2], eax
    mov   ax, [esp + 8]
    mov   [gdtr], ax
    lgdt  [gdtr]
    jmp   MANUX_CODE_SEG_SEL:vidangeGDT

vidangeGDT :
    mov ax, MANUX_DATA_SEG_SEL
    mov ds, ax
    mov es, ax
    mov fs, ax
    mov gs, ax
    mov ss, ax
    
    ret