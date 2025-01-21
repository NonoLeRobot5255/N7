;-------------------------------------------------------------------------------
; Quelques macros spécifiques à multiboot
;-------------------------------------------------------------------------------
MULTIBOOT_PAGE_ALIGN   equ 0x00000001 ; Alignement des modules sur des pages
MULTIBOOT_MEMORY_INFO  equ 0x00000002 ; Pour que multiboot nous donne le plan

;-------------------------------------------------------------------------------
; Définition de notre entête
;-------------------------------------------------------------------------------
FLAGS    equ  MULTIBOOT_MEMORY_INFO 
MAGIC    equ  0x1BADB002        
CHECKSUM equ -(MAGIC + FLAGS)
header_addr   dd 0
load_addr     dd 0
load_end_addr dd 0
bss_end_addr  dd 0
entry_addr    dd 0
mode_type     dd 0
width         dd 0
height        dd 0
depth         dd 0

;-------------------------------------------------------------------------------
; L'entête à proprement parler
;-------------------------------------------------------------------------------
section .multiboot
align 4
	dd MAGIC
	dd FLAGS
	dd CHECKSUM
     
;-------------------------------------------------------------------------------
; Le code de démarrage. On se contente d'initialiser le pointeur de pile, car
; ce n'est pas prévu par multiboot. Apparemment GRUB le fait, mais pas le
; loader de qemu par exemple.
;-------------------------------------------------------------------------------
global _startManuX
extern _adresseLimitePileManuX
extern startManuX

_startManuX :
	mov esp, _adresseLimitePileManuX
 
	call startManuX
 
	cli
.FinDesTemps:	hlt
	jmp .FinDesTemps

