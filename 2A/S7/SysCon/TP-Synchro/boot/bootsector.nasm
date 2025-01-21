;-------------------------------------------------------------------------------
;      Secteur de boot de ManuX ...
;
;      Ce code doit tenir dans un secteur (512 octets). Il se contente donc de
;   charger en mémoire le code de init puis le code du noyau et de faire un
;   saut à l'adrese de init.
;                                                      (C) Manu Chaput 2000-2023
;-------------------------------------------------------------------------------

; La directive suivante permet de dire à NASM que le secteur de boot
; est chargé à cette adresse. Cela lui permet de déterminer à quelle
; adresse exacte se situe chaque élément.
org MANUX_BOOT_START_ADDRESS 

[bits 16]
        ; On se prépare une pile
	;-----------------------
        cli                        ; Pas d'interruption SVP
        mov ax, MANUX_STACK_SEG_16 ; Initialisation du segment de pile
        mov ss, ax
        mov sp, 0
        sti                        ; OK, on accepte à nouveau

        ; Chargement de l'init depuis le disque 
        ;--------------------------------------
ChargeInit :
        mov ax, 0
        mov es, ax                       ; es:bx
        mov bx, MANUX_INIT_START_ADDRESS ; Adresse de destination

        mov ah, 2                  ; Lecture = fonction 2
        mov al, MANUX_NB_SECT_INIT ; taille d'init
        mov cx, 2                  ; à partir du secteur 2
        mov dx, 0                  ; head=0, drive=0
        int 13h                    ; On place ça en ES:BX

        jc InitDisquette           ; En cas d'erreur, on réinitialise

%ifdef VIRE_DANS_INI
        ; Chargement du noyau depuis le disque. On va la convertir
        ; sous la forme es:bx 
        ;---------------------------------------------------------
        mov ax, MANUX_KERNEL_START_ADDRESS>>4      ; Adresse de destination 
        mov es,ax                                  ; es:bx
        mov bx, MANUX_KERNEL_START_ADDRESS & 0x0F  ; cf 3 lignes plus haut

        mov al, MANUX_NB_SECT_KERNEL    ; x secteurs (taille du noyau)
        mov ah, 2                       ; On veut lire
        mov cx, 4                       ; à partir du secteur 4
        mov dx, 0                       ; head=0, drive=0
        int 13h                         ; On place ça en ES:BX

        jc InitDisquette            ; 0x7c34
%endif
        ; Arret du lecteur de disquette WARNING violent et pas beau
        ;----------------------------------------------------------
        mov dx, 03f2h
        in al, dx                    ; On lit l'état du contrôleur
        and al, 0fh                  ; on y met à 0 le "bit moteur"
        out dx, al                   ; et on lui renvoie ...

        ; On saute à l'adresse de l'init
        ;-------------------------------
        jmp MANUX_INIT_START_ADDRESS

BoucleFolle:
	jmp BoucleFolle            ; Inutile a priori !

        ; Réinitialisation du lecteur de disquette (en cas de pb)
        ;--------------------------------------------------------
InitDisquette :
        mov dl, 0                  ; Disquette A: = 0
        mov ax, 0                  ; Initialisation = fonction 0
        int 13h
        jnc ChargeInit             ; Si erreur carry = 0

; On complète par des 0 pour faire 512 octets

times 510-($-$$) db 0
        dw 0AA55h
