;===============================================================================
;      Initialisation de ManuX
;                                                      (C) Manu Chaput 2000-2023
;===============================================================================
%define portCmdClavier  0x64
%define portDonneesClavier  0x60

;org  MANUX_INIT_START_ADDRESS
global InitManuX
[bits 16]


InitManuX :
        ; C'est à cette adresse qu'est chargé l'init
        mov ax, 0 ; MANUX_INIT_START_ADDRESS
        mov ds, ax
        mov es, ax

        ; Chargement du noyau depuis la disquette
	;----------------------------------------
        mov si, msgChargement     ; afficheBIOS le message de chargement
        call afficheBIOS

        call chargerManuX
;        call arretDisquette ; WARNING !? WTF
	
        mov si, msgFinChargement  ; afficheBIOS le message de fin de chargement
        call afficheBIOS

        ; Détection du matériel
        ;----------------------
        mov si, msgDetection
        call afficheBIOS

        ; Lecture de la mémoire conventionnelle
        int 12h
        mov [MemoireDeBase], ax

        ; Lecture de la taille mémoire étendue ([3] p 984)
        mov al, 17h               ;  Demande lecture de la taille
        out 70h, al               ; mémoire étendue (poids faible).
        in al, 71h                ;  Lecture et 
        mov bl, al                ; stockage dans bl
        mov al,18h                ;  Demande lecture de la taille
        out 70h,al                ; mémoire étendue (poids fort).
        in al,71h                 ;  Lecture et
        mov bh, al                ; stockage dans bh
        mov [MemoireEtendue], bx  ; @ 0x10028

        ; Vérifions que nous sommes bien en mode réel
        ;--------------------------------------------
        mov eax, cr0      ; L'info est dans cr0
        and al, 1         ; On vérifie le bit de poids faible
        jz ModeReelOK     ; Il doit être nul ...

        mov si, msgPasEnModeReel
        call afficheBIOS

        mov ah, 9
        int 21h
        mov ax, 4cffh
        int 21h
        jmp BlocageDebug

ModeReelOK :
        mov si, msgModeReel
        call afficheBIOS        ; @ 0x10048

        ; Activation de la ligne A20
        ;---------------------------
        mov si, msgValideA20
        call afficheBIOS

        cli
        call ValideA20
        sti

%ifdef MANUX_RAMDISK
        call ChargerRamdisk
%endif

        ; Passage en mode protégé
        ;------------------------
        mov si, msgPassageProtege
        call afficheBIOS


        ; Chargement de la GDT
        ;---------------------
	cli

        lgdt [LaGDT]                ; Chargement de la GDT

        ; Changement effectif de mode
        ;----------------------------
        mov eax, cr0     ; On positionne
        or eax, 01       ; à un le bit pmode
        mov cr0, eax     ; du registre cr0

        jmp IndSegCode32:Mode32       ; Pour vider le pipe

;-------------------------------------------------------------------------------
;
;-------------------------------------------------------------------------------
%include "gestion-manux.nasm"

%ifdef MANUX_RAMDISK
%include "gestion-ramdisk.nasm"
%endif

;-------------------------------------------------------------------------------
;
;-------------------------------------------------------------------------------
[bits 32]

Mode32:

        ; Initialisation des segments
        ;----------------------------
	mov ax, IndSegData32    ; @ 0x7e70
        mov ds, ax
        mov ss, ax
        mov es, ax
        mov fs, ax
        mov gs, ax

        ; La pile ...
        mov bx, IndSegStack32
        mov ss, bx
;        mov eax, 90000h - 4     ; WARNING !! Reprendre _adresseLimitePileManuX
	                        ; comme dans mb-manux ? sauf qu'on n'est pas linké
				; avec ici, donc comment la connaître ?

        mov eax, 27000h
        mov esp, eax

	sti

%ifdef MANUX_RAMDISK
        call DeplaceRamDisk
%endif

        ; On passe au noyau quelques infos
        ;---------------------------------
        mov eax, MANUX_INIT_MAGIC
        mov ebx, InfoSysteme

        ; Et c'est parti, on saute sur le noyau !
        ;----------------------------------------
        call MANUX_KERNEL_START_ADDRESS
        cli
soLongAndThankYouForTheFish :
        hlt
        jmp soLongAndThankYouForTheFish

[bits 16]

;-------------------------------------------------------------------------------
;      Les sous-programmes
;-------------------------------------------------------------------------------

;      Validation de la ligne A20
;--------------------------------
ValideA20 :
        call AttenteClavierPret
        jnz ValideA20Fin          ; Si pas pret, on arrète
        mov al, 0d1h              ; On veut écrire dans le port de sortie
        out portCmdClavier, al

        call AttenteClavierPret
        jnz ValideA20Fin           ; Si pas pret, on arrète
        mov al, 0dfh               ; Activation ligne A20
        out portDonneesClavier, al ;

ValideA20Fin :
        ret

;      Attente que le clavier soit pret avant de lui envoyer des données
;-----------------------------------------------------------------------
AttenteClavierPret :
        mov ecx, 0ffffffffh
AttenteClavierBcle :
        in al, portCmdClavier     ;  On attend que la mémoire du contrôleur
        test al, 2                ; ne soit pas pleine.
        loopnz AttenteClavierBcle ;
        ret

;      Affichage par le BIOS de la chaine pointée par SI
;-------------------------------------------------------
afficheBIOS:
        lodsb
        or al,al
        jz short afficheBIOSFin
        mov ah,0x0E
        mov bx,0x0007
        int 0x10
        jmp afficheBIOS
afficheBIOSFin :
        retn

;      Blocage de la machine pour débugger
;-----------------------------------------
BlocageDebug :
        mov si, msgBlocage
        call afficheBIOS

BoucleFolle :
        hlt
        jmp BoucleFolle

;-------------------------------------------------------------------------------
;      Les données
;-------------------------------------------------------------------------------
[bits 32]
; Les infos sur le système pour passer au noyau
;----------------------------------------------
InfoSysteme :
   PourFlagsMB :      ; Attention 
        dd 0x02       ; On ne fournit que les info mémoire       
   MemoireDeBase :    ; seuls les deux premiers sont
        dd 0x00       ; compatibles avec multiboot
   MemoireEtendue :   ; mais la suite (ramdisk) ne l'est
        dd 0x00       ; absolument pas

%ifdef MANUX_RAMDISK
   TailleRamdisk :
        dd 0
   AdresseRamdisk :
        dd 0
%endif

[bits 16]

%include "gdt.nasm"

; Les messages
;-------------
;msgChargement     db      'ManuX loading ...',13,10,0
msgChargement     db      '123456789012345678901234567890123456789012345678901234567890',13,10,0
msgFinChargement  db      'ManuX en memoire ...',13,10,0
msgDetection      db      'La, je devrais detecter le matos !', 13, 10, 0
msgBlocage        db      '(Blocage de debug)', 13, 10, 0
msgPassageProtege db      'Allez zou, on passe en mode protege ...', 13, 10, 0
msgModeReel       db      'OK, on est en mode reel !', 13, 10, 0
msgPasEnModeReel  db      'ERREUR, on n est pas en mode reel ...', 13, 10, 0
msgValideA20      db      'Validation de la ligne A20 ...', 13, 10, 0
%ifdef MANUX_RAMDISK
msgLoadRamDisk    db      'Chargement du RamDisk ...', 13, 10, 0
msgNoRamDisk      db      'Pas de RamDisk ...', 13, 10, 0
msgErreurRamDisk  db      'Erreur de chargement RamDisk ...', 13, 10, 0
%endif
msgRunningManux   db      'On lance ManuX, ...', 13, 10, 0
msgDisquetteErr   db      13, 10, 'Erreur disquette !', 13, 10, 0
msgChargementSec  db      '#', 0
msgChargementFin  db      '!', 13, 10, 0

; Le bourrage (pour faire 2 blocs)
;---------------------------------
        times   1024-($-$$) db 0

