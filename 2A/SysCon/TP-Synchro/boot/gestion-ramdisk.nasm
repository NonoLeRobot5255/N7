chargerRamDisk :

; Chargement du RamDisk, si nécessaire
        ;-------------------------------------
        mov ax, MANUX_NB_SECT_RAMDISK
        cmp ax, 0h
        je PasDeRamdisk

        mov si, MsgLoadRamDisk
        call AfficheBIOS

        mov ax, MANUX_NB_SECT_RAMDISK
        shr ax, 1
        mov [TailleRamdisk], ax
        xor ebx, ebx
        mov bx, [MemoireEtendue]    ; OK, bx = taille de la mémoire étendue
        add bx, 0400h               ; on lui ajoute le Méga de base ...
        mov ax, MANUX_NB_SECT_RAMDISK     ; ... et on lui enlève la taille du ramdisk
        shr ax, 1                   ; 1 secteur = 1/2 Ko
        sub bx, ax
        shl ebx, 10                 ; 1 Ko = 2^10 Octets ...
        mov [AdresseRamdisk], ebx    ; On stoque l'adresse de début du RamDisk

        ; Chargement effectif
        mov ax, MANUX_SEGMENT_TRANSIT_RAMDISK ; Adresse de destination ...
        mov es,ax                       ; ... dans es:bx
        mov bx, 0

        mov ah, 2                 ; Lecture = fonction 2
        mov al, MANUX_NB_SECT_RAMDISK
        mov cx, MANUX_NB_SECT_INIT + MANUX_NB_SECT_KERNEL + 2
        mov dx, 0                 ; head=0, drive=0
        int 13h                   ; On place ça en ES:BX

        jc ErreurChargeRamDisk

        jmp SuiteRamdisk

ErreurChargeRamDisk :
        mov si, MsgErreurRamDisk
        call AfficheBIOS

PasDeRamdisk :
        mov si, MsgNoRamDisk
        call AfficheBIOS

SuiteRamdisk:

	ret

%
%
%
DeplacerRamdisk :

        ; On déplace ensuite le RamDisk vers le haut de la mémoire

        mov eax, MANUX_SEGMENT_TRANSIT_RAMDISK ; Calcul de l'adresse "flat" ...
        shl eax, 0x4                     ; ... du transit du ramdisk.
        mov esi, eax

        mov eax, MANUX_INIT_START_ADDRESS   ; Calcul de l'adresse "flat" ...
        shl eax, 0x4                  ; ... de la variable ...
        add eax, AdresseRamdisk       ; ... AdresseRamdisk .
        mov edi, [eax]

        mov eax, MANUX_INIT_START_ADDRESS   ; Calcul de l'adresse "flat" ...
        shl eax, 0x4                  ; ... de la variable ...
        add eax, TailleRamdisk        ; ... TailleRamdisk .

        mov ecx, [eax]
        shl ecx, 10

        cld
        rep movsb                     ; [ES:ESI]->[DS:EDI] ECX fois

	ret