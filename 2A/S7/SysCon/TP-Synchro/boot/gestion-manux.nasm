;===============================================================================
; Sous-programme de chargement de ManuX en mémoire.
;                                                      (C) Manu Chaput 2000-2023
;===============================================================================

; Le nombre de secteurs que l'on charge à chaque fois (par un appel à l'int 13h
; du BIOS). Concrètement, on peut aller jusqu'à 72, mais il faut alors
; veiller à ne pas traverser une frontière de page pour viter une
; erreur 9. Le plus simple est donc de faire 1 par 1 ...

%define NB_SECT_MAX 1 

;-------------------------------------------------------------------------------
;    Chargement en mémoire du noyau de ManuX.
;
;    L'adresse à laquelle i ldoit être placé en mémoire est définie
; par la macro MANUX_KERNEL_START_ADDRESS et le nombre de secteurs qui
; le contiennent dans MANUX_NB_SECT_KERNEL.
;
;-------------------------------------------------------------------------------
chargerManuX :

        ; Récupération des informations du lecteur

	mov ah, 08h
	mov dl, 00h
	int 13h
	
        ; Chargement du noyau depuis le disque.
	; L'adresse est dans MANUX_KERNEL_START_ADDRESS. On va la convertir
        ; sous la forme es:bx 

        mov ax, MANUX_KERNEL_START_ADDRESS>>4      ; Adresse de destination 
        mov es,ax                                  ; es:bx
        mov bx, MANUX_KERNEL_START_ADDRESS & 0x0F  ; cf 3 lignes plus haut

        mov word ax, MANUX_NB_SECT_KERNEL    ; x secteurs (taille du noyau)

        mov cx, 3                       ; à partir du secteur LBA = 3
        mov dl, 0                       ; premier lecteur de disquettes

        ; On utilise une fonction qui va permettre de contourner les
        ; limites du BIOS (cf chargerSecteurs)
	
        call chargerPleinDeSecteurs
	
chargerManuXFin :
	ret

;-------------------------------------------------------------------------------
;    Utilisation du BIOS pour charger des secteurs en mémoire depuis le lecteur
; de disquettes.
;
;    On va utiliser l'interruption 13h (avec ah=02h : read sectors from drive),
; les paramètres sont
;
;    . al    : nombre de secteurs
;    . ch    : numéro de cylindre
;    . cl    : numéro de secteur
;    . dh    : tête
;    . dl    : lecteur
;    . es:bx : adresse destination
;
;    Attention, l'ensemble de secteurs ainsi chargés ne doit pas franchir une
; frontière de 64K (le BIOS utilise le DMA). 
;-------------------------------------------------------------------------------
chargerSecteurs :
        int 13h                    ; C'est tout !
        jc reInitDisquette         ; En cas de soucis
        ret

        ; Réinitialisation du lecteur de disquette (en cas de pb)

reInitDisquette :
        mov dl, 0                  ; Disquette A: = 0
        mov ax, 0                  ; Initialisation = fonction 0
        int 13h
        jnc chargerSecteurs        ; Si erreur carry = 0

        ; On affiche un message et on s'arrète
	
        mov si, msgDisquetteErr
        call afficheBIOS

        ; Arret du lecteur de disquette

        mov dx, 03f2h
        in al, dx                    ; On lit l'état du contrôleur
        and al, 0fh                  ; on y met à 0 le "bit moteur"
        out dx, al                   ; et on lui renvoie ...

        ; Et on bloque le système
	
arretDisquetteFin :
        cli
        hlt
	jmp arretDisquetteFin

;-------------------------------------------------------------------------------
;    Chargement de plus de 256 secteurs depuis le lecteur de
; disquette. On va utiliser chargerSecteurs.
;
;    Les paramètres sont les suivants
;
;    . ax    : nombre de secteurs à lire
;    . cx    : numéro (LBA) du premier secteur à lire
;    . dl    : lecteur
;    . es:bx : adresse destination
;-------------------------------------------------------------------------------
chargerPleinDeSecteurs :

        ; On stocke les paramètres
        mov word [nbTotalSecteurs], ax    ; Le nombre de secteurs à charger
        mov [numLBAProchainSec], cx       ; Le numéro du premier secteur
	mov [numLecteur], dl              ; Le numéro du lecteur
	
cpsProchaineLecture :
        ; On calcule le nombre de secteurs à lire lors du prochain
	; appel à chargerSecteurs, sachant qu'on est limité par la
	; valeur de NB_SECT_MAX.
        ; Si il reste moins de NB_SECT_MAX secteurs à lire, c'est donc
	; la dernière lecture ...
	
	cmp word [nbTotalSecteurs], NB_SECT_MAX
        jbe cpsDerniereLecture

        ; ... sinon on se limite à NB_SECT_MAX
	
        mov byte [nbSecteurs], NB_SECT_MAX
	jmp cpsUneLecture
		
cpsDerniereLecture :
        mov word ax, [nbTotalSecteurs]
        mov byte [nbSecteurs], al

        ; Il y a donc maintenant dans nbSecteurs le nombre de secteurs
	; que l'on s'apprete à lire

cpsUneLecture :
        ; On affiche un # en prenant garde à bx et es

	push bx
	push es
	
        mov si, msgChargementSec
        call afficheBIOS

        pop es
        pop bx


LBAversCHS :	
        ; On calcule les paramètres à fournir au BIOS pour la lecture
	; et on les place dans des variables plutôt que jongler avec
	; les registres ;-)

        mov         AX, [numLBAProchainSec]
        xor         DX, DX
        mov         CX, 18
        div         CX
        inc         DX
        mov         [numSecteur], DL
        xor         DX, DX
        mov         CX, 2
        div         CX
        mov         [numCylindre], AL
        mov         [numTete], DL

        ; On récupère les paramètres et on appelle chargerSecteurs
	
	mov al, [nbSecteurs]
	mov ah, 2               ; Lecture
	mov ch, [numCylindre]
	mov cl, [numSecteur]
	mov dh, [numTete]
	mov dl, [numLecteur]
	
        call chargerSecteurs

        ; On avance la position absolue du prochain secteur en y
	; ajoutant le nombre de secteurs effectivement lus, renvoyé
	; dans al

        mov ah, 0
	add ax, [numLBAProchainSec]
	mov [numLBAProchainSec], ax

        ; On avance le pointeur es:bx

        xor ah, ah
	mov al, [nbSecteurs];
	mov cx, 0x0200   ; Taille d'un secteur
	mul cx
	add bx, ax
	jnc cpsSuite
        mov ax, es
	add word ax, 0x1000
        mov es, ax
	
cpsSuite:
        ; On a lu nbSecteurs donc on le décompte du nombre total
	; pour la suite.

	xor ah, ah
	mov al, [nbSecteurs]
        sub word [nbTotalSecteurs], ax

        ; S'il en reste à lire, on recommence
	
        cmp word [nbTotalSecteurs], 0
	ja cpsProchaineLecture

cpsFin :
        ; On affiche un message de fin et on termine
	
        push bx
	push es
	
        mov si, msgChargementFin
        call afficheBIOS

        pop es
        pop bx

        ret
	
; Le nombre total de secteurs à lire
nbTotalSecteurs   dw 0

; Le numéro absolu du prochain secteur
numLBAProchainSec dw 0

; Les paramètres de chargerSecteurs
nbSecteurs        db 0
numSecteur        db 0
numCylindre       db 0
numLecteur        db 0
numTete           db 0

