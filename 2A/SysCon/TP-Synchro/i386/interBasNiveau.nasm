;===============================================================================
;      Définition des fonctions de bas niveau permettant la gestion des
;   interruptions.
;      Sauf indication contraire, les paramètres (s'il y en a) sont passés "à la
;   C", c'est à dire empilés en ordre inverse et dépilés par l'appelant.
;
;                                                      (C) Manu Chaput 2000-2023
;===============================================================================
[bits 32]

;===============================================================================
;   Gestion des exceptions
;
;   Certaines exceptions empilent un code d'erreur (32 bits), d'autres
; non. Nous allons les traiter en passant par une fonction commune,
;   écrite en C et nommée "handlerException". C'est elle qui
;   aiguillera ensuite vers la fonction de traitement spéfifique à
;   chaque exception.
; Il est donc nécessaire de définir deux types de handler "bas niveau".
; Un handler associé à une exception avec un code d'erreurs va empiler
;   le numéro de l'exception (qui servira à handlerException pour
;   réaliser l'aiguillage). Un handler associé à une exception sans
;   code d'erreur
;   
;===============================================================================

extern gestionException    ; La fonction générale de gestion

%macro stubHandlerException 1
       push dword 0x0           ; On empile un "code"
       push dword %1            ; On empile le numéro de l'exception
       jmp versHandlerException ; On invoque la fonction d'aiguillage
%endmacro
%macro stubHandlerExceptionCode 1
       push dword %1            ; On empile le numéro de l'exception
       jmp versHandlerException ; On invoque la fonction d'aiguillage
%endmacro

versHandlerException :
       pushad                   ; sauvegarde des registres
       call gestionException    ; appel de la fonction d'aiguillage
       popad                    ; restauration des registres
       add esp, 0x08            ; on "dépile" le code et le numéro
       iret

; Et maintenant on définit tous les handlers d'exception
;-------------------------------------------------------
global stubHandlerExDiv0
stubHandlerExDiv0 :                ; Exception "division par zéro"
       stubHandlerException 0x00

global stubHandlerExDebug
stubHandlerExDebug :               ; Exception "debug"
       stubHandlerException 0x01
       
global stubHandlerExNMI
stubHandlerExNMI :                 ; Exception "non maskable interrupt"
       stubHandlerException 0x02
       
global stubHandlerExBreakpoint
stubHandlerExBreakpoint:           ;
       stubHandlerException 0x03
       
global stubHandlerExOverflow
stubHandlerExOverflow :            ; Exception "Overflow"
       stubHandlerException 0x04

global stubHandlerExBoundExceeded
stubHandlerExBoundExceeded :       ;
       stubHandlerException 0x05

global stubHandlerExDeviceInvalidOpcode
stubHandlerExDeviceInvalidOpcode : ; Exception "invalid opcode"
       stubHandlerException 0x06
              
global stubHandlerExDeviceUnavailable
stubHandlerExDeviceUnavailable :   ; Exception "device unavailable"
       stubHandlerException 0x07

global stubHandlerExDoubleFault
stubHandlerExDoubleFault :
       stubHandlerExceptionCode 0x08

global stubHandlerExCoproOverrun
stubHandlerExCoproOverrun :        ; Exception "Coprocessor Segment Overrun"
       stubHandlerException 0x09

global stubHandlerExInvalidTSS
stubHandlerExInvalidTSS :
       stubHandlerExceptionCode 0x0a

global stubHandlerExSegmentNotPresent
stubHandlerExSegmentNotPresent :
       stubHandlerExceptionCode 0x0b

global stubHandlerExStackSegmentFault
stubHandlerExStackSegmentFault :
       stubHandlerExceptionCode 0x0c

global stubHandlerExGeneralProtectionFault
stubHandlerExGeneralProtectionFault :
       stubHandlerExceptionCode 0x0d

global stubHandlerExPageFault
stubHandlerExPageFault :
       stubHandlerExceptionCode 0x0e

global stubHandlerExReserved
stubHandlerExReserved :
       stubHandlerException 0x0f

global stubHandlerExFloatingPoint
stubHandlerExFloatingPoint :
       stubHandlerException 0x10

global stubHandlerExAlignmentCheck
stubHandlerExAlignmentCheck :
       stubHandlerExceptionCode 0x11

global stubHandlerExFloatingMachineCheck
stubHandlerExFloatingMachineCheck :
       stubHandlerException 0x12

global stubHandlerExFloatingSIMDFPE
stubHandlerExFloatingSIMDFPE :
       stubHandlerException 0x13

global stubHandlerExFloatingVirtualization
stubHandlerExFloatingVirtualization :
       stubHandlerException 0x14

global stubHandlerExControlProtection
stubHandlerExControlProtection :
       stubHandlerExceptionCode 0x15

global stubHandlerExReserved2
stubHandlerExReserved2 :
       stubHandlerException 0x16

global stubHandlerExReserved3
stubHandlerExReserved3 :
       stubHandlerException 0x17

global stubHandlerExReserved4
stubHandlerExReserved4 :
       stubHandlerException 0x18

global stubHandlerExReserved5
stubHandlerExReserved5 :
       stubHandlerException 0x19

global stubHandlerExReserved6
stubHandlerExReserved6 :
       stubHandlerException 0x1a

global stubHandlerExReserved7
stubHandlerExReserved7 :
       stubHandlerException 0x1b

global stubHandlerExHypervisionInjection
stubHandlerExHypervisionInjection :
       stubHandlerException 0x1c

global stubHandlerExVMMCommunication
stubHandlerExVMMCommunication :
      stubHandlerExceptionCode 0x1d

global stubHandlerExSecurity
stubHandlerExSecurity :
      stubHandlerExceptionCode 0x1e

global stubHandlerExReserved8
stubHandlerExReserved8 :
      stubHandlerException 0x1f

;===============================================================================
;   Gestion des IRQ.
;
;   Ces IRQ sont transmises par un PIC. Nous supposerons que ce dernier gère
; un nombre d'IRQ défini dans MANUX_NB_IRQ et que la fonction de gestion
; associée est définie dans MANUX_HANDLER_IRQ.
;
;   On définit (à l'aide de la macro stubHandlerIRQn) un handler pour chacune
; des IRQ. Ce handler empile le numéro de l'IRQ (pas de l'interruption,
; qui dépend du remapping configuré sur le PIC) puis invoque le gestionnaire
; global (la fonction C dont le nom est donné par MANUX_HANDLER_IRQ).
;
;    Ces handlers ont pour nom stubHandlerIRQ1, stubHandlerIRQ2, ...
;===============================================================================

extern MANUX_HANDLER_IRQ            ; La fonction de gestion, liée au PIC

; Un handler pour l'IRQ n
;------------------------
%macro stubHandlerIRQn 1
        push dword %1               ; On empile le numéro de l'IRQ
	jmp  handlerIRQ
%endmacro

handlerIRQ :
	pusha                       ; On empile les registres 
	
        call MANUX_HANDLER_IRQ      ; On appelle la fonction d'aiguillage 

	popa                        ; On dépile les registres
        add esp, 4                  ; Dépile le numéro d'IRQ

        iret

; Génération des MANUX_NB_IRQ handlers (ce nombre est défini par le PIC)
;-----------------------------------------------------------------------
%assign i 0
%rep MANUX_NB_IRQ
global stubHandlerIRQ%[i]
stubHandlerIRQ%[i] : stubHandlerIRQn i
%assign i i+1
%endrep

;===============================================================================
;   Gestion des interruptions logicielles
;
;===============================================================================
extern  gestionInterruption 

%macro stubHandlerInt 1
        push dword %1            ; On empile le numéro de l'interruption
	jmp  handlerInt
%endmacro

handlerInt :
	pushad                   ; Sauvegarde des registres
	
        call gestionInterruption ; Invocation de la focntion d'aiguillage

	popad                    ; Restauration des registres
        add esp, 4               ; On dépile le numéro d'interruption
        iret

; On génère les gestionnaires bas niveau
;---------------------------------------

%assign i MANUX_INT_BASE_IRQ + MANUX_NB_IRQ
%rep MANUX_NB_INTERRUPTIONS - (MANUX_INT_BASE_IRQ + MANUX_NB_IRQ)
global stubHandlerInt%[i] 
stubHandlerInt%[i] : stubHandlerInt i
%assign i i+1
%endrep

;------------------------------------------------------------------------------
; La fonction suivante initialise un tableau avec les addresses des
; gestionnaires bas niveau. Son interface C est la suivante
;
; void initialiserHandlersInterruption(void * hbn, uint32_t n);
;
; Elle place dans le tableau hbn les adresses des handlers bas niveau que l'on
; vient de définir (au maximum n fonctions)
;------------------------------------------------------------------------------
%macro ajoutHandlerInt 1
        mov dword [eax], stubHandlerInt%[i]
	add eax, 4
        inc ebx
	cmp ebx, [esp + 16]
	ja IHIFin
%endmacro

global initialiserHandlersInterruption
initialiserHandlersInterruption :
        push eax
        push ebx
	mov eax, [esp + 12]
	mov ebx, 1

%assign i MANUX_INT_BASE_IRQ + MANUX_NB_IRQ 
%rep MANUX_NB_INTERRUPTIONS - (MANUX_INT_BASE_IRQ + MANUX_NB_IRQ)
        ajoutHandlerInt i
%assign i i+1
%endrep

IHIFin  pop ebx
        pop eax
        ret
	
;===============================================================================
;   Gestion des appels système
;
;   Le mécanisme des appels système est fondé sur l'utilisation d'une
; interruption logicielle. Son handler est un peu particulier : il va s'occuper
; de sauvegarder l'état du processeur et invoquer la fonction de traitement de
; l'appel système visé.
;   Deux fonctions supplémentaires d'entrée et sortie du noyau sont invoquées,
; qui pourront servir par exemple à de l'audit, à verouiller le noyau, ....
;===============================================================================
%ifdef MANUX_APPELS_SYSTEME

extern vecteurAppelsSysteme
extern entrerAppelSysteme
extern sortirAppelSysteme

global handlerAppelSysteme

; Le handler des appels systèmes
;-------------------------------
handlerAppelSysteme :
        push edi
        push esi
        push ebp
        push esp
        push ebx
        push edx
        push ecx

        ; On appelle la fonctin d'entrée en AS
        push eax
        call entrerAppelSysteme
	pop eax

        push eax      ; On empile eax pour avoir le numéro d'AS dans la pile
        shl eax, 02h  ; On multiplie par 4 our aller taper dans le tableau

        ; On autorise les IT WARNING, est-ce bien raisonable ?
        sti
	
        ; On invoque l'AS
        call [vecteurAppelsSysteme+eax] ; Le numéro est dans EAX (cf appelsysteme.h)
        push eax  ; On sauvegarde la valeur de retour

        ; On va récupérer (sans la dépiler) la valeur dans la pile et on la passe
	; à la fonction de sortie
        mov eax, [esp + 4]
        push eax
        call sortirAppelSysteme
	pop eax
	
	pop eax   ; On récupère la valeur de retour de l'AS
	
        pop ecx ; On enlève eax de la pile, mais sans altérer eax car c'est
	        ; la valeur de retour de l'appel système
        pop ecx
        pop edx
        pop ebx
        pop esp
        pop ebp
        pop esi
        pop edi
        iret
%endif   ; MANUX_APPELS_SYSTEME
