; Définition de la GDT utilisée pour le démarrage. Elle sera remplacée
; par une GDT créée dans ManuX lors du boot du noyau.
;
; (Voir par exemple [1] p 3-11, [2] )
;----------------------------------------------------------------------
DebutGDT :
   SegCodeNul :        ; Un descripteur de segment nul obligatoire
        dw 0
        dw 0
        db 0
        db 0
        db 0
        db 0

   SegCode32 :         ; Descripteur pour le segment de code 32 bits
        dw 0ffffh        ; Segment limit 15:00  (4 GB)
        dw 00000h        ; Segment base address 15:00
        db 00            ; Segment base address 23:16
        db 09ah          ; P=1 (present) DPL=0 (privilège) S=1 Type=Code Read/Exec
        db 0cfh          ; Segment limit 19:16 AVL=0 D/B=1 G=1 (4GB)
        db 0             ; Segment base address 31:24

   SegData32 :         ; Descripteur pour le segment de données 32 bits
        dw 0ffffh        ; Segment limit 15:00  (4 GB)
        dw 00000h        ; Segment base address 15:00
        db 00            ; Segment base address 23:16
        db 092h          ; P=1 (present) DPL=0 (privilège) S=1 Type=Data r/w
        db 0cfh          ; Segment limit 19:16 AVL=0 D/B=1 G=1 (4GB)
        db 0             ; Segment base address 31:24

   SegStack32 :         ; Descripteur pour le segment de pile 32 bits
        dw 0ffffh        ; Segment limit 15:00  (4 GB)
        dw 00000h        ; Segment base address 15:00
        db 00            ; Segment base address 23:16
        db 092h          ; P=1 (present) DPL=0 (privilège) S=1 Type=Data r/w
        db 0cfh          ; Segment limit 19:16 AVL=0 D/B=1 G=1 (4GB)
        db 0             ; Segment base address 31:24
FinGDT:

;------------------------------------------------------------------------------
; La description de la LDT à charger
;------------------------------------------------------------------------------
LaGDT :
        dw FinGDT - SegCodeNul - 1  ; Taille de notre GDT
        dd DebutGDT                 ; Son Adresse

;------------------------------------------------------------------------------
; Calcul des indices des différents descripteurs
;------------------------------------------------------------------------------
IndSegCode32  equ SegCode32 - SegCodeNul
IndSegData32  equ SegData32 - SegCodeNul
IndSegStack32 equ SegStack32 - SegCodeNul
