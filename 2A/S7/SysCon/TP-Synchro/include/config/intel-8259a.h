/**
 * On utilise ici des intel 8259a
 */
#define MANUX_HANDLER_IRQ i8259aGestionIRQ

/**
 * Combien de handlers peut-on greffer sur une interruption ?
 */
#ifndef MANUX_NB_HANDLER_PAR_IRQ
#   define MANUX_NB_HANDLER_PAR_IRQ 4
#endif

/**
 * Le nombre d'IRQ gérées. On a deux circuits et donc 16 IRQ potentielles
 */
#define I8259A_NB_IRQ 16

#ifndef MANUX_NB_IRQ
#   define MANUX_NB_IRQ 16 //I8259A_NB_IRQ
#endif

/**
 * La fonction d'initalisation
 */
#ifndef MANUX_PIC_INIT
#   define MANUX_PIC_INIT i8259aInit
#endif
