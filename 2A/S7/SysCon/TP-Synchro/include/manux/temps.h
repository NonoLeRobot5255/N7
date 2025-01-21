/*----------------------------------------------------------------------------*/
/*      Implantation des sous-programmes de manipulation des dates et durées. */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#include <manux/config.h>   // MANUX_FREQUENCE_HORLOGE
#include <manux/types.h>    // Temps

/*
 * Conversion d'une date/durée exprimée en nombre de top horloges vers
 * une structure ValTemps. 
 */
int nbTopVersValTemps(Temps nbTop, ValTemps * vt);

#define totalSecondesDansTemps(t) (t / MANUX_FREQUENCE_HORLOGE)

#define totalMinutesDansTemps(t) (totalSecondesDansTemps(t)/60)

#define secondesDansTemps(t) (totalSecondesDansTemps(t) - 60*(totalMinutesDansTemps(t)))
