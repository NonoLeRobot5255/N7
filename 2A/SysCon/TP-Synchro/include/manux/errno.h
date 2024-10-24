/*----------------------------------------------------------------------------*/
/*      Définition des numéros d'erreur de Manux. On va essayer de garder les */
/*   même numéro que Linux.                                                   */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#ifndef ERRNO_H
#define ERRNO_H

#define ESUCCES          0      /* Succés, donc "non erreur */
#define EBADF            9
#define ENOENT           2      /* Fichier ou répertoire inexistant  */
#define ENOMEM          12      /* Plus de mémoire          */
#define EINVAL          22      /* Argument non valide      */
#define EPASDEF          1      /* Pas de fichier ouvert */
#endif
