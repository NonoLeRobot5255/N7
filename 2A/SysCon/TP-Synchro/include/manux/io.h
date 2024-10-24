/*----------------------------------------------------------------------------*/
/*       Manipulation des entrées/sorties.                                    */
/*                                                  (C) Manu Chaput 2000-2022 */
/*----------------------------------------------------------------------------*/
#ifndef IO_DEF
#define IO_DEF

// WARNING les "Nd" étaient des "N", ...

/**
 * @brief Emission d'un octet sur un port
 */
#define outb(port, octet) \
   asm ("outb %%al, %1":: "a"(octet), "Nd"(port))

/**
 * @brief Lecture d'un octet depuis un port
 */
#define inb(port, adresseOctet) \
   asm ("inb %1, %%al": "=a"(adresseOctet): "Nd"(port))

/**
 * @brief Emission d'un mot sur un port
 */
#define outw(port, mot) \
   asm ("outw %%ax, %1":: "a"(mot), "Nd"(port))

/**
 * @brief Lecture d'un mot depuis un port
 */
#define inw(port, adresseMot) \
   asm ("inw %1, %%ax": "=a"(adresseMot): "Nd"(port))

/**
 * @brief Emission d'un long sur un port
 */
#define outl(port, lng) \
   asm ("outl %%eax, %1":: "a"(lng), "Nd"(port))

/**
 * @brief Lecture d'un long depuis un port
 */
#define inl(port, adresseLong) \
   asm ("inl %1, %%eax": "=a"(adresseLong): "Nd"(port))

#endif
