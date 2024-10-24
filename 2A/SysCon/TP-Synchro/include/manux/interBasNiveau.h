/*----------------------------------------------------------------------------*/
/*      Définition des fonctions de bas-niveau permettant de manipuler les    */
/*   interruptions.                                                           */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#ifndef INTER_BAS_NIVEAU_DEF
#define INTER_BAS_NIVEAU_DEF

void stubHandlerNop();
/*
 * Un handler de bas niveau qui ne fait rien
 */

/**
 * Les gestionnaires bas niveau des exceptions
 */
void stubHandlerExDiv0();
void stubHandlerExDebug();
void stubHandlerExNMI();
void stubHandlerExBreakpoint();
void stubHandlerExOverflow();
void stubHandlerExBoundExceeded();
void stubHandlerExDeviceInvalidOpcode();
void stubHandlerExDeviceUnavailable();
void stubHandlerExDoubleFault();
void stubHandlerExCoproOverrun();
void stubHandlerExInvalidTSS();
void stubHandlerExSegmentNotPresent();
void stubHandlerExStackSegmentFault();
void stubHandlerExGeneralProtectionFault();
void stubHandlerExPageFault();
void stubHandlerExReserved();
void stubHandlerExFloatingPoint();
void stubHandlerExAlignmentCheck();
void stubHandlerExFloatingMachineCheck();
void stubHandlerExFloatingSIMDFPE();
void stubHandlerExFloatingVirtualization();
void stubHandlerExControlProtection();
void stubHandlerExReserved2();
void stubHandlerExReserved3();
void stubHandlerExReserved4();
void stubHandlerExReserved5();
void stubHandlerExReserved6();
void stubHandlerExReserved7();
void stubHandlerExHypervisionInjection();
void stubHandlerExVMMCommunication();
void stubHandlerExSecurity();
void stubHandlerExReserved8();


/**
 * Les gestionnaires bas niveau des IRQ
 */
void stubHandlerIRQ0();
void stubHandlerIRQ1();
void stubHandlerIRQ2();
void stubHandlerIRQ3();
void stubHandlerIRQ4();
void stubHandlerIRQ5();
void stubHandlerIRQ6();
void stubHandlerIRQ7();
void stubHandlerIRQ8();
void stubHandlerIRQ9();
void stubHandlerIRQ10();
void stubHandlerIRQ11();
void stubHandlerIRQ12();
void stubHandlerIRQ13();
void stubHandlerIRQ14();
void stubHandlerIRQ15();

void stubHandlerInt66();

void initialiserHandlersInterruption(void * table, uint32_t taille);
#endif
