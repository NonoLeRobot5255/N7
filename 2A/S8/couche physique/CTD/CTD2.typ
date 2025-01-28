= Fédération des Danseurs Danois

== Rédaction d'un document d'aide à la décision entre FDD et TDD

#table(columns: 3,
[],[TDD],[FDD],
[latence],[plus de latence(besoin de synchroniseur avec horloge atomique qui coute très chère)],[si en simultanée ],
[Géographique],[petites zones(villes). Si émission et récéption éloigné on augmente les périodes de garde],[grandes zones(rural)],
[paramétrage],[un seul paramétrage (plus simple)],[plusieurs pour FDD (plus complexe)],
[type de transmission],[transmission discontinu -> dégrade performance de l'amplificateur en puissance ],[en continue -> pas de dégradation de l'amplificateur],
[Comunication en chine ],[TDD ++ car TD-SCDMA très compatible],[moins FDD car pas de compatibilité avec TD-SCDMA],
[ressources spectrales], [si moins de ressources on utilise TDD],[si plus de ressources on utilise FDD],
[cas d'utilisation], [TDD si inégalité entre up et down (ex : streaming)],[FDD si égalité entre up et down(ex : voix)],
[coût],[pas de duplexeur mais coût pour la synchro et maintenace de l'amplificateur],[plus chère car il faut deux modules RF (pour l'émition et la récéption), un duplexeur],
)
