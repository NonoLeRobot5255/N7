TD2 = début du projet

+ il décrit un process composé d'éléments (process element) a un travail (workdefinition) et une séquence de travail    (workspace)
+ Vision tabulaire : 
    
    eClass
    #table(columns: 5,
    [ID],[nom],[esupertype],[eAttributs],[eReference],
    [C1],[Process],[/],[A1],[R1],
    [C2],[ProcessElement],[/],[/],[/],
    [C3],[workdefinition],[C2],[A3],[R2,R4],
    [C4],[workspace],[C2],[A4],[R3,R5]
    )
    eAttributs
    #table(columns: 5,
    [ID],[name],[lowerBound],[upperBound],[eAttributeType],
    [A1],[name],[1],[1],[D1],
    [A2],[name],[1],[1],[D1],
    [A3],[linkType],[1],[1],[E1]
    )
    eReference    
    #table(columns: 5, 
    [ID],[name],
    )
*Plus de batterie, je finirais après*