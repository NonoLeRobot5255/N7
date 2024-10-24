% Fonction ecriture_RVB

function image_RVB = ecriture_RVB(image_originale)
R=image_originale(2:2:end , 1:2:end);
B=image_originale(1:2:end , 2:2:end);
V=(image_originale(1:2:end, 1:2:end) + image_originale(2:2:end, 2:2:end))/2;

image_RVB=cat(3,R,V,B);




end