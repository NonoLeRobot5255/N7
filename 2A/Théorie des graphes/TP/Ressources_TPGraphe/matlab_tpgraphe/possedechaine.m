function T = possedechaine(G,chaine)
T = true;
k = length(chaine);

for i=1:k-1
    if G(chaine(i),chaine(i+1))~=1
        T = false;
        break;
    end
end
end

