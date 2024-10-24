% Fonction RANSAC_2droites (exercice_2.m)

function [rho_F_estime,theta_F_estime] = RANSAC_2droites(rho,theta,parametres)

    % Parametres de l'algorithme RANSAC :
    S_ecart = parametres(1); % seuil pour l'ecart
    S_prop = parametres(2); % seuil pour la proportion
    k_max = parametres(3); % nombre d'iterations
    n_donnees = length(rho);
    ecart_moyen_min = Inf;

    for i=1:k_max

        indices = randperm(length(rho),2);
        [rho_F1,theta_F1,~] = estim_param_F(rho(indices),theta(indices));
        n = sum( abs ( rho-rho_F1 * cos ( theta - theta_F1 )) <= S_ecart)/n_donnees;

        if n >=S_prop
            indices_new = abs ( rho-rho_F1 * cos ( theta - theta_F1 )) <= S_ecart;
            [rho_F2,theta_F2,ecart_moyen] = estim_param_F(rho(indices_new),theta(indices_new));

            if ecart_moyen < ecart_moyen_min
                rho_F_estime = rho_F2;
                theta_F_estime = theta_F2;
                
            end
        end

    end

end