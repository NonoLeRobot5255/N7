function [W, V, flag, q, qv] = eigen_2023(imat, n, v, m, eps, maxit, percentage, p, genere)

%%%%%%%%%%%%
% RÉSULTATS
%%%%%%%%%%%%

% W les valeurs propres
% V les vecteurs propres
% flag == 0, le calcul des couples propres a réussi
% q qualité des valeurs propres (par rapport au spectre de la matrice)
% qv qualité des valeurs propres (critère de convergence)

%%%%%%%%%%%%
% PARAMÈTRES
%%%%%%%%%%%%

% n, taille de la matrice symétrique

% imat, type de la matrice (voir matgen_csad)
% imat == 1 valeurs propres D(i) = i
% imat == 2 valeurs propres D(i) = random(1/cond, 1) avec leur logarithmes
%                                  uniformément répartie, cond = 1e10
% imat == 3 valeurs propres D(i) = cond**(-(i-1)/(n-1)) avec cond = 1e5
% imat == 4 valeurs propres D(i) = 1 - ((i-1)/(n-1))*(1 - 1/cond) avec cond = 1e2

% v, méthode de calcul des couples propres
% v == 10, méthode eig de matlab
% v == 11, méthode de la puissance itérée avec déflation
% v == 12, méthode de la puissance itérée avec déflation améliorée (à écrire)
% v == 0, méthode subspace iteration v0 (à compléter pendant la séance)
% v == 1, méthode subspace iteration v1 (fournie)
% v == 2, méthode subspace iteration v2 (à développer)
% v == 3, méthode subspace iteration v3 (à développer)

% m, nombre de valeurs propres cherchées (v0)
% ou taille du sous-espace (V1, v2, v3)

% percentage, pourcentage de la trace que l'on veut atteindre (v1, v2, v3)

% p, puissance de A que l'on applique à chaque itération (v2, v3)

% genere, contruction ou non de la matrice
% genere == 1, on génère et on sauve la matrice et le vecteur des valeurs
%              propres
% genere == 0, on lit la matrice et le vecteur des valeurs propres 
%              dans un fichier

% paramètres pour les méthodes itératives
% eps, tolérance
% maxit, nombre d'itérations max pour atteindre la convergence

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% si on veut que d'une expérience à l'autre la graine de l'aléatoire soit la même
rng('default');

fprintf('\nMatrice %d x %d - type %d\n', n, n, imat);

if(genere == 1)
    % Génération d'une matrice rectangulaire aléatoire symétrique définie
    % positive A de taille (n x n)
    
    % A matrice
    % D ses valeurs propres
    fprintf('\n******* création de la matrice ******\n');
    t_v =  cputime;
    [A, D, ~] = matgen_csad(imat,n);
    t_v = cputime-t_v;
    fprintf('\nTemps de création de la matrice = %0.3e\n',t_v)
    save(['A_' num2str(n) '_' num2str(imat)], 'A', 'D', 'imat', 'n');
    
else
    load(['A_' num2str(n) '_' num2str(imat)]);
end

switch v
    case 10
        fprintf('\n******* calcul avec eig ******\n');
        % appel à eig de matlab : calcul de toutes les valeurs propres
        t_v =  cputime;
        % WA valeurs propres
        % VA vecteurs propres
        [VA, DA] = eig(A);
        t_v = cputime-t_v;
        
        [WA, indices] = sort(diag(DA), 'descend');
        VA = VA(:, indices);
        
        fprintf('\nTemps eig = %0.3e\n',t_v);
        [qA, qvA] = verification_qualite(A, D, WA, VA, n);
        %fprintf('Qualité des valeurs propres (par rapport au spectre de la matrice) = [%0.3e , %0.3e] \n', min(qA), max(qA));
        %fprintf('Qualité des couples propres = [%0.3e , %0.3e]\n', min(qvA), max(qvA));
        
        % Sauvegarde de quelques résultats
        %save("eig", 'VA', 'WA', 'qA', 'qvA');
        
        W = WA;
        V = VA;
        q = qA;
        qv = qvA;
        flag = 0;
        
    case 11
        fprintf('\n******* calcul avec la méthode de la puissance itérée ******\n');
        t_v =  cputime;

        % VB vecteurs propres
        [ VB, DB, n_evB, itvB, flagB ] = power_v11( A, m, percentage, eps, maxit );
        t_v = cputime-t_v;

        % WB valeurs propres
        WB = diag(DB);
        
        if(flagB == 0)

            fprintf('\nTemps puissance itérée = %0.3e\n',t_v);  
            fprintf('Nombre de valeurs propres pour attendre le pourcentage = %d\n', n_evB);
            %fprintf('Nombre d''itérations pour chaque couple propre\n');
            %for i=1:n_evB
            %    fprintf('couple %d : %d\n', i, itvB(i));
            %end
            
            [qB, qvB] = verification_qualite(A, D, WB, VB, n_evB);
            %fprintf('Qualité des valeurs propres (par rapport au spectre de la matrice) = [%0.3e , %0.3e] \n', min(qB), max(qB));
            %fprintf('Qualité des couples propres = [%0.3e , %0.3e]\n', min(qvB), max(qvB));
            
            % Sauvegarde de quelques résultats
            %save("power", 'VB', 'WB', 'qB', 'qvB');
                       
            W = WB;
            V = VB;
            q = qB;
            qv = qvB;

        else
            if(flagB == 1)
                fprintf('puissance itérée : pourcentage %0.3e non atteint avec %d valeurs propres\n', percentage, m);
            else
                fprintf('puissance_itérée : convergence non atteinte pour un des couples propres\n')
            end
            
            W = 0;
            V = 0;
            q = 0;
            qv = 0;
        end
        
        flag = flagB;
        
      case 12
        fprintf('\n******* calcul avec la méthode de la puissance itérée améliorée ******\n');
        t_v =  cputime;

        % VB vecteurs propres
        [ VB, DB, n_evB, itvB, flagB ] = power_v12( A, m, percentage, eps, maxit );
        t_v = cputime-t_v;
 
        % WB valeurs propres
        WB = diag(DB);

        if(flagB == 0)

            fprintf('\nTemps puissance itérée = %0.3e\n',t_v);            
            fprintf('Nombre de valeurs propres pour attendre le pourcentage = %d\n', n_evB);
            %fprintf('Nombre d''itérations pour chaque couple propre\n');
            %for i=1:n_evB
            %    fprintf('couple %d : %d\n', i, itvB(i));
            %end
            
            [qB, qvB] = verification_qualite(A, D, WB, VB, n_evB);
            %fprintf('Qualité des valeurs propres (par rapport au spectre de la matrice) = [%0.3e , %0.3e] \n', min(qB), max(qB));
            %fprintf('Qualité des couples propres = [%0.3e , %0.3e]\n', min(qvB), max(qvB));
            
            % Sauvegarde de quelques résultats
            %save("power", 'VB', 'WB', 'qB', 'qvB');
                       
            W = WB;
            V = VB;
            q = qB;
            qv = qvB;

        else
            if(flagB == 1)
                fprintf('puissance itérée : pourcentage %0.3e non atteint avec %d valeurs propres\n', percentage, m);
            else
                fprintf('puissance_itérée : convergence non atteinte pour un des couples propres\n')
            end
            
            W = 0;
            V = 0;
            q = 0;
            qv = 0;

        end
        
        flag = flagB;

    case 0
        fprintf('\n******* calcul avec subspace iteration v0 ******\n');
        % appel à la version 0 de la subspace iteration method
        t_v0 =  cputime;
        % W0 valeurs propres
        % V0 vecteurs propres
        [V0, D0, it0, flag0] = subspace_iter_v0(A, m, eps, maxit);
        t_v0 = cputime-t_v0;
        
        W0 = diag(D0);
        
        if(flag0 == 0)
            
            fprintf('\nTemps subspace iteration v0 = %0.3e\n',t_v0);
            fprintf('Nombre d''itérations : %d\n', it0);
            
            [q0, qv0] = verification_qualite(A, D, W0, V0, m);
            %fprintf('Qualité des valeurs propres (par rapport au spectre de la matrice) = [%0.3e , %0.3e] \n', min(q0), max(q0));
            %fprintf('Qualité des couples propres = [%0.3e , %0.3e]\n', min(qv0), max(qv0));
           
            % Sauvegarde de quelques résultats
            %save("iter_v0", 'V0', 'W0', 'q0', 'qv0');
            
            W = W0;
            V = V0;
            q = q0;
            qv = qv0;

        else
            fprintf('subspace iteration v0 : convergence non atteinte : %d\n', it0);
            W = 0;
            V = 0;
            q = 0;
            qv = 0;
        end
        
        flag = flag0;
        
    case 1
        fprintf('\n******* calcul avec subspace iteration v1 ******\n');        
        % appel à la version 1 de la subspace iteration method
        
        t_v1 =  cputime;
        % W1 valeurs propres
        % V1 vecteurs propres
        [ V1, D1, n_ev1, it1, itv1, flag1 ] = subspace_iter_v1( A, m, percentage, eps, maxit );
        t_v1 = cputime-t_v1;
        
        W1 = diag(D1);

        if(flag1 == 0)

            fprintf('\nTemps subspace iteration v1 = %0.3e\n',t_v1);
            fprintf('Nombre d''itérations : %d\n', it1);            
            fprintf('Nombre de valeurs propres pour attendre le pourcentage = %d\n', n_ev1);
            %fprintf('Nombre d''itérations pour chaque couple propre\n');
            %for i=1:n_ev1
            %    fprintf('couple %d : %d\n', i, itv1(i));
            %end
            
            [q1, qv1] = verification_qualite(A, D, W1, V1, n_ev1);
            %fprintf('Qualité des valeurs propres (par rapport au spectre de la matrice) = [%0.3e , %0.3e] \n', min(q1), max(q1));
            %fprintf('Qualité des couples propres = [%0.3e , %0.3e]\n', min(qv1), max(qv1));
            
            % Sauvegarde de quelques résultats
            %save("iter_v1", 'V1', 'W1', 'q1', 'qv1');
            
            W = W1;
            V = V1;
            q =q1;
            qv = qv1;

        else
            if(flag1 == 1)
                fprintf('subspace iteration v1 : pourcentage %0.3e non atteint avec %d valeurs propres\n', percentage, m);
            else
                fprintf('subspace iteration v1 : convergence non atteinte: %d\n', it1)
            end
            
            W = 0;
            V = 0;
            q = 0;
            qv = 0;
        end
        
        flag = flag1;
        
      case 2
        fprintf('\n******* calcul avec subspace iteration v2 ******\n');
        % appel à la version 2 de la subspace iteration method
        
        t_v2 =  cputime;
        % W2 valeurs propres
        % V2 vecteurs propres
        [ V2, D2, n_ev2, it2, itv2, flag2 ] = subspace_iter_v2( A, m, percentage, p, eps, maxit );
        t_v2 = cputime-t_v2;

        W2 = diag(D2);
        
        if(flag2 == 0)
            
            
            fprintf('\nTemps subspace iteration v2 = %0.3e\n',t_v2);
            fprintf('Nombre d''itérations : %d\n', it2);
            fprintf('Nombre de valeurs propres pour attendre le pourcentage = %d\n', n_ev2);
%             fprintf('Nombre d''itérations pour chaque couple propre\n');
%             for i=1:n_ev2
%                fprintf('couple %d : %d\n', i, itv2(i));
%             end

            [q2, qv2] = verification_qualite(A, D, W2, V2, n_ev2);
            %fprintf('Qualité des valeurs propres (par rapport au spectre de la matrice) = [%0.3e , %0.3e] \n', min(q2), max(q2));
            %fprintf('Qualité des couples propres = [%0.3e , %0.3e]\n', min(qv2), max(qv2));
            
            % Sauvegarde de quelques résultats
            %save("iter_v2", 'V2', 'W2', 'q2', 'qv2');
            
            W = W2;
            V = V2;
            q = q2;
            qv = qv2;
            
        else
            if(flag2 == 1)
                fprintf('subspace iteration v2 : pourcentage %0.3e non atteint avec %d valeurs propres\n', percentage, m);
            else
                fprintf('subspace iteration v2 : convergence non atteinte: %d\n', it2)
            end
            
            W = 0;
            V = 0;
            q = 0;
            qv = 0;

        end
        
        flag = flag2;

      case 3
        fprintf('\n******* calcul avec subspace iteration v3 ******\n');
        % appel à la version 3 de la subspace iteration method
        
        t_v3 =  cputime;
        % W3 valeurs propres
        % V3 vecteurs propres
        [ V3, D3, n_ev3, it3, itv3, flag3 ] = subspace_iter_v3( A, m, percentage, p, eps, maxit );
        t_v3 = cputime-t_v3;
        
        W3 = diag(D3);

        if(flag3 == 0)
            
            fprintf('\nTemps subspace iteration v3 = %0.3e\n',t_v3);
            fprintf('Nombre d''itérations : %d\n', it3);
            fprintf('Nombre de valeurs propres pour attendre le pourcentage = %d\n', n_ev3);
            %fprintf('Nombre d''itérations pour chaque couple propre\n');
            %for i=1:n_ev3
            %    fprintf('couple %d : %d\n', i, itv3(i));
            %end

            [q3, qv3] = verification_qualite(A, D, W3, V3, n_ev3);
            %fprintf('Qualité des valeurs propres (par rapport au spectre de la matrice) = [%0.3e , %0.3e] \n', min(q3), max(q3));
            %fprintf('Qualité des couples propres = [%0.3e , %0.3e]\n', min(qv3), max(qv3));
            
            % Sauvegarde de quelques résultats
            %save("iter_v3", 'V3', 'W3', 'q3', 'qv3');
            
            W = W3;
            V = V3;
            q = q3;
            qv = qv3;
            
        else
            if(flag3 == 1)
                fprintf('subspace iteration v3 : pourcentage %0.3e non atteint avec %d valeurs propres\n', percentage, m);
            else
                fprintf('subspace iteration v3 : convergence non atteinte: %d\n', it3)
            end
            
            W = 0;
            V = 0;
            q = 0;
            qv = 0;
            
        end
        
        flag = flag3;
        
    otherwise
        fprintf('\n il n''existe pas (encore) de méthode avec ce numéro\n');
        
end

end
