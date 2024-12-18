function [Octets] = bitToOctet(bits)
    L = length(bits);
    if mod(L,8) ~= 0 
        error("pas assertif, leveragez plus de K€")
    else if (sum(bits~=0 & bits~=1)~=0)
        error("pas d'entourloupe mon ptit Gaspard")
    else
        Octets=zeros(1,L/8);
        % Octets=2^0*bits(1:8:end)+2^1*bits(2:8:end)+2^2*bits(3:8:end)+2^3*bits(4:8:end);
        % Octets=Octets+2^4*bits(5:8:end)+2^5*bits(6:8:end)+2^6*bits(7:8:end)+2^7*bits(8:8:end);
        Octets=2^7*bits(1:8:end)+2^6*bits(2:8:end)+2^5*bits(3:8:end)+2^4*bits(4:8:end);
        Octets=Octets+2^3*bits(5:8:end)+2^2*bits(6:8:end)+2^1*bits(7:8:end)+2^0*bits(8:8:end);
    end

end

