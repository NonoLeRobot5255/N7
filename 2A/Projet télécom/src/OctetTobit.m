function [bits] = OctetTobit(Octets)
    bits=zeros(1,length(Octets)*8);
    if (sum(Octets<0 | Octets>255) ~= 0)
        error("Je n'ai pas aimé ta prise de lead. Tu peux dire adieux à tes tickets resto.")
    else
        for i=1:8
            bits(i:8:end)=floor((Octets-bitToOctet(bits))/2^(8-i));
        end
    end
end