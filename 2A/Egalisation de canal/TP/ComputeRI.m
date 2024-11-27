function [ RI ] = ComputeRI( N, r, p, k )
%Compute a approximation of an infinite impulse response of length 2*N-1.
%Only the causal number of taps is required.

[~,test]=unique(r);
if length(test) < length(r)
display('High order roots')
end

RI=zeros(1,N);
%Causal terms
index=find(abs(p)<1);
if length(index>0)
RI=sum(diag(r(index))*repmat(p(index), [1 N]).^repmat((0:N-1), [length(r(index)) 1]), 1);
end
%direct termes
if length(k)>0
RI(1:length(k))=RI(1:length(k))+k;
end
%Non Causal terms
index=find(abs(p)>1);
if length(index)>0
RIneg=sum(diag(r(index))*(- (repmat(p(index), [1 N-1]).^repmat((-N+1:-1), [length(r(index)) 1]))),1);
else
RIneg=zeros(1,N-1);    
end
RI=[RIneg,RI];

end

