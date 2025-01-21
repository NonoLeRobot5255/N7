FROM ubuntu

ENV IP_ADDRESS=10.0.1.1
ENV NET_MASK=24

RUN apt-get update && apt-get install -y iproute2

CMD ["ip", "link", "set", "lo up"]
