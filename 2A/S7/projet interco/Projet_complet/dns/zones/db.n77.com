$TTL    604800
@       IN      SOA     ns.n77.com. admin.n77.com. (
                       2         ; Serial
                       604800    ; Refresh
                       86400     ; Retry
                       2419200   ; Expire
                       604800 )  ; Negative Cache TTL
;
@       IN      NS      ns.n77.com.
ns      IN      A       120.0.30.11
web     IN      A       120.0.30.10
