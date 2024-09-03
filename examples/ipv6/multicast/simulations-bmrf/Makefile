DEFINES+=PROJECT_CONF_H=\"project-conf.h\"
UIP_CONF_IPV6=1
APPS=servreg-hack

CONTIKI_PROJECT = root intermediate sink internal-seed unicast-sender unicast-receiver
all: $(CONTIKI_PROJECT)

CONTIKI = ../../../..

MODULES += core/net/ipv6/multicast

include $(CONTIKI)/Makefile.include
