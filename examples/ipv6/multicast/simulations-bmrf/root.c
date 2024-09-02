/*
 * Copyright (c) 2010, Loughborough University - Computer Science
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 */

/**
 * \file
 *         This node is part of the RPL multicast example. It is an RPL root
 *         and sends a multicast message periodically. For the example to work,
 *         we need one of those nodes.
 *
 * \author
 *         George Oikonomou - <oikonomou@users.sourceforge.net>
 */

#include "contiki.h"
#include "contiki-lib.h"
#include "contiki-net.h"
#include "net/ipv6/multicast/uip-mcast6.h"
#include "net/ipv6/multicast/uip-mcast6-route.h"
#include "net/ipv6/uip-ds6.h"

#include <string.h>

#define DEBUG DEBUG_PRINT
#include "net/ip/uip-debug.h"
#include "net/rpl/rpl.h"

#include "simstats.h"
#include "lib/list.h"

#define MAX_PAYLOAD_LEN 120
#define MCAST_SINK_UDP_PORT 3001 /* Host byte order */

#ifdef MCAST_CONF_SEND_INTERVAL
#define SEND_INTERVAL MCAST_CONF_SEND_INTERVAL * CLOCK_SECOND /* clock ticks */
#else
#define SEND_INTERVAL CLOCK_SECOND
#endif

#if (SENDER_IS == ROOT)
#ifdef MCAST_CONF_MESSAGES
#define ITERATIONS MCAST_CONF_MESSAGES /* messages */
#endif
#else
#define ITERATIONS 0
#endif


/* Start sending messages START_DELAY secs after we start so that routing can
 * converge */
#ifdef MCAST_CONF_START_DELAY
#define START_DELAY MCAST_CONF_START_DELAY
#else
#define START_DELAY 60
#endif

static struct uip_udp_conn * mcast_conn;
static char buf[MAX_PAYLOAD_LEN];
static uint32_t seq_id;

#if !UIP_CONF_IPV6 || !UIP_CONF_ROUTER || !UIP_CONF_IPV6_MULTICAST || !UIP_CONF_IPV6_RPL
#error "This example can not work with the current contiki configuration"
#error "Check the values of: UIP_CONF_IPV6, UIP_CONF_ROUTER, UIP_CONF_IPV6_RPL"
#endif
/*---------------------------------------------------------------------------*/
PROCESS(rpl_root_process, "RPL ROOT, Multicast Sender");
AUTOSTART_PROCESSES(&rpl_root_process);
/*---------------------------------------------------------------------------*/

/*
ID:1 

Multicast Routing Table:
Group Address: ff1e::89:abcd
Lifetime: 65532 seconds
RPL DAG Pointer: 0x2c0a
Subscribed Child: 00:12:74:09:00:09:09:09
----------------------------
Group Address: ff1e::89:abcd
Lifetime: 65508 seconds
RPL DAG Pointer: 0x2c0a
Subscribed Child: 00:12:74:0d:00:0d:0d:0d
----------------------------
Group Address: ff1e::89:abcd
Lifetime: 65526 seconds
RPL DAG Pointer: 0x2c0a
Subscribed Child: 00:12:74:15:00:15:15:15
----------------------------
Group Address: ff1e::89:abcd
Lifetime: 65502 seconds
RPL DAG Pointer: 0x2c0a
Subscribed Child: 00:12:74:0f:00:0f:0f:0f
----------------------------
Group Address: ff1e::89:abcd
Lifetime: 65510 seconds
RPL DAG Pointer: 0x2c0a
Subscribed Child: 00:12:74:04:00:04:04:04
----------------------------
End of Multicast Routing Table
*/
void print_mcast6_routes() {
  uip_mcast6_route_t *route;
  uip_ipaddr_t *group_addr;
  uint32_t lifetime;
  void *dag;
#if UIP_MCAST6_CONF_ENGINE == UIP_MCAST6_ENGINE_SeRI || UIP_MCAST6_CONF_ENGINE == UIP_MCAST6_ENGINE_BMRF
  uip_lladdr_t *subscribed_child;
#endif
    // Iterate through the multicast routing list
  for (route = uip_mcast6_route_list_head(); route != NULL; route = route->next) {
    group_addr = &route->group;
    lifetime = route->lifetime;
    dag = route->dag;
    // Print multicast group address
    printf("Group Address: ");
    uip_debug_ipaddr_print(group_addr);
    printf("\n");
    // Print the route's lifetime
    printf("Lifetime: %u seconds\n", lifetime);
    // Print the RPL DAG pointer (or its details if needed)
    printf("RPL DAG Pointer: %p\n", dag);
    // Print subscribed child address
#if UIP_MCAST6_CONF_ENGINE == UIP_MCAST6_ENGINE_SeRI || UIP_MCAST6_CONF_ENGINE == UIP_MCAST6_ENGINE_BMRF
    subscribed_child = &route->subscribed_child;
    printf("Subscribed Child: ");
    uip_debug_lladdr_print(subscribed_child); // Print link-layer address
    printf("\n");
    printf("----------------------------\n");
#endif
  }
}

/*
Unicast Routing Table:
Destination: aaaa::212:740e:e:e0e
Next Hop: fe80::212:7409:9:909
Lifetime: 65248 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7408:8:808
Next Hop: fe80::212:7409:9:909
Lifetime: 65249 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7413:13:1313
Next Hop: fe80::212:740d:d:d0d
Lifetime: 65249 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7403:3:303
Next Hop: fe80::212:7409:9:909
Lifetime: 65249 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7415:15:1515
Next Hop: fe80::212:7415:15:1515
Lifetime: 65250 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:740f:f:f0f
Next Hop: fe80::212:740f:f:f0f
Lifetime: 65250 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7404:4:404
Next Hop: fe80::212:7404:4:404
Lifetime: 65251 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:740d:d:d0d
Next Hop: fe80::212:740d:d:d0d
Lifetime: 65251 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7402:2:202
Next Hop: fe80::212:740d:d:d0d
Lifetime: 65252 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7405:5:505
Next Hop: fe80::212:740d:d:d0d
Lifetime: 65252 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7410:10:1010
Next Hop: fe80::212:7404:4:404
Lifetime: 65253 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7411:11:1111
Next Hop: fe80::212:7404:4:404
Lifetime: 65254 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7407:7:707
Next Hop: fe80::212:7415:15:1515
Lifetime: 65255 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:740c:c:c0c
Next Hop: fe80::212:7404:4:404
Lifetime: 65255 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7414:14:1414
Next Hop: fe80::212:740d:d:d0d
Lifetime: 65256 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:740a:a:a0a
Next Hop: fe80::212:7404:4:404
Lifetime: 65257 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:740b:b:b0b
Next Hop: fe80::212:7404:4:404
Lifetime: 65258 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7412:12:1212
Next Hop: fe80::212:7404:4:404
Lifetime: 65258 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7406:6:606
Next Hop: fe80::212:7415:15:1515
Lifetime: 65274 seconds
Prefix Length: 128
----------------------------
Destination: aaaa::212:7409:9:909
Next Hop: fe80::212:7409:9:909
Lifetime: 65280 seconds
Prefix Length: 128
----------------------------
End of Unicast Routing Table
*/
void print_ucast6_table() {
  uip_ds6_route_t *r;
  uip_ipaddr_t *ipaddr;
  uip_ipaddr_t *nexthop;
  uint16_t lifetime;

  // Print the Unicast Routing Table
  for (r = uip_ds6_route_head(); r != NULL; r = uip_ds6_route_next(r)) {
    ipaddr = &r->ipaddr;
    nexthop = uip_ds6_route_nexthop(r);
    lifetime = r->state.lifetime;
    printf("Destination: ");
    uip_debug_ipaddr_print(ipaddr);
    printf("\n");
    printf("Next Hop: ");
    uip_debug_ipaddr_print(nexthop);
    printf("\n");
    printf("Lifetime: %u seconds\n", lifetime);
    printf("Prefix Length: %u\n", r->length);
    printf("----------------------------\n");
  }
}

void print_routing_tables() {
  // Print the Unicast Routing Table
  printf("Unicast Routing Table:\n");
  print_ucast6_table();
  printf("End of Unicast Routing Table\n");

  printf("----------------------------\n");
  // Print the Multicast Routing Table
  printf("Multicast Routing Table:\n");
  print_mcast6_routes();
  printf("End of Multicast Routing Table\n");
}

static void
multicast_send(void)
{
  uint32_t id;

  id = uip_htonl(seq_id);
  memset(buf, 0, MAX_PAYLOAD_LEN);
  memcpy(buf, &id, sizeof(seq_id));

  PRINTF("Send to: ");
  PRINT6ADDR(&mcast_conn->ripaddr);
  PRINTF(" Remote Port %u,", uip_ntohs(mcast_conn->rport));
  PRINTF(" (msg=0x%08lx)", (unsigned long)uip_ntohl(*((uint32_t *)buf)));
  PRINTF(" %lu bytes\n", (unsigned long)sizeof(id));

  PRINTF("Out;%lu\n", seq_id);

  seq_id++;
  uip_udp_packet_send(mcast_conn, buf, sizeof(id));
}
/*---------------------------------------------------------------------------*/
static void
prepare_mcast(void)
{
  uip_ipaddr_t ipaddr;

  /*
   * IPHC will use stateless multicast compression for this destination
   * (M=1, DAC=0), with 32 inline bits (1E 89 AB CD)
   */
  uip_ip6addr(&ipaddr, 0xFF1E,0,0,0,0,0,0x89,0xABCD);
  mcast_conn = udp_new(&ipaddr, UIP_HTONS(MCAST_SINK_UDP_PORT), NULL);
}
/*---------------------------------------------------------------------------*/
static void
set_own_addresses(void)
{
  int i;
  uint8_t state;
  rpl_dag_t *dag;
  uip_ipaddr_t ipaddr;

  uip_ip6addr(&ipaddr, 0xaaaa, 0, 0, 0, 0, 0, 0, 0);
  uip_ds6_set_addr_iid(&ipaddr, &uip_lladdr);
  uip_ds6_addr_add(&ipaddr, 0, ADDR_AUTOCONF);

  PRINTF("Our IPv6 addresses:\n");
  for(i = 0; i < UIP_DS6_ADDR_NB; i++) {
    state = uip_ds6_if.addr_list[i].state;
    if(uip_ds6_if.addr_list[i].isused && (state == ADDR_TENTATIVE || state
        == ADDR_PREFERRED)) {
      PRINTF("  ");
      PRINT6ADDR(&uip_ds6_if.addr_list[i].ipaddr);
      PRINTF("\n");
      if(state == ADDR_TENTATIVE) {
        uip_ds6_if.addr_list[i].state = ADDR_PREFERRED;
      }
    }
  }

  /* Become root of a new DODAG with ID our global v6 address */
  dag = rpl_set_root(RPL_DEFAULT_INSTANCE, &ipaddr);
  if(dag != NULL) {
    rpl_set_prefix(dag, &ipaddr, 64);
    PRINTF("Created a new RPL dag with ID: ");
    PRINT6ADDR(&dag->dag_id);
    PRINTF("\n");
  }
}
/*---------------------------------------------------------------------------*/
PROCESS_THREAD(rpl_root_process, ev, data)
{
  static struct etimer et;

  PROCESS_BEGIN();

  PRINTF("Multicast Engine: '%s'\n", UIP_MCAST6.name);

  NETSTACK_MAC.off(1);

  set_own_addresses();

  prepare_mcast();

  etimer_set(&et, START_DELAY * CLOCK_SECOND);
  while(1) {
    PROCESS_YIELD();
    if(etimer_expired(&et)) {
      if(seq_id == ITERATIONS) {
        etimer_stop(&et);
#if (SENDER_IS == ROOT)
        PRINTF("n; %lu; %lu; %lu; %lu; %lu; %lu\n",
          SIMSTATS_GET(lltx),
          SIMSTATS_GET(pkttx),
          energest_type_time(ENERGEST_TYPE_LISTEN),
          energest_type_time(ENERGEST_TYPE_TRANSMIT),
          energest_type_time(ENERGEST_TYPE_LPM),
          energest_type_time(ENERGEST_TYPE_CPU));
#endif
      } else {
        print_routing_tables(); break;
        multicast_send();
        etimer_set(&et, SEND_INTERVAL);
      }
    }
  }

  PROCESS_END();
}
/*---------------------------------------------------------------------------*/
