/*
 * Copyright (c) 2011, Swedish Institute of Computer Science.
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
 *
 */

#include "contiki.h"
#include "lib/random.h"
#include "sys/ctimer.h"
#include "sys/etimer.h"
#include "net/ip/uip.h"
#include "net/ipv6/uip-ds6.h"
#include "net/ipv6/uip-ds6-route.h"
#define DEBUG DEBUG_PRINT
#include "net/ip/uip-debug.h"
#include "net/rpl/rpl.h"

#include "net/ipv6/multicast/uip-mcast6.h"
#include "net/ipv6/multicast/uip-mcast6-route.h"

#include "sys/node-id.h"

#include "simple-udp.h"
#include "servreg-hack.h"
#include "simstats.h"
#include "lib/list.h"

#include <stdio.h>
#include <string.h>

#define UDP_PORT 1234
#define SERVICE_ID 190

#ifdef MCAST_CONF_SEND_INTERVAL
#define SEND_INTERVAL MCAST_CONF_SEND_INTERVAL * CLOCK_SECOND /* clock ticks */
#else
#define SEND_INTERVAL CLOCK_SECOND
#endif

#ifdef MCAST_CONF_START_DELAY
#define START_DELAY MCAST_CONF_START_DELAY
#else
#define START_DELAY 60
#endif

#define SEND_TIME		(random_rand() % (SEND_INTERVAL))
#define UIP_DS6_ROUTE_NB 30 // the maximum number of children
#define MAX_PAYLOAD_LEN 120

#if (SENDER_IS == ROOT)
#ifdef MCAST_CONF_MESSAGES
#define ITERATIONS MCAST_CONF_MESSAGES /* messages */
#endif
#else
#define ITERATIONS 0
#endif

static struct simple_udp_connection unicast_connection;
static uint32_t seq_id;
static char buf[MAX_PAYLOAD_LEN];

/*---------------------------------------------------------------------------*/
PROCESS(unicast_sender_process, "Unicast sender process 2");
AUTOSTART_PROCESSES(&unicast_sender_process);
/*---------------------------------------------------------------------------*/
static void
receiver(struct simple_udp_connection *c,
         const uip_ipaddr_t *sender_addr,
         uint16_t sender_port,
         const uip_ipaddr_t *receiver_addr,
         uint16_t receiver_port,
         const uint8_t *data,
         uint16_t datalen)
{
  PRINTF("Data received on port %d from port %d with length %d\n",
         receiver_port, sender_port, datalen);
}
/*---------------------------------------------------------------------------*/
static void
set_global_address(void)
{
  uip_ipaddr_t ipaddr;
  int i;
  uint8_t state;
  rpl_dag_t *dag;

  uip_ip6addr(&ipaddr, 0xaaaa, 0, 0, 0, 0, 0, 0, 0);
  uip_ds6_set_addr_iid(&ipaddr, &uip_lladdr);
  uip_ds6_addr_add(&ipaddr, 0, ADDR_AUTOCONF);

  PRINTF("IPv6 addresses: ");
  for(i = 0; i < UIP_DS6_ADDR_NB; i++) {
    state = uip_ds6_if.addr_list[i].state;
    if(uip_ds6_if.addr_list[i].isused &&
       (state == ADDR_TENTATIVE || state == ADDR_PREFERRED)) {
      uip_debug_ipaddr_print(&uip_ds6_if.addr_list[i].ipaddr);
      PRINTF("\n");
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
void print_ucast6_table() {
  uip_ds6_route_t *r;
  uip_ipaddr_t *ipaddr;
  uip_ipaddr_t *nexthop;
  uint16_t lifetime;
  int all_children = 0;

  // Print the Unicast Routing Table
  for (r = uip_ds6_route_head(); r != NULL; r = uip_ds6_route_next(r)) {
    all_children++;
    ipaddr = &r->ipaddr;
    nexthop = uip_ds6_route_nexthop(r);
    lifetime = r->state.lifetime;
    PRINTF("Destination: ");
    uip_debug_ipaddr_print(ipaddr);
    PRINTF("\n");
    PRINTF("Next Hop: ");
    uip_debug_ipaddr_print(nexthop);
    PRINTF("\n");
    PRINTF("Lifetime: %u seconds\n", lifetime);
    PRINTF("Prefix Length: %u\n", r->length);
    PRINTF("----------------------------\n");
  }
  PRINTF("all_children: %d\n", all_children);
}

/*
* Make a copy of all the objects in the routing table before entering the loop
*/
static void send_unicast_to_children() {
  uip_ipaddr_t *child_addr;
  uip_ds6_route_t *r;
  uip_ds6_route_t routes_copy[UIP_DS6_ROUTE_NB];
  int route_count = 0;
  static unsigned int message_number;

  // Traverse the routing table and copy all entries to routes_copy
  for (r = uip_ds6_route_head(); r != NULL; r = uip_ds6_route_next(r)) {
    memcpy(&routes_copy[route_count], r, sizeof(uip_ds6_route_t));
    route_count++;
  }

  uint32_t id;
  id = uip_htonl(seq_id);
  memset(buf, 0, MAX_PAYLOAD_LEN);
  memcpy(buf, &id, sizeof(seq_id));

  // Print log for Cooja
  if (route_count > 0) {
    PRINTF("Out;%lu\n", seq_id);
  }

  // Iterate over the copied routes
  int i = 0;
  for (i = 0; i < route_count; i++) {
    child_addr = &routes_copy[i].ipaddr;
    if (child_addr != NULL) {
      // PRINTF("Sending unicast to ");
      // uip_debug_ipaddr_print(child_addr);
      // PRINTF("\n");
      PRINTF("Send to: ");
      uip_debug_ipaddr_print(child_addr);
      // PRINTF(" Remote Port %u,", uip_ntohs(unicast_connection.rport));
      PRINTF(" (msg=0x%08lx)", (unsigned long)uip_ntohl(*((uint32_t *)buf)));
      PRINTF(" %lu bytes\n", (unsigned long)sizeof(id));
      simple_udp_sendto(&unicast_connection, buf, sizeof(id), child_addr);
    }
  }
  seq_id++;
}
/*---------------------------------------------------------------------------*/
PROCESS_THREAD(unicast_sender_process, ev, data)
{
  static struct etimer et;
  uip_ipaddr_t *addr;

  PROCESS_BEGIN();
  NETSTACK_MAC.off(1);

  set_global_address();

  simple_udp_register(&unicast_connection, UDP_PORT,
                      NULL, UDP_PORT, receiver);

  etimer_set(&et, START_DELAY * CLOCK_SECOND);
  while(1) {
    PROCESS_YIELD();
    if(etimer_expired(&et)) {
      if(seq_id == ITERATIONS) {
        PRINTF("n; %lu; %lu; %lu; %lu; %lu; %lu\n",
          SIMSTATS_GET(lltx),
          SIMSTATS_GET(pkttx),
          energest_type_time(ENERGEST_TYPE_LISTEN),
          energest_type_time(ENERGEST_TYPE_TRANSMIT),
          energest_type_time(ENERGEST_TYPE_LPM),
          energest_type_time(ENERGEST_TYPE_CPU));
        PROCESS_EXIT();
      } else {
        etimer_set(&et, SEND_INTERVAL);
      }
    }
    send_unicast_to_children();
  }
  PROCESS_END();
}
/*---------------------------------------------------------------------------*/
