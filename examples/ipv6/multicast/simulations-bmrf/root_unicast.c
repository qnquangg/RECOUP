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

#include "simple-udp.h"
// #include "servreg-hack.h"
#define UNICAST_UDP_PORT 1234
#define SERVICE_ID 190
static struct simple_udp_connection unicast_connection;


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
PROCESS(rpl_root_process, "RPL ROOT, Unicast Sender");
AUTOSTART_PROCESSES(&rpl_root_process);
/*---------------------------------------------------------------------------*/
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
  printf("all_children: %d\n", all_children);
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
/*---------------------------------------------------------------------------*/
void send_unicast_to_children() {
  uip_ipaddr_t *child_addr;
  uip_ds6_route_t *r;
  // Traverse the routing table to get all child nodes
  for (r = uip_ds6_route_head(); r != NULL; r = uip_ds6_route_next(r)) {
    child_addr = &r->ipaddr;
    if (child_addr != NULL) {
      static unsigned int message_number;
      char buf[20];
      printf("Sending unicast to ");
      uip_debug_ipaddr_print(child_addr);
      printf("\n");
      sprintf(buf, "Message %d", message_number);
      message_number++;
      simple_udp_sendto(&unicast_connection, buf, strlen(buf) + 1, child_addr);
    }
  }
}

/*---------------------------------------------------------------------------*/
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
  static struct etimer periodic_timer;
  static struct etimer send_timer;

  PROCESS_BEGIN();

  NETSTACK_MAC.off(1);

  set_own_addresses();
  
  simple_udp_register(&unicast_connection, UNICAST_UDP_PORT,
                      NULL, UNICAST_UDP_PORT, NULL);

  etimer_set(&et, START_DELAY * CLOCK_SECOND);

  while(1) {
    PROCESS_YIELD();
    if(etimer_expired(&et)) {
      if(seq_id == ITERATIONS) {
        break;
      }
      else { 
        send_unicast_to_children();
        etimer_set(&et, SEND_INTERVAL);
      }
    }
  }

  PROCESS_END();
}
/*---------------------------------------------------------------------------*/
