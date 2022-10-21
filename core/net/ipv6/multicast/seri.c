/*
 * Copyright (c) 2014, VUB - ETRO
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
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERlRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 */

/**
 *         Original code for calculating delays by
 *         George Oikonomou - <oikonomou@users.sourceforge.net>
 *         from smrf.c
 */

/**
 * \file
 *         This file implements 'Secure and Robust Multicast RPL Forwarding' (SeRI)
 *
 *         It will only work in RPL networks in MOP 3 "Storing with Multicast"
 *
 * \author
 *         Pallavi Kaliyar
 */

#include "contiki.h"
#include "contiki-net.h"
#include "net/ipv6/multicast/uip-mcast6.h"
#include "net/ipv6/multicast/uip-mcast6-route.h"
#include "net/ipv6/multicast/uip-mcast6-stats.h"
#include "net/ipv6/uip-ds6-nbr.h"
#include "net/ipv6/multicast/seri.h"
#include "net/rpl/rpl.h"
#include "net/rpl/rpl-private.h"
#include "net/netstack.h"
#include "lib/list.h"
#include <string.h>

#define DEBUG DEBUG_PRINT
#include "net/ip/uip-debug.h"

#if UIP_CONF_IPV6
#if UIP_MCAST6_ENGINE == UIP_MCAST6_ENGINE_SeRI
/*---------------------------------------------------------------------------*/
/* Macros */
/*---------------------------------------------------------------------------*/
/* CCI */
#define SeRI_FWD_DELAY()  NETSTACK_RDC.channel_check_interval()
/* Number of slots in the next 500ms */
#define SeRI_INTERVAL_COUNT  ((CLOCK_SECOND >> 2) / fwd_delay)
/* uip_lladdr comparison */
#define uip_lladdr_cmp(addr1, addr2) (memcmp(addr1, addr2, UIP_LLADDR_LEN) == 0)
/* uip_ipaddr partial comparison */
#define uip_partial_cmp(addr1, addr2, len) (memcmp(addr1, addr2, len) == 0)
/*---------------------------------------------------------------------------*/
/* Maintain Stats */
/*---------------------------------------------------------------------------*/
#if UIP_MCAST6_STATS
static struct seri_stats stats;
#define SeRI_STATS_ADD(x) stats.x++
#define SeRI_STATS_INIT() do { memset(&stats, 0, sizeof(stats)); } while(0)
#else /* UIP_MCAST6_STATS */
#define SeRI_STATS_ADD(x)
#define SeRI_STATS_INIT()
#endif
/*---------------------------------------------------------------------------*/
/* Internal Data */
/*---------------------------------------------------------------------------*/
static struct ctimer mcast_periodic;
static uint8_t mcast_len;
static uip_buf_t mcast_buf;
static uint8_t fwd_delay;
static uint8_t fwd_spread;
/*---------------------------------------------------------------------------*/
/* uIPv6 Pointers */
/*---------------------------------------------------------------------------*/
#define UIP_IP_BUF                ((struct uip_ip_hdr *)&uip_buf[UIP_LLH_LEN])
#define UIP_HBHO_BUF              ((struct uip_hbho_hdr *)&uip_buf[uip_l2_l3_hdr_len])
#define UIP_EXT_HDR_OPT_RPL_BUF   ((struct uip_ext_hdr_opt_rpl *)&uip_buf[uip_l2_l3_hdr_len + 2])
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
static void
mcast_fwd_with_unicast(void)
{
  uip_mcast6_route_t *mcast_entries;
  for(mcast_entries = uip_mcast6_route_list_head();
      mcast_entries != NULL;
      mcast_entries = list_item_next(mcast_entries)) {
    if(uip_ipaddr_cmp(&mcast_entries->group, &UIP_IP_BUF->destipaddr)) {
      tcpip_output(&mcast_entries->subscribed_child);
      PRINTF("%s, SeRI: Forwarded with LL-unicast to ", __func__);
      PRINTLLADDR(&mcast_entries->subscribed_child);
      PRINTF("%s, \n", __func__);
    }
  }
  PRINTF("%s, SeRI: Ended forwarding with LL-unicast\n", __func__);
}
/*---------------------------------------------------------------------------*/
static void
mcast_fwd_with_unicast_up_down(const uip_lladdr_t *preferred_parent)
{
  uip_mcast6_route_t *mcast_entries;
  uip_lladdr_t sender;
  memcpy(&sender, (uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER), UIP_LLADDR_LEN);
  UIP_IP_BUF->ttl--;    /* Decrease TTL before forwarding */
  for(mcast_entries = uip_mcast6_route_list_head();
      mcast_entries != NULL;
      mcast_entries = list_item_next(mcast_entries)) {
    /* Only send if it is not the origin */
    if(uip_ipaddr_cmp(&mcast_entries->group, &UIP_IP_BUF->destipaddr)
       && !uip_lladdr_cmp(&mcast_entries->subscribed_child, &sender)) {
      tcpip_output(&mcast_entries->subscribed_child);
      PRINTF("%s, SeRI: Forwarded with LL-unicast to ", __func__);
      PRINTLLADDR(&mcast_entries->subscribed_child);
      PRINTF("%s, \n", __func__);
    }
  }
  /* If preferred_parent == NULL, we are the DODAG root */
  if(preferred_parent != NULL) {
    tcpip_output(preferred_parent);
    PRINTF("%s, SeRI: Forwarded with LL-unicast up and down\n", __func__);
    PRINTF("%s, SeRI: Preferred parent LL: ", __func__);
    PRINTLLADDR(preferred_parent);
    PRINTF("%s, \n", __func__);
  }
  UIP_IP_BUF->ttl++;   /* Restore before potential upstack delivery */
}
/*---------------------------------------------------------------------------*/
static void
mcast_fwd_down(void)
{
  UIP_IP_BUF->ttl--;   
#if SeRI_MODE == SeRI_UNICAST_MODE
  SeRI_STATS_ADD(seri_fwd_uncst);
  mcast_fwd_with_unicast();

#endif
}
/*---------------------------------------------------------------------------*/
static void
mcast_fwd_down_delayed(void *p)
{
  memcpy(uip_buf, &mcast_buf, mcast_len);
  uip_len = mcast_len;
  mcast_fwd_down();
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
/* Comparing uip_ipaddr without the first 16 prefix bits */
uip_ds6_route_t *
uip_ds6_route_lookup_from_nbr_ip(uip_ipaddr_t *addr)
{
  uip_ds6_route_t *r;
  uip_ds6_route_t *found_route;
  uint8_t longestmatch;

  found_route = NULL;
  longestmatch = 0;
  for(r = uip_ds6_route_head();
      r != NULL;
      r = uip_ds6_route_next(r)) {
    if(r->length >= longestmatch &&
       uip_partial_cmp(&(((uint16_t *)addr)[1]), &(((uint16_t *)(&r->ipaddr))[1]), ((r->length >> 3) - 2))) {
      longestmatch = r->length;
      found_route = r;
    }
  }

  return found_route;
}
/*---------------------------------------------------------------------------*/

static uint8_t
in()
{
  PRINTF("%s, SeRI: in\n", __func__);
  rpl_dag_t *d;                       /* Our DODAG */
  uip_ipaddr_t *aux_ipaddr;
  const uip_lladdr_t *parent_lladdr;  /* Our pref. parent's LL address */
  const uip_lladdr_t *neighbor_lladdr;
  int idc, idn;
  //dag = rpl_get_any_dag();


  /*
   * Fetch a pointer to the LL address of our preferred parent
   */
  /* RPL HBHO present */
  if(UIP_IP_BUF->proto == UIP_PROTO_HBHO && UIP_HBHO_BUF->len == RPL_HOP_BY_HOP_LEN - 8) {
    PRINTF("%s, SeRI: RPL HBHO present 1\n", __func__);
    d = ((rpl_instance_t *)rpl_get_instance(UIP_EXT_HDR_OPT_RPL_BUF->instance))->current_dag;
  } else {
    PRINTF("%s, SeRI: RPL HBHO present 2\n", __func__);
    d = rpl_get_any_dag();
  }

  if(!d) {
    PRINTF("%s, SeRI: Dropped, no DODAG\n", __func__);
    UIP_MCAST6_STATS_ADD(mcast_dropped);
    return UIP_MCAST6_DROP;
  }

  if(UIP_IP_BUF->ttl < 1) {
    PRINTF("%s, SeRI: Dropped because ttl=0\n", __func__);
    UIP_MCAST6_STATS_ADD(mcast_dropped);
    return UIP_MCAST6_DROP;
  } else if(UIP_IP_BUF->ttl == 1) {
    PRINTF("%s, SeRI: Not forwarded because ttl=0\n", __func__);
    goto check_membership;  /* Check if we are a member of the multicast group before dropping */
  }

  /* We are not the root */
  if(d->rank != ROOT_RANK(default_instance)) {
    PRINTF("%s, SeRI: We are not the root\n", __func__);
    /* Retrieve our preferred parent's LL address */
    aux_ipaddr = rpl_get_parent_ipaddr(d->preferred_parent);
    parent_lladdr = uip_ds6_nbr_lladdr_from_ipaddr(aux_ipaddr);
  } else {
    PRINTF("%s, SeRI: We are the root\n", __func__);
    parent_lladdr = NULL;
    if(uip_lladdr_cmp(packetbuf_addr(PACKETBUF_ADDR_RECEIVER), &linkaddr_null)) {
      PRINTF("%s, SeRI: Dropped, broadcast from a child\n", __func__);
      UIP_MCAST6_STATS_ADD(mcast_dropped);
      return UIP_MCAST6_DROP;
    } else {
      PRINTF("%s, SeRI: We are the root, packet_from_bellow\n", __func__);
      goto packet_from_bellow;
    }
  }

  if(parent_lladdr == NULL) {
    PRINTF("%s, SeRI: Dropped, no preferred parent\n", __func__);
    UIP_MCAST6_STATS_ADD(mcast_dropped);
    return UIP_MCAST6_DROP;
  }

  /* LL Broadcast */
  if(uip_lladdr_cmp(packetbuf_addr(PACKETBUF_ADDR_RECEIVER), &linkaddr_null)) {
    PRINTF("%s, SeRI: LL Broadcast\n", __func__);
    /*
     * We accept a datagram if it arrived from our preferred parent, discard
     * otherwise.
     */
    if(!uip_lladdr_cmp(parent_lladdr, packetbuf_addr(PACKETBUF_ADDR_SENDER))) {
      PRINTF("%s, SeRI: Routable in but SeRI ignored it\n", __func__);
      UIP_MCAST6_STATS_ADD(mcast_dropped);
      return UIP_MCAST6_DROP;
    }
    PRINTF("%s, SeRI: Broadcast packet. LL-sender: ", __func__);
    PRINTLLADDR(packetbuf_addr(PACKETBUF_ADDR_SENDER));
    PRINTF("%s, \n", __func__);
    /* If we have an entry in the mcast routing table, something with
     * a higher RPL rank (somewhere down the tree) is a group member */
    if(uip_mcast6_route_lookup(&UIP_IP_BUF->destipaddr)) {
      PRINTF("%s, SeRI: we have an entry in the mcast routing table\n", __func__);
      UIP_MCAST6_STATS_ADD(mcast_fwd);

      /*
       * Add a delay (D) of at least SeRI_FWD_DELAY() to compensate for how
       * contikimac handles broadcasts. We can't start our TX before the sender
       * has finished its own.
       */
      fwd_delay = SeRI_FWD_DELAY();

      /* Finalise D: D = max(SeRI_FWD_DELAY(), SeRI_MIN_FWD_DELAY) */
#if SeRI_MIN_FWD_DELAY
      if(fwd_delay < SeRI_MIN_FWD_DELAY) {
        fwd_delay = SeRI_MIN_FWD_DELAY;
      }
#endif

      if(fwd_delay == 0) {
        /* No delay required, send it, do it now, why wait? */
        PRINTF("%s, SeRI: mcast_fwd_down\n", __func__);
        mcast_fwd_down();
      } else {
        /* Randomise final delay in [D , D*Spread], step D */
        PRINTF("%s, SeRI: Randomise final delay\n", __func__);
        fwd_spread = SeRI_INTERVAL_COUNT;
        if(fwd_spread > SeRI_MAX_SPREAD) {
          fwd_spread = SeRI_MAX_SPREAD;
        }
        if(fwd_spread) {
          fwd_delay = fwd_delay * (1 + ((random_rand() >> 11) % fwd_spread));
        }

        memcpy(&mcast_buf, uip_buf, uip_len);
        mcast_len = uip_len;
        ctimer_set(&mcast_periodic, fwd_delay, mcast_fwd_down_delayed, NULL);
      }
      PRINTF("%s, SeRI: %u bytes: fwd in %u [%u]\n", __func__,
             uip_len, fwd_delay, fwd_spread);

    } else {
      PRINTF("%s, SeRI: No entries for this group\n", __func__);
    }
  /* LL Unicast from above us */
  } else if(uip_lladdr_cmp(parent_lladdr, packetbuf_addr(PACKETBUF_ADDR_SENDER))) {
    /* If we have an entry in the mcast routing table, something with
     * a higher RPL rank (somewhere down the tree) is a group member */
    if(uip_mcast6_route_lookup(&UIP_IP_BUF->destipaddr)) {
      PRINTF("%s, SeRI: UIP_MCAST6_STATS_ADD\n", __func__);
      UIP_MCAST6_STATS_ADD(mcast_fwd);
      mcast_fwd_down();
    } else {
      PRINTF("%s, SeRI: No entries for this group\n", __func__);
    }
  } else {
packet_from_bellow:
    aux_ipaddr = uip_ds6_nbr_ipaddr_from_lladdr((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
    PRINTF("%s, SeRI: Should be a packet from bellow. ll_src: ", __func__);
    PRINTLLADDR((uip_lladdr_t *)packetbuf_addr(PACKETBUF_ADDR_SENDER));
    PRINTF("%s, \n", __func__);
    /* Unicast from below */
    if(aux_ipaddr != NULL && uip_ds6_route_lookup_from_nbr_ip(aux_ipaddr) != NULL) {
      /* If we enter here, we will definitely forward */
      UIP_MCAST6_STATS_ADD(mcast_fwd);
      SeRI_STATS_ADD(seri_fwd_uncst);
      mcast_fwd_with_unicast_up_down(parent_lladdr);
    } else {
      PRINTF("%s, SeRI: Not a packet from bellow, drop\n", __func__);
      UIP_MCAST6_STATS_ADD(mcast_dropped);
      return UIP_MCAST6_DROP;
    }
   //check for the packet from different cluster here only
     int idc = uip_ds6_nbr_lookup_for_cluster_id(parent_lladdr);
     PRINTF("%s, SeRI: Quang dump idc = %d ", __func__ ,idc);
     neighbor_lladdr = uip_ds6_nbr_lladdr_from_ipaddr(parent_lladdr);
     int idn = uip_ds6_nbr_lookup_for_cluster_id(neighbor_lladdr);
         if(idc != -1 && idn != -1 && idc != idn)
             {  UIP_MCAST6_STATS_ADD(mcast_fwd); 
                PRINTF("%s, SeRI: Should be a packet from Different Cluster ", __func__);
             }
          else
             { return 0;
             }
       
}
     
  UIP_MCAST6_STATS_ADD(mcast_in_all);
  UIP_MCAST6_STATS_ADD(mcast_in_unique);

check_membership:
  /* Done with this packet unless we are a member of the mcast group */
  if(!uip_ds6_is_my_maddr(&UIP_IP_BUF->destipaddr)) {
    PRINTF("%s, SeRI: Not a group member. No further processing\n", __func__);
    return UIP_MCAST6_DROP;
  } else {
    PRINTF("%s, SeRI: Ours. Deliver to upper layers\n", __func__);
    UIP_MCAST6_STATS_ADD(mcast_in_ours);
    return UIP_MCAST6_ACCEPT;
  }

}
/*---------------------------------------------------------------------------*/
static void
init()
{
  SeRI_STATS_INIT();
  UIP_MCAST6_STATS_INIT(&stats);

  uip_mcast6_route_init();
}
/*---------------------------------------------------------------------------*/
static void
out()
{
  rpl_dag_t *dag;                       /* Our DODAG */
  const uip_lladdr_t *parent_lladdr;  /* Our pref. parent's LL address */
  const uip_lladdr_t *neighbor_lladdr;
  dag = rpl_get_any_dag();
  UIP_MCAST6_STATS_ADD(mcast_out);
  PRINTF("%s, SeRI: Send ", __func__);

  if(dag->rank != ROOT_RANK(default_instance)) {
    /* Retrieve our preferred parent's LL address */
    parent_lladdr = uip_ds6_nbr_lladdr_from_ipaddr(rpl_get_parent_ipaddr(dag->preferred_parent));
    if(parent_lladdr != NULL) {
      /* Send to our preferred parent LL-address */
      PRINTF("%s, SeRI: Seed, send to our preferred parent with address: ", __func__);
      PRINTLLADDR(parent_lladdr);
      PRINTF("%s, \n", __func__);
      tcpip_output(parent_lladdr);
    } else {
      PRINTF("%s, SeRI: We are the seed but not preferred parent found\n", __func__);
    }
  }

  if(uip_mcast6_route_lookup(&UIP_IP_BUF->destipaddr)) {
    UIP_IP_BUF->ttl++;   /* Dirty: increment TTL since it is going to be decremented before tcpip_output */
    mcast_fwd_down();
  } else {
    PRINTF("%s, SeRI: No entries for this group\n", __func__);
  }

  if(parent_lladdr != NULL) {
     parent_lladdr = uip_ds6_nbr_lladdr_from_ipaddr(rpl_get_parent_ipaddr(dag->preferred_parent));    
     int cid = uip_ds6_nbr_lookup_for_cluster_id(parent_lladdr);
     neighbor_lladdr = uip_ds6_nbr_lladdr_from_ipaddr(parent_lladdr);
     int nid = uip_ds6_nbr_lookup_for_cluster_id(neighbor_lladdr);
         if(cid != -1 && nid != -1 && cid != nid)
             {  
              PRINTF("%s, SeRI: Seed, send to Different cluster also ", __func__);
              mcast_fwd_with_unicast();                
             }
          else
             { return;
             }
       }    

  /* Set uip_len = 0 to stop the core from re-sending it. */
  uip_len = 0;
  return;
}
/*---------------------------------------------------------------------------*/
const struct uip_mcast6_driver seri_driver = {
  "SeRI",
  init,
  out,
  in,
};
/*---------------------------------------------------------------------------*/

#endif /* UIP_MCAST6_ENGINE */
#endif /* UIP_CONF_IPV6 */
