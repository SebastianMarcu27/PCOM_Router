#include <string.h>
#include <arpa/inet.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "lib.h"
#include "protocols.h"
#include "queue.h"

#define ETHERTYPE_IP 0x0800
#define ETHERTYPE_ARP 0x0806 
#define ARPOP_REQUEST 1
#define ARPOP_REPLY 2
#define MAX_PREFIX_LEN 32

struct arp_table_entry *arp_records = NULL;
int total_arp_records = 0;

static struct arp_table_entry *lookup_recursive (struct arp_table_entry *start, uint32_t ip, int remaining) {
    if (remaining == 0)
        return NULL;
    if (start->ip == ip)
        return start;
    return lookup_recursive (start + 1, ip, remaining - 1);
}

struct arp_table_entry *resolve_arp (uint32_t target_ip) {
    return lookup_recursive (arp_records, target_ip, total_arp_records);
}

struct trie_element {
    struct trie_element *branches[2];
    struct route_table_entry * associated_route;
};

struct trie_element *trie_base = NULL;
int number_of_nodes = 0;

static void *allocate_memory_for_trie () {
    return malloc (sizeof (struct trie_element));
}

struct trie_element * initialize_trie_node () {
    struct trie_element *new_node = allocate_memory_for_trie ();
    if (!new_node) 
        return NULL;
    for (int direction = 0; direction < 2; ++direction)
        *((new_node->branches) + direction) = NULL;
    new_node->associated_route = NULL;
    return new_node;
}

static int extract_bit (uint32_t value, int position) {
    return (value >> position) & 1;
}

static struct trie_element *descend (struct trie_element *node, int direction) {
    if (!node) 
        return NULL;
    struct trie_element **paths = node->branches;
    return *(paths + direction);
}

static int has_associated_route (struct trie_element *node) {
    return node && node->associated_route != NULL;
}

struct route_table_entry *determine_best_match (struct trie_element *start, uint32_t raw_ip) {
    if (!start) 
        return NULL;
    struct trie_element *walker = start;
    struct route_table_entry *last_valid_route = NULL;
    uint32_t normalized_ip = ntohl (raw_ip);
    int bit_pointer = MAX_PACKET_LEN;
    while (bit_pointer-- > 0) {
        int dir = extract_bit (normalized_ip, bit_pointer);
        struct trie_element *next_node = descend (walker, dir);
        if (!next_node)
            break;
        if (has_associated_route (next_node))
            last_valid_route = next_node->associated_route;
        walker = next_node;
    }
    return last_valid_route;
}

static int compute_significant_bits (uint32_t netmask) {
    uint32_t counter = 0, current = netmask;
    while (current & 0x80000000) {
        counter++;
        current <<= 1;
    }
    return counter;
}

static struct trie_element *ensure_branch_exists (struct trie_element *current, int direction) {
    struct trie_element **next = current->branches + direction;
    if (!*next)
        *next = initialize_trie_node();
    return *next;
}

void add_route_to_trie (struct trie_element *base, struct route_table_entry *record) {
    if (!base || !record) 
        return;
    uint32_t net_prefix = ntohl (record->prefix);
    uint32_t net_mask = ntohl (record->mask);
    struct trie_element *position = base;
    int depth = compute_significant_bits (net_mask);
    for (int step = 0; step < depth; ++step) {
        int dir = (net_prefix >> (31 - step)) & 1;
        position = ensure_branch_exists (position, dir);
    }
    position->associated_route = record;
}

int load_routes_from_file (const char *cale, struct trie_element *radacina) {
    FILE *fisier = fopen(cale, "r");
    if (!fisier) return -1;
    char linie[64];
    int total_rute = 0;
    while (fgets(linie, sizeof(linie), fisier)) {
        struct route_table_entry *rutie = malloc(sizeof(struct route_table_entry));
        if (!rutie) continue;
        unsigned char *prefix = (unsigned char *)&rutie->prefix;
        unsigned char *next_hop = (unsigned char *)&rutie->next_hop;
        unsigned char *masca = (unsigned char *)&rutie->mask;
        char *cursor = strtok(linie, " .");
        int camp_curent = 0;
        while (cursor) {
            uint8_t valoare = (uint8_t)atoi(cursor);
            if (camp_curent < 4)
                prefix[camp_curent] = valoare;
            else if (camp_curent < 8)
                next_hop[camp_curent - 4] = valoare;
            else if (camp_curent < 12)
                masca[camp_curent - 8] = valoare;
            else if (camp_curent == 12)
                rutie->interface = valoare;
            cursor = strtok(NULL, " .");
            camp_curent++;
        }
        add_route_to_trie(radacina, rutie);
        total_rute++;
    }
    fclose(fisier);
    return total_rute;
}

static struct arp_hdr *create_arp_header(uint32_t sender_ip, uint32_t target_ip,
                                         uint8_t *mac_sender, uint8_t *mac_target,
                                         uint16_t op_code) {
    struct arp_hdr *arp = malloc(sizeof(struct arp_hdr));
    DIE(!arp, "malloc failed for ARP header");
    arp->hw_type = htons(1);
    arp->proto_type = htons(ETHERTYPE_IP);
    arp->hw_len = 6;
    arp->proto_len = 4;
    arp->opcode = op_code;
    memcpy(arp->shwa, mac_sender, 6);
    memcpy(arp->thwa, mac_target, 6);
    arp->sprotoa = sender_ip;
    arp->tprotoa = target_ip;
    return arp;
}

static struct ether_hdr *build_ethernet_header(uint8_t *mac_dst, uint8_t *mac_src, uint16_t ether_type) {
    struct ether_hdr *eth = malloc(sizeof(struct ether_hdr));
    DIE(!eth, "malloc failed for Ethernet header");
    memcpy(eth->ethr_dhost, mac_dst, 6);
    memcpy(eth->ethr_shost, mac_src, 6);
    eth->ethr_type = htons(ether_type);
    return eth;
}

char *assemble_arp_packet(uint32_t ip_dest, uint32_t ip_src, struct ether_hdr *eth_template, uint16_t op_code) {
    struct ether_hdr *eth_custom = build_ethernet_header(
        eth_template->ethr_dhost, eth_template->ethr_shost, ETHERTYPE_ARP);
    struct arp_hdr *arp_custom = create_arp_header(
        ip_src, ip_dest, eth_template->ethr_shost, eth_template->ethr_dhost, op_code);
    size_t total_len = sizeof(struct ether_hdr) + sizeof(struct arp_hdr);
    char *packet = malloc(total_len);
    DIE(!packet, "malloc failed for final ARP packet");
    memcpy(packet, eth_custom, sizeof(struct ether_hdr));
    memcpy(packet + sizeof(struct ether_hdr), arp_custom, sizeof(struct arp_hdr));
    free(eth_custom);
    free(arp_custom);
    return packet;
}

char *construct_icmp_packet(
    struct ip_hdr *received_ip,
    struct ether_hdr *received_eth,
    struct icmp_hdr *received_icmp,
    uint8_t icmp_type,
    uint8_t icmp_code
) {
    size_t total_length = sizeof(struct ether_hdr) + sizeof(struct ip_hdr) + sizeof(struct icmp_hdr);
    char *packet = malloc(total_length);
    DIE(packet == NULL, "malloc failed in build_icmp_response");
    struct ether_hdr *eth = (struct ether_hdr *) packet;
    size_t ip_offset = sizeof(struct ether_hdr);
    size_t icmp_offset = ip_offset + sizeof(struct ip_hdr);
    struct ip_hdr *ip = (void *)(packet + ip_offset);
    struct icmp_hdr *icmp = (void *)(packet + icmp_offset);
    for (size_t i = 0; i < sizeof(struct icmp_hdr); i++) {
        ((uint8_t *)icmp)[i] = 0;
    }
    *((uint8_t *)icmp + 0) = icmp_type;
    *((uint8_t *)icmp + 1) = icmp_code;
    if (*(uint8_t *)received_icmp == 8 && *((uint8_t *)received_icmp + 1) == 0) {
        uint16_t icmp_hrd_new = received_icmp->un_t.echo_t.id;
        uint16_t sequence = received_icmp->un_t.echo_t.seq;
        memcpy((uint8_t *)icmp + 4, &icmp_hrd_new, sizeof(uint16_t));
        memcpy((uint8_t *)icmp + 6, &sequence, sizeof(uint16_t));
    }
    uint16_t result = checksum((uint16_t *)icmp, sizeof(struct icmp_hdr));
    memcpy((uint8_t *)icmp + 2, &result, sizeof(uint16_t));
    memcpy(eth->ethr_dhost, received_eth->ethr_shost, 6);
    memcpy(eth->ethr_shost, received_eth->ethr_dhost, 6);
    eth->ethr_type = htons(ETHERTYPE_IP);
    *ip = (struct ip_hdr) {
        .ver = 4,
        .ihl = 5,
        .tos = 0,
        .tot_len = htons(sizeof(struct ip_hdr) + sizeof(struct icmp_hdr)),
        .id = htons(1),
        .frag = 0,
        .ttl = 64,
        .proto = IPPROTO_ICMP,
        .checksum = 0,
        .source_addr = received_ip->dest_addr,
        .dest_addr = received_ip->source_addr
    };
    ip->checksum = checksum((uint16_t *) ip, sizeof(struct ip_hdr));
    return packet;
}

int main (int argc, char * argv[]) {
    char buffer[MAX_PACKET_LEN];
    // do not modify this line
    init(argc - 2, argv + 2);
    struct trie_element *radacina_trie = NULL;
    radacina_trie = initialize_trie_node();
    if (radacina_trie != NULL) {
        number_of_nodes = load_routes_from_file(argv[1], radacina_trie);
        trie_base = radacina_trie;
    }
    #define ARP_ENTRY_LIMIT 100
    arp_records = calloc(ARP_ENTRY_LIMIT, sizeof(*arp_records));
    total_arp_records = 0;
    queue pending_packets;
    pending_packets = NULL;
    pending_packets = create_queue();
    while (1) {
        size_t len = 0;
        const uint16_t arp_components[] = {
            sizeof(struct ether_hdr),
            sizeof(struct arp_hdr)
        };
        const uint16_t icmp_fields[] = {
            sizeof(struct ether_hdr),
            sizeof(struct ip_hdr),
            sizeof(struct icmp_hdr)
        };
        uint32_t len_arp = 0;
        for (size_t i = 0; i < sizeof(arp_components) / sizeof(uint16_t); ++i)
            len_arp += arp_components[i];
        uint32_t len_icmp = 0;
        for (size_t j = 0; j < sizeof(icmp_fields) / sizeof(uint16_t); ++j)
            len_icmp += icmp_fields[j];
        int interface = recv_from_any_link (buffer, & len);
        DIE (interface < 0, "recv_from_any_links");
        struct ether_hdr * eth_hdr = (struct ether_hdr * ) buffer;
        u_int16_t ethr_type = ntohs (eth_hdr -> ethr_type);
        if (ethr_type == ETHERTYPE_IP) {
            void *payload = buffer + sizeof(struct ether_hdr);
            struct ip_hdr *ip_hdr = payload;
            uint8_t *protocol_field = (uint8_t *)payload + (ip_hdr->ihl * 4);
            struct icmp_hdr *icmp_hdr = (struct icmp_hdr *)protocol_field;
            int echo_request = (icmp_hdr->mtype == 8 && icmp_hdr->mcode == 0);
            char *local_ip_str = get_interface_ip(interface);
            uint32_t local_ip_bin = inet_addr(local_ip_str);
            int addressed_to_us = (ip_hdr->dest_addr == local_ip_bin);
            if (echo_request && addressed_to_us) {
                char *reply_packet = construct_icmp_packet(ip_hdr, eth_hdr, icmp_hdr, 0, 0);
                send_to_link(len_icmp, reply_packet, interface);
                free(reply_packet);
                continue;
            }
            union {
                struct ip_hdr *header;
                uint8_t *bytes;
            } ip_view;
            ip_view.header = ip_hdr;
            uint16_t original_cksum = *(uint16_t *)(ip_view.bytes + 10);
            memset(ip_view.bytes + 10, 0, 2);
            uint16_t computed_cksum = ntohs(
                checksum((uint16_t *)ip_view.header, sizeof(struct ip_hdr))
            );
            memcpy(ip_view.bytes + 10, &original_cksum, 2);
            if (computed_cksum != original_cksum) {
                continue;
            }
            struct route_table_entry *nhop = determine_best_match(trie_base, ip_hdr->dest_addr);
            if (!nhop) {
                char *no_route_reply = construct_icmp_packet(ip_hdr, eth_hdr, icmp_hdr, 3, 0);
                send_to_link(len_icmp, no_route_reply, interface);
                free(no_route_reply);
                continue;
            }
            if (ip_hdr->ttl <= 1) {
                char *ttl_exceeded = construct_icmp_packet(ip_hdr, eth_hdr, icmp_hdr, 11, 0);
                send_to_link(len_icmp, ttl_exceeded, interface);
                free(ttl_exceeded);
                continue;
            }
            uint8_t prev_ttl = ip_hdr->ttl;
            ip_hdr->ttl--;
            uint32_t delta = ~((uint16_t)prev_ttl) + ip_hdr->ttl;
            ip_hdr->checksum = ~(~ip_hdr->checksum + delta + 1);
            struct arp_table_entry *mac_info = resolve_arp(ip_hdr->dest_addr);
            if (mac_info == NULL) {
                char *packet_copy = malloc(MAX_PACKET_LEN);
                DIE(!packet_copy, "malloc failed for packet copy");
                memcpy(packet_copy, buffer, MAX_PACKET_LEN);
                queue_enq(pending_packets, packet_copy);
                uint8_t local_mac[6];
                get_interface_mac(nhop->interface, local_mac);
                uint8_t broadcast_mac[6] = {255, 255, 255, 255, 255, 255};
                memcpy(eth_hdr->ethr_shost, local_mac, 6);
                memcpy(eth_hdr->ethr_dhost, broadcast_mac, 6);
                *((uint16_t *)((uint8_t *)eth_hdr + 12)) = htons(0x0806);
                char ip_buffer[INET_ADDRSTRLEN];
                strncpy(ip_buffer, get_interface_ip(nhop->interface), INET_ADDRSTRLEN);
                uint32_t local_interface_ip;
                inet_pton(AF_INET, ip_buffer, &local_interface_ip);
                char *arp_packet = assemble_arp_packet(
                    nhop->next_hop,
                    local_interface_ip,
                    eth_hdr,
                    htons(ARPOP_REQUEST)
                );
                int sent_bytes = send_to_link(len_arp, arp_packet, nhop->interface);
                (void)sent_bytes;
                free(arp_packet);
                continue;
            }
            uint8_t mac_src[6];
            get_interface_mac(interface, mac_src);
            memcpy(eth_hdr->ethr_shost, mac_src, 6);
            memcpy(eth_hdr->ethr_dhost, mac_info->mac, 6);
            send_to_link(len, buffer, nhop->interface);
        }
        if (ethr_type == ETHERTYPE_ARP) {
            struct arp_hdr *arp_hdr = (void *)(buffer + sizeof(struct ether_hdr));
            uint16_t operation = ntohs(arp_hdr->opcode);
            switch (operation) {
                case ARPOP_REQUEST: {
                    uint8_t local_mac[6];
                    char *interface_name = get_interface_ip(interface);
                    uint32_t local_ip = inet_addr(interface_name);
                    get_interface_mac(interface, local_mac);
                    struct ether_hdr eth_reply;
                    memcpy(eth_reply.ethr_shost, local_mac, 6);
                    memcpy(eth_reply.ethr_dhost, eth_hdr->ethr_shost, 6);
                    eth_reply.ethr_type = htons(ETHERTYPE_ARP);
                    struct arp_hdr arp_reply;
                    arp_reply.hw_type = htons(1);
                    arp_reply.proto_type = htons(ETHERTYPE_IP);
                    arp_reply.hw_len = 6;
                    arp_reply.proto_len = 4;
                    arp_reply.opcode = htons(ARPOP_REPLY);
                    memcpy(arp_reply.shwa, local_mac, 6);
                    arp_reply.sprotoa = local_ip;
                    memcpy(arp_reply.thwa, arp_hdr->shwa, 6);
                    arp_reply.tprotoa = arp_hdr->sprotoa;
                    size_t packet_size = sizeof(struct ether_hdr) + sizeof(struct arp_hdr);
                    char *response = malloc(packet_size);
                    DIE(!response, "malloc failed for ARP reply");
                    memcpy(response, &eth_reply, sizeof(struct ether_hdr));
                    memcpy(response + sizeof(struct ether_hdr), &arp_reply, sizeof(struct arp_hdr));
                    send_to_link(packet_size, response, interface);
                    free(response);
                    break;
                }
                case ARPOP_REPLY: {
                    if (resolve_arp(arp_hdr->sprotoa) == NULL && total_arp_records < ARP_ENTRY_LIMIT) {
                        struct arp_table_entry *slot = &arp_records[total_arp_records++];
                        slot->ip = arp_hdr->sprotoa;
                        memcpy(slot->mac, arp_hdr->shwa, 6);
                    }
                    void process_queue(queue q, int iface, struct arp_table_entry *resolved) {
                        if (queue_empty(q)) return;
                        char *pkt = queue_deq(q);
                        if (!pkt) return;
                        if (!resolved) {
                            queue_enq(q, pkt);
                        } else {
                            struct ether_hdr *eth_pkt = (struct ether_hdr *)pkt;
                            uint8_t mac_local[6];
                            get_interface_mac(iface, mac_local);
                            memcpy(eth_pkt->ethr_shost, mac_local, 6);
                            memcpy(eth_pkt->ethr_dhost, resolved->mac, 6);
                            send_to_link(len_arp, pkt, iface);
                            free(pkt);
                        }
                        process_queue(q, iface, resolve_arp(arp_hdr->sprotoa));
                    }
                    process_queue(pending_packets, interface, resolve_arp(arp_hdr->sprotoa));
                    break;
                }
            }
        }
    }
}
