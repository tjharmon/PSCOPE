/* PSCOPE is a tool intended to parse through PCAP files and keep track of
 * packet "flows" within the file. A flow consists of an source and
 * destination ip address, and the protocol for that packet. Each unique
 * tuple is counted as one flow. Per command line options, the order can be
 * displayed as any combination of the source address (s), destination
 * address (d), and protocol (p). Flows will also change with which options
 * are selected.
 * Author: Tim Harmon
 * Date: 10/01/2019
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include <unistd.h>
#include <stdarg.h>
#include <ctype.h>
#include <net/ethernet.h>
#include <linux/ip.h>
#include <linux/ipv6.h>
#include <byteswap.h>
#include <linux/types.h>

/* variable to toggle debug mode */
static bool debug = false;
#define DEBUG_PRINTF(...) if(debug)  printf( __VA_ARGS__)
#define MAX_BYTES (16)
/*
 * ORDER_SIZE is two 128-bit addresses,
 * and 1 byte for each, protocol/version
 */
#define ORDER_SIZE (MAX_BYTES + MAX_BYTES + 2)
#define TABLE_SIZE (64 * 1024)
#define PKT_SIZE (9 * 1024)

/* Global packet header struct for pcap format */
typedef struct pcap_hdr_glbl {
    uint32_t magic_number;
    uint16_t version_major;
    uint16_t version_minor;
    uint32_t  thiszone;
    uint32_t sigfigs;
    uint32_t snaplen;
    uint32_t network;
} pcap_hdr_glbl_t;

/* Common packet header sctruct for pcap format */
typedef struct pcap_pkt_hdr {
    uint32_t time_in_sec;
    uint32_t time_in_usec;
    uint32_t incl_len;
    uint32_t pkt_len;
} pcap_pkt_hdr_t;

/* Struct to hold src and dest IPs, protocol, and version number */
typedef struct tuple_ {
    uint8_t src_addr[MAX_BYTES];
    uint8_t dst_addr[MAX_BYTES];
    uint8_t protocol;
    uint8_t version;
} tuple_t;

/* Struct that will be placed in hash buckets */
typedef struct pkt_node {
    tuple_t *pkt;
    struct pkt_node *hash_next;
    struct pkt_node *hash_prev;
    struct pkt_node *sorted_next;
    struct pkt_node *sorted_prev;
    uint32_t num_pkts;
    uint32_t total_data;
} pkt_node_t;


/* global ("to this file" -prateek) variables */
static pkt_node_t *head_of_sorted;
static pkt_node_t *head_of_sorted_ipv6;
static pkt_node_t *hash_table[TABLE_SIZE];
static int ipv4_size = 0;

/* checks is tuple is same */
static bool tuple_equals_check (tuple_t *tbl_tup, tuple_t *curr_tup)
{
    if (memcmp(tbl_tup->src_addr,
               curr_tup->src_addr,
               sizeof(curr_tup->src_addr)) == 0) {
        if (memcmp(tbl_tup->dst_addr,
                   curr_tup->dst_addr,
                   sizeof(curr_tup->dst_addr)) == 0) {
            if (tbl_tup->protocol == curr_tup->protocol) {
                return true;
            }
        }
    }
    return false;
}

/* Set tuple based on sort order/selected options */
static void set_tuple (const char *options, tuple_t *tuple)
{
    /* if option isn't selected, set value to 0 */
    if (strchr(options, 's') == NULL) {
        memset(tuple->src_addr, 0, sizeof(tuple->src_addr));
    }
    if (strchr(options, 'd') == NULL) {
        memset(tuple->dst_addr, 0, sizeof(tuple->dst_addr));
    }
    if (strchr(options, 'p') == NULL) {
        tuple->protocol = 0;
    }
}

/* hashing key creation function  */
static uint32_t hash_key_creation (tuple_t *tuple)
{
    uint16_t key;
    int i;
    
    key = 0;

    /* calculate key using XOR on each index */
    for (i = 0; i < (MAX_BYTES); i++) {
        key += (tuple->src_addr[i] ^ tuple->dst_addr[i]);
    }
    key ^= tuple->protocol;
    key = key % TABLE_SIZE;
    return key;
}

/* organize the data in sorted order as a bit stream */
static void sort_order (const char *options, tuple_t *tuple,
                        uint8_t *order)
{
    int i;
    int j; /* index for order */
    
    j = 0;
    order[0] = tuple->version;
    if (strcmp(options, "p") == 0) {
        order[0] = 0;
    }
    j++;
    for (i = 0; i < sizeof(options); i++) {
        if (options[i] == 's') {
            memcpy(&order[j], &tuple->src_addr,
                   MAX_BYTES * sizeof(uint8_t));
            j += (MAX_BYTES);
        }
        if (options[i] == 'd') {
            memcpy(&order[j], &tuple->dst_addr,
                   MAX_BYTES * sizeof(uint8_t));
            j += (MAX_BYTES);
        }
        if (options[i] == 'p') {
            order[j] = tuple->protocol;
            j++;
        }
    }
}

/* insert node in sorted order */
static void insert_pkt (pkt_node_t *node_ptr,
                        const char *options)
{
    DEBUG_PRINTF("Reached insert\n");
    pkt_node_t *ptr;
    pkt_node_t *trailer;
    uint8_t order_curr[ORDER_SIZE];
    uint8_t order_ptr[ORDER_SIZE];
    
    memset(order_curr, 0, ORDER_SIZE * sizeof(uint8_t));
    memset(order_ptr, 0, ORDER_SIZE * sizeof(uint8_t));

    if (node_ptr->pkt->version != 6) {
        ptr = *head_of_sorted;
        ipv4_size++;
    } else {
        ptr = *head_of_sorted_ipv6;
    }
    
    /* sort current tuple */
    sort_order(options, node_ptr->pkt, order_curr);

    /* sort head tuple if it exsists */
    if (ptr != NULL) {
        sort_order(options, ptr->pkt, order_ptr);
    }
    /* add node on front of list if less than head or no head exists*/
    if (ptr == NULL ||
        memcmp(order_curr, order_ptr, ORDER_SIZE * sizeof(uint8_t)) <  0) {
        node_ptr->sorted_next = *head_of_sorted;
        *head_of_sorted = node_ptr;
        
    } else {
        /* find insert location */
        while (ptr->sorted_next != NULL) {
            /* check against next node's tuple */
            memset(order_ptr, 0, ORDER_SIZE * sizeof(uint8_t));
            sort_order(options, ptr->sorted_next->pkt, order_ptr);
            if (memcmp(order_curr, order_ptr,
                       ORDER_SIZE * sizeof(uint8_t)) < 0) {
                break;
            }
            ptr = ptr->sorted_next;
        }
        /* insert node */
        node_ptr->sorted_next = ptr->sorted_next;
        node_ptr->sorted_prev = ptr;
        ptr->sorted_next = node_ptr;
        
    }
}

/* function hash tuples */
static void hash_packets (tuple_t *temp_tup, uint32_t data_len,
                          const char *options)
{
    pkt_node_t *ptr;
    pkt_node_t *node;
    tuple_t *node_tup;
    uint16_t index;

    /* Get hash key and set ptr to that index */
    index = hash_key_creation(temp_tup);
    ptr = hash_table[index];

    /* loop through hash bucket until a match is found */
    while(ptr != NULL) {
        if (tuple_equals_check(ptr->pkt, temp_tup)) {
            ptr->num_pkts += 1;
            ptr->total_data += data_len;
            return;
        }
        ptr = ptr->hash_next;
    }
    /* if no match is found, allocate memory and put new node in bucket */
    node_tup = calloc(1, sizeof(tuple_t));
    node = calloc(1, sizeof(pkt_node_t));
    /* memory capacity check */
    if (!node_tup || !node) {
        fprintf(stderr, "Out of memory, can't read more packets");
        return;
    }
    memcpy(node_tup, temp_tup, sizeof(tuple_t));
    node->pkt = node_tup;
    node->total_data = data_len;
    node->num_pkts = 1;
    node->hash_next = hash_table[index];
    hash_table[index] = node;
    insert_pkt(node, options);
    
}

/* free memory no longer in use */
static void free_mem (pkt_node_t *del_node)
{
    pkt_node_t *inter_ptr;
    uint16_t index;

    /* Get hash key and set inter_ptr to that index */
    index = hash_key_creation(del_node->pkt);
    inter_ptr = hash_table[index];

    /* head of bucket replacement */
    if (inter_ptr == del_node) {
        DEBUG_PRINTF("new head of bucket\n");
        hash_table[index] = del_node->hash_next;
        free(del_node);
        return;
    }
    /* find node to be deleted */

    while (inter_ptr != NULL) {
        if (inter_ptr->hash_next == del_node) {
            DEBUG_PRINTF("del node is next\n");
            break;
        }
        inter_ptr = inter_ptr->hash_next;
    }
    if (inter_ptr != NULL) {
        DEBUG_PRINTF("stitch table back together\n");
        inter_ptr->hash_next = del_node->hash_next;
    }
    DEBUG_PRINTF("Freed node\n");
    free(del_node);
}

/* PCAP binary file read function */
static void pcap_file_read (FILE *reader, const char *options)
{
    /* import ehternet/ip structs to help handle packet data */
    struct ether_header ethr_hdr;
    struct iphdr ip_hdr;
    struct ipv6hdr ipv6_hdr;
    pcap_hdr_glbl_t glbl_hdr;
    pcap_pkt_hdr_t pkt_hdr;
    tuple_t tuple;
    long read_len;
    uint32_t data_len;

    /* read in global header */
    if ((fread(&glbl_hdr, sizeof(glbl_hdr), 1, reader)) != 1) {
        fprintf(stderr, "File isn't in pcap format\n");
        return;
    }

    /* check global header for version number and network */
    if (glbl_hdr.network != 1 && glbl_hdr.version_major != 2
        && glbl_hdr.version_minor != 4) {
        fprintf(stderr,
               "File format doesn't appear to be PCAP, exit program\n");
        exit(EXIT_FAILURE);
    }
    /* read each pcap record header */
    while (fread(&pkt_hdr, sizeof(pkt_hdr), 1, reader) == 1) {
        data_len = pkt_hdr.pkt_len;
        /* initialize tuple each time a packet is read in */
        memset(&tuple, 0, sizeof(tuple));
        /* get length of total data read in file */
        read_len = ftell(reader);
        DEBUG_PRINTF("%d\n", pkt_hdr.incl_len);
        /* check for corrupt/garbage data */
        if (pkt_hdr.incl_len > pkt_hdr.pkt_len ||
            pkt_hdr.incl_len > PKT_SIZE) {
            fprintf(stderr, "Corrupt packet, ending file read\n");
            return;
        }
        /* read in ethernet header */
        if (fread(&ethr_hdr, sizeof(ethr_hdr), 1, reader) != 1) {
            return;
        };
            
        /*
         *  check ethernet header -> ethernet type for:
         *  check 0800 for ipv4
         *  check 8100 for ipv4 with vlan tag
         *  check 86dd for ipv6
         */
    IF_VLAN:
        if (ntohs(ethr_hdr.ether_type) == 0x8100) {
            /* Move foreward 2 bytes then get next 2 bytes in ethrhdr */
            fseek(reader, 2, SEEK_CUR);
            if (fread(&ethr_hdr.ether_type, sizeof(ethr_hdr.ether_type),
                      1, reader) != 1) {
                return;
            }
            goto IF_VLAN;
        } else if (ntohs(ethr_hdr.ether_type) == 0x0800) {
            if (fread(&ip_hdr, sizeof(ip_hdr), 1, reader) != 1) {
                return;
            }
            DEBUG_PRINTF("ip: %08x\n", ip_hdr.saddr);
            memcpy(&(tuple.src_addr),
                   &ip_hdr.saddr, sizeof(ip_hdr.saddr));
            memcpy(&(tuple.dst_addr),
                   &ip_hdr.daddr, sizeof(ip_hdr.daddr));
            tuple.protocol = ip_hdr.protocol;
            tuple.version = 4;
        } else if (ntohs(ethr_hdr.ether_type) == 0x86dd) {
            if (fread(&ipv6_hdr, sizeof(ipv6_hdr), 1, reader) != 1) {
                return;
            }
            memcpy(&(tuple.src_addr),
                   &ipv6_hdr.saddr, sizeof(ipv6_hdr.saddr));
            memcpy(&(tuple.dst_addr),
                   &ipv6_hdr.daddr, sizeof(ipv6_hdr.daddr));
            tuple.protocol = ipv6_hdr.nexthdr;
            tuple.version = 6;
        } else {
            DEBUG_PRINTF("Not ip packet\n");
        }
        /* set tuple base on options selected then hash tuple  */
        set_tuple(options, &tuple);
        hash_packets(&tuple, data_len, options);
        fseek(reader, (read_len + pkt_hdr.incl_len), SEEK_SET);
    }
}

/* Fuction to parse a file depending on the format of the input file */
static void parse_args (int argc, char *argv[], FILE **reader,
                        char **options)
{
    char opt_arg;
    char *input_file;
    int opt;

    input_file = NULL;

    /* optional argument parser */
    while ((opt = getopt(argc, argv, "hDf:o:")) != -1) {
        switch (opt) {
            case 'o':
                if (optarg != NULL) {
                    *options = strdup(optarg);
                } else {
                    fprintf(stderr, "No file name provided\n");
                    exit(0);
                }
                DEBUG_PRINTF("output format: %s\n", *options);
                break;
            case 'f':
                if (optarg != NULL) {
                    input_file = strdup(optarg);
                } else {
                    fprintf(stderr, "No options provided\n");
                    exit(0);
                }
                DEBUG_PRINTF("in file: %s\n", input_file);
                break;
            case 'h':
                printf("\n"
                       "    ***********************************\n"
                       "    *         HELP SECTION            *\n"
                       "    *                                 *\n"
                       "    *                                 *\n"
                       "    *   -f argument represents the    *\n"
                       "    *   input file and must be        *\n"
                       "    *   followed by a pcap file name  *\n"
                       "    *                                 *\n"
                       "    *                                 *\n"
                       "    *   -o argument repesents the     *\n"
                       "    *   output format which should    *\n"
                       "    *   be followed by accepted       *\n"
                       "    *   characters for the selected   *\n"
                       "    *   format. Any combination of    *\n"
                       "    *   's','d', and 'p' can be used  *\n"
                       "    *   where s is source ip, d is    *\n"
                       "    *   destination address, and p    *\n"
                       "    *   is protocol. At least one     *\n"
                       "    *   must be provided.             *\n"
                       "    *                                 *\n"
                       "    *                                 *\n"
                       "    ***********************************\n");
                exit(0);
            case 'D':
                debug = true;
                break;
            case ':':
                fprintf(stderr, "Option needs a value\n");
                exit(0);
            case '?':
                fprintf(stderr, "Unknown option: %c\n", optopt);
                exit(0);
        }
    }

    /* Opens file for reading */
    *reader = fopen(input_file,"rb");
    if (*reader == NULL) {
        perror("fopen");
        exit(EXIT_FAILURE);
    }
}

/* Print out sorted data */
static void print_sorted_list (char *options)
{
    pkt_node_t *ptr;
    pkt_node_t *trailer;
    tuple_t *curr_tup;
    int i;
    int flow;
    int tot_pkts;
    int tot_data;
    char option_str[3];
    char src[40];
    char dst[40];
    char prot[6];
    char num_pkts[10];
    char total_data[20];
    char temp_str[5];

    i = 0;
    flow = 0;
    tot_pkts = 0;
    tot_data = 0;
    strcpy(option_str, options);
    ptr = *head_of_sorted;
    
    printf("%-45s%-50s%-11s%-8s%s\n",
           "Source Address", "Destination Address",
           "Protocol", "Found", "Total Data");

    /* print sorted list */
    while (ptr != NULL) {
        curr_tup = ptr->pkt;
        src[0] = '\0';
        dst[0] = '\0';
        prot[0] = '\0';
        num_pkts[0] = '\0';
        total_data[0] = '\0';
        /* check if ipv4, ipv6, or no version */
         if (curr_tup->version == 0 || curr_tup->version == 4) {
            /* check the options and print '*' for options not selected */
            if (strchr(option_str, 's') == NULL) {
                sprintf(src, "***.***.***.***");
            } else {
                /* loop through ip to create ip string */
                for (i = 0; i < (MAX_BYTES / 4); i++) {
                    temp_str[0] = '\0';
                    if (i != ((MAX_BYTES/4)-1)) {
                        sprintf(temp_str, "%d.",
                                ptr->pkt->src_addr[i]);
                    } else {
                        sprintf(temp_str, "%d",
                                ptr->pkt->src_addr[i]);
                    }
                    strcat(src, temp_str);
                    
                }
            }
            if (strchr(option_str, 'd') == NULL) {
                sprintf(dst, "***.***.***.***");
            } else {
                /* loop through ip to create ip string */
                for (i = 0; i < (MAX_BYTES / 4); i++) {
                    temp_str[0] = '\0';
                    if (i != ((MAX_BYTES / 4) -1)) {
                        sprintf(temp_str, "%d.",
                                ptr->pkt->dst_addr[i]);
                    } else {
                        sprintf(temp_str, "%d",
                                ptr->pkt->dst_addr[i]);
                    }
                    strcat(dst, temp_str);
                }
            }
            if (strchr(option_str, 'p') == NULL) {
                sprintf(prot, "***");
            } else {
                sprintf(prot, "%d", ptr->pkt->protocol);
            }
            sprintf(num_pkts, "%d", ptr->num_pkts);
            sprintf(total_data, "%d", ptr->total_data);
            printf("%-45s%-50s%-11s%-8s%-8s\n",
                   src, dst, prot, num_pkts, total_data);
        } else if (curr_tup->version == 6) {
            /* check the options and print '*' for options not selected */
            if (strchr(option_str, 's') == NULL) {
                sprintf(src, "****:****:****:****:****:****:****:****");
            } else {
                /* loop through ip to create ip string */
                for (i = 0; i < MAX_BYTES; i++) {
                    temp_str[0] = '\0';
                    if (i != (MAX_BYTES - 2)) {
                        sprintf(temp_str, "%02x%02x:",
                                ptr->pkt->src_addr[i],
                                ptr->pkt->src_addr[i+1]);
                    } else {
                        sprintf(temp_str, "%02x%02x",
                                ptr->pkt->src_addr[i],
                                ptr->pkt->src_addr[i+1]);
                    }
                    strcat(src, temp_str);
                    i++;
                }
            }
            if (strchr(option_str, 'd') == NULL) {
                sprintf(dst, "****:****:****:****:****:****:****:****");
            } else {
                /* loop through ip to create ip string */
                for (i = 0; i < MAX_BYTES; i++) {
                    temp_str[0] = '\0';
                    if (i != (MAX_BYTES - 2)) {
                        sprintf(temp_str, "%02x%02x:",
                                ptr->pkt->dst_addr[i],
                                ptr->pkt->dst_addr[i+1]);
                    } else {
                        sprintf(temp_str, "%02x%02x",
                                ptr->pkt->dst_addr[i],
                                ptr->pkt->dst_addr[i+1]);
                    }
                    strcat(dst, temp_str);
                    i++;
                }
            }
            if (strchr(option_str, 'p') == NULL) {
                sprintf(prot, "***");
            } else {
                sprintf(prot, "%d", ptr->pkt->protocol);
            }
            sprintf(num_pkts, "%d", ptr->num_pkts);
            sprintf(total_data, "%d", ptr->total_data);
            printf("%-45s%-50s%-11s%-8s%-8s\n",
                   src, dst, prot, num_pkts, total_data);
         }
        /*  add up flows, total packets processed, total data processed */
        flow++;
        tot_pkts += ptr->num_pkts;
        tot_data += ptr->total_data;
        trailer = ptr;
        ptr = ptr->sorted_next;
        /* free memory and keep hash table in tact*/
        free_mem(trailer);
    }

    printf("Number of flows: %d\n", flow);
    printf("Number of packets processed: %d\n", tot_pkts);
    printf("Total data processed: %d\n", tot_data);
}

/*
 * Main Working Flow:
 * 1. Parse command line args
 * 2. Read through and exract data from file
 * 3. Print exracted data in sorted order
 */
int main (int argc, char *argv[])
{
    FILE *reader;
    char *options;
    
    ipv4_size = 0;
    memset(hash_table, 0, sizeof(pkt_node_t *) * TABLE_SIZE);
    head_of_sorted = NULL;
    options = NULL;

    parse_args(argc, argv, &reader, &options);
    pcap_file_read(reader, options);
    print_sorted_list(options);
    fclose(reader);
}
