#include <sys/socket.h>
#include <sys/select.h>
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>

#include "../../../shim.h"

extern void* initialstate$1(void*, void*);
extern void* handleinput$5(void*, void*);
extern void* handlemsg$6(void*, void*);


#define NHOSTS 2

static char* hosts[NHOSTS] = {"localhost", "localhost"};
static int ports[NHOSTS] = {8001, 8002};
static struct sockaddr_in addrs[NHOSTS]; 

void send_msgs(int sock, union list* msgs) {
    char buf[BUFSIZ];

    while (msgs->tag == 1) {
        union pair* packet = msgs->cons.data;
        union bool* dest = packet->pair.left;
        union bool* payload = packet->pair.right;
            
        bzero(buf, BUFSIZ);
        buf[0] = read_bool(payload);
        log_info("sending msg %d", buf[0]);

        int n = sendto(sock, buf, 1, 0, 
                   (struct sockaddr*) &addrs[read_bool(dest)], 
                   sizeof(addrs[read_bool(dest)]));
        if (n < 0) { log_info("sendto failed; ignoring..."); continue; }
                       
        msgs = msgs->cons.next;
    }
}


int main(int argc, char** argv) {
    if (argc != 2) { 
        printf("Usage: %s <MYNAME>\n", argv[0]);
        goto error;
    }

    int my_name;
    sscanf(argv[1], "%d", &my_name);
    union bool* my_nameb = make_bool(my_name);

    int i;
    for (i = 0; i < NHOSTS; i++) {
        if (i == my_name) continue;
        struct hostent *hent = gethostbyname(hosts[i]);
        check(hent != NULL, "gethostbyname failed on host %d: %s", i, hosts[i]);
        bzero((char *) &addrs[i], sizeof(addrs[i]));
        addrs[i].sin_family = AF_INET;
        bcopy((char *)hent->h_addr, 
              (char *)&addrs[i].sin_addr.s_addr, hent->h_length);
        addrs[i].sin_port = htons(ports[i]);
    }
    
    int sock = socket(AF_INET, SOCK_DGRAM, 0);
    check (sock >= 0, "socket");

    int optval = 1;
    setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, 
               (const void *)&optval , sizeof(int));

    struct sockaddr_in serveraddr;
    bzero((char *) &serveraddr, sizeof(serveraddr));
    serveraddr.sin_family = AF_INET;
    serveraddr.sin_addr.s_addr = htonl(INADDR_ANY);
    serveraddr.sin_port = htons((unsigned short)ports[my_name]);

    int res = bind(sock, (struct sockaddr *) &serveraddr, sizeof(serveraddr));
    check(res == 0, "bind");

    void* initialstate = initialstate$1(NULL, NULL);
    void* handleinput = handleinput$5(NULL, NULL);
    void* handlemsg = handlemsg$6(NULL, NULL);

    void* state = initialstate;

    char buf[BUFSIZ];
    struct sockaddr_in clientaddr;
    socklen_t clientlen = sizeof(clientaddr);
    int n;

    fd_set fds, read_fds;
    FD_ZERO(&fds);
    FD_SET(sock, &fds);
    FD_SET(0, &fds);

    log_info("entering event loop...");

    while (1) {
        read_fds = fds;
        res = select(FD_SETSIZE, &read_fds, NULL, NULL, NULL);
        check(res >= 0, "select");

        log_info("select returned!");

        int i;
        for (i = 0; i < FD_SETSIZE; i++) {
            if (FD_ISSET (i, &read_fds)) {
                if (i == sock) {
                    bzero(buf, BUFSIZ);
                    n = recvfrom(sock, buf, BUFSIZ, 0, (struct sockaddr*) &clientaddr, &clientlen);
                    if (n < 0) { log_info("recvfrom failed; ignoring..."); continue; }

                    if (n == 0) { log_info("received 0 length msg; ignoring..."); continue; }
        
                    union bool* msg = make_bool(buf[0] & 1);

                    log_info("got msg %d", read_bool(msg));

                    union pair* result = vcall(handlemsg, my_nameb, msg, state, NULL);

                    state = result->pair.left;
                    send_msgs(sock, result->pair.right);
                } else {
                    check(i == 0, "select returned unknown socket");
                    int input; 
                    scanf("%d", &input);  // bogus
                    
                    log_info("got input!");

                    union pair* result = vcall(handleinput, my_nameb, make_unit(), state, NULL);

                    state = result->pair.left;
                    send_msgs(sock, result->pair.right);
                }
            }
        }
    }

    return 0;
 error:
    return 1;
}

