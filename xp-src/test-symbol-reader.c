#include <stdio.h>
#include "i2c-test-symbol-reader.h"

#define BYTE_ACT_START  11
#define BYTE_ACT_STOP   12
#define BYTE_ACT_WRITE  13
#define BYTE_ACT_READ   14

#define SYM_START 23
#define SYM_STOP  24
#define SYM_BIT0  25
#define SYM_BIT1  26
#define SYM_IDLE  27

#define RES_OK 1
#define RES_FAIL 2

char * fmt_sym(int sym){
    switch(sym) {
        case SYM_START:
            return "Start";
            break;
        case SYM_STOP:
            return "Stop";
            break;
        case SYM_BIT0:
            return "BIT0";
            break;
        case SYM_BIT1:
            return "BIT1";
            break;
        case SYM_IDLE:
            return "IDLE";
            break;
        default:
            printf("Unknown sym format request? %d\n", sym);
            return "INVALID";
            break;
    }
}

void ByteMaster(int sym, int *out){
    printf("%s recv --> ", fmt_sym(sym));
    ByteMasterStub(sym, out);
    printf("%s\n", fmt_sym(*out));
}

int main() {
    printf("SCL:SDA\n");
    int scl=1, sda=1;
    for(int i=0;i<100;i++){
        MasterDriver(scl, sda, &scl, &sda);
        printf("%d:%d\n",scl,sda);
    }
}
