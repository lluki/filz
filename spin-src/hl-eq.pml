/*
 * Shows the equivalence of Hl+Trans+Byte+Symbol+El and HlAbs
 */

#include "common.xp"
#include "eep.pml"
#include "i2c-spec.pml"

#if ABS_LEVEL >= 4
    #error "Makes no sense with this ABS_LEVEL"
#endif

init {
    HlRun();
    run verifier();
}

proctype verifier() {
    /* the abstract channels */
    chan abs_m_out = [0] of {int,intarr};
    chan abs_m_in  = [0] of {int,int,int,intarr};
    chan abs_s_out = [0] of {int,int,int,intarr};
    chan abs_s_in  = [0] of {int,int,intarr};

    /* upstream channels */
    chan eepm_in  = [0] of {int,intarr};
    chan eepm_out = [0] of {int,int,int,intarr};

    chan eeps_in  = [0] of {int,int,int,intarr};
    chan eeps_out = [0] of {int,int,intarr};

    /* the concrete channels, hard-named in i2c.pml */
    #define conc_m_out controller_Eep_in
    #define conc_m_in  controller_Eep_out
    #define conc_s_out responder_Eep_in 
    #define conc_s_in  responder_Eep_out 

    run HlAbs(abs_m_in, abs_m_out, abs_s_in, abs_s_out);
    run EepValid(eepm_in, eepm_out, eeps_in, eeps_out);

    int a, b, c, a1, b1, c1;
    intarr d, d1;
    
progress:
    do
    ::  abs_m_out?a,d;
        conc_m_out?a1,d1;
        if
        :: a != a1 || ARR_NEQ(d,d1) -> 
             printf("abs_m_out %d,...  conc_m_out %d,...\n", a, a1);
             false;
        :: else ->skip;
        fi
        eepm_in!a1,d1;

    ::  abs_s_out?a,b,c,d;
        conc_s_out?a1,b1,c1,d1;
        if
        :: a != a1 || b != b1 || c != c1 || ARR_NEQ(d,d1) ->
           printf("abs_s_out %d,%d,%d,...   conc_s_out %d,%d,%d,...\n",
             a,b,c,a1,b1,c1);
            printf("d\n");
            ARR_PRINT(d);
            printf("d1\n");
            ARR_PRINT(d1);
        :: else -> skip;
        fi
        eeps_in!a1,b1,c1,d1;

    ::  eepm_out?a,b,c,d;
        printf("m_in %d,%d,%d,...\n", a,b,c);
        abs_m_in!a,b,c,d;
        conc_m_in!a,b,c,d;

    ::  eeps_out?a,b,d;
        printf("s_in %d,%d,...\n", a,b,c);
        abs_s_in!a,b,d;
        conc_s_in!a,b,d;
    od
}

#ifndef MASTER_WRITE_START
#define MASTER_WRITE_START 6
#endif

#ifndef MASTER_WRITE_LEN
#define MASTER_WRITE_LEN 4
#endif

#ifndef MASTER_READ_START
#define MASTER_READ_START 6
#endif

#ifndef MASTER_READ_LEN
#define MASTER_READ_LEN 4
#endif

proctype EepValid(chan m_in; chan m_out; chan s_in; chan s_out) {
    intarr dat;
    intarr null_dat;

    intarr dat_master_send;
    intarr dat_master_send_prev;

    intarr dat2;
    int me_res;

    me_res = ME_RES_IDLE;

    int m_act;
    int delay_s_write_res = false;

start:
    if
    :: true -> 
        printf("Master Write\n");
        m_in?eval(me_res), dat;

        ARR_ASSIGN(dat_master_send_prev, dat_master_send);
        if
        :: dat_master_send.arr[0] = 4;
        :: dat_master_send.arr[0] = 5;
        :: dat_master_send.arr[0] = 6;
        fi
        dat_master_send.arr[1] = 1;
        dat_master_send.arr[2] = 2;
        dat_master_send.arr[3] = 3;

        m_out!ME_ACT_WRITE_EEPROM,MASTER_WRITE_START,MASTER_WRITE_LEN,dat_master_send;
        m_act = ME_ACT_WRITE_EEPROM;

    :: true -> 
        printf("Master Read\n");
        m_in?eval(me_res), dat;
        m_out!ME_ACT_READ_EEPROM,MASTER_READ_START,MASTER_READ_LEN,null_dat;
        m_act = ME_ACT_READ_EEPROM;
    fi

    // handle delayed s_write_res
    if 
    :: delay_s_write_res ->
        s_in?SE_RES_WRITE,MASTER_WRITE_START,MASTER_WRITE_LEN,dat2;
        // equivalence check in verifier, no need here 
        s_out!SE_ACT_OK, 0, null_dat;
        delay_s_write_res = false;
    :: else -> skip
    fi

    int a,b;
    if
    :: m_act == ME_ACT_WRITE_EEPROM ->
        delay_s_write_res = true;
        me_res = ME_RES_OK;

    :: m_act == ME_ACT_READ_EEPROM ->
        s_in?SE_RES_READ,a,b,dat2;
        // equivalence check in verifier, no need here 
        s_out!SE_ACT_OK, 0, dat;
        me_res = ME_RES_OK;
    fi
    
    goto start;
}


