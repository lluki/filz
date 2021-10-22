/*
 * Shows the equivalence of Trans+Byte+Symbol+El and TransAbs
 */
#include "common.xp"
#include "eep.pml"
#include "i2c-spec.pml"

#if ABS_LEVEL >= 3
    #error "Makes no sense with this ABS_LEVEL"
#endif

init {
    TransactionRun();
    run verifier();
}

proctype verifier()
{
    /* the abstract channels */
    chan abs_m_out = [0] of {int,int,intarr};
    chan abs_m_in  = [0] of {int,int,int,intarr};
    chan abs_s_out = [0] of {int,int};
    chan abs_s_in  = [0] of {int,int};

    /* upstream channels */
    chan hlm_in  = [0] of {int,int,intarr};
    chan hlm_out = [0] of {int,int,int,intarr};
    chan hls_in  = [0] of {int,int};
    chan hls_out = [0] of {int,int};

    run TransactionAbs(abs_m_in, abs_m_out, abs_s_in, abs_s_out);

    /* the concrete channels, hard-named in i2c.pml */
    #define conc_m_out controller_Hl_in
    #define conc_m_in  controller_Hl_out
    #define conc_s_out responder_Hl_in
    #define conc_s_in  responder_Hl_out


    run HlValid(hlm_in, hlm_out, hls_in, hls_out);

    // The verification is driven by the abstract model, 
    // that is we first observe an event there, then we ensure
    // the same event happens in the concrete model. If that's the case,
    // we forward it to Transaction valid, which produces all valid
    // sequences of the transaction layer
    int a, b, d, a1, b1, d1;
    intarr c, c1;
progress:
    do
    :: abs_m_out?a,b,c;
       printf("m_out  %d,%d,...\n", a, b);
       conc_m_out?a1,b1, c1;
       if
       :: a != a1 || b != b1 || ARR_NEQ(c,c1)  ->
          printf("abs_m_out %d,%d,...   conc_m_out %d,%d,...\n", a,b, a1, b1);
          printf("abs:\n");
          ARR_PRINT(c);
          printf("conc:\n");
          ARR_PRINT(c1);
          false;
       :: else -> skip;
       fi
       hlm_in!a,b,c;

    :: abs_s_out?a,b;
       printf("s_out  %d,%d\n", a, b);
       conc_s_out?a1,b1;
       if
       :: a != a1 || b != b1 ->
          printf("abs_s_out %d,%d   conc_s_out %d,%d\n", a, b, a1, b1);
          false;
       :: else -> skip;
       fi
       hls_in!a,b;

    :: hlm_out?a,b,d,c;
       printf("m_in  %d,%d,%d,...\n", a, b, d);
       abs_m_in!a,b,d,c; 
       conc_m_in!a,b,d,c;

    :: hls_out?a,b;
       printf("s_in %d, %d\n", a, b);
       abs_s_in!a,b; 
       conc_s_in!a,b; 

    od
}

/*
 * All valid actions of the HL Layer
 */ 
proctype HlValid(chan m_in; chan m_out; chan s_in; chan s_out) {
    intarr in_dat;
    intarr out_dat;

    int expected_mres;
    int extra_sres;
    int write_len;
    int read_pos;
    int read_len;
    int write_pos;

    expected_mres = TR_RES_OK;
    extra_sres = HLS_RES_IDLE;
    

start:
    if
    :: goto master_write;
    :: goto master_read;
    fi

stop_or_restart:
    if
    :: true -> //Restart
        extra_sres = -1;
        goto start;
    :: true -> //Stop, followed by Start
        m_in?TR_RES_OK, 0, in_dat;
        // ONLY WHEN master_read: in_dat.arr[0] == 0; // TODO verify data when
        m_out!TR_ACT_STOP,0,0,out_dat;
        extra_sres = HLS_RES_STOP;
        goto start;
    fi

master_write:
    printf("requesting write transaction\n");
    select(write_len : 1..4);
    m_in?eval(expected_mres), 0, in_dat;
    out_dat.arr[0] = 23;
    out_dat.arr[1] = 19;
    out_dat.arr[2] = 14;
    out_dat.arr[3] = 18;
    m_out!TR_ACT_WRITE,EEPROM_ADDR,write_len,out_dat;  

    printf("W1!\n");

    if
    :: extra_sres == -1 -> skip;
    :: extra_sres == HLS_RES_IDLE ->
        s_in?HLS_RES_IDLE,0;
        s_out!HLS_ACT_IDLE,0;
    :: extra_sres == HLS_RES_STOP ->
        s_in?HLS_RES_STOP,0;
        s_out!HLS_ACT_IDLE,0;
    fi

    printf("W2!\n");

    s_in?HLS_RES_START, 0;
    s_out!HLS_ACT_IDLE, 0;

    printf("W3!\n");
    read_pos = 0;
    do
    :: read_pos < write_len ->
        /* no need to check READ result */
        s_in?HLS_RES_WRITE, _;
        s_out!HLS_ACT_ACK,0;
        printf("H1\n");
        read_pos = read_pos + 1;
    :: else -> break
    od

    printf("master_write finished yeah!\n");
    extra_sres = -1;
    goto stop_or_restart;

master_read:
    printf("requesting read transaction\n");
    m_in?eval(expected_mres),0,in_dat;
    select( read_len : 1 .. 4);
    printf("read_len = %d\n", read_len);
    m_out!TR_ACT_READ,EEPROM_ADDR,read_len,out_dat;  

    printf("R1!\n");

    if
    :: extra_sres == -1 -> skip;
    :: extra_sres == HLS_RES_IDLE ->
        s_in?HLS_RES_IDLE,0;
        s_out!HLS_ACT_IDLE,0;
    :: extra_sres == HLS_RES_STOP ->
        s_in?HLS_RES_STOP,0;
        s_out!HLS_ACT_IDLE,0;
    fi

    printf("R2!\n");

    s_in?HLS_RES_START, 0;
    s_out!HLS_ACT_IDLE, 0;

    printf("R3!\n");
    write_pos = 0;
    do
    :: write_pos < read_len ->
        s_in?HLS_RES_READ, 0;
        s_out!HLS_ACT_WRITE,15;
        write_pos = write_pos + 1;
    :: else -> break;
    od

    printf("master_read finished yeah!\n");
    extra_sres = -1;
    goto stop_or_restart;
    
}

