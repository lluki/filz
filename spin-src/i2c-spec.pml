/* specifications of the machines */

/*
 *  ABS_LEVEL configures at which layer in the stack we replace
 *  implementation with the abstract machines.
 *  ABS_LEVEL = 0 -> No abstraction (run down to EL)
 *  ABS_LEVEL = 1 -> abstract at symbol level (runs SymbolAbs)
 *  ABS_LEVEL = 2 -> abstract at byte level (runs ByteAbs)
 *  ABS_LEVEL = 3 -> abstract at transaction level (runs trans act)
 *  ABS_LEVEL = 4 -> abstract at HL LEVEL

 *
 *  For excluding the standard I2C specifications, the following defines
 *  are considered:
 *  SKIP_DEFAULT_BYTE
 * 
 */
#if !defined(ABS_LEVEL) || ABS_LEVEL < 0 || ABS_LEVEL > 4 
    #error "ABS_LEVEL must be >= 0 and <= 4"
#endif

#if ABS_LEVEL >= 1
#define SymbolRun() run Sym_abs_run()
#else
#define SymbolRun() run Sym_conc_run(); run El_conc_run()
#endif 

#if ABS_LEVEL >= 2
#define ByteRun() run Byte_abs_run()
#else
#define ByteRun() run Byte_conc_run(); SymbolRun()
#endif 

#if ABS_LEVEL >= 3
#define TransactionRun() run Tr_abs_run()
#else
#define TransactionRun() run Tr_conc_run(); ByteRun()
#endif 

#if ABS_LEVEL >= 4
#define HlRun() run HlAbsRun();
#else
#define HlRun() run Hl_conc_run(); TransactionRun()
#endif 

proctype ElBus1(chan p1_in; chan p1_out) {
    int scl, sda, scl1, sda1; 
    scl = 1;
    sda = 1;
start:
    p1_in!scl,sda;
    p1_out?scl,sda;
    goto start; 
}

proctype ElBus2(chan p1_in; chan p1_out; chan p2_in; chan p2_out) {
    int scl, sda, scl1, sda1, scl2, sda2; 
    scl = 1;
    sda = 1;
start:
    p1_in!scl,sda;
    p1_out?scl1,sda1;
    p2_in!scl,sda;
    p2_out?scl2,sda2;

    if
    :: scl1 == 0 || scl2 == 0 -> scl = 0;
    :: else -> scl = 1;
    fi

    if
    :: sda1 == 0 || sda2 == 0 -> sda = 0;
    :: else -> sda = 1;
    fi
    
    goto start; 
}

proctype ElBus3(chan p1_in; chan p1_out; chan p2_in; chan p2_out; chan p3_in; chan p3_out) {
    int scl, sda, scl1, sda1, scl2, sda2, scl3, sda3; 
    scl = 1;
    sda = 1;
start:
    p1_in!scl,sda;
    p1_out?scl1,sda1;
    p2_in!scl,sda;
    p2_out?scl2,sda2;
    p3_in!scl,sda;
    p3_out?scl3,sda3;

    if
    :: scl1 == 0 || scl2 == 0 || scl3 == 0 -> scl = 0;
    :: else -> scl = 1;
    fi

    if
    :: sda1 == 0 || sda2 == 0 || sda3 == 0 -> sda = 0;
    :: else -> sda = 1;
    fi
    
    goto start; 
}

proctype ElBus4(chan p1_in; chan p1_out; chan p2_in; chan p2_out; chan p3_in; chan p3_out; chan p4_in; chan p4_out) {
    int scl, sda, scl1, sda1, scl2, sda2, scl3, sda3, scl4, sda4; 
    scl = 1;
    sda = 1;
start:
    p1_in!scl,sda;
    p1_out?scl1,sda1;
    p2_in!scl,sda;
    p2_out?scl2,sda2;
    p3_in!scl,sda;
    p3_out?scl3,sda3;
    p3_in!scl,sda;
    p3_out?scl4,sda4;

    if
    :: scl1 == 0 || scl2 == 0 || scl3 == 0 || scl4 == 0 -> scl = 0;
    :: else -> scl = 1;
    fi

    if
    :: sda1 == 0 || sda2 == 0 || sda3 == 0 || sda4 == 0 -> sda = 0;
    :: else -> sda = 1;
    fi
    
    goto start; 
}









#ifndef SKIP_DEFAULT_SYM
/*
 * Run SymbolAbs in place of the actual EL machines
 */
proctype Sym_abs_run(){
    run SymbolAbs(controller_Byte_out, responder_Byte_out, controller_Byte_in, responder_Byte_in);
}
/*
 * The symbol layer specification
 */
proctype SymbolAbs(chan in1; chan in2; chan out1; chan out2)
{
    int sin1;
    int sin2;
    int sout;

    sout = SYM_IDLE;

next_sym:
    out1!sout;
read1:
    in1?sin1;
    if 
    :: sin1 == SYM_STRETCH -> out1!SYM_STRETCH; goto read1;
    :: else -> skip
    fi
 
    out2!sout;
read2:
    in2?sin2;
    if 
    :: sin2 == SYM_STRETCH -> out2!SYM_STRETCH; goto read2;
    :: else -> skip
    fi

    printf("SymbolAbs: sin1=%d  sin2=%d\n", sin1, sin2);
    if 
    :: sin1 == SYM_START && sin2 == SYM_IDLE  ; sout = SYM_START
    :: sin1 == SYM_IDLE  && sin2 == SYM_START ; sout = SYM_START
    :: sin1 == SYM_STOP  && sin2 == SYM_IDLE  ; sout = SYM_STOP
    :: sin1 == SYM_IDLE  && sin2 == SYM_STOP  ; sout = SYM_STOP
    :: sin1 == SYM_IDLE  && sin2 == SYM_IDLE  ; sout = SYM_IDLE

    :: sin1 == SYM_START && sin2 == SYM_BIT1  ; sout = SYM_START
    :: sin1 == SYM_BIT1  && sin2 == SYM_START  ; sout = SYM_START

    :: sin1 == SYM_START && sin2 == SYM_BIT0  ; sout = SYM_BIT0
    :: sin1 == SYM_BIT0 && sin2 == SYM_START  ; sout = SYM_BIT0

    :: sin1 == SYM_BIT1 && sin2 == SYM_BIT0 ; sout = SYM_BIT0;
    :: sin1 == SYM_BIT0 && sin2 == SYM_BIT1 ; sout = SYM_BIT0;
    :: sin1 == SYM_BIT0 && sin2 == SYM_BIT0 ; sout = SYM_BIT0;
    :: sin1 == SYM_BIT1 && sin2 == SYM_BIT1 ; sout = SYM_BIT1;

    :: sin1 == SYM_STOP && sin2 == SYM_BIT1 ; sout = SYM_STOP;
    :: sin1 == SYM_BIT1 && sin2 == SYM_STOP ; sout = SYM_STOP;

    :: else -> printf("Unkown combination %d %d", sin1, sin2); false;
    fi

    printf("SymbolAbs: sout=%d\n", sout);

    goto next_sym;
}
#endif /* SKIP_DEFAULT_SYM */

#ifndef SKIP_DEFAULT_BYTE
proctype Byte_abs_run() {
    run ByteAbs(controller_Tr_out, controller_Tr_in,
        responder_Tr_out, responder_Tr_in);
}
/*
 * The byte layer specification
 */
proctype ByteAbs(chan master_in; chan master_out; chan slave_in; chan slave_out){
    int mout;
    int mout_d;
    int sout;
    int sout_d;
    int mact;
    int mact_d;
    int sact;
    int sact_d;

    mout = BYTE_RES_IDLE;
    sout = BYTE_RES_IDLE;
 
begin:
    master_out!mout, 0;
    master_in?mact,mact_d;
    
    slave_out!sout, 0;
    slave_in?sact,sact_d;

    if 
    :: mact == BYTE_ACT_IDLE && sact == BYTE_ACT_IDLE;
       goto begin; 
    :: mact == BYTE_ACT_START && sact == BYTE_ACT_IDLE;
       mout = BYTE_RES_START; mout_d = 0;
       sout = BYTE_RES_START; sout_d = 0;
       goto in_trans; 
    fi

in_trans:
    master_out!mout, mout_d;
    master_in?mact, mact_d;
    
    slave_out!sout, sout_d;
    slave_in?sact, sact_d;

    if
    // Master write, Slave read
    :: mact == BYTE_ACT_WRITE && sact == BYTE_ACT_READ;
       slave_out!BYTE_RES_READ,mact_d; 
       if
       :: slave_in?BYTE_ACT_ACK,0 ->
             mout = BYTE_RES_ACK;
             mout_d = 0;
             sout = BYTE_RES_ACK;
             sout_d = 0;
             goto in_trans;
       :: slave_in?BYTE_ACT_NACK,0 ->
             mout = BYTE_RES_NACK;
             mout_d = 0;
             sout = BYTE_RES_NACK;
             sout_d = 0;
             goto in_trans;
       fi

    // Master read, Slave write
    :: mact == BYTE_ACT_READ && sact == BYTE_ACT_WRITE;
       master_out!BYTE_RES_READ,sact_d; 
       if
       :: master_in?BYTE_ACT_ACK,0 ->
             sout = BYTE_RES_ACK;
             sout_d = 0;
             mout = BYTE_RES_ACK;
             mout_d = 0;
             goto in_trans;
       :: master_in?BYTE_ACT_NACK,0 ->
             sout = BYTE_RES_NACK;
             sout_d = 0;
             mout = BYTE_RES_NACK;
             mout_d = 0;
             goto in_trans;
       fi

    // Master repeated start, slave read
    :: mact == BYTE_ACT_START && (sact == BYTE_ACT_READ || sact == BYTE_ACT_IDLE);
       mout = BYTE_RES_START; mout_d = 0; sout = BYTE_RES_START; sout_d = 0; 
       goto in_trans;

    :: mact == BYTE_ACT_STOP && (sact == BYTE_ACT_READ || sact == BYTE_ACT_IDLE);
       mout = BYTE_RES_STOP; mout_d = 0; sout = BYTE_RES_STOP; sout_d = 0; 
       goto begin;

    :: else ->
        printf("Unknown combo mact=%d  sact=%d\n", mact, sact);
        false;
    fi
}
#endif


#ifndef SKIP_DEFAULT_TR
/*
 * Specification (expected behaviour) of the Transaction Layer
 */
#define TRABS_DEBUG(...) 
//#define TRABS_DEBUG printf
proctype Tr_abs_run() {
    run TransactionAbs(controller_Hl_out, controller_Hl_in, responder_Hl_out, responder_Hl_in);
}
proctype TransactionAbs(chan m_in; chan m_out; chan s_in; chan s_out) {
    intarr out_dat;
    intarr res_dat;
    intarr null_dat;

    int out_dat_len;
    int out_dat_pos;

    int dat;
    int act;

    // extra_sres encodes an extra slave res to be delivered
    // HLS_RES_IDLE  -> Expect an extra RES_IDLE, happens the first iteration
    // HLS_RES_STOP  -> Expect an extra STOP, happens when the master delivers a STOP
    // -1            -> No extra expected
    int extra_sres;
    extra_sres = HLS_RES_IDLE;

begin:
    m_out!TR_RES_OK,0, res_dat;
    
    if
    :: m_in?TR_ACT_WRITE,EEPROM_ADDR,out_dat_len,out_dat -> goto master_write
    :: m_in?TR_ACT_READ, EEPROM_ADDR,out_dat_len,ARR_DONT_CARE -> goto master_read;
    :: m_in?TR_ACT_STOP,_,_,ARR_DONT_CARE -> goto master_stop;
    fi

master_stop:
    TRABS_DEBUG("ABS STOP\n");
    extra_sres = HLS_RES_STOP;
    goto begin;

master_write:
    TRABS_DEBUG("ABS WRITE\n");
    if
    :: extra_sres == HLS_RES_IDLE -> 
        s_out!HLS_RES_IDLE,0;
        s_in?HLS_ACT_IDLE,0;
    :: extra_sres == HLS_RES_STOP ->
        s_out!HLS_RES_STOP,0;
        s_in?HLS_ACT_IDLE,0;
    :: extra_sres == -1 -> skip
    fi

    s_out!HLS_RES_START,0;
    s_in?HLS_ACT_IDLE,0;


    out_dat_pos = 0;
    do
    :: out_dat_pos < out_dat_len ->
        TRABS_DEBUG("sending out_dat_pos=%d\n", out_dat_pos);
        s_out!HLS_RES_WRITE,out_dat.arr[out_dat_pos];

        if
        :: s_in?HLS_ACT_ACK,0 -> skip;
        :: s_in?HLS_ACT_NACK,0 -> TRABS_DEBUG("NACK\n"); break;
        fi

        out_dat_pos = out_dat_pos + 1; 
    :: else -> break;
    od

    ARR_SET_NULL(out_dat);

    extra_sres = -1;
    goto begin;

master_read:
    TRABS_DEBUG("ABS READ\n");
    if
    :: extra_sres == HLS_RES_IDLE -> 
        s_out!HLS_RES_IDLE,0;
        s_in?HLS_ACT_IDLE,0;
    :: extra_sres == HLS_RES_STOP ->
        s_out!HLS_RES_STOP,0;
        s_in?HLS_ACT_IDLE,0;
    :: extra_sres == -1 -> skip
    fi

    s_out!HLS_RES_START,0;
    s_in?HLS_ACT_IDLE,0;

    out_dat_pos = 0;
    do
    :: out_dat_pos < out_dat_len; 
        s_out!HLS_RES_READ,0;
        s_in?HLS_ACT_WRITE,dat;
        printf("[%d] = %d\n", out_dat_pos, dat);
        res_dat.arr[out_dat_pos] = dat;
        out_dat_pos = out_dat_pos + 1;
    :: else -> break
    od

    extra_sres = -1;
    goto begin;
}
#endif


#ifndef SKIP_DEFAULT_HL
proctype Hl_abs_run() {
    run HlAbs(controller_Eep_out, controller_Eep_in, responder_Eep_out, 
            responder_Eep_in);
}
/* HlAbs */
// The synchronous pattern of events
// is as follows, read from left to right:

// Master write only:     
// MW----\                
// MW-\  SW               
// MW SW                  
// ...                    

//Master read only:
//MR   SR
//MR   SR
//MR   SR                 
//...                     

//The combined pattern is as follows
// MW---\
// MR   SW   SR
// MW---\    SR
// MR   SW   SR

proctype HlAbs(chan m_in; chan m_out; chan s_in; chan s_out) {
    intarr dat;
    int m_act;
    int m_addr;
    int m_dat_len;
    intarr m_dat;
    intarr null_dat;

    intarr delay_dat;
    int delay_addr;
    int delay_dat_len;

    int m_res;
    m_res = ME_RES_IDLE;

    bool delay_s_write_res = false;

start:
    m_out!m_res, dat;
    m_in?m_act, m_addr, m_dat_len, m_dat;

    if
    :: delay_s_write_res -> 
       printf("ABS: Sending slave delayed RES_WRITE\n");
       s_out!SE_RES_WRITE, delay_addr, delay_dat_len, delay_dat;
       s_in?SE_ACT_OK, 0, ARR_DONT_CARE;
       delay_s_write_res = false;
    :: else -> skip
    fi

    if
    :: m_act == ME_ACT_WRITE_EEPROM -> goto write;
    :: m_act == ME_ACT_READ_EEPROM -> goto read;
    fi

write:
   delay_s_write_res = true;

   ARR_ASSIGN(delay_dat, m_dat);
   delay_dat_len = 4; // impl currently always requests 4 bytes from EEP
   delay_addr = m_addr;
   printf("delay  dat_len=%d,  addr=%d\n", delay_dat_len, delay_addr);

   m_res = ME_RES_OK;
   goto start;

read:
    printf("ABS: read request\n");
    s_out!SE_RES_READ, m_addr, 4, m_dat;   
    s_in?SE_ACT_OK, 0, ARR_DONT_CARE;

    m_res = ME_RES_OK;
    goto start;
}
#endif
