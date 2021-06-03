/*  filz - a model checked I2C specification 
 *  copyright (c) 2021, ETH Zurich, Systems Group
 *
 *  this program is free software: you can redistribute it and/or modify
 *  it under the terms of the gnu general public license as published by
 *  the free software foundation, either version 3 of the license, or
 *  (at your option) any later version.
 *
 *  this program is distributed in the hope that it will be useful,
 *  but without any warranty; without even the implied warranty of
 *  merchantability or fitness for a particular purpose.  see the
 *  gnu general public license for more details.
 *
 *  you should have received a copy of the gnu general public license
 *  along with this program.  if not, see <https://www.gnu.org/licenses/>.
 */

/*
 * Shows the equivalence of Byte+Symbol+El and ByteAbs
 */
#include "i2c-spec.pml"

#if ABS_LEVEL >= 2
    #error "Makes no sense with this ABS_LEVEL"
#endif


init {
    run ByteRun();
    run verifier();
}

proctype verifier() {
    /* the abstract channels */
    chan abs_m_out = [0] of {int,int};
    chan abs_m_in  = [0] of {int,int};
    chan abs_s_out = [0] of {int,int};
    chan abs_s_in  = [0] of {int,int};

    /* upstream channels */
    chan transm_in  = [0] of {int,int};
    chan transm_out = [0] of {int,int};
    chan transs_in  = [0] of {int,int};
    chan transs_out = [0] of {int,int};

    run ByteAbs(abs_m_in, abs_m_out, abs_s_in, abs_s_out);


    /* the concrete channels, hard-named in i2c.pml */
    #define conc_m_out TransactionMaster_in
    #define conc_m_in  TransactionMaster_out
    #define conc_s_out TransactionSlave_in
    #define conc_s_in  TransactionSlave_out


    run TransactionValid(transm_in, transm_out, transs_in, transs_out);


    // The verification is driven by the abstract model, 
    // that is we first observe an event there, then we ensure
    // the same event happens in the concrete model. If that's the case,
    // we forward it to Transaction valid, which produces all valid
    // sequences of the transaction layer
    int a,b, a1, b1;
progress:
    do
    :: abs_m_out?a,b;
       printf("m_out  %d,%d\n", a, b);
       conc_m_out?a1,b1;
       if
       :: a != a1 || b != b1 ->
          printf("abs_m_out %d,%d   conc_m_out %d,%d\n", a,b, a1, b1);
          false;
       :: else -> skip;
       fi
       transm_in!a,b;

    :: abs_s_out?a,b;
       printf("s_out  %d,%d\n", a, b);
       conc_s_out?a1,b1;
       if
       :: a != a1 || b != b1 ->
          printf("abs_s_out %d,%d   conc_s_out %d,%d\n", a, b, a1, b1);
          false;
       :: else -> skip;
       fi
       transs_in!a,b;

    :: transm_out?a,b;
       printf("m_in  %d,%d\n", a, b);
       abs_m_in!a,b; 
       conc_m_in!a,b;

    :: transs_out?a,b;
       printf("s_in %d, %d\n", a, b);
       abs_s_in!a,b; 
       conc_s_in!a,b;

    od

}

proctype TransactionValid(chan m_in; chan m_out; chan s_in; chan s_out)
{
    int expected_ma_res;
    int expected_ma_data;
    int expected_sl_res;
    int expected_sl_data;
    int wdata;

    expected_ma_res = BYTE_RES_IDLE;
    expected_ma_data = 0;
    expected_sl_res = BYTE_RES_IDLE;
    expected_sl_data = 0;


// Master sends start
ma_start:
    printf("ma_start\n");
    m_in?eval(expected_ma_res),eval(expected_ma_data);
    m_out!BYTE_ACT_START,0;

    s_in?eval(expected_sl_res),eval(expected_sl_data);
    s_out!BYTE_ACT_IDLE,0;

    expected_ma_res = BYTE_RES_START;
    expected_ma_data = 0;
    expected_sl_res = BYTE_RES_START;
    expected_sl_data = 0;

//actions that can be taken inside a transaction
ma_in_trans: 
    printf("ma_in_trans\n");
    if
    :: goto ma_write;
    :: goto ma_read;
    :: goto ma_restart;
    :: goto ma_stop;
    fi

// Master writes byte 
ma_write:
    printf("ma_write\n");

#ifdef BYTE_FULL
    select(wdata : 0 .. 255);
#else
    if
    :: true -> wdata = 0;
    :: true -> wdata = 1;
    :: true -> wdata = 2;
    :: true -> wdata = 4;
    :: true -> wdata = 8;
    :: true -> wdata = 16;
    :: true -> wdata = 32;
    :: true -> wdata = 64;
    :: true -> wdata = 128;
    :: true -> wdata = 255;
    fi
#endif

    m_in?eval(expected_ma_res),eval(expected_ma_data);
    m_out!BYTE_ACT_WRITE,wdata;

    s_in?eval(expected_sl_res),eval(expected_sl_data);
    s_out!BYTE_ACT_READ,0;

    s_in?BYTE_RES_READ,eval(wdata);
    if 
    :: s_out!BYTE_ACT_ACK,0;
       expected_sl_res = BYTE_RES_ACK;
       expected_sl_data = 0;
       expected_ma_res = BYTE_RES_ACK;
       expected_ma_data = 0;
    :: s_out!BYTE_ACT_NACK,0;
       expected_sl_res = BYTE_RES_NACK;
       expected_sl_data = 0;
       expected_ma_res = BYTE_RES_NACK;
       expected_ma_data = 0;
    fi

    goto ma_in_trans;

// Master reads byte 
ma_read:
    printf("ma_in_read\n");


#ifdef BYTE_FULL
    select(wdata : 0 .. 255);
#else
    if
    :: true -> wdata = 0;
    :: true -> wdata = 1;
    :: true -> wdata = 2;
    :: true -> wdata = 4;
    :: true -> wdata = 8;
    :: true -> wdata = 16;
    :: true -> wdata = 32;
    :: true -> wdata = 64;
    :: true -> wdata = 128;
    :: true -> wdata = 255;
    fi
#endif

    m_in?eval(expected_ma_res),eval(expected_ma_data);
    m_out!BYTE_ACT_READ,wdata;

    s_in?eval(expected_sl_res),eval(expected_sl_data);
    s_out!BYTE_ACT_WRITE,wdata;

    m_in?BYTE_RES_READ,eval(wdata);
    if 
    ::  m_out!BYTE_ACT_ACK,0;
        expected_sl_res = BYTE_RES_ACK;
        expected_sl_data = 0;
        expected_ma_res = BYTE_RES_ACK;
        expected_ma_data = 0;

    ::  m_out!BYTE_ACT_NACK,0;
        expected_sl_res = BYTE_RES_NACK;
        expected_sl_data = 0;
        expected_ma_res = BYTE_RES_NACK;
        expected_ma_data = 0;
    fi

    goto ma_in_trans;

ma_restart:
    printf("ma_restart\n");
    m_in?eval(expected_ma_res),eval(expected_ma_data);
    m_out!BYTE_ACT_START,wdata;

    s_in?eval(expected_sl_res),eval(expected_sl_data);
    s_out!BYTE_ACT_READ,0;

    expected_sl_res = BYTE_RES_START;
    expected_sl_data = 0;
    expected_ma_res = BYTE_RES_START;
    expected_ma_data = 0;

    goto ma_in_trans;

ma_stop:
    printf("ma_stop\n");
    m_in?eval(expected_ma_res),eval(expected_ma_data);
    m_out!BYTE_ACT_STOP,wdata;

    s_in?eval(expected_sl_res),eval(expected_sl_data);
    s_out!BYTE_ACT_READ,0;

    expected_sl_res = BYTE_RES_STOP;
    expected_sl_data = 0;
    expected_ma_res = BYTE_RES_STOP;
    expected_ma_data = 0;

    goto ma_start;
}



