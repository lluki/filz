#define SKIP_DEFAULT_TR
#define SKIP_DEFAULT_HL

#include "common.xp"
#include "as5011.pml"
#include "i2c-spec.pml"

#if ABS_LEVEL >= 1
    #error "Makes no sense with this ABS_LEVEL"
#endif

proctype HlsValid(chan m_in; chan m_out; chan s_in; chan s_out)
{
start:
    m_in?_;
    if
    :: m_out!HLS_ACT_READ,1,0; 
    :: m_out!HLS_ACT_WRITE,1,2; 
    fi
    
    s_in?_,_,_; s_out!0;
    goto start;
}

proctype TrAbs(chan m_in; chan s_in; chan m_out; chan s_out)
{
    int res;
    int act, reg_idx, reg, read_reg;
    res = RES_OK;

start:
    m_out!res;
    m_in?act,reg_idx,reg; 
    if 
    :: act == HLS_ACT_WRITE -> s_out!HLS_ACT_WRITE,reg_idx,reg;
        s_in?0; res=RES_OK; // Send "success" back to controller
    :: act == HLS_ACT_READ -> s_out!HLS_REG_READ,reg_idx,0;
        s_in?res; // Send "read data" back to controller
    fi
    goto start;
}


proctype verifier() 
{
    /* abstract channels */
    chan abs_m_out = [0] of {int}; 
    chan abs_m_in = [0] of {int,int,int}; 
    chan abs_s_out = [0] of {int,int,int};
    chan abs_s_in = [0] of {int};

    /* concrete channels */
    #define conc_m_out  controller_Hls_in
    #define conc_m_in   controller_Hls_out
    #define conc_s_out  responder_Hls_in 
    #define conc_s_in   responder_Hls_out 

    /* upstream */
    chan hls_m_out = [0] of {int,int,int};
    chan hls_m_in = [0] of {int};
    chan hls_s_out = [0] of {int};
    chan hls_s_in = [0] of {int,int,int};

    run TrAbs(abs_m_in, abs_s_in, abs_m_out, abs_s_out);
    run HlsValid(hls_m_in, hls_m_out, hls_s_in, hls_s_out); 
    int x1; int x2; int x3;
    int x1z;

progress:
    do
    :: hls_m_out?x1,x2,x3 ->
        printf("hls_m_out %d,%d,%d\n", x1,x2,x3);
        abs_m_in!x1,x2,x3;
        conc_m_in!x1,x2,x3;
    :: hls_s_out?x1 ->
        printf("hls_s_out %d\n", x1);
        abs_s_in!x1;
        conc_s_in!x1;
    :: abs_m_out?x1 ->
        printf("abs_m_out %d\n", x1);
        conc_m_out?eval(x1);
        hls_m_in!x1;
    :: abs_s_out?x1,x2,x3 ->
        printf("abs_s_out %d,%d,%d\n", x1,x2,x3);
        conc_s_out?eval(x1),eval(x2),eval(x3);
        hls_s_in!x1,x2,x3;
    od
}

init {
    run verifier(); 

    run El_conc_run();
    run Sym_conc_run();
    run Byte_conc_run();
    run Tr_conc_run();
}
