/*
 * Shows the equivalence of Symbol+El and SymbolAbs
 */

#if ABS_LEVEL >= 1
    #error "Makes no sense with this ABS_LEVEL"
#endif

#include "common.xp"
#include "eep.pml"
#include "i2c-spec.pml"

inline print_sym(in){
    if
    :: in == SYM_START -> printf("SYM_START\n");
    :: in == SYM_STOP ->  printf("SYM_STOP\n");
    :: in == SYM_BIT0 ->  printf("SYM_BIT0\n");
    :: in == SYM_BIT1 ->  printf("SYM_BIT1\n");
    :: in == SYM_IDLE ->  printf("SYM_IDLE\n");
    :: in == SYM_STRETCH ->  printf("SYM_STRETCH\n");
    :: else -> printf("unknown symbol %d\n", in);
    fi
}

proctype verifier() 
{
    /* abstract channels */
    chan abs_m_out = [0] of {int}; 
    chan abs_m_in = [0] of {int}; 
    chan abs_s_out = [0] of {int};
    chan abs_s_in = [0] of {int};

    /* concrete channels */
    #define conc_m_out  controller_Byte_in
    #define conc_m_in   controller_Byte_out
    #define conc_s_out  responder_Byte_in 
    #define conc_s_in   responder_Byte_out 

    /* upstream */
    chan byte_m_out = [0] of {int};
    chan byte_m_in = [0] of {int};
    chan byte_s_out = [0] of {int};
    chan byte_s_in = [0] of {int};

    run SymbolAbs(abs_m_in, abs_s_in, abs_m_out, abs_s_out);
    run ByteValid(byte_m_in, byte_m_out, byte_s_in, byte_s_out);

    int x; int x1;

progress:
    do
    :: byte_m_out?x ->
        printf("byte_m_out %d\n", x);
        abs_m_in!x;
        conc_m_in!x;
    :: byte_s_out?x ->
        printf("byte_s_out %d\n", x);
        abs_s_in!x;
        conc_s_in!x;
    :: abs_m_out?x ->
        printf("abs_m_out %d\n", x);
        conc_m_out?eval(x);
        byte_m_in!x;
    :: abs_s_out?x ->
        printf("abs_s_out %d\n", x);
        conc_s_out?eval(x);
        byte_s_in!x;
    od
}

init { 
    SymbolRun();
    run verifier();
}

inline stretch(){
    do
    :: s_out!SYM_STRETCH; s_in?_;
    :: break;
    od
}

proctype ByteValid(chan m_in; chan m_out; chan s_in; chan s_out)
{
    int m_res;

out_trans:
    do
    :: m_in?_; m_out!SYM_START; s_in?_; s_out!SYM_IDLE; break;
    :: m_in?_; m_out!SYM_IDLE; s_in?_; s_out!SYM_IDLE;
    od

in_trans:
    do
    :: m_in?_; m_out!SYM_BIT1; s_in?_; stretch(); s_out!SYM_BIT1;
    :: m_in?_; m_out!SYM_BIT1; s_in?_; stretch(); s_out!SYM_BIT0;
    :: m_in?_; m_out!SYM_BIT0; s_in?_; stretch(); s_out!SYM_BIT1;
    :: m_in?_; m_out!SYM_BIT0; s_in?_; stretch(); s_out!SYM_BIT0;
    :: m_in?_; m_out!SYM_START; s_in?_; stretch(); s_out!SYM_BIT1;
    :: m_in?_; m_out!SYM_STOP; s_in?_; stretch(); s_out!SYM_BIT1; break;
    od

    goto out_trans;

}


