#include "example.pml" 

proctype ElBus2(chan p1_in; chan p1_out; chan p2_in; chan p2_out) {
    int scl, scl1, scl2; 
    scl = 1;
start:
    p1_in!scl;
    p1_out?scl1;
    p2_in!scl;
    p2_out?scl2;

    if
    :: scl1 == 0 || scl2 == 0 -> scl = 0;
    :: else -> scl = 1;
    fi
    
    goto start; 
}

#define RES_ACK 0
#define RES_NACK 1

#define ACT_ACK 0
#define ACT_NACK 1

/* the verifier process */
init  {
    /* the abstract channels */
    chan abs_c_out = [0] of {int};
    chan abs_c_in  = [0] of {int};
    chan abs_r_out = [0] of {int};
    chan abs_r_in  = [0] of {int};

    /* upstream channels */
    chan nibble_c_in  = [0] of {int};
    chan nibble_c_out = [0] of {int};
    chan nibble_r_in  = [0] of {int};
    chan nibble_r_out = [0] of {int};
    
    #define conc_c_out controller_Nibble_in 
    #define conc_c_in  controller_Nibble_out 
    #define conc_r_out responder_Nibble_in
    #define conc_r_in  responder_Nibble_out

    /* The concrete machines */
    run El_conc_run();
    run Bus_conc_run();

    /* Abstract and valid */
    run NibbleValid(nibble_c_in, nibble_c_out, nibble_r_in, nibble_r_out);
    run BusSpec(abs_c_in, abs_c_out, abs_r_in, abs_r_out);

    /* Verify that abs and conc equal */
    int x;
    int x1;
progress:
    do
    :: abs_c_out?x; conc_c_out?eval(x); nibble_c_in!x;
    :: abs_r_out?x; conc_r_out?eval(x); nibble_r_in!x;
    :: nibble_c_out?x; conc_c_in!x; abs_c_in!x;
    :: nibble_r_out?x; conc_r_in!x; abs_r_in!x;
    od
}

//<CUT>
proctype NibbleValid(chan ci, co, ri, ro) {
    int c_res = RES_ACK; int dat;
start:
    select(dat : 0..15);
    ci?_; co!dat;
    ri?_;
    if
    :: ro!ACT_ACK; c_res = RES_ACK; goto start;
    :: ro!ACT_NACK; c_res = RES_NACK; goto start;
    fi }

proctype BusSpec(chan ci, co, ri, ro){
    int dat; int res = RES_ACK;
start:
    co!res; ci?dat;
    ro!dat;
    if
    :: ri?ACT_ACK; res = RES_ACK; goto start;
    :: ri?ACT_NACK; res = RES_NACK; goto start;
    fi }
//</CUT>
