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

#include "example.pml" 

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
    
    #define conc_c_out NibbleController_in
    #define conc_c_in  NibbleController_out
    #define conc_r_out NibbleResponder_in
    #define conc_r_in  NibbleResponder_out

    /* The concrete machines */
    run El();
    El_in!1;
    run BusResponder();
    run BusController();

    /* Abstract and valid */
    run NibbleValid(nibble_c_in, nibble_c_out, nibble_r_in, nibble_r_out);
    run BusControllerSpec(abs_c_in, abs_c_out, abs_r_in, abs_r_out);

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

proctype BusControllerSpec(chan ci, co, ri, ro){
    int dat; int res = RES_ACK;
start:
    co!res; ci?dat;
    ro!dat;
    if
    :: ri?ACT_ACK; res = RES_ACK; goto start;
    :: ri?ACT_NACK; res = RES_NACK; goto start;
    fi }
//</CUT>
