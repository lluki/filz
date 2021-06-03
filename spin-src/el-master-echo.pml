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
 * Shows the equivalence of Symbol+El and SymbolAbs
 */

#if ABS_LEVEL != 0
    #error "This file is not using ABS_LEVEL, must be set to 0"
#endif

#include "common.xp"
#include "i2c.pml"

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

init {
    // Verify that the master EL side reads back symbols
    // as they have been sent.

    int x;

    run ElBus1();
    run MasterDriver();
    run SdaDriver();
    run SclDriver();
    run SymbolReader();
    run SymbolMasterAgg();

    // Start the bus
    ElBus1_in!1;

    ByteMaster_in?SYM_IDLE; 

start:
    // Idle outside of transaction
    do
    :: ByteMaster_out!SYM_IDLE; ByteMaster_in?SYM_IDLE;
    :: break;
    od

    // Start transaction
    ByteMaster_out!SYM_START;
    ByteMaster_in?SYM_START;

    // Valid in transaction statements
    do
    :: ByteMaster_out!SYM_STRETCH; ByteMaster_in?SYM_STRETCH;
    :: ByteMaster_out!SYM_BIT0;    ByteMaster_in?SYM_BIT0;
    :: ByteMaster_out!SYM_BIT1;    ByteMaster_in?SYM_BIT1;
    :: ByteMaster_out!SYM_START;   ByteMaster_in?SYM_START;
    :: break;
    od

    // end transaction
    ByteMaster_out!SYM_STOP;
    ByteMaster_in?SYM_STOP;

    printf("Transaction complete\n");
end:
    goto start;
}

