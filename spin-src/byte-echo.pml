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

#include "common.xp"
#include "i2c.pml"

#if ABS_LEVEL != 0
    #error "This file is not using ABS_LEVEL, must be set to 0"
#endif

// This property is not very interesting, without any other
// clients on the bus, we always read the byte 0xff

proctype TMDummy(){
    int res;
    int res_data;

    TransactionMaster_in?res,res_data;

start:
    do
    ::  TransactionMaster_out!BYTE_ACT_IDLE,0;
        TransactionMaster_in?BYTE_RES_IDLE,0;
    :: break
    od

    TransactionMaster_out!BYTE_ACT_START,0;
    TransactionMaster_in?BYTE_RES_START,0;

    do
    :: TransactionMaster_out!BYTE_ACT_READ,0;
       TransactionMaster_in?BYTE_RES_READ,255;
       TransactionMaster_out!BYTE_ACT_ACK,0;
       TransactionMaster_in?BYTE_RES_ACK,0;

    :: TransactionMaster_out!BYTE_ACT_WRITE,128;
       TransactionMaster_in?BYTE_RES_NACK,0;

    od
    
    TransactionMaster_out!BYTE_ACT_STOP,0;
    TransactionMaster_in?RES_OK,0;
    
    goto start;
};

init {

    // Use EL machines
    run ElBus1();
    run MasterDriver();
    run SdaDriver();
    run SclDriver();
    run SymbolReader();
    run SymbolMasterAgg();
    run ByteMaster();
    run TMDummy();

    // Start the bus
    ElBus1_in!1;

    
}
