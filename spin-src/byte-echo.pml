#include "common.xp"
#include "eep.pml"

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
