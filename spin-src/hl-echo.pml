#include "common.xp"
#include "i2c.pml"


init {

    // Use EL machines
    run ElBus1();
    run MasterDriver();
    run SdaDriver();
    run SclDriver();
    run SymbolReader();
    run SymbolMasterAgg();
    run SymbolMaster();
    run TransactionMaster();
    run HlMaster();

    // Start the bus
    ElBus1_in!1;
    
}
