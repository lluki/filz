# Tutorial

## Introduction
This guide shows how to use this toolchain
to create a driver interacting with a non standard I2C
device.

First we identify up to which level our non-compliant 
device is still compatible with the stack. For
 example our AS5011 device is following the Byte
level protocol, but not the transaction level 
standard.

## Writing the state machines
Hence we start by creating a new file (as5011.xp) that describes
the driver (driving the byte statemachine),
the device model and the system. The system declares
which devices are present, and from which
layers they are composed. Since the device 
is compliant up to and including the byte level,
we include the default i2c definitions (the build
pipeline will pass it through the C preprocessor).

    #include "i2c.xp"
    
    ....
    
    system {
        layers [Sym, Byte, Tr, Hls];

        device controller {
            Sym : SymController;
            Byte : ByteCommon;
            Tr : TrAsController<AS5011_ADDR>;
            Hls : HlsAsController;
        };

        device responder {
            Sym : SymResponder;
            Byte : ByteCommon; 
            Tr : TrAsResponder<AS5011_ADDR>;
            Hls : HlsAsResponder;
        };
    }

We re-use the Sym layer as well as the Byte layer, but
we re-implement the transaction layer (in the state
machines `TrAsController` as well as `TrAsResponder`).


## Writing the verifier

Implemented in spin-src/as5011-eq.pml


## Debugging 

It helps to simply simulate the system,
in the Makefile, change the "BASENAME" variable
to `as5011-eq.pml`

## Verifying it
To perform the complete verification run, use the
command

> make build/verif/as5011-eq

This will transform the description into Promela
and invoke spin. It will
run spin in the verification mode twice, once
to find non-progress cycles, and once to check
no deadlocks.
