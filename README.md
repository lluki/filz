Filz - A model checked I2C stack
======

I2C is a pervasive bus protocol used for querying sensors and actuators, but it
is plagued with incompatible devices, violating the specification at various
levels. 

Interacting with partially compliant devices poses several challenges.
Compatibility of the  master interface, as well as the driver code, must be
checked manually and potentially changed. This is a difficult process, as also
interactions with other bus devices have to be considered. We propose a model
checking approach to quickly write high assurance drivers and layers of the
I2C stack. We do not propose a single, true formalization of I2C, but a
framework that allows to rapidly model non-compliant devices and verify the
correct interaction with a host driver process.

Our contribution to this is twofold: First, a framework that allows to specify
device and driver behavior together, and verify their correct interaction.
Second, fine grained building blocks, representing layers of the I2C stack,
that are already verified and can be reused to interact with partially compliant 
devices, as well as reducing model checking complexity.

Our specifications are stated in a machine readable, executable and layered DSL. 
From the DSL, we generate both Promela and C code. The first is used to apply model
checking to ensure the layers implementations follow the abstract specifications. The
second is used to  build and verify a EEPROM model and driver running on a Raspberry Pi.

The corresponding paper of this project is published at [SPIN2021](https://conf.researchr.org/home/spin-2021).

Directory structure
----
*  paper/ - Paper.
*  spin-gen/ - DSL for state machine (XP) files. Generates C and promela
*  xp-src/   - Statemachine description in XP format.
*  spin-src/   - Verification in promela
*  docs/       - Documentation


Dependencies
----
`apt-get install ghc libghc-megaparsec-dev spin build-essential clang-format libghc-missingh-dev`.


Make
----
Interesting targets: 

 * make paper - build the paper
 * make run   - build the I2C state machine and run a sample C program
 * make verif - Verify all the targets
 * make build/rpi  - build the raspberry pi executable. Note that you have to build it on the RPI itself, no cross-compilation support (yet).

For debugging, it is helpful to execute spin in simulation mode. 
Edit the BASENAME in Makefile to point to your to be debugged
target.

 * make spinrun - Run the spin simulation
 * make spinprun - Run the spin simulation with -p (very verbose)

The output of spinprun can be filtered with the tool symgrep tool to make
it human readable, the symgrep tool (currently) accepts "tr" "sym" "byte" 
as argument and filters and pretty prints the messages exchanged at this
layer. Run for example `make spinprun | ./tools/symgrep tr`

Tutorial
----
[Can be found here](docs/tutorial.md)

DSL
===
The spin-gen compiler accepts the following command line arguments
 * -i  - The input file
 * -o  - The output file
 * -H  - generate a C header file with the state machine signatures
 * -C  - generate a C file with the state machine implementations
 * -P  - generate Promela

