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

#include "i2c.h"
#include "stdio.h"
#include "unistd.h"
#include "string.h"
#include "assert.h"

static int last_scl = 1;
static int last_sda = 1;
static int simulate = 1;

#define SDA_PIN 2
#define SCL_PIN 3

//#define DEBUG(...) printf(__VA_ARGS__)
#define DEBUG(...) do {} while(0)

static void ms_sleep(int ms){
	usleep(ms * 1000);
}


static void set_dir(int pin, const char* dir){
	FILE *f;
	char fn[128];
	snprintf(fn, sizeof(fn), "/sys/class/gpio/gpio%d/direction", pin);
	f = fopen(fn, "w");
	assert(f);
	fprintf(f, "%s", dir);
	fclose(f);
}

static int get_value(int pin){
	FILE *in;
	char fn[128];
	snprintf(fn, sizeof(fn), "/sys/class/gpio/gpio%d/value", pin);
	in = fopen(fn, "r");
	assert(in);
	int val;
	int conversions = fscanf(in, "%d", &val);
    assert(conversions == 1);
	fclose(in);
	return val;
}

static void i2c_set_pin(int pin, int val){
	// If val == 1 -> high impedance output
	// if val == 0 -> drive low
	if(val) set_dir(pin, "in");
	else set_dir(pin, "low"); //Setting dir to low will set out and value to 0
}

void i2c_init(void){
	// Determine if we're on RPI and use the GPIOs
	char hostname[128];
	gethostname(hostname, sizeof(hostname));
	if(strcmp(hostname, "raspberrypi") != 0) {
		printf("\n#I2C: Not on RPI, using GPIO Simulation!\n");
		simulate = 1;
		return;
	}

	simulate = 0; 
	FILE *exp;

	exp = fopen("/sys/class/gpio/export", "w");
	assert(exp);
	fprintf(exp, "%d\n", SCL_PIN);
	fclose(exp);

	exp = fopen("/sys/class/gpio/export", "w");
	assert(exp);
	fprintf(exp, "%d\n", SDA_PIN);
	fclose(exp);

	i2c_set_pin(SDA_PIN, 1);
	i2c_set_pin(SCL_PIN, 1);

	printf("\n#I2C: On RPI using GPIOs!\n");
}

void i2c_send(int scl, int sda)
{
    DEBUG("\n#I2C send: %d,%d\n", scl, sda);
    last_scl = scl;
    last_sda = sda;
    if(!simulate){
    	ms_sleep(2);
	if(scl){
		// Avoid generating spurious start/stop
		i2c_set_pin(SDA_PIN, sda);	
    		ms_sleep(2);
		i2c_set_pin(SCL_PIN, scl);	
	} else {
		i2c_set_pin(SCL_PIN, scl);	
    		ms_sleep(2);
		i2c_set_pin(SDA_PIN, sda);	
	}
    }
}

void i2c_recv(int *scl, int *sda)
{
	if(simulate)
	{
		*scl = last_scl;
		*sda = last_sda;
	} else {
    		ms_sleep(5);
		*scl = get_value(SCL_PIN);
		*sda = get_value(SDA_PIN);
	}
	DEBUG("\n#I2C recv: %d,%d\n", *scl, *sda);
}

int main() {
    printf("Hello from RPI driver\n");
    i2c_init();

    int scl, sda;

    while(1) {
        i2c_recv(&scl, &sda);
        MasterDriver(scl, sda, &scl, &sda);
        i2c_send(scl, sda);
    }
    
};

