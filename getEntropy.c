/*
 * avalanche - reads a random bit sequence generated by avalanche noise in a
 * pn junction and appends the bits to a file every hour
 * If SIGINT is received, append the sequence acquired so far and exit
 *
 * Copyright 2012 Giorgio Vazzana
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

// Compile: gcc -Wall -O getEntropy.c -o getEntropy

// README!
// This version (getEntropy.c) is modified from avalanche_hour.c by Giorgio Vazzana to be used in TFC suite: github.com/maqp/tfc/
// This version uses shorter sleep time between recording samples.
// Original program code is available from http://holdenc.altervista.org/avalanche/downloads/avalanche-test-utils.tgz

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>
#include <signal.h>
#include <time.h>

// GPIO Avalanche input
#define AVALANCHE_IN  4
#define LED           9
#define NSAMPLES      (60*60*2000)

// GPIO registers address
#define BCM2708_PERI_BASE  0x20000000
#define GPIO_BASE          (BCM2708_PERI_BASE + 0x200000) /* GPIO controller */
#define BLOCK_SIZE         (256)

// GPIO setup macros. Always use GPIO_IN(x) before using GPIO_OUT(x) or GPIO_ALT(x,y)
#define GPIO_IN(g)    *(gpio+((g)/10)) &= ~(7<<(((g)%10)*3))
#define GPIO_OUT(g)   *(gpio+((g)/10)) |=  (1<<(((g)%10)*3))
#define GPIO_ALT(g,a) *(gpio+(((g)/10))) |= (((a)<=3?(a)+4:(a)==4?3:2)<<(((g)%10)*3))

#define GPIO_SET(g) *(gpio+7)  = 1<<(g)  // sets   bits which are 1, ignores bits which are 0
#define GPIO_CLR(g) *(gpio+10) = 1<<(g)  // clears bits which are 1, ignores bits which are 0
#define GPIO_LEV(g) (*(gpio+13) >> (g)) & 0x00000001

int                mem_fd;
void              *gpio_map;
volatile uint32_t *gpio;
static volatile sig_atomic_t keep_going = 1;

void signal_handler(int sig)
{
	keep_going = 0;
}

// Set up a memory regions to access GPIO

void setup_io()
{
	/* open /dev/mem */
	mem_fd = open("/dev/mem", O_RDWR|O_SYNC);
	if (mem_fd == -1) {
		perror("Cannot open /dev/mem");
		exit(1);
	}

	/* mmap GPIO */
	gpio_map = mmap(NULL, BLOCK_SIZE, PROT_READ|PROT_WRITE, MAP_SHARED, mem_fd, GPIO_BASE);
	if (gpio_map == MAP_FAILED) {
		perror("mmap() failed");
		exit(1);
	}

	// Always use volatile pointer!
	gpio = (volatile uint32_t *)gpio_map;

	// Configure GPIOs
	GPIO_IN(AVALANCHE_IN); // must use GPIO_IN before we can use GPIO_OUT

	GPIO_IN(LED);
//	GPIO_OUT(LED);
}

// Release GPIO memory region

void close_io()
{
	int ret;

	/* munmap GPIO */
	ret = munmap(gpio_map, BLOCK_SIZE);
	if (ret == -1) {
		perror("munmap() failed");
		exit(1);
	}

	/* close /dev/mem */
	ret = close(mem_fd);
	if (ret == -1) {
		perror("Cannot close /dev/mem");
		exit(1);
	}
}

int main(int argc, char *argv[])
{
	uint32_t i, j, bit;
	uint8_t *samples;
	FILE *fp;
	int iterate;
	int increasethis = 0;

	// Setup gpio pointer for direct register access
	setup_io();

	samples = calloc(NSAMPLES, sizeof(*samples));
	if (!samples) {
		printf("Error on calloc()\n");
		exit(1);
	}

	signal(SIGINT, signal_handler);

	while (keep_going) {
		for (i = 0; i < NSAMPLES; i++) {
			if (!keep_going)
				break;

			bit = GPIO_LEV(AVALANCHE_IN);

		//Useless iterating that only causes slight sleep time before next sample is read.
		for (iterate = 0; iterate < 1000; iterate++) {
			increasethis++;
			}
		increasethis = 0;
		
		samples[i] = bit;
		}

		fp = fopen("HWRNGEntropy", "a");
		if (fp) {
			for (j = 0; j < i; j++)
				fprintf(fp, "%s", samples[j] ? "1" : "0");
			fclose(fp);
		}
	}

	close_io();

	return 0;
}
