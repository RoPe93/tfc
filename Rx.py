#!/usr/bin/env python
# -*- coding: utf-8 -*-

import binascii
import csv
import datetime
import math
import os
import serial
import subprocess
import sys
from time import sleep



######################################################################
#                             LICENCE                                #
######################################################################

# TFC-CEV (Cascading Encryption Version) || Rx.py
version = 'CEV 0.4.13 beta'

"""
This software is part of the TFC application, which is free software:
You can redistribute it and/or modify it under the terms of the GNU
General Public License as published by the Free Software Foundation,
either version 3 of the License, or (at your option) any later version.

TFC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License
for more details. For a copy of the GNU General Public License, see
<http://www.gnu.org/licenses/>.
"""



######################################################################
#                           CONFIGURATION                            #
######################################################################

fileSavingAllowed  = False
debugging          = False
logMessages        = False
injectionTesting   = False

logChangeAllowed   = True
logTamperingEvent  = True
showLongMsgWarning = True
displayTime        = True

logTimeStampFmt    = '%Y-%m-%d / %H:%M:%S'
displayTimeFmt     = '%H:%M'
kfOWIterations     = 3

localTesting       = False

if not localTesting:
    port        = serial.Serial('/dev/ttyAMA0', baudrate=9600, timeout=0.1)



######################################################################
#                          KECCAK STREAM CIPHER                      #
######################################################################

"""
Algorithm Name: Keccak

Authors: Guido Bertoni, Joan Daemen, Michael Peeters and Gilles
Van Assche Implementation by Renaud Bauvin, STMicroelectronics

This code, originally by Renaud Bauvin, is hereby put in the public
domain. It is given as is, without any guarantee.

For more information, feedback or questions, please refer to our
website: http://keccak.noekeon.org/
"""



class KeccakError(Exception):
    """Class of error used in the Keccak implementation

    Use: raise KeccakError.KeccakError("Text to be displayed")"""

    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)



class Keccak:
    """
    Class implementing the Keccak sponge function
    """
    def __init__(self, b=1600):
        """Constructor:

        b: parameter b, must be 25, 50, 100, 200, 400, 800 or 1600 (default value)"""
        self.setB(b)



    def setB(self,b):
        """Set the value of the parameter b (and thus w,l and nr)

        b: parameter b, must be choosen among [25, 50, 100, 200, 400, 800, 1600]
        """

        if b not in [25, 50, 100, 200, 400, 800, 1600]:
            raise KeccakError.KeccakError('b value not supported - use 25, 50, 100, 200, 400, 800 or 1600')

        # Update all the parameters based on the used value of b
        self.b=b
        self.w=b//25
        self.l=int(math.log(self.w,2))
        self.nr=12+2*self.l

    # Constants

    ## Round constants
    RC=[0x0000000000000001,
        0x0000000000008082,
        0x800000000000808A,
        0x8000000080008000,
        0x000000000000808B,
        0x0000000080000001,
        0x8000000080008081,
        0x8000000000008009,
        0x000000000000008A,
        0x0000000000000088,
        0x0000000080008009,
        0x000000008000000A,
        0x000000008000808B,
        0x800000000000008B,
        0x8000000000008089,
        0x8000000000008003,
        0x8000000000008002,
        0x8000000000000080,
        0x000000000000800A,
        0x800000008000000A,
        0x8000000080008081,
        0x8000000000008080,
        0x0000000080000001,
        0x8000000080008008]

    ## Rotation offsets
    r=[[0,    36,     3,    41,    18]    ,
       [1,    44,    10,    45,     2]    ,
       [62,    6,    43,    15,    61]    ,
       [28,   55,    25,    21,    56]    ,
       [27,   20,    39,     8,    14]    ]


    ## Generic utility functions

    def rot(self,x,n):
        """Bitwise rotation (to the left) of n bits considering the \
        string of bits is w bits long"""

        n = n%self.w
        return ((x>>(self.w-n))+(x<<n))%(1<<self.w)



    def enc(self,x,n):
        """Encode the integer x in n bits (n must be a multiple of 8)"""

        if x>=2**n:
            raise KeccakError.KeccakError('x is too big to be coded in n bits')
        if n%8!=0:
            raise KeccakError.KeccakError('n must be a multiple of 8')
        return ("%%0%dX" % (2*n//8)) % (x)



    def fromHexStringToLane(self, string):
        """Convert a string of bytes written in hexadecimal to a lane value"""

        #Check that the string has an even number of characters i.e. whole number of bytes
        if len(string)%2!=0:
            raise KeccakError.KeccakError("The provided string does not end with a full byte")

        #Perform the modification
        temp=''
        nrBytes=len(string)//2
        for i in range(nrBytes):
            offset=(nrBytes-i-1)*2
            temp+=string[offset:offset+2]
        return int(temp, 16)



    def fromLaneToHexString(self, lane):
        """Convert a lane value to a string of bytes written in hexadecimal"""

        laneHexBE = (("%%0%dX" % (self.w//4)) % lane)
        #Perform the modification
        temp=''
        nrBytes=len(laneHexBE)//2
        for i in range(nrBytes):
            offset=(nrBytes-i-1)*2
            temp+=laneHexBE[offset:offset+2]
        return temp.upper()



    def printState(self, state, info):
        """Print on screen the state of the sponge function preceded by \
        string info

        state: state of the sponge function
        info: a string of characters used as identifier"""

        print("Current value of state: %s" % (info))
        for y in range(5):
            line=[]
            for x in range(5):
                 line.append(hex(state[x][y]))
            print('\t%s' % line)



    ### Conversion functions String <-> Table (and vice-versa)
    def convertStrToTable(self,string):
        """Convert a string of bytes to its 5x5 matrix representation

        string: string of bytes of hex-coded bytes (e.g. '9A2C...')"""

        #Check that input paramaters
        if self.w%8!= 0:
            raise KeccakError("w is not a multiple of 8")
        if len(string)!=2*(self.b)//8:
            raise KeccakError.KeccakError("string can't be divided in 25 blocks of w bits\
            i.e. string must have exactly b bits")

        #Convert
        output=[[0,0,0,0,0],
                [0,0,0,0,0],
                [0,0,0,0,0],
                [0,0,0,0,0],
                [0,0,0,0,0]]
        for x in range(5):
            for y in range(5):
                offset=2*((5*y+x)*self.w)//8
                output[x][y]=self.fromHexStringToLane(string[offset:offset+(2*self.w//8)])
        return output



    def convertTableToStr(self,table):
        """Convert a 5x5 matrix representation to its string representation"""

        #Check input format
        if self.w%8!= 0:
            raise KeccakError.KeccakError("w is not a multiple of 8")
        if (len(table)!=5) or (False in [len(row)==5 for row in table]):
            raise KeccakError.KeccakError("table must be 5x5")

        #Convert
        output=['']*25
        for x in range(5):
            for y in range(5):
                output[5*y+x]=self.fromLaneToHexString(table[x][y])
        output =''.join(output).upper()
        return output



    ### Padding function
    def pad(self,M, n):
        """Pad M with reverse-padding to reach a length multiple of n

        M: message pair (length in bits, string of hex characters ('9AFC...')
        n: length in bits (must be a multiple of 8)
        Example: pad([60, 'BA594E0FB9EBBD30'],8) returns 'BA594E0FB9EBBD13'
        """

        [my_string_length, my_string]=M

        # Check the parameter n
        if n%8!=0:
            raise KeccakError.KeccakError("n must be a multiple of 8")

        # Check the length of the provided string
        if len(my_string)%2!=0:
            #Pad with one '0' to reach correct length (don't know test
            #vectors coding)
            my_string=my_string+'0'
        if my_string_length>(len(my_string)//2*8):
            raise KeccakError.KeccakError("the string is too short to contain the number of bits announced")

        #Add the bit allowing reversible padding
        nr_bytes_filled=my_string_length//8
        if nr_bytes_filled==len(my_string)//2:
            #bits fill the whole package: add a byte '01'
            my_string=my_string+"01"
        else:
            #there is no addition of a byte... modify the last one
            nbr_bits_filled=my_string_length%8

            #Add the leading bit
            my_byte=int(my_string[nr_bytes_filled*2:nr_bytes_filled*2+2],16)
            my_byte=(my_byte>>(8-nbr_bits_filled))
            my_byte=my_byte+2**(nbr_bits_filled)
            my_byte="%02X" % my_byte
            my_string=my_string[0:nr_bytes_filled*2]+my_byte

        #Complete my_string to reach a multiple of n bytes
        while((8*len(my_string)//2)%n!=0):
            my_string=my_string+'00'
        return my_string



    def Round(self,A,RCfixed):
        """Perform one round of computation as defined in the Keccak-f permutation

        A: current state (5x5 matrix)
        RCfixed: value of round constant to use (integer)
        """

        #Initialisation of temporary variables
        B=[[0,0,0,0,0],
           [0,0,0,0,0],
           [0,0,0,0,0],
           [0,0,0,0,0],
           [0,0,0,0,0]]
        C= [0,0,0,0,0]
        D= [0,0,0,0,0]

        #Theta step
        for x in range(5):
            C[x] = A[x][0]^A[x][1]^A[x][2]^A[x][3]^A[x][4]

        for x in range(5):
            D[x] = C[(x-1)%5]^self.rot(C[(x+1)%5],1)

        for x in range(5):
            for y in range(5):
                A[x][y] = A[x][y]^D[x]

        #Rho and Pi steps
        for x in range(5):
          for y in range(5):
                B[y][(2*x+3*y)%5] = self.rot(A[x][y], self.r[x][y])

        #Chi step
        for x in range(5):
            for y in range(5):
                A[x][y] = B[x][y]^((~B[(x+1)%5][y]) & B[(x+2)%5][y])

        #Iota step
        A[0][0] = A[0][0]^RCfixed

        return A



    def KeccakF(self,A, verbose=False):
        """Perform Keccak-f function on the state A

        A: 5x5 matrix containing the state
        verbose: a boolean flag activating the printing of intermediate computations
        """

        if verbose:
            self.printState(A,"Before first round")

        for i in range(self.nr):
            #NB: result is truncated to lane size
            A = self.Round(A,self.RC[i]%(1<<self.w))

            if verbose:
                  self.printState(A,"Satus end of round #%d/%d" % (i+1,self.nr))

        return A



    def Keccak(self,M,r=1024,c=576,d=0,n=1024,verbose=False):
        """Compute the Keccak[r,c,d] sponge function on message M

        M: message pair (length in bits, string of hex characters ('9AFC...')
        r: bitrate in bits (defautl: 1024)
        c: capacity in bits (default: 576)
        d: diversifier in bits (default: 0 bits)
        n: length of output in bits (default: 1024),
        verbose: print the details of computations(default:False)
        """

        #Check the inputs
        if (r<0) or (r%8!=0):
            raise KeccakError.KeccakError('r must be a multiple of 8')
        if (n%8!=0):
            raise KeccakError.KeccakError('outputLength must be a multiple of 8')
        if (d<0) or (d>255):
            raise KeccakError.KeccakError('d must be in the range [0, 255]')
        self.setB(r+c)

        if verbose:
            print("Create a Keccak function with (r=%d, c=%d, d=%d (i.e. w=%d))" % (r,c,d,(r+c)//25))

        #Compute lane length (in bits)
        w=(r+c)//25

        # Initialisation of state
        S=[[0,0,0,0,0],
           [0,0,0,0,0],
           [0,0,0,0,0],
           [0,0,0,0,0],
           [0,0,0,0,0]]

        #Padding of messages
        P=self.pad(M,8) + self.enc(d,8) + self.enc(r//8,8)
        P=self.pad([8*len(P)//2,P],r)

        if verbose:
            print("String ready to be absorbed: %s (will be completed by %d x '00')" % (P, c//8))

        #Absorbing phase
        for i in range((len(P)*8//2)//r):
            Pi=self.convertStrToTable(P[i*(2*r//8):(i+1)*(2*r//8)]+'00'*(c//8))

            for y in range(5):
              for x in range(5):
                  S[x][y] = S[x][y]^Pi[x][y]
            S = self.KeccakF(S, verbose)

        if verbose:
            print("Value after absorption : %s" % (self.convertTableToStr(S)))

        #Squeezing phase
        Z = ''
        outputLength = n
        while outputLength>0:
            string=self.convertTableToStr(S)
            Z = Z + string[:r*2//8]
            outputLength -= r
            if outputLength>0:
                S = self.KeccakF(S, verbose)

            # NB: done by block of length r, could have to be cut if outputLength
            #     is not a multiple of r

        if verbose:
            print("Value after squeezing : %s" % (self.convertTableToStr(S)))

        return Z[:2*n//8]



def keccak_256(hashInput):
    hexMsg = binascii.hexlify(hashInput)
    return Keccak().Keccak(((8 * len(hashInput)), hexMsg), 1088, 512, 0, 256, 0)



def keccak_decrypt(ciphertext, HexKey):

    # CTR mode, no authentication.

    # Convert hexadecimal key to binary data.
    key        = binascii.unhexlify(HexKey)

    # Separate 256-bit nonce from ciphertext.
    nonce      = ciphertext[:32]
    ciphertext = ciphertext[32:]

    # Generate 512-bit IV.
    iv         = (key + nonce)

    # Sponge function takes 512-bit IV, squeezes out 256 bit keystream block #1.
    step       = keccak_256(iv)

    i          = 0
    keystream  = ''

    # For n-byte message, n/32 additional rounds is needed to generate proper length keystream.
    while i < (len(ciphertext) / 32):
        keystream += step
        step       = keccak_256(key + step)
        i         += 1

    # Convert key from hex format to binary.
    keystreamBIN = binascii.unhexlify(keystream)

    # XOR keystream with plaintext to acquire ciphertext.
    if len(ciphertext) == len(keystreamBIN):
        plaintext = ''.join(chr(ord(msgLetter) ^ ord(keyLetter)) for msgLetter, keyLetter in zip(ciphertext, keystreamBIN))
    else:
        os.system('clear')
        print '\nCRITICAL ERROR! Keccak ciphertext - keystream length mismatch. Exiting.\n'
        exit()

    # Remove padding.
    plaintext      = plaintext[:-ord(plaintext[-1:])]

    return plaintext



######################################################################
#                        SALSA20 STREAM CIPHER                       #
######################################################################

"""
This file is part of Python Salsa20
a Python bridge to the libsodium C [X]Salsa20 library
Released under The BSD 3-Clause License

Copyright (c) 2013 Keybase
Python module and ctypes bindings
"""

import imp
from ctypes import (cdll, c_char_p, c_int, c_uint64, create_string_buffer)
from ctypes import (cdll, Structure, POINTER, pointer, c_char_p, c_int, c_uint32, create_string_buffer)


_salsa20 = cdll.LoadLibrary(imp.find_module('_salsa20')[1])


_stream_salsa20 = _salsa20.exp_stream_salsa20
_stream_salsa20.argtypes = [  c_char_p,  # unsigned char * c
                              c_uint64,  # unsigned long long clen
                              c_char_p,  # const unsigned char * n
                              c_char_p   # const unsigned char * k
                           ]
_stream_salsa20.restype = c_int

_stream_salsa20_xor = _salsa20.exp_stream_salsa20_xor
_stream_salsa20_xor.argtypes = [  c_char_p,  # unsigned char * c
                                  c_char_p,  # const unsigned char *m
                                  c_uint64,  # unsigned long long mlen
                                  c_char_p,  # const unsigned char * n
                                  c_char_p   # const unsigned char * k
                               ]
_stream_salsa20_xor.restype = c_int

_stream_xsalsa20 = _salsa20.exp_stream_xsalsa20
_stream_xsalsa20.argtypes = [  c_char_p,  # unsigned char * c
                               c_uint64,  # unsigned long long clen
                               c_char_p,  # const unsigned char * n
                               c_char_p   # const unsigned char * k
                            ]
_stream_xsalsa20.restype = c_int

_stream_xsalsa20_xor = _salsa20.exp_stream_xsalsa20_xor
_stream_xsalsa20_xor.argtypes = [  c_char_p,  # unsigned char * c
                                   c_char_p,  # const unsigned char *m
                                   c_uint64,  # unsigned long long mlen
                                   c_char_p,  # const unsigned char * n
                                   c_char_p   # const unsigned char * k
                                ]
_stream_xsalsa20_xor.restype = c_int

IS_PY2 = sys.version_info < (3, 0, 0, 'final', 0)



def _ensure_bytes(data):
    if (IS_PY2 and not isinstance(data, str)) or (not IS_PY2 and not isinstance(data, bytes)):
        raise TypeError('can not encrypt/decrypt unicode objects')



def Salsa20_keystream(length, nonce, key):
    _ensure_bytes(nonce)
    _ensure_bytes(key)
    if not len(key) == 32: raise ValueError('invalid key length')
    if not len(nonce) == 8: raise ValueError('invalid nonce length')
    if not length > 0: raise ValueError('invalid length')

    outbuf = create_string_buffer(length)
    _stream_salsa20(outbuf, length, nonce, key)
    return outbuf.raw



def Salsa20_xor(message, nonce, key):
    _ensure_bytes(nonce)
    _ensure_bytes(key)
    _ensure_bytes(message)
    if not len(key) == 32: raise ValueError('invalid key length')
    if not len(nonce) == 8: raise ValueError('invalid nonce length')
    if not len(message) > 0: raise ValueError('invalid message length')

    outbuf = create_string_buffer(len(message))
    _stream_salsa20_xor(outbuf, message, len(message), nonce, key)
    return outbuf.raw



def XSalsa20_keystream(length, nonce, key):
    _ensure_bytes(nonce)
    _ensure_bytes(key)
    if not len(key) == 32: raise ValueError('invalid key length')
    if not len(nonce) == 24: raise ValueError('invalid nonce length')
    if not length > 0: raise ValueError('invalid length')

    outbuf = create_string_buffer(length)
    _stream_xsalsa20(outbuf, length, nonce, key)
    return outbuf.raw



def XSalsa20_xor(message, nonce, key):
    _ensure_bytes(nonce)
    _ensure_bytes(key)
    _ensure_bytes(message)
    if not len(key) == 32: raise ValueError('invalid key length')
    if not len(nonce) == 24: raise ValueError('invalid nonce length')
    if not len(message) > 0: raise ValueError('invalid message length')

    outbuf = create_string_buffer(len(message))
    _stream_xsalsa20_xor(outbuf, message, len(message), nonce, key)
    return outbuf.raw



def salsa_20_decrypt(ciphertext, hexKey):

    # Separate nonce from ciphertext.
    nonce      = ciphertext[:24]
    ciphertext = ciphertext[24:]

    # Convert hexadecimal key to bitstring.
    key        = binascii.unhexlify(hexKey)

    # XOR ciphertext with keystream to acquire plaintext.
    plaintext  = XSalsa20_xor(ciphertext, nonce, key)

    return plaintext



######################################################################
#                        TWOFISH BLOCK CIPHER                        #
######################################################################

"""
This file is part of Python Twofish a Python bridge to the C Twofish library by Niels Ferguson
Released under The BSD 3-Clause License
Copyright (c) 2013 Keybase
Python module and ctypes bindings
"""

import imp

_twofish = cdll.LoadLibrary(imp.find_module('_twofish')[1])



class _Twofish_key(Structure):
    _fields_ = [("s", (c_uint32 * 4) * 256),
                ("K", c_uint32 * 40)]

_Twofish_initialise = _twofish.exp_Twofish_initialise
_Twofish_initialise.argtypes = []
_Twofish_initialise.restype = None

_Twofish_prepare_key = _twofish.exp_Twofish_prepare_key
_Twofish_prepare_key.argtypes = [ c_char_p,  # uint8_t key[]
                                  c_int,     # int key_len
                                  POINTER(_Twofish_key) ]
_Twofish_prepare_key.restype = None

_Twofish_encrypt = _twofish.exp_Twofish_encrypt
_Twofish_encrypt.argtypes = [ POINTER(_Twofish_key),
                              c_char_p,     # uint8_t p[16]
                              c_char_p      # uint8_t c[16]
                            ]
_Twofish_encrypt.restype = None

_Twofish_decrypt = _twofish.exp_Twofish_decrypt
_Twofish_decrypt.argtypes = [ POINTER(_Twofish_key),
                              c_char_p,     # uint8_t c[16]
                              c_char_p      # uint8_t p[16]
                            ]
_Twofish_decrypt.restype = None

_Twofish_initialise()

IS_PY2 = sys.version_info < (3, 0, 0, 'final', 0)



def _ensure_bytes(data):
    if (IS_PY2 and not isinstance(data, str)) or (not IS_PY2 and not isinstance(data, bytes)):
        raise TypeError('can not encrypt/decrypt unicode objects')



class Twofish():
    def __init__(self, key):
        if not len(key) > 0 and len(key) <= 32:
            raise ValueError('invalid key length')
        _ensure_bytes(key)

        self.key = _Twofish_key()
        _Twofish_prepare_key(key, len(key), pointer(self.key))



    def encrypt(self, data):
        if not len(data) == 16:
            raise ValueError('invalid block length')
        _ensure_bytes(data)

        outbuf = create_string_buffer(len(data))
        _Twofish_encrypt(pointer(self.key), data, outbuf)
        return outbuf.raw



    def decrypt(self, data):
        if not len(data) == 16:
            raise ValueError('invalid block length')
        _ensure_bytes(data)

        outbuf = create_string_buffer(len(data))
        _Twofish_decrypt(pointer(self.key), data, outbuf)
        return outbuf.raw



def self_test():
    # Repeat the test on the same vectors checked at runtime by the library
    # 128-bit test is the I=3 case of section B.2 of the Twofish book.
    t128 = ('9F589F5CF6122C32B6BFEC2F2AE8C35A',
        'D491DB16E7B1C39E86CB086B789F5419',
        '019F9809DE1711858FAAC3A3BA20FBC3')

    # 192-bit test is the I=4 case of section B.2 of the Twofish book.
    t192 = ('88B2B2706B105E36B446BB6D731A1E88EFA71F788965BD44',
        '39DA69D6BA4997D585B6DC073CA341B2',
        '182B02D81497EA45F9DAACDC29193A65')

    # 256-bit test is the I=4 case of section B.2 of the Twofish book.
    t256 = ('D43BB7556EA32E46F2A282B7D45B4E0D57FF739D4DC92C1BD7FC01700CC8216F',
        '90AFE91BB288544F2C32DC239B2635E6',
        '6CB4561C40BF0A9705931CB6D408E7FA')

    for t in (t128, t192, t256):
        k = binascii.unhexlify(t[0])
        p = binascii.unhexlify(t[1])
        c = binascii.unhexlify(t[2])

        T = Twofish(k)
        if not T.encrypt(p) == c or not T.decrypt(c) == p:
            exit_with_msg('CRITICAL ERROR! Twofish library is corrupted.')

# Perform Twofish library self-test.
self_test()



def twofish_decrypt(ciphertext, HexKey):

    # Separate nonce from ciphertext.
    nonce          = ciphertext[:16]
    ciphertext     = ciphertext[16:]

    # Convert hexadecimal key to binary data.
    key            = binascii.unhexlify(HexKey)

    # n.o. keystream blocks equals the n.o. CT blocks.
    ctArray        = [ciphertext[i:i + 16] for i in range(0, len(ciphertext), 16)]

    keystream      = ''
    counter        = 1

    for block in ctArray:

        # Hash the counter value and output 64 hex numbers.
        counterHash = keccak_256(str(counter))

        # Convert the digest to 32-bit binary.
        counterBin  = binascii.unhexlify(counterHash)

        # Truncate length to 128 bits.
        ctr         = counterBin[:16]

        # XOR 128-bit nonce with 128-bit hash of counter to create IV of Twofish cipher.
        if len(ctr) == 16 and len(nonce) == 16:
            iv       = ''.join(chr(ord(msgLetter) ^ ord(keyLetter)) for msgLetter, keyLetter in zip(ctr, nonce))
        else:
            exit_with_msg('CRITICAL ERROR! Twofish counter hash - nonce length mismatch. Exiting.')

        # Initialize Twofish cipher with key.
        E           = Twofish(key)

        # Encrypt unique IV with key.
        keyBlock    = E.encrypt(iv)

        # Append new block to keystream.
        keystream  += keyBlock

        # Increase the counter of randomized CTR mode.
        counter    += 1

    # XOR keystream with ciphertext to acquire plaintext.
    if len(ciphertext) == len(keystream):
        plaintext = ''.join(chr(ord(msgLetter) ^ ord(keyLetter)) for msgLetter, keyLetter in zip(ciphertext, keystream))
    else:
        exit_with_msg('CRITICAL ERROR! Twofish ciphertext - keystream length mismatch.')

    # Remove padding.
    plaintext = plaintext[:-ord(plaintext[-1:])]

    return plaintext



######################################################################
#     AES (GCM) AUTHENTICATED ENCRYPTION (RIJNDAEL BLOCK CIPHER)     #
######################################################################

"""
#  Cipher/AES.py : AES
# ===================================================================
# The contents of this file are dedicated to the public domain.  To
# the extent that dedication to the public domain is not available,
# everyone is granted a worldwide, perpetual, royalty-free,
# non-exclusive license to exercise all rights associated with the
# contents of this file for any purpose whatsoever.
# No rights are reserved.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,

# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
# BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN

# ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

PyCrypto licence (https://raw.githubusercontent.com/dlitz/pycrypto/master/COPYRIGHT)
To the best of our knowledge, with the exceptions noted below or
within the files themselves, the files that constitute PyCrypto are in
the public domain. Most are distributed with the following notice:
The contents of this file are dedicated to the public domain. To
the extent that dedication to the public domain is not available,
everyone is granted a worldwide, perpetual, royalty-free,
non-exclusive license to exercise all rights associated with the
contents of this file for any purpose whatsoever.
No rights are reserved.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
"""

from Crypto.Cipher import AES

try:
    import Crypto.Random.random
    secure_random = Crypto.Random.random.getrandbits

except ImportError:
    import OpenSSL
    print 'WARNING Failed to import Crypto.Random, trying OpenSSL instead.'
    secure_random = lambda x: long(hexlify(OpenSSL.rand.bytes(x>>3)), 16)



def AES_GCM_decrypt(ctInput, hexKey):

    nonce      = ctInput[:64]
    ciphertext = ctInput[64:-16]
    mac        = ctInput[-16:]

    AESkey     = binascii.unhexlify(hexKey)
    cipher     = AES.new(AESkey, AES.MODE_GCM, nonce)
    cipher.update('')

    plaintext  = cipher.decrypt(ciphertext)

    try:
        cipher.verify(mac)
        return plaintext

    except ValueError:
        os.system('clear')
        print "\nWARNING! MAC verification failed! This might mean someone is tampering your messages!\n"
        return None

    except TypeError:
        os.system('clear')
        print "\nWARNING! MAC verification failed! This might mean someone is tampering your messages!\n"
        return None



######################################################################
#                    DECRYPTION AND KEY MANAGEMENT                   #
######################################################################

def get_keyset(xmpp, output=True):
    try:
        keySet = []

        with open(xmpp + '.e', 'r') as file:
            keyFile = file.readlines()

        for line in keyFile:
            key = line.strip('\n')

            # Verify keys in keyfile have proper hex-format.
            validChars = ['0','1','2','3','4','5','6','7','8','9','A',
                          'B','C','D','E','F','a','b','c','d','e','f']

            for char in key:
                if not char in validChars:
                    exit_with_msg('CRITICAL ERROR! Illegal char \'' + str(char) + '\' in keyfile\n' + xmpp + '.e.')


            # Verify keys are of proper length.
            if len(key) != 64:
                exit_with_msg('CRITICAL ERROR! Illegal length key in keyfile\n' + xmpp + '.e. Exiting.')
            else:
                keySet.append(key)

        # Verify that four keys were loaded.
        if len(keySet) != 4:
            exit_with_msg('CRITICAL ERROR! Keyfile ' + xmpp + '.e\nhas illegal number of keys.')

        # Verify that all keys are unique.
        if any(keySet.count(key) > 1 for key in keySet):
            exit_with_msg('CRITICAL ERROR! Two identical keys in keyfile\n' + xmpp + '.e.')

        if debugging and output:
            print '\nM(get_keyset): Loaded following set of keys for XMPP' + xmpp + '\n'
            for key in keySet:
                print key

        return keySet

    except IOError:
        exit_with_msg('CRITICAL ERROR! Failed to open keyfile for XMPP\n' + xmpp + '.')



def rotate_keyset(xmpp, keySet):
    try:

        newKeys = []
        with open(xmpp + '.e', 'w+') as file:
            for key in keySet:
                newKey = keccak_256(key)
                newKeys.append(newKey)
                file.write(newKey + '\n')

        if debugging:
            print '\nM(rotate_keyset): Wrote following keys for contact ' + xmpp + '\n'
            for key in newKeys:
                print key

        # Verify that keys were successfully written.
        storedKeySet = get_keyset(xmpp, False)

        if newKeys != storedKeySet:
            exit_with_msg('CRITICAL ERROR! Next keyset was not properly stored.')

        else:
            if debugging:
                print '\nM(rotate_keys): Key overwriting successful.\n'

    except IOError:
        exit_with_msg('CRITICAL ERROR! Keyfile ' + xmpp + '.e\ncould not be loaded.')



def decrypt(xmpp, ct4, keyID):

    # Load expected keyset.
    keySet       = get_keyset(xmpp)

    # Calculate offset of contact's keyset.
    storedKeyID  = int(get_keyID(xmpp))
    contactKeyID = int(keyID)
    offset       = contactKeyID - storedKeyID


    if offset > 0:

        # Notify user about missing messages implicated by the offset.
        if xmpp == 'rx.local':
            print '\nATTENTION! The last ' + str(offset) + ' commands\nhave not been received from TxM.\n'
        elif xmpp.startswith('me.'):
            print '\nATTENTION! The last ' + str(offset) + ' messages sent to contact\n' + xmpp[3:] + ' have not been received from TxM.\n'
        else:
            print '\nATTENTION! The last ' + str(offset) + ' messages have not\nbeen received from ' + xmpp[3:] + '.\n'

        # Iterate keyset through Keccak hash function until there is no offset.
        i = 0
        while i < offset:
            n = 0
            while n < 4:
                keySet[n] = keccak_256(keySet[n])
                n += 1
            i+=1

    # Decrypt ciphertext.
    ct3 = AES_GCM_decrypt  (ct4, keySet[3])
    ct2 = twofish_decrypt  (ct3, keySet[2])
    ct1 = salsa_20_decrypt (ct2, keySet[1])
    pt  = keccak_decrypt   (ct1, keySet[0])

    # Store next keyset.
    rotate_keyset(xmpp, keySet)

    # Store keyID.
    write_keyID(xmpp, contactKeyID + 1)

    return pt



######################################################################
#                        rxc.tfc MANAGEMENT                          #
######################################################################

def add_contact(nick, xmpp):
    try:
        with open('rxc.tfc', 'a+') as file:
                file.write(nick + ',' + xmpp + ',1\n')

        if debugging:
            print '\nM(add_contact): Added contact ' + nick + ' (xmpp = ' + xmpp + ') to rxc.tfc\n'

    except IOError:
        exit_with_msg('ERROR! rxc.tfc could not be loaded. Exiting.')



def write_nick(xmpp, nick):
    try:
        contacts = []

        with open ('rxc.tfc', 'r') as file:
            csvData = csv.reader(file)

            for row in csvData:
                contacts.append(row)

        nickChanged = False

        for i in range( len(contacts) ):
            if contacts[i][1] == xmpp:
                contacts[i][0] = nick
                nickChanged = True

        if not nickChanged:
            exit_with_msg('ERROR! Could not find XMPP\n' + xmpp + ' from rxc.tfc.')


        with open('rxc.tfc', 'w') as file:
            writer = csv.writer(file)
            writer.writerows(contacts)

        if debugging:
            print '\nM(write_nick):\nWrote nick ' + nick + ' for account ' + xmpp + ' to rxc.tfc\n'

    except IOError:
        exit_with_msg('ERROR! rxc.tfc could not be loaded.')



def get_nick(xmpp):
    try:
        contacts = []

        with open('rxc.tfc', 'r') as file:
            csvData = csv.reader(file)

            for row in csvData:
                contacts.append(row)

        for i in range( len(contacts) ):
            if contacts[i][1] == xmpp:
                nick = contacts[i][0]
                return nick

        exit_with_msg('ERROR! Failed to load nick for contact.')

    except IOError:
        exit_with_msg('ERROR! rxc.tfc could not be loaded.')



def write_keyID(xmpp, keyID):
    try:
        contacts = []

        with open('rxc.tfc', 'r') as file:
            csvData = csv.reader(file)

            for row in csvData:
                contacts.append(row)

        keyIDChanged = False

        for i in range(len(contacts) ):
            if contacts[i][1] == xmpp:
                contacts[i][2] = keyID
                keyIDChanged   = True

        if not keyIDChanged:
            exit_with_msg('ERROR! Could not find XMPP\n' + xmpp + ' from rxc.tfc.')

        with open('rxc.tfc', 'w') as file:
            writer = csv.writer(file)
            writer.writerows(contacts)

        # Verify keyID has been properly written.
        newStoredKey = get_keyID(xmpp)
        if keyID != newStoredKey:
            exit_with_msg('CRITICAL ERROR! KeyID was not properly stored.')


        if debugging:
            print '\nM(write_keyID): Wrote line \'' + str(keyID) + '\' for contact ' + xmpp + ' to rxc.tfc\n'

    except IOError:
        exit_with_msg('ERROR! rxc.tfc could not be loaded.')



def get_keyID(xmpp):
    try:
        contacts = []

        with open('rxc.tfc', 'r') as file:
            csvData = csv.reader(file)

            for row in csvData:
                contacts.append(row)

        for i in range( len(contacts) ):
            if contacts[i][1] == xmpp:
                keyID = int(contacts[i][2])

        # Verify keyID is positive.
        if keyID > 0:
            return keyID
        else:
            exit_with_msg('ERROR! Failed to load valid keyID for XMPP\n' + xmpp + '.')

    except ValueError:
        exit_with_msg('ERROR! Failed to load valid keyID for XMPP\n' + xmpp + '.')

    except IOError:
        exit_with_msg('ERROR! rxc.tfc could not be loaded.')



def add_keyfiles(keyFileNames):
    try:
        contacts = []

        with open('rxc.tfc', 'a+') as file:
            csvData = csv.reader(file)

            for row in csvData:
                contacts.append(row)

        for fileName in keyFileNames:
            onList = False
            xmpp   = fileName[:-2]

            for user in contacts:
                if xmpp in user[1]:
                    onList = True

            if not onList:

                if xmpp == 'tx.local':
                    continue

                if xmpp == 'rx.local':
                    add_contact('rx.local', 'rx.local')
                    continue

                if xmpp.startswith('me.'):
                    localNick = xmpp.split('@')[0][3:]
                    add_contact('me.' + localNick, xmpp)
                    continue

                if xmpp.startswith('rx.'):
                    os.system('clear')
                    print 'TFC ' + version + ' || Rx.py\n'
                    newNick = raw_input('New contact ' + xmpp[3:] + ' found. Enter nick: ')
                    add_contact(newNick, xmpp)

    except IOError:
        exit_with_msg('ERROR! rxc.tfc could not be loaded.')



######################################################################
#                             GETTERS                                #
######################################################################

def get_keyfile_list():
    keyFileList = []

    for file in os.listdir('.'):
        if file.endswith('.e') and not file.startswith('tx.'):
            keyFileList.append(file)
    return keyFileList



######################################################################
#                        CHECKS AND WARNINGS                         #
######################################################################

def search_keyfiles():
    keyfiles  = []
    keyfiles += [each for each in os.listdir('.') if each.endswith('.e')]
    if not keyfiles:
        exit_with_msg('Error: No keyfiles for contacts were found.\n'\
                      'Make sure keyfiles are in same directory as Rx.py\n')



def disp_opsec_warning():
    print '''
REMEMBER! DO NOT MOVE RECEIVED FILES FROM RxM TO LESS SECURE
ENVIRONMENTS INCLUDING UNENCRYPTED SYSTEMS, ONES IN PUBLIC USE,
OR TO ANY SYSTEM THAT HAS NETWORK-CAPABILITY, OR THAT MOVES
FILES TO A COMPUTER WITH NETWORK CAPABILITY.

DOING SO WILL RENDER DATA-DIODE PROTECTION USELESS, AS MALWARE
\'STUCK IN RXM\' CAN EASILY EXFILTRATE KEYS AND/OR PLAINTEXT
THROUGH THIS RETURN CHANNEL!

IF YOU NEED TO RETRANSFER A DOCUMENT, EITHER READ IT FROM RxM SCREEN
USING OPTICAL CHARACTER RECOGNITION (OCR) SOFTWARE RUNNING ON TxM,
OR USE A PRINTER TO EXPORT THE DOCUMENT, AND A SCANNER TO READ IT TO
TxM FOR ENCRYPTED RE-TRANSFER. REMEMBER TO DESTROY THE PRINTS, AND IF
YOUR LIFE DEPENDS ON IT, THE PRINTER AND SCANNER AS WELL.\n'''



######################################################################
#                         MSG PROCESSING                             #
######################################################################

def base64_decode(content):
    import base64
    return base64.b64decode(content)



def crc32(content):
    import zlib
    return str(hex(zlib.crc32(content)))



def depadding(string):
    return string[:-ord(string[-1:])]



######################################################################
#                         MESSAGE RECEPTION                          #
######################################################################

def clear_msg_file():
    if localTesting:
        if injectionTesting:
            open('INoutput', 'w+').close()
        open('NHoutput', 'w+').close()



def load_message_from_file():
    if injectionTesting:
        with open('INoutput', 'r') as file:
            message = file.readline()

        if debugging and message != '':
            print '\n\nM(load_message_from_file): Loaded following message \n' + message + '\n'

        return message

    else:
        with open('NHoutput', 'r') as file:
            message = file.readline()

        if debugging and message != '':
            print '\n\nM(load_message_from_file): Loaded following message \n' + message + '\n'

        return message



######################################################################
#                       COMMANDS AND FUNCTIONS                       #
######################################################################

def write_log_entry(nick, xmpp, message):

    message = message.strip('\n')

    with open('logs.' + xmpp + '.tfc', 'a+') as file:
        file.write( datetime.datetime.now().strftime(logTimeStampFmt) + ' ' + nick + ': ' + message + '\n' )

    if debugging:
        print '\nM(write_log_entry): Added log entry \n\'' + message + '\' for contact ' + xmpp + '\n'



def packet_anomality(errorType='', packetType=''):

    errorMsg = ''

    if errorType == 'MAC':
        print 'WARNING! MAC of received ' + packetType + ' failed!\n' \
              'This might indicate an attempt to tamper ' + packetType + 's!\n'
        errorMsg = 'AUTOMATIC LOG ENTRY: MAC of ' + packetType + ' failed.'

    if errorType == 'replay:':
        print 'WARNING! Received a ' + packetType + ', the key-id of which is not valid!\n' \
              'This might indicate tampering or keyfile mismatch.'
        errorMsg = 'AUTOMATIC LOG ENTRY: Replayed ' + packetType +' detected.'

    if errorType == 'tamper':
        print 'WARNING! Received a ' + packetType + ' that appears to be malformed!\n'\
              'This might indicate tampering of packets.'
        errorMsg = 'AUTOMATIC LOG ENTRY: Possibly tampered ' + packetType + ' detected.'

    if errorType == 'crc':
        print 'WARNING! Received a ' + packetType + ', the CRC of which failed!\n' \
              'This might indicate tampering or problem with your RxM Datadiode.'
        errorMsg = 'AUTOMATIC LOG ENTRY: CRC error in ' + packetType + '.'

    if errorType == 'hash':
        print 'WARNING! The hash of received long ' + packetType + ' failed!\n' \
              'The file was rejected.'
        errorMsg = 'AUTOMATIC LOG ENTRY: hash error in long ' + packetType + '.'

    if logTamperingEvent:
        with open('syslog.tfc', 'a+') as file:
            file.write( datetime.datetime.now().strftime(logTimeStampFmt) + errorMsg + '\n')
        print '\nThis event has been logged to syslog.tfc.\n'



def exit_with_msg(message, error=True):
    os.system('clear')
    if error:
        print '\n' + message + ' Exiting.\n'
    else:
        print '\n' + message + '\n'
    exit()



def store_file(preName, fileName):
    if not os.path.isfile('f.' + preName + '.tfc'):
        print '\nError: Could not find tmp file.\n'
        return None

    if os.path.isfile(fileName):
        os.system('clear')
        print '\nError: file already exists. Please use different file name.\n'
        return None

    if fileName != 'r':
        subprocess.Popen('base64 -d f.' + preName + '.tfc > ' + fileName, shell=True).wait()
        print '\nStored tmp file \'f.' + preName + '.tfc\' as \'' + fileName + '\'.'
        subprocess.Popen('shred -n ' + str(kfOWIterations) + ' -z -u f.' + preName + '.tfc', shell=True).wait()
        print 'Temporary file \'f.' + preName + '.tfc\' has been overwritten.\n'
        disp_opsec_warning()

    else:
        subprocess.Popen('shred -n ' + str(kfOWIterations) + ' -z -u f.' + preName + '.tfc', shell=True).wait()
        print 'Temporary file \'f.' + preName + '.tfc\' was rejected and overwritten.\n'

    return None



######################################################################
#                             PRE LOOP                               #
######################################################################

# Set initial values.
os.chdir(sys.path[0])
longMsgComplete  = False
fileReceive      = False
longMsg          = {}

# Run initial checks.
clear_msg_file()
search_keyfiles()

# Load initial data.
keyFileNames     = get_keyfile_list()
add_keyfiles(keyFileNames)

os.system('clear')
header = 'TFC ' + version + ' || Rx.py '

# Display configuration on header during start of program.
if logMessages:
    header += '|| Logging on '
else:
    header += '|| Logging off '

if fileSavingAllowed:
    header += '|| File reception on'
else:
    header += '|| File reception off'

print header + '\n'


# Set initial status of file and message reception.
longMsgOnWay = {}
msgReceived  = {}
message      = {}
for key in keyFileNames:
    xmpp               = key[:-2]
    longMsgOnWay[xmpp] = False
    msgReceived[xmpp]  = False
    message[xmpp]      = ''


if fileSavingAllowed:
    fileOnWay    = {}
    fileReceived = {}
    fileA        = {}
    for key in keyFileNames:
        xmpp               = key[:-2]
        fileOnWay[xmpp]    = False
        fileReceived[xmpp] = False
        fileA[xmpp]        = ''



######################################################################
#                               LOOP                                 #
######################################################################

try:
    while True:
        sleep(0.01)
        receivedPacket = ''

        if localTesting:
            try:
                receivedPacket = load_message_from_file()
                if not receivedPacket.endswith('\n'):
                    continue
            except IOError:
                continue

            clear_msg_file()

        else:
            receivedPacket = port.readline()


        if not (receivedPacket == ''):
            try:

                # Process unencrypted commands.
                if receivedPacket.startswith('EXITTFC'):
                    exit_with_msg('Exiting TFC.', False)


                if receivedPacket.startswith('CLEARSCREEN'):
                    os.system('clear')
                    continue


                ####################################
                #         ENCRYPED COMMANDS        #
                ####################################
                if receivedPacket.startswith('<ctrl>'):
                    cmdMACln, crcPkg = receivedPacket[6:].split('~')
                    crcPkg           = crcPkg.strip('\n')


                    # Check that CRC32 Matches.
                    if crc32(cmdMACln) != crcPkg:
                        packet_anomality('crc', 'command')
                        continue

                    payload, keyID = cmdMACln.split('|')
                    ciphertext     = base64_decode(payload)


                    try:
                        # Check that keyID is fresh.
                        if int(keyID) < get_keyID('rx.local'):
                            packet_anomality('replay', 'command')
                            continue

                    except KeyError:
                        packet_anomality('tamper', 'command')
                        continue

                    except TypeError:
                        packet_anomality('tamper', 'command')
                        continue


                    # Check that local keyfile for decryption exists.
                    if not os.path.isfile('rx.local.e'):
                        print '\nError: rx.local.e was not found.\n'\
                              'Command could not be decrypted.\n'
                        continue


                    # Decrypt command if MAC verification succeeds.
                    try:
                        paddedCommand = decrypt('rx.local', ciphertext, keyID)
                        command       = depadding(paddedCommand)

                    except ValueError:
                            packet_anomality('MAC', 'command')
                            continue
                    except TypeError:
                            packet_anomality('MAC', 'command')
                            continue


                    ##########################
                    #     Enable logging     #
                    ##########################
                    if command == 'LOGSON':
                        if logChangeAllowed:
                            if logMessages:
                                print 'Logging is already enabled.'
                            else:
                                logMessages = True
                                print 'Logging has been enabled.'
                            continue

                        else:
                            print '\nLogging settings can not be altered: Boolean\n'\
                                  'value \'logChangeAllowed\' is set to False.\n'
                            continue


                    ###########################
                    #     Disable logging     #
                    ###########################
                    if command == 'LOGSOFF':
                        if logChangeAllowed:
                            if not logMessages:
                                print 'Logging is already disabled.'
                            else:
                                logMessages = False
                                print 'Logging has been disabled.'
                            continue

                        else:
                            print '\nLogging settings can not be altered: Boolean\n'\
                                  'value \'logChangeAllowed\' is set to False.\n'
                            continue


                    #################################
                    #     Decode and store file     #
                    #################################
                    if command.startswith('STOREFILE '):
                        notUsed, tmpName, outoutName = command.split(' ')
                        store_file(tmpName, outoutName)
                        continue


                    #######################
                    #     Change nick     #
                    #######################
                    if command.startswith('NICK '):

                        notUsed, xmpp, nick = command.split(' ')

                        # Write and load nick.
                        write_nick(xmpp, nick)
                        storedNick = get_nick(xmpp)

                        print '\nChanged ' + xmpp[3:] + ' nick to \'' + storedNick + '\'\n'
                        continue


                ####################################
                #         NORMAL MESSAGE           #
                ####################################
                if receivedPacket.startswith('<mesg>'):
                    xmpp, ctMACln, crcPkg = receivedPacket[6:].split('~')
                    crcPkg = crcPkg.strip('\n')


                    # Check that CRC32 Matches.
                    if crc32(ctMACln) != crcPkg:
                        packet_anomality('crc', 'message')
                        continue

                    payload, keyID = ctMACln.split('|')
                    ciphertext     = base64_decode(payload)


                    try:
                        # Check that keyID is fresh.
                        if int(keyID) < get_keyID(xmpp):
                            packet_anomality('replay', 'message')
                            continue

                    except KeyError:
                        packet_anomality('tamper', 'message')
                        continue

                    except TypeError:
                        packet_anomality('tamper', 'message')
                        continue

                    # Check that keyfile for decryption exists.
                    if not os.path.isfile(xmpp + '.e'):
                        print '\nError: keyfile for contact ' + xmpp + 'was not found.\n' \
                              'Message could not be decrypted.\n'
                        continue


                    # Decrypt message if MAC verification succeeds.
                    try:
                        decryptedPacket = decrypt(xmpp, ciphertext, keyID)
                        decryptedPacket = depadding(decryptedPacket)

                    except ValueError:
                            packet_anomality('MAC', 'message')
                            continue

                    except TypeError:
                            packet_anomality('MAC', 'message')
                            continue


                    #########################################################
                    #     Process cancelled messages and file transfers     #
                    #########################################################
                    '''
                    All received message/ file packets have header {s,l,a,e,c}{m,f}.

                    Second character:
                        m = message
                        f = file

                    First character:
                        s = short packet: message can be shown or stored immediately.

                        l = first     packet of long msg / file
                        a = appended  packet of long msg / file
                        e = last      packet of long msg / file, can be shown / stored.
                        c = cancelled packet of long msg / file, discarts packet content.

                    '''

                    # Cancel file.
                    if decryptedPacket.startswith('cf'):
                        if fileOnWay[xmpp]:
                            if xmpp.startswith('me.'):
                                print 'File transmission to contact \'' + xmpp[3:] + '\' cancelled.\n'
                            if xmpp.startswith('rx.'):
                                print 'Contact \'' + xmpp[3:] + '\' cancelled file transmission.\n'

                            fileOnWay[xmpp]    = False
                            fileReceived[xmpp] = False
                            fileA[xmpp]        = ''
                            continue

                    # Cancel message.
                    if decryptedPacket.startswith('cm'):
                        if longMsgOnWay[xmpp]:
                            if xmpp.startswith('me.'):
                                print 'Long message to contact \'' + xmpp[3:] + '\' cancelled.\n'
                            if xmpp.startswith('rx.'):
                                print 'Contact \'' + xmpp[3:] + '\' cancelled long message.\n'

                            longMsgOnWay[xmpp] = False
                            msgReceived[xmpp]  = False
                            message[xmpp]      = ''
                            continue


                    #####################################################
                    #     Process short messages and file transfers     #
                    #####################################################

                    # Even if cf / cm packet dropped, Rx.py should inform user
                    # about interrupted reception of long message / file when
                    # short message / file is received.

                    # Short file.
                    if decryptedPacket.startswith('sf'):
                        if fileOnWay[xmpp]:
                            if xmpp.startswith('me.'):
                                print 'File transmission to contact \'' + xmpp[3:] + '\' cancelled.\n'
                            if xmpp.startswith('rx.'):
                                print 'Contact \'' + xmpp[3:] + '\' cancelled file transmission.\n'

                        if fileSavingAllowed:
                            fileReceived[xmpp] = True
                            fileOnWay[xmpp]    = False
                            fileA[xmpp]        = decryptedPacket[2:]


                    # Short message.
                    if decryptedPacket.startswith('sm'):
                        if longMsgOnWay[xmpp]:
                            if xmpp.startswith('me.'):
                                print 'Long message to contact \'' + xmpp[3:] + '\' cancelled.\n'
                            if xmpp.startswith('rx.'):
                                print 'Contact \'' + xmpp[3:] + '\' cancelled long message.\n'

                        msgReceived[xmpp]  = True
                        longMsgOnWay[xmpp] = False
                        message[xmpp]      = decryptedPacket[2:]



                    ####################################################
                    #     Process long messages and file transfers     #
                    ####################################################

                    # Header packet of long file.
                    if decryptedPacket.startswith('lf'):
                        if fileOnWay[xmpp]:
                            if xmpp.startswith('me.'):
                                print 'File transmission to contact \'' + xmpp[3:] + '\' cancelled.\n'
                            if xmpp.startswith('rx.'):
                                print 'Contact \'' + xmpp[3:] + '\' cancelled file transmission.\n'

                        # Print notification about receiving file.
                        if fileSavingAllowed:
                            if xmpp.startswith('me.'):
                                print'\nReceiving file sent to \''       + xmpp[3:] + '\'.\n'
                            if xmpp.startswith('rx.'):
                                print '\nReceiving file from contact \'' + xmpp[3:] + '\'.\n'

                            fileReceived[xmpp] = False
                            fileOnWay[xmpp]    = True
                            fileA[xmpp]        = decryptedPacket[2:]
                            continue


                    # Header packet of long message.
                    if decryptedPacket.startswith('lm'):
                        if longMsgOnWay[xmpp]:
                            if xmpp.startswith('me.'):
                                print 'Long message to contact \'' + xmpp[3:] + '\' cancelled.\n'
                            if xmpp.startswith('rx.'):
                                print 'Contact \'' + xmpp[3:] + '\' cancelled long message.\n'

                        if showLongMsgWarning:
                            if xmpp.startswith('me.'):
                                print '\nReceiving long message sent to \''      + xmpp[3:] + '\'.\n'
                            if xmpp.startswith('rx.'):
                                print '\nReceiving long message from contact \'' + xmpp[3:] + '\'.\n'

                        msgReceived[xmpp]  = False
                        longMsgOnWay[xmpp] = True
                        message[xmpp]      = decryptedPacket[2:]
                        continue


                    # Append packet of long file.
                    if decryptedPacket.startswith('af'):
                            if fileSavingAllowed:

                                fileReceived[xmpp] = False
                                fileOnWay[xmpp]    = True
                                fileA[xmpp]        = fileA[xmpp] + decryptedPacket[2:]
                                continue


                    # Append packet of long message.
                    if decryptedPacket.startswith('am'):

                            msgReceived[xmpp]  = False
                            longMsgOnWay[xmpp] = True
                            message[xmpp]      = message[xmpp] + decryptedPacket[2:]
                            continue


                    #Final packet of long file.
                    if decryptedPacket.startswith('ef'):
                        if fileSavingAllowed:

                            fileA[xmpp] = fileA[xmpp] + decryptedPacket[2:]

                            fileContent = fileA[xmpp][:-64]
                            hashOfFile  = fileA[xmpp][-64:]

                            if keccak_256(fileContent) != hashOfFile:
                                os.system('clear')
                                packet_anomality('hash', 'file')
                                continue

                            fileA[xmpp]        = fileContent
                            fileReceived[xmpp] = True
                            fileOnWay[xmpp]    = False


                    #Final packet of long message.
                    if decryptedPacket.startswith('em'):

                        message[xmpp] = message[xmpp] + decryptedPacket[2:]

                        msgContent = message[xmpp][:-64]
                        hashOfMsg  = message[xmpp][-64:]

                        if keccak_256(msgContent) != hashOfMsg:
                            os.system('clear')

                            packet_anomality('hash', 'message')
                            continue

                        message[xmpp]      = msgContent
                        msgReceived[xmpp]  = True
                        longMsgOnWay[xmpp] = False



                    ######################################
                    #     Process printable messages     #
                    ######################################
                    if msgReceived[xmpp]:

                        if xmpp.startswith('me.'):
                            nick = 'Me > ' + get_nick('rx' + xmpp[2:])
                        else:
                            nick = 5 * ' ' + get_nick(xmpp)


                        # Print timestamp and message to user.
                        if displayTime:
                            msgTime = datetime.datetime.now().strftime(displayTimeFmt)
                            print msgTime + '  ' + nick + ':  ' + message[xmpp]
                        else:
                            print                  nick + ':  ' + message[xmpp]


                        # Log messages if logging is enabled.
                        if logMessages:
                            if nick.startswith('Me > '):
                                spacing = len(get_nick('rx' + xmpp[2:]))
                                nick    = (spacing - 2) * ' ' + 'Me'
                                write_log_entry(nick, xmpp[3:], message[xmpp])
                            else:
                                write_log_entry(nick[5:], xmpp[3:], message[xmpp])

                        msgReceived[xmpp]  = False
                        longMsgOnWay[xmpp] = False
                        message[xmpp]      = ''
                        continue



                    ##################################
                    #     Process received files     #
                    ##################################
                    if fileReceived[xmpp]:

                        # Generate random filename.
                        tmpFileName = 'f.' + str(binascii.hexlify(os.urandom(2))) + '.tfc'
                        while os.path.isfile(tmpFileName):
                            tmpFileName = 'f.' + str(binascii.hexlify(os.urandom(2))) + '.tfc'

                        # Store file.
                        with open(tmpFileName, 'w+') as file:
                            file.write(fileA[xmpp])

                        if xmpp.startswith('me.'):
                            print 'File sent to contact \'' + xmpp[3:] + '\' received locally.\n'
                        if xmpp.startswith('rx.'):
                            print 'File transmission from contact \'' + xmpp[3:] + '\' complete.\n'

                        print 'Stored base64 encoded file under temporary file name \'' + tmpFileName + '\'.\n'   \
                              'Use command \'/store ' + tmpFileName[2:][:-4] + ' <desired file name>\' to obtain file or\n'\
                              'use command \'/store ' + tmpFileName[2:][:-4] + ' r\' to reject file.\n'

                        fileReceived[xmpp] = False
                        fileOnWay[xmpp]    = False
                        fileA[xmpp]        = ''
                        continue

                    else:
                        continue

            except IndexError:
                os.system('clear')
                packet_anomality('tamper', 'packet')
                continue

            except ValueError:
                os.system('clear')
                packet_anomality('tamper', 'packet')
                continue

except KeyboardInterrupt:
    exit_with_msg('Exiting TFC.', False)


