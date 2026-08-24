#!/bin/env python3
##
#  Copyright 2026 Univ. Grenoble Alpes, Inria, TIMA Laboratory
#
#  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
##
##
#  Author     : Cesar Fuguet
#  Date       : March, 2026
#  Description: short nonregression script
##
import struct

class MemOp:
    """Memory Operation Type Definition
    """
    def __init__(self):
        self.delay = 0
        self.addr = 0
        self.size = 0
        self.is_cacheable = False
        self.is_store = False
        self.needs_reponse = False
        self.wdata = 0xbabef00ddeadbeef

    def __str__(self):
        retString  = "STORE" if self.is_store else "LOAD"
        retString += "/ @={}".format(self.addr)
        retString += "/ SIZE={}".format(self.size)
        retString += "/ WDATA={}".format(self.wdata) if self.is_store else ""
        retString += "/ CACHEABLE" if self.is_cacheable else ""
        retString += "/ NEEDS_RESPONSE" if self.needs_reponse else ""
        return retString

    def initCacheableLoad(self, addr, size, delay=0):
        self.delay = delay
        self.addr = addr
        self.size = size
        self.is_cacheable = True
        self.is_store = False
        self.needs_reponse = True

    def initIOLoad(self, addr, size, delay=0):
        self.delay = delay
        self.addr = addr
        self.size = size
        self.is_cacheable = False
        self.is_store = False
        self.needs_reponse = True

    def initCacheableStore(self, addr, size, wdata, delay=0):
        self.delay = delay
        self.addr = addr
        self.size = size
        self.is_cacheable = True
        self.is_store = True
        self.needs_reponse = False
        self.wdata = wdata

    def initIOStore(self, addr, size, wdata, delay=0):
        self.delay = delay
        self.addr = addr
        self.size = size
        self.is_cacheable = False
        self.is_store = True
        self.needs_reponse = False
        self.wdata = wdata

    def packFlags(self):
        ret  = 0
        ret |= 0x1 if  self.is_cacheable else 0
        ret |= 0x2 if self.needs_reponse else 0
        ret |= 0x4 if      self.is_store else 0
        return ret

    def pack(self):
        if self.is_store:
            return struct.pack('<BQBBQ',
                    self.delay,
                    self.addr,
                    self.size,
                    self.packFlags(),
                    self.wdata)

        return struct.pack('<BQBB',
                self.delay,
                self.addr,
                self.size,
                self.packFlags())

    def unpack(self, val):
        unpacked = struct.unpack('<BQBBQ', val)
        self.delay = unpacked[0]
        self.addr = unpacked[1]
        self.size = unpacked[2]
        self.is_cacheable = unpacked[3] & 0x1
        self.needs_reponse = unpacked[3] & 0x2
        self.is_store = unpacked[3] & 0x4
        self.wdata = unpacked[4]

if __name__ == '__main__':
    with open("test.bin", 'wb') as f:
        op = MemOp()

        op.initCacheableLoad(0x80000000, 3)
        f.write(op.pack())

        op.initCacheableLoad(0x80000040, 3)
        f.write(op.pack())

        op.initCacheableLoad(0x80000080, 3)
        f.write(op.pack())

        op.initCacheableStore(0x80000040, 3, 0xbabef00d)
        f.write(op.pack())

        op.initCacheableStore(0x80000048, 3, 0xcafecafe)
        f.write(op.pack())

        op.initCacheableLoad(0x80000040, 3)
        f.write(op.pack())
