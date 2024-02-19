#!/usr/bin/python
import time
#import rsa
import random
import hashlib
import secrets
import math
#poolsize = 8
#accurate = True
import copy
import os
import sys
from hashlib import sha256
# Primality Testing with the Rabin-Miller Algorithm
# http://inventwithpython.com/hacking (BSD Licensed)
debug = False

def get_FileSize(filePath):
    filePath = str(filePath)
    fsize = os.path.getsize(filePath)
    fsize = fsize / float(1024)
    return round(fsize, 4)

RSA_KEY_SIZE = 3072  # RSA key size for 128 bits of security (modulu size)3072
RSA_PRIME_SIZE = int(RSA_KEY_SIZE / 2)
ACCUMULATED_PRIME_SIZE = 128  #128

def rabin_miller(num):
    # Returns True if num is a prime number.

    s = num - 1
    t = 0
    while s % 2 == 0:
        # keep halving s while it is even (and use t
        # to count how many times we halve s)
        s = s // 2
        t += 1

    for trials in range(5): # try to falsify num's primality 5 times
        a = random.randrange(2, num - 1)
        v = pow(a, s, num)
        if v != 1: # this test does not apply if v is 1.
            i = 0
            while v != (num - 1):
                if i == t - 1:
                    return False
                else:
                    i = i + 1
                    v = (v ** 2) % num
    return True


def is_prime(num):
    # Return True if num is a prime number. This function does a quicker
    # prime number check before calling rabin_miller().

    if (num < 2):
        return False # 0, 1, and negative numbers are not prime

    # About 1/3 of the time we can quickly determine if num is not prime
    # by dividing by the first few dozen prime numbers. This is quicker
    # than rabin_miller(), but unlike rabin_miller() is not guaranteed to
    # prove that a number is prime.
    lowPrimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

    if num in lowPrimes:
        return True

    # See if any of the low prime numbers can divide num
    for prime in lowPrimes:
        if (num % prime == 0):
            return False

    # If all else fails, call rabin_miller() to determine if num is a prime.
    return rabin_miller(num)


def generate_large_prime(num_of_bits):
    while True:
        num = secrets.randbelow(pow(2, num_of_bits))
        if is_prime(num):
            return num


def generate_two_large_distinct_primes(num_of_bits):
    p = generate_large_prime(num_of_bits)
    while True:
        q = generate_large_prime(num_of_bits)
        while q != p:
            return p, q

def hash_to_prime(x, num_of_bits=128, nonce=0):
    while True:
        num = hash_to_length(x + nonce, num_of_bits)
        if is_prime(num):
            return num, nonce
        nonce = nonce + 1


def hash_to_length(x, num_of_bits):
    pseudo_random_hex_string = ""
    num_of_blocks = math.ceil(num_of_bits / 256)
    for i in range(0, num_of_blocks):
        pseudo_random_hex_string += hashlib.sha256(str(x + i).encode()).hexdigest()

    if num_of_bits % 256 > 0:
        pseudo_random_hex_string = pseudo_random_hex_string[int((num_of_bits % 256)/4):]  # we do assume divisible by 4
    return int(pseudo_random_hex_string, 16)

def hash_to_integer(s):
    h = int(sha256(str(s).encode('utf-8')).hexdigest(), base=16) % (2 ** 128)
    return h


def xgcd(b, a):
    x0, x1, y0, y1 = 1, 0, 0, 1
    while a != 0:
        q, b, a = b // a, a, b % a
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return b, x0, y0


def mul_inv(b, n):
    g, x, _ = xgcd(b, n)
    if g == 1:
        return x % n


def concat(*arg):
    res = ""
    for i in range(len(arg)):
        res += str(arg[i])
    return res


def bezoute_coefficients(a, b):
    o = xgcd(a, b)
    return o[1], o[2]


class RSASeq:
    def __init__(self, RSA_KEY_SIZE, len, level):
        #global RSASeq_pp = {}
        p, q = generate_two_large_distinct_primes(RSA_PRIME_SIZE)
        n = p * q
        phi_n = (p-1) * (q-1)
        vector_v = [secrets.randbelow(n) for j in range(len)]
        T = 2**(level+1) - 2
        self.RSASeq_pp = {'n': n, 'T': T, 'vector_v': vector_v, 'phi_n': phi_n, 'level': level, 'len': len}

    def setup(self):
        state = {}
        sets_S = [None] * (self.RSASeq_pp['level']+1)
        for i in range(2, self.RSASeq_pp['level'] + 1):
            #print(i)
            sets_S[i] = {}
            exp1 = int(1)
            for j in range(1, 2**i):
                exp1 = (exp1 * hash_to_prime(j, 128)[0]) % (self.RSASeq_pp['phi_n'])
            #print(2**(i+1) - 1, self.RSASeq_pp['T']+1)
            for x in range(2**(i+1) - 1, self.RSASeq_pp['T']+1):
                #print(x)pow(pp['U'], x, pp['n'])
                exp1 = (exp1 * hash_to_prime(x, 128)[0]) % self.RSASeq_pp['phi_n']
            #print(exp1)
            #vector_w = [None] * (self.RSASeq_pp['len'])
            vector_w = [pow(self.RSASeq_pp['vector_v'][j], exp1, self.RSASeq_pp['n']) for j in range(self.RSASeq_pp['len'])]
            #print(self.RSASeq_pp['vector_v'][0])
            #vector_w[0] = self.RSASeq_pp['vector_v'][0]**exp1 % self.RSASeq_pp['n']
            #vector_w = [self.RSASeq_pp['vector_v'][j]**exp1 for j in range(self.RSASeq_pp['len'])]
            #print(33)
            sets_S[i][0] = {}
            sets_S[i][1] = {}
            sets_S[i][0]['vector'] = vector_w
            sets_S[i][0]['open'] = 2**i -1 + 2**(i-1)
            sets_S[i][0]['closing'] = 2**i -1
            sets_S[i][0]['count'] = 1
            sets_S[i][1]['vector'] = [pow(vector_w[j], hash_to_prime(2 ** i - 1 + 2 ** (i - 1), 128)[0], self.RSASeq_pp['n']) for j in range(self.RSASeq_pp["len"])]
            sets_S[i][1]['open'] = 2 ** i - 1
            sets_S[i][1]['closing'] = 2 ** i - 1 + 2**(i-1)
            sets_S[i][1]['count'] = 0
        exp2 = 1
        for j in range(3, self.RSASeq_pp['T']+1):
            exp2 = (exp2 * hash_to_prime(j, 128)[0]) % self.RSASeq_pp['phi_n']
        sets_S[1] = {}
        sets_S[1][0] = {}
        sets_S[1][0]['vector'] = [pow(self.RSASeq_pp['vector_v'][j], exp2, self.RSASeq_pp['n']) for j in range(self.RSASeq_pp['len'])]
        sets_S[1][0]['open'] = 2
        sets_S[1][0]['closing'] = 1
        sets_S[1][0]['count'] = 0
        current = [pow(sets_S[1][0]['vector'][j], hash_to_prime(2, 128)[0], self.RSASeq_pp['n']) for j in range(self.RSASeq_pp['len'])]
        state['index'] = 1
        state['current'] = current
        state['sets_S'] = sets_S
        return state

    def update(self, state):
        for i in range(1, self.RSASeq_pp['level']+1):
            open_values = [state['sets_S'][i][j]['open'] for j in range(len(state['sets_S'][i]))]
            smallest = min(open_values)
            for j in range(len(state['sets_S'][i])):
                if state['sets_S'][i][j]['open'] == smallest:
                    state['sets_S'][i][j]['vector'] = [pow(state['sets_S'][i][j]['vector'][l], hash_to_prime(state['sets_S'][i][j]['closing']+state['sets_S'][i][j]['count'], 128)[0], self.RSASeq_pp['n']) for l in range(self.RSASeq_pp['len'])]
                    state['sets_S'][i][j]['count'] = +1
        for i in range(self.RSASeq_pp['level'], 1, -1):
            for j in range(len(state['sets_S'][i])):
                if state['sets_S'][i][j]['count'] == 2**(i-1):
                    state['sets_S'][i].pop(j)
                    k = len(state['sets_S'][i - 1])
                    state['sets_S'][i-1][k]['count'] = 0
                    state['sets_S'][i - 1][k]['vector'] = state['sets_S'][i][j]['vector']
                    state['sets_S'][i - 1][k]['open'] = state['sets_S'][i][j]['open']
                    state['sets_S'][i - 1][k]['closing'] = state['sets_S'][i][j]['open'] + 2**(i-2)

                    state['sets_S'][i - 1][k+1]['count'] = 0
                    state['sets_S'][i - 1][k+1]['vector'] = state['sets_S'][i][j]['vector']
                    state['sets_S'][i - 1][k+1]['open'] = state['sets_S'][i][j]['open'] + 2**(i-2)
                    state['sets_S'][i - 1][k+1]['closing'] = state['sets_S'][i][j]['open']

        for j in state['sets_S'][1].keys():
            #print(state['sets_S'][1])
            if state['sets_S'][1][j]['open'] == state['index'] + 1 and state['sets_S'][1][j]['count'] == 1:
                state['index'] = state['index'] + 1
                state['current'] = state['sets_S'][1][j]['vector']
                state['sets_S'][1].pop(j)
                break
        return state

    def current(self, state):
        return state['current']

    def shift(self, state, vector):
        for i in range(1, self.RSASeq_pp['level']+1):
            if len(state['sets_S'][i]) > 0:
                for key in state['sets_S'][i].keys():
                    state['sets_S'][i][key]['vector'] = [pow(state['sets_S'][i][key]['vector'][x], vector[x], self.RSASeq_pp['n']) for x in range(self.RSASeq_pp['len'])]
        state['current'] = [pow(state['current'][x], vector[x], self.RSASeq_pp['n']) for x in range(self.RSASeq_pp['len'])]
        return state




class Pixel_plus:
    def setup(self, RSA_KEY_SIZE, level):
        sqa = RSASeq(RSA_KEY_SIZE, 1, level)
        exp = 1
        for j in range(1, sqa.RSASeq_pp['T']+1):
            exp = (exp * hash_to_prime(j, 128)[0]) % (sqa.RSASeq_pp['phi_n'])
        U = pow(sqa.RSASeq_pp['vector_v'][0], exp, sqa.RSASeq_pp['n'])
        pp = {'sqa': sqa, 'U': U, 'state': sqa.setup()}
        return pp

    def keygen(self, pp):
        s = secrets.randbelow(pp['sqa'].RSASeq_pp['n'])
        state1 = pp['sqa'].shift(pp['state'], [s])
        pk = pow(pp['U'], s, pp['sqa'].RSASeq_pp['n'])
        sk = {'state': state1, 'et': hash_to_prime(1, 128)[0], 'period': 1}
        return pk, sk

    def update(self, pp, sk):
        sk['state'] = pp['sqa'].update(sk['state'])
        sk['et'] = hash_to_prime(sk['period']+1, 128)[0]
        sk['period'] = sk['period'] + 1
        return sk

    def keyagg(self, pp, pks):
        apk = 1
        str = concat(pks)
        for i in range(len(pks)):
            stri = concat([pks[i], str])
            apk = apk * pow(pks[i], hash_to_integer(stri), pp['sqa'].RSASeq_pp['n'])
        return apk

    def sign(self, pp, pk, sk, pks, m):
        u = sk['state']['current'][0]
        str = concat([pk, concat(pks)])
        a = hash_to_integer(str)
        r = hash_to_integer(concat([m, sk['period']]))
        sigma = pow(u, r*a, pp['sqa'].RSASeq_pp['n'])
        return sigma

    def sigagg(self, sigs):
        sig = 1
        for i in range(len(sigs)):
            sig = sig * sigs[i]
        return sig

    def verify(self, pp, apk, sig, m, t):
        et = hash_to_prime(t, 128)[0]
        r = hash_to_integer(concat([m, t]))
        if pow(sig, et, pp['sqa'].RSASeq_pp['n']) == pow(apk, r, pp['sqa'].RSASeq_pp['n']):
            print("Verification Success")



def main():
    #if sys.version_info[0] < 3:

    #testtime()
    pixel = Pixel_plus()
    pp = pixel.setup(RSA_KEY_SIZE, 10)
    pk, sk = pixel.keygen(pp)

    print(pk, sk)
    #nextsk = pixel.update(pp, sk)
    #print(nextsk)
    pks = [pk]
    apk = pixel.keyagg(pp, pks)
    m = "hello"
    sigs = pixel.sign(pp, pk, sk, pks, m)
    print(sigs)
    pixel.verify(pp, apk, sigs, m, 1)


if __name__ == "__main__":
  main()
