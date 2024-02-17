#!/usr/bin/python


curve = 1
## curve = 1: uses BLS12-381
## curve = 0: insecure! demonstrates arithmetic "in the exponent".
##   This is useful for debugging -- runs much faster and does
##   not have any dependencies on the underlying curve implementations.
import copy
import os
import sys
from bf.pybloom import BloomFilter
import bitarray, math, time
from bf.utils import range_fn
from random import randint
from hashlib import sha256
if (curve == 1):
  # requires Python 3 for the underlying BLS12-381 arithmetic
  from consts import g1suite, q
  from curve_ops import g1gen, g2gen, point_mul, point_neg, point_add, point_eq
  from pairing import pairing, multi_pairing
  #from util import get_cmdline_options, prepare_msg, print_g1_hex, print_g2_hex, print_tv_sig
else:
  q = 17
  g1gen = 1
  g2gen = 1

### public constants
D = 4   # depth

### helper functions to interface with curve operations

if (curve == 1):
  def G1add(a,b):
    return point_add(a,b)

  def G2add(a,b):
    return point_add(a,b)

  def G1mul(a,b):
    ## a group element, b scalar
    return point_mul(b,a)

  def G2mul(a,b):
    return point_mul(b,a)

  def G2neg(a):
    return point_neg(a)

  def GTtestpp(va,vb):
  ## checks whether <va, vb> == 0
    return (multi_pairing(va,vb) == 1)

else:
  def point_eq(a,b):
    return a == b

  def G1add(a,b):
    return (a+b) % q

  def G2add(a,b):
    return (a+b) % q

  def G1mul(a,b):
    return (a*b) % q

  def G2mul(a,b):
    return (a*b) % q

  def G2neg(a):
    return -a

  def GTtestpp(va,vb):
  ## checks whether <va, vb> == 0
    return (vip(va,vb) == 0)


def get_FileSize(filePath):
    filePath = str(filePath)
    fsize = os.path.getsize(filePath)
    fsize = fsize / float(1024)
    return round(fsize, 4)


def G1rand():
#  if r is None:
#    r = randint(1,q-1)
  return G1mul(g1gen,randint(1,q-1))

def G2rand():
  return G2mul(g2gen,randint(1,q-1))

# defined in RFC 3447, section 4.2
def OS2IP(octets):
  ret = 0
  for o in octets:
    ret = ret << 8
    ret += o
  assert ret == int.from_bytes(octets, 'big')
  return ret

### helper functions layered on top of curve operations

def vadd(va, vb):
## input: vectors va, vb
## return coordinate-wise addition of va, vb
## in group setting: first entry over G2, remaining entries over G1 
  assert (len(va) > 0)
  ans = [ G2add(va[0],vb[0]) ]
  for i in range(1,len(va)):
      ans.append( G1add(va[i],vb[i]) )
  return ans

def vmul(va, b):
## multiply each entry of vector va by scalar b
## in group setting: first entry over G2, remaining entries over G1 
  assert (len(va) > 0)
  ans = [ G2mul(va[0],b) ]
  for i in range(1,len(va)):
      ans.append( G1mul(va[i],b) )
  return ans

def vip(va, vb):
## return inner product of va, vb
## in group setting: this is over G1
  ans = G1mul(va[0],vb[0])
  for i in range(1,len(va)):
      ans = G1add(ans, G1mul(va[i],vb[i]))
  return ans

def tmv(tv, M):
## returns the vector associated with time tv and message M
  return tv + [0] * (D-len(tv)-1) + [M]

## helper functions for handling time

def time2vec(t,D):
   ## converts number to vector representation
   ## requires D >=1 and t in {1,2,...,2^D-1}
   if t==1:
     return []
   if D>0 and t > pow(2,D-1):
      return [2] + time2vec(t-pow(2,D-1),D-1)
   else:
      return [1] + time2vec(t-1,D-1)

def vec2time(tv,D):
   ## converts vector representation to number
   if tv == []:
      return 1
   else:
      ti = tv.pop(0)
      return 1 + (ti-1) * (pow(2,D-1)-1) + vec2time(tv,D-1)

### public parameters
g2 = g2gen # using fixed generator for g2
h = 0
hv = [0] * (D+1) ## vector of D+1 group elements in G1

def hw(wv):
  ## h_0 prod hj^wj
  ## wv is a vector
  return vip(hv[:len(wv)+1], [1]+wv)

## === formatting issues
## sk_tv is a pair tv, skv_tv
##   skv is a vector starting with tsk_tv, followed by remaining subkeys
##   assert len(skv) == len(tv)+1
## tsk_w doesn't contain w
##   assert len(tsk) == D-len(w)+2
## signature on a message doesn't contain time period


def setup():
  global h, h0, h1, h2 
  h = G1rand()
  h0 = G1rand() 
  h1 = G1rand() 
  h2 = G1rand()


def keygen(capacity, error_rate):
  bloomf = BloomFilter(capacity, error_rate)
  x = randint(0, q-1)
  pk = G2mul(g2,x)
  k = bloomf.num_slices
  ell = bloomf.num_bits
  #print(ell)
  sk_b = [None] * (ell)
  for i in range(0,ell):
    #print(i)
    sk_b[i] = [None] * 3
    r = randint(0, q-1)
    a = int(sha256(str(i).encode('utf-8')).hexdigest(),base=16) % q
    sk_b[i][0] = G2mul(g2,r)
    sk_b[i][1] = G1mul(h2,r)
    sk_b[i][2] = G1add(G1mul(h,x),G1mul(G1add(h0,G1mul(h1,a)),r))
  hpk = G1mul(g1gen,int(sha256(str(pk).encode('utf-8')).hexdigest(),base=16) % q)
  pi = G1mul(hpk, x)
  sk = {'bloomfilter': bloomf, 'skb': sk_b}
  return (sk, pk, pi)

## check e(sig[1], g2) = e(h, pk) * e(hw(tv) h_D^M, sig[0])
  ## TODO: add subgroup membership check for sig[0], sig[1]
def keyverify(pk, pi):

  return GTtestpp( [pi, G1mul(g1gen,int(sha256(pk).hexdigest(),base=16) % q)], [G2neg(g2), pk] )

def punc(sk, str):
  sk['bloomfilter'].add(str)
  for i in range(sk['bloomfilter'].num_bits):
    if sk['bloomfilter'].bitarray[i]:
      sk['skb'][i] = None
  return sk


def sign(sk,m):
  if m in sk['bloomfilter']:
    raise ValueError("punctured message.")
  index = sk['bloomfilter'].findindex(m)
  r = randint(0, q-1)

  a = int(sha256(str(index).encode('utf-8')).hexdigest(),base=16) % q
  hm = int(sha256(str(m).encode('utf-8')).hexdigest(),base=16) % q
  sigma1 = G1add(sk['skb'][index][2], G1add(G1mul(sk['skb'][index][1], hm),G1mul(G1add(h0,G1add(G1mul(h1,a),G1mul(h2,hm))),r)))
  sigma2 = G2add(sk['skb'][index][0],G2mul(g2gen,r))
  return [sigma1, sigma2, index]


def keyagg(pks):
  apk = G2add(g2gen,G2neg(g2))
  for user in pks:
    apk = G2add(apk, pks[user])
  return apk


def sigagg(sigmas):
  sigma1 = G1mul(g1gen,0)
  sigma2 = G2add(g2gen,G2neg(g2gen))
  for user in sigmas:
    sigma1 = G1add(sigmas[user][0], sigma1)
    sigma2 = G2add(sigmas[user][1], sigma2)
    index = sigmas[user][2]
  return [sigma1, sigma2, index]

def verify(apk, aggsig, m):
  m = int(sha256(str(m).encode('utf-8')).hexdigest(),base=16) % q
  temp = G1add(h0, G1add(G1mul(h1, int(sha256(str(aggsig[2]).encode('utf-8')).hexdigest(),base=16) % q),G1mul(h2, m)))
  return GTtestpp( [aggsig[0], h, temp], [G2neg(g2), apk, aggsig[1]] )


def testsize():
      setup()
      user_num = 2
      pks = {}
      sks = {}
      pis = {}
      sigmas = {}
      for x in range(user_num):
        print(x)
        (sks[x], pks[x], pis[x]) = keygen(10, 0.1)
      #print("q", q, "msk", x)
      #print("g2, h, h1,...,hD, ", g2, h, hv)
      print("pk,sk,pi", pks, sks, pis)

      print("== testing sign")
      for x in range(user_num):
        sigmas[x] = sign(sks[x],1)
        print("sig on M=1", sigmas[x]) #, sig1[0], (hw([0,0,1]) * sig1[0] + h*x) % q

      print("== testing aggregation")
      apk = keyagg(pks)
      aggsig = sigagg(sigmas)
      print("aggreated publick key and  siganture", apk, aggsig)
      f_signature_size = open('signature.txt', 'w+')
      f_signature_size.write(str(aggsig[0]))
      f_signature_size.close()
      size_signature = get_FileSize("C:/Users/wjh/Desktop/Pixel_plus/signature.txt")
      print("signature size", size_signature)



      print("== testing verify")

      print("verifying sign M=1")
      assert verify(apk, aggsig, 1)
      
      
      # assert verify(pk,[],"hello",(sign(sk1,"hello")))

      print("== testing puncture")

      for i in range(user_num):
        punc(sks[i], i)
        #sign(sks[i],i)


def test():
    setup()
    user_num = 2
    pks = {}
    sks = {}
    pis = {}
    sigmas = {}
    for x in range(user_num):
        print(x)
        (sks[x], pks[x], pis[x]) = keygen(10, 0.1)
    # print("q", q, "msk", x)
    # print("g2, h, h1,...,hD, ", g2, h, hv)
    print("pk,sk,pi", pks, sks, pis)

    print("== testing sign")
    for x in range(user_num):
        sigmas[x] = sign(sks[x], 1)
        print("sig on M=1", sigmas[x])  # , sig1[0], (hw([0,0,1]) * sig1[0] + h*x) % q

    print("== testing aggregation")
    apk = keyagg(pks)
    aggsig = sigagg(sigmas)
    print("aggreated publick key and  siganture", apk, aggsig)

    print("== testing verify")

    print("verifying sign M=1")
    assert verify(apk, aggsig, 1)

    # assert verify(pk,[],"hello",(sign(sk1,"hello")))

    print("== testing puncture")

    for i in range(user_num):
        punc(sks[i], i)
        # sign(sks[i],i)

def testbf():
    setup()
    pks = {}
    sks = {}
    pis = {}
    user_num = 2
    sigmas = {}
    capacity = [100, 1000, 10000]
    fpb = [0.1, 0.01, 0.001]
    for x in range(3):
        for y in range(3):
            print("key generation time under capacity and fpb", fpb[x], capacity[y])
            start = time.time()
            (sks[y], pks[y], pis[y]) = keygen(capacity[y], fpb[x])
            end = time.time()
            print("time cost", end-start)
            f_sk_size = open('sk.txt', 'w+')
            f_pk_size = open('pk.txt', 'w+')
            for item in sks[y]:
                f_sk_size.write(str(sks[y][item]))
            f_sk_size.close()
            ssk = get_FileSize("C:/Users/wjh/Desktop/Pixel_plus/sk.txt")
            print("sk size", ssk)
            f_pk_size.write(str(pks[y]))
            f_pk_size.close()
            spk = get_FileSize("C:/Users/wjh/Desktop/Pixel_plus/pk.txt")
            print("pk size", spk)

def testtime():
    setup()
    pks = {}
    sks = {}
    pis = {}
    user_num = 100
    sigmas = {}
    capacity = [100, 1000, 10000]
    for x in range(user_num):
        (sks[x], pks[x], pis[x]) = keygen(100, 0.1)

    print("testing pk aggregation cost")
    start = time.time()
    apk = keyagg(pks)
    end = time.time()
    print("time cost", end - start)

    print("testing signing cost")
    start = time.time()
    for x in range(user_num):
        sigmas[x] = sign(sks[x], 1)
    end = time.time()
    print("signing time cost", (end - start)/user_num)

    print("testing signature aggregation cost")
    start = time.time()
    aggsig = sigagg(sigmas)
    end = time.time()
    print("signature aggregation time cost", (end - start))

    print("testing verify cost")
    start = time.time()
    assert verify(apk, aggsig, 1)
    end = time.time()
    print("verify time cost", (end - start))

    f_signature_size = open('signature.txt', 'w+')
    for item in range(2):
        f_signature_size.write(str(aggsig[item]))
    f_signature_size.close()
    size_signature = get_FileSize("C:/Users/wjh/Desktop/Pixel_plus/signature.txt")
    print("signature size", size_signature)

    print("testing puncture cost")
    start = time.time()
    for i in range(user_num):
        punc(sks[i], i)
    end = time.time()
    print("puncture time cost", (end - start) / user_num)




if __name__ == "__main__":
  def main():
    #if sys.version_info[0] < 3:
    #  sys.exit("This script requires Python3 or PyPy3 for the underlying BLS12-381 operations.")
    testsize()

  main()
