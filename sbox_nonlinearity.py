"""  cryptopy.analysis.sbox_nonlinearity.py

    sbox non-linearity analysis using walsh functions
    
    Currently hardcoded AES, SMS4 and Streebog.

    Copyright (c) 2008 by Paul A. Lambert
    
    2019 - added Streebog sbox

    Modified by A. Stone Olguin 2023 to allow calculations of s_boxes
"""

## Huge thanks for Paul Lambert and the cryptopy library for help with calculating the nonlinearity of an s_box
# Github link: https://github.com/nymble/cryptopy
# File link: https://github.com/nymble/cryptopy/blob/master/analysis/sbox_nonlinearity.py

def sboxNonlinearity(sbox):
    """ Calcualte a measure of the nonlinearity of an sbox using Walsh Transform.
        Transform is calculated on 255 different 1 bit versions
        of the sbox that are formed by the binary inner product of
        the sbox with sequence 1 through 255.  This is all possible
        linear combinations of the 8 bits into a 1 bit valued sequence
    """
    n = log2n(len(sbox)) # sbox length must be power of 2
    nlv = (2**n-1)*[0] # vector of each nonlinearity calculation
                       # of inner product skipping zero
                       # this just initializes the vector of 255 results

    for c in range(len(nlv)):    # for each of the 255 ways to combine the 8 bits
        t = [ binaryInnerProduct(c+1,sbox[i]) for i in range(len(sbox)) ]
        nlv[c] = nonLinearity(t)
    minNonlinearity = min( [ abs(i) for i in nlv ] )
    maxNonlinearity = max( [ abs(i) for i in nlv ] )
    return minNonlinearity, maxNonlinearity

def walshTransform(t):
    n = log2n(len(t))  # n not used, but asserts if n not a power of 2
    wt = len(t)*[0]
    for w in range( len(t) ):
        for x in range( len(t) ):
            wt[w] = wt[w]+(-1)**(t[x] ^ binaryInnerProduct(w,x) )
    return wt

def binaryInnerProduct(a,b):
    """  """
    ip=0
    ab = a & b
    while ab > 0:
        ip=ip^(ab&1)   # either ^ or + works for walsh transform ...
        ab = ab>>1
    return ip

def nonLinearity(t):
    """ Non-linearity of a binary sequence
    """
    wt = walshTransform(t)
    nl = len(t)/2 - .5*max( [ abs(i) for i in wt ] )
    return nl
    
def log2n(l):
    """ Log2 of an integer only for numbers that are powers of 2 """
    x = l
    n = 0
    while x > 0:
        x=x>>1
        n=n+1
    n = n-1
    assert 2**n == l , "log2n(l) valid only for l=2**n"
    return n

if __name__ == "__main__":
    print(" ... be patient, this will take a while ... ")