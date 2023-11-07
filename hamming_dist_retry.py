from math import *
from z3 import *
import re
import pickle
import os
from tqdm import trange
from sbox_nonlinearity import sboxNonlinearity

def MatrixFromSquareArray(square_arr):
    """
    Creates an n-sized array of n-sized arrays from an array with n^2 entries.

    :param square_arr: An array with a square number of entries
    """
    N = math.sqrt(len(square_arr))
    if not N.is_integer():
        print("Invalid dimensions! Not a square array")
        return [[]]
    else:
        N = int(N)  # Is an integer from if statement, can do
        matrix = [[square_arr[i + N*j] for i in range(N)] for j in range(N)]
        return matrix
    
def print_matrix(matrix):
    """
    Prints a matrix row by row.

    :param matrix: An m-sized array of n-sized arrays.
    """
    for row in matrix:
        formatted_row = ["{0: >3}".format(i) for i in row]
        row_string = "["
        for i in range(len(formatted_row)-1):
            row_string += formatted_row[i] + ", "
        row_string += formatted_row[len(formatted_row)-1] + "]"
        print(row_string)
    
def IntCeilLog2(val): return int(ceil(log2(val)))

def Hamming_Weight(bv):
    """
    Calculates the Hamming Weight of a Bitvector (from z3).

    :param bv: The bitvector in the Hamming Weight calculation
    """
    return Sum([
        ZeroExt(IntCeilLog2(bv.size()), Extract(i,i,bv)) 
        for i in range(bv.size())
    ])

def Hamming_Distance(bv1, bv2):
        """
        Calculates the Hamming Distance between two bitvectors (from z3).

        :param bv1: The first bitvector in the distance calculation
        :param bv2: The second bitvector in the distance calculation
        """
        return Sum([
        ZeroExt(IntCeilLog2(bv1.size()), Extract(i,i, bv1 ^ bv2)) 
        for i in range(bv1.size())
    ])

def create_s_box_complement(s_box, weight):
    """
    Given an s_box, returns a 256 size array of the complement.
    This uses the results from `n_by_n_s_box_unknown` which finds that it only works for equal weight and hamming distance.

    :param s_box: The 256 size array of an s_box to be found as the complement
    :param weight: What the weight constant (and thereby distance) should be for the complement's elements
    """
    elements = 16**2
    bits = ceil(log2(elements))
    
    s_box_complement = [0] * 256
    
    distance = weight ## We are using the results from the n_by_n_s_unknown

    unknown_bvs = []
    for i in range(elements):
        name = "unknown_bv_{s_index}".format(s_index = i)
        bv = BitVec(name, bits)
        unknown_bvs.append(bv)

    known_bvs = []
    for i in range(elements):
        bv = BitVecVal(s_box[i], bits)
        known_bvs.append(bv)

    s = Solver();
    s.set("timeout", 1000000)

    s.add(Distinct(*unknown_bvs))

    # Hamming Weight and Hamming Distance check
    for i in range(len(known_bvs)):
        s.add(Hamming_Weight(known_bvs[i] + unknown_bvs[i]) == weight)
        s.add(Hamming_Distance(known_bvs[i], unknown_bvs[i]) == weight)

    if(s.check() == sat):
        print("Constraints Satisified for HW: %d and HD: %d" %(weight, distance)),
        m = s.model()
        for d in m.decls():
            # print(type(d.name()))
            index = int(re.search(r'\d+', d.name()).group())
            s_box_complement[index] = m[d].as_long()
            # print('\t{state}\t->\t{encode:0{fieldsize}b}'.format(state=d.name(),encode=m[d].as_long(),fieldsize=bits))

    else:
        print("Constraints Not Satisified for HW: %d and HD: %d" %(weight, distance))
        sys.stdout.flush()
    return s_box_complement

def s_box_def():
    """ 
    Returns the definition of the tiny_aes_c s_box from CW tutorials asn a 256 size array in hex
    """
    s_box =  [
        # 0    1    2    3    4    5    6    7    8    9    a    b    c    d    e    f 
        0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76, # 0
        0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0, # 1
        0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15, # 2
        0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75, # 3
        0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84, # 4
        0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf, # 5
        0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8, # 6
        0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2, # 7
        0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73, # 8
        0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb, # 9
        0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79, # a
        0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08, # b
        0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a, # c
        0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e, # d
        0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf, # e
        0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16  # f
        ]  
    return s_box

def new_hd_constraint(n, filename):
    """
    Uses z3 to solve if there can be another matrix such that each element has the same Hamming Weight and the same Hamming Distance between them

    :param n: Dimension of the s_box (n by n)
    :param filename: What the name of the output file should be

    The output will show something like:
         unknown_bv_10 -> 01011100
    Which means that the number 10 should be matched with int(01011100)=92 to have a fixed hamming distance
    """
    with open(filename, "w") as f:
        elements = n**2
        bits = ceil(log2(elements))
        for weight in range(0, bits+1):
            for distance_1 in range(0, bits+1):
                for distance_2 in range(0, bits+1):
                    unknown_bvs = []

                    # These will be the variables we solve for
                    for i in range(elements):
                        name = "unknown_bv_{element}".format(element=i)
                        bv = BitVec(name, bits)
                        unknown_bvs.append(bv)

                    # 256 values in bits, used for comparison
                    known_bvs = []
                    for i in range(elements):
                        bv = BitVecVal(i, bits)
                        known_bvs.append(bv)

                    s = Solver();
                    s.set("timeout", 1000000)

                    s.add(Distinct(*unknown_bvs))

                    # Hamming Weight and Hamming Distance check
                    for i in range(len(known_bvs)):
                        s.add(Hamming_Weight(known_bvs[i] + unknown_bvs[i]) == weight)
                        s.add(Hamming_Distance(known_bvs[i], unknown_bvs[i]) == distance_1)
                    for i in range(len(known_bvs)):
                        for j in range(len(known_bvs)):
                            if i != j:
                                # print(f"i {i}, j: {j}", simplify(Hamming_Distance(known_bvs[i] + unknown_bvs[i], known_bvs[j] + unknown_bvs[j])), file=f)
                                s.add(Hamming_Distance(known_bvs[i] + unknown_bvs[i], known_bvs[j] + unknown_bvs[j]) == distance_2)

                    if(s.check() == sat):
                        print("Constraints Satisified for HW: %d and HD1: %d and HD2: %d" %(weight, distance_1, distance_2), file=f),
                        m = s.model()
                        for d in m.decls():
                            print('\t{state}\t->\t{encode:0{fieldsize}b}'.format(state=d.name(),encode=m[d].as_long(),fieldsize=bits), file=f)
                    else:
                        print("Constraints Not Satisified for HW: %d and HD1: %d and HD2: %d" %(weight, distance_1, distance_2), file=f)
                        sys.stdout.flush()
    return


def main():
    s_box = s_box_def()

    # n = 16
    for n in range(9, 17):
        filename = f"results/new_hd_measure/{n}_by_{n}_S_box.txt"
        new_hd_constraint(n, filename)
    # bits = ceil(log2(n**2))

    # for weight in trange(4, 5):
    #     s_box_complement = create_s_box_complement(s_box, weight)
    #     if s_box_complement != [0] * 256:
    #         print(f"\nComplement s-box with HW: {weight}")
    #         print_matrix(MatrixFromSquareArray(s_box_complement))
    #         print(f"Calculating nonlinearity for weight {weight}, will take a while")
    #         print(f"s_box weight {weight} nonlinearity: (min, max)", sboxNonlinearity(s_box_complement))
    #     else :
    #         print("There was no satisfiable s_box")


    return

if __name__ == "__main__":
    main()