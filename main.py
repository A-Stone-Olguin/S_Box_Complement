from math import *
from z3 import *
import re

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
        print(row)
    
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

def n_by_n_s_box_unknown(n, filename):
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
        for weight in range(2, bits+1):
            for distance in range(2, bits+1):
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
                    s.add(Hamming_Distance(known_bvs[i], unknown_bvs[i]) == distance)

                if(s.check() == sat):
                    print("Constraints Satisified for HW: %d and HD: %d" %(weight, distance), file=f),
                    m = s.model()
                    for d in m.decls():
                        print('\t{state}\t->\t{encode:0{fieldsize}b}'.format(state=d.name(),encode=m[d].as_long(),fieldsize=bits), file=f)
                else:
                    print("Constraints Not Satisified for HW: %d and HD: %d" %(weight, distance), file=f)
                    sys.stdout.flush()
    return

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
        # name = f"known_bv_{row}_{col}".format(row=i%n, col = floor(i/n))
        bv = BitVecVal(s_box[i], bits)
        known_bvs.append(bv)

    s = Solver();
    s.set("timeout", 1000000)

    s.add(Distinct(*unknown_bvs))

    # Hamming Weight and Hamming Distance check
    for i in range(len(known_bvs)):
        s.add(Hamming_Weight(known_bvs[i] + unknown_bvs[i]) == weight)
        s.add(Hamming_Distance(known_bvs[i], unknown_bvs[i]) == distance)

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

def potential_s_box_complement():
    """
    Returns a 256 size array s_box complement generated from the 16 by 16 s_box with HW and HD = 4 in hex.
    """
    potential_s_box_complement = [
        210, 186, 197, 190, 134, 200, 202, 105,  68,  42, 211, 243,  87,  99,  26,  32,
          0, 165, 160,  40,  66, 108, 212, 101, 199, 183, 140,   5,  46,  14, 195, 177, 
        102,  81, 169, 171, 245,  36, 158,  75, 173,  12,  73, 107, 221, 237,  67,   2,
         41, 117, 251, 166, 125,   3,  96,  15,   8, 135, 112,  90,  51, 141,  23, 196,
        207, 239,   7, 124, 126,  56, 252,  80, 128, 157, 162,  47, 143, 213,  28,  78,
        149,  92, 139, 184, 118,  58, 235,  50,  71, 248, 123, 144, 127,  25,  61, 226,
         94, 164,  27, 168, 110,  24, 175, 146, 244,  85,  21,  22,  33, 150,  39, 253, 
        131, 249,  13,  69,  38,  52,  19, 153, 217, 227, 188,  72,  76, 178, 129, 187, 
          4, 189, 182, 133, 246, 176,  95, 142, 161, 224,  83,  88, 242,  70, 179, 218,
        130,  20,  84, 138, 116, 121, 170,  89,  93, 219, 147,  63,  10, 115, 167, 232, 
        174,  91,  17,  48, 241, 114,  18,  57, 152, 137, 250, 233, 203, 192, 163, 181, 
        222, 155,  98, 230, 216, 185, 255, 240, 231, 154, 151, 191, 198,  55,  35, 145, 
        148,  34,  16, 119,  11, 225, 159,  30,  77,  65, 215, 254, 120,   9, 132, 223, 
          1,  37,  31,  45,  29, 113,  53, 214,  44,  86, 208, 234, 205, 247, 136,  82, 
        106,  62,  74, 180, 209,  97, 228, 194, 193, 111, 172, 220, 104, 201,   6, 122, 
        100, 236,  79, 103, 206, 109,  54,  59,  43, 204, 156,  60,  64, 229, 238,  49
        ]
    return potential_s_box_complement

def validate_complement(s_box, s_box_complement, d_weight, d_distance):
    """
    A function to validate that there is an equal Hamming Weight on the sums of the s_box and its complement and a constant Hamming Distance.

    :param s_box: A 256-sized array
    :param s_box_complement: A 256-sized array, most likely generated
    :param d_weight: The desired constant weight
    :param d_distance: The desired constant distance
    """
    for i in range(256):
        # Using the z3-build Hamming Weight and Hamming Distance functions on BitVecs, uses 8 bits
        s_box_element = BitVecVal(s_box[i], 8)
        complement_element = BitVecVal(s_box_complement[i], 8)
        weight_not_satisfied = (Hamming_Weight(s_box_element + complement_element) != d_weight)
        distance_not_satisfied = (Hamming_Distance(s_box_element, complement_element) != d_distance)

        # If either weight or distance is not satisfied, return false
        if is_false(Or(weight_not_satisfied, distance_not_satisfied)):
            return False
    return True

def create_graph(s_box, s_box_complement):
    # V = [i for i in range(256)]
    # E = {}
    # for i in range(256):
    #     E[i] = s_box_complement[s_box[i]]

    Adj_matrix = [[0] * 16 for _ in range(16)]
    for i in range(16):
        for j in range(16):
            if i == j:
                Adj_matrix[i][j] = 0
            else:
                Adj_matrix[i][j] = -1
    print_matrix(Adj_matrix)
    return


def main():
    # Generates the n by n s_box possibilities and prints the results to a file
    # COMMENT OUT IF YOU WANT TO REGENERATE
    # for n in range(2, 17):
    #     filename = f"results/{n}_by_{n}_S_box.txt"
    #     n_by_n_s_box_unknown(n, filename)
    s_box = [element for element in s_box_def()]

    s_box_complement = potential_s_box_complement()

    # if (validate_complement(s_box, s_box_complement, 4, 4)):
    #     print("Found a successful complement to s_box:")
    #     print_matrix(MatrixFromSquareArray(s_box))
    #     print("\nWith complement:")
    #     print_matrix(MatrixFromSquareArray(s_box_complement))
    # else:
    #     print("Something was created wrong. The test failed.")

    create_graph(s_box, s_box_complement)
    return

if __name__ == "__main__":
    main()
