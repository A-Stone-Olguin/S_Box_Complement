from math import *
from z3 import *

# Modified version of CheckLatinSquare by decode2207 
# from: https://www.geeksforgeeks.org/check-whether-a-matrix-is-a-latin-square-or-not/
def CheckLatinSquare(mat):
    # Size of square matrix is NxN
    N = len(mat)

    # Vector of N sets corresponding
    # to each row and column.
    rows = []
    cols = []
    for i in range(N):
        rows.append(set([]))
        cols.append(set([]))

    for i in range(N):
        for j in range(N):
            rows[i].add(mat[i][j])
            cols[j].add(mat[i][j])

            if (mat[i][j] > N or mat[i][j] <= 0) :
                print("NO")
                return

    # Checking each row and column
    for i in range(N):
        if (len(rows[i]) != N) :
            print("NO")
            return
        
        elif (len(cols[i]) != N) :
            print("NO")
            return
    print("YES")
    return

def MatrixFromSquareArray(square_arr):
    N = math.sqrt(len(square_arr))
    if not N.is_integer():
        print("Invalid dimensions! Not a square array")
        return [[]]
    else:
        N = int(N)  # Is an integer from if statement, can do
        matrix = [[square_arr[i + N*j] for i in range(N)] for j in range(N)]
        return matrix
    
def IntCeilLog2(val): return int(ceil(log2(val)))

def Hamming_Weight(bv):
    return Sum([
        ZeroExt(IntCeilLog2(bv.size()), Extract(i,i,bv)) 
        for i in range(bv.size())
    ])

def Hamming_Distance(bv1, bv2):
        return Sum([
        ZeroExt(IntCeilLog2(bv1.size()), Extract(i,i, bv1 ^ bv2)) 
        for i in range(bv1.size())
    ])

def test_z3():
    d_bv = {}
    for row in range(16):
        for col in range(16):
            name = f"bv{row}_{col}"
            d_bv[name] = BitVecs(name, 8)
    bvs = []
    for bv in d_bv.values():
        bvs.append(bv[0])
    s = Solver();
    s.set("timeout", 1000000)

    ## Hamming Weights:
    for bits in [j for j in range(9)]:
        for i, bv1 in enumerate(bvs):
            for k in range(len(bvs)):
                bv2 = bvs[(i + k)%256]
                s.add(Hamming_Weight(bv1+bv2) == bits)

        if(s.check() == sat):
            print("Constraints Satisified In %d Bits" %(bits)),
            m = s.model()
            for d in m.decls():
                print('\t{state}\t->\t{encode:0{fieldsize}b}'.format(state=d.name(),encode=m[d].as_long(),fieldsize=bits))
        else:
            print("Constraints Not Satisified in %d Bits" %(bits))
            sys.stdout.flush()
    return

def two_by_two_s_box_unknown():
    bits = 2
    u_bv0_0, u_bv0_1, u_bv1_0, u_bv1_1 = BitVecs('u_bv0_0 u_bv0_1 u_bv1_0 u_bv1_1', bits)
    s = Solver();
    s.set("timeout", 1000000)
    
    bv0_0 = BitVecVal(0, bits)
    bv0_1 = BitVecVal(1, bits)
    bv1_0 = BitVecVal(2, bits)
    bv1_1 = BitVecVal(3, bits)

    s.add(Distinct(u_bv0_0, u_bv0_1, u_bv1_0, u_bv1_1))
    
    # s.add(And(Hamming_Weight(bv0_0 + u_bv0_0) == 1, Hamming_Weight(bv1_0 + u_bv1_0) == 1, Hamming_Weight(bv0_1 + u_bv0_1) == 1,Hamming_Weight(bv1_1 + u_bv1_1) == 1))
    s.add(Hamming_Weight(bv0_0 + u_bv0_0) == 1)
    s.add(Hamming_Weight(bv0_1 + u_bv0_1) == 1)
    s.add(Hamming_Weight(bv1_0 + u_bv1_0) == 1)
    s.add(Hamming_Weight(bv1_1 + u_bv1_1) == 1)

    s.add(Hamming_Distance(bv0_0, u_bv0_0) == 1)
    s.add(Hamming_Distance(bv0_1, u_bv0_1) == 1)
    s.add(Hamming_Distance(bv1_0, u_bv1_0) == 1)
    s.add(Hamming_Distance(bv1_1, u_bv1_1) == 1)

    if(s.check() == sat):
        print("YAY! Constraints Satisified In %d Bits" %(bits)),
        m = s.model()
        for d in m.decls():
            print('\t{state}\t->\t{encode:0{fieldsize}b}'.format(state=d.name(),encode=m[d].as_long(),fieldsize=bits))
    else:
        print("Constraints Not Satisified in %d Bits" %(bits))
        sys.stdout.flush()
    return

def n_by_n_s_box_unknown(n, weight, distance):
    elements = n**2
    bits = ceil(log2(elements))

    unknown_bvs = []
    for i in range(elements):
        name = "unknown_bv_{row}_{col}".format(row=i%n, col = floor(i/n))
        bv = BitVec(name, bits)
        unknown_bvs.append(bv)

    known_bvs = []
    for i in range(elements):
        # name = f"known_bv_{row}_{col}".format(row=i%n, col = floor(i/n))
        bv = BitVecVal(i, bits)
        known_bvs.append(bv)

    s = Solver();
    s.set("timeout", 1000000)

    s.add(Distinct(*unknown_bvs))

    # Hamming Weight check
    for i in range(len(known_bvs)):
        s.add(Hamming_Weight(known_bvs[i] + unknown_bvs[i]) == weight)
        s.add(Hamming_Distance(known_bvs[i], unknown_bvs[i]) == distance)

    if(s.check() == sat):
        print("YAY! Constraints Satisified In %d Bits" %(bits)),
        m = s.model()
        for d in m.decls():
            print('\t{state}\t->\t{encode:0{fieldsize}b}'.format(state=d.name(),encode=m[d].as_long(),fieldsize=bits))
    else:
        print("Constraints Not Satisified in %d Bits" %(bits))
        sys.stdout.flush()
    return

def main():
    n_by_n_s_box_unknown(n=2, weight=1, distance=1)
    return

if __name__ == "__main__":
    main()
