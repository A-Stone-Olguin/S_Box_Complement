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

def main():
    # mat_array = [1, 2, 3, 4,
    #                2, 1, 4, 3,
    #              3, 4, 1, 2,
    #              4, 3, 2, 1]
    # matrix = MatrixFromSquareArray(mat_array)
    # print(matrix)
    # CheckLatinSquare(matrix)
    test_z3()
    return

if __name__ == "__main__":
    main()
