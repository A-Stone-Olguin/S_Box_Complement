from math import *
from z3 import *

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

def n_by_n_s_box_unknown(n, file_object):
    elements = n**2
    bits = ceil(log2(elements))
    for weight in range(2, bits+1):
        for distance in range(2, bits+1):
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

            # Hamming Weight and Hamming Distance check
            for i in range(len(known_bvs)):
                s.add(Hamming_Weight(known_bvs[i] + unknown_bvs[i]) == weight)
                s.add(Hamming_Distance(known_bvs[i], unknown_bvs[i]) == distance)

            if(s.check() == sat):
                print("Constraints Satisified for HW: %d and HD: %d" %(weight, distance), file=file_object),
                m = s.model()
                for d in m.decls():
                    print('\t{state}\t->\t{encode:0{fieldsize}b}'.format(state=d.name(),encode=m[d].as_long(),fieldsize=bits), file=file_object)
            else:
                print("Constraints Not Satisified for HW: %d and HD: %d" %(weight, distance), file=file_object)
                sys.stdout.flush()
    return

def main():
    for n in range(2, 17):
        filename = f"{n}_by_{n}_S_box.txt"
        with open(filename, "w") as f:
            n_by_n_s_box_unknown(n, f)
    return

if __name__ == "__main__":
    main()
