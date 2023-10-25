import math

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

def main():
	mat_array = [1, 2, 3, 4,
			  	 2, 1, 4, 3,
				 3, 4, 1, 2,
				 4, 3, 2, 1]
	matrix = MatrixFromSquareArray(mat_array)
	print(matrix)
	return CheckLatinSquare(matrix)

if __name__ == "__main__":
	main()
