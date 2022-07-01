import pycosat
import numpy as np
import pandas as pd


K = int(input("Enter Value of K:  "))
T = K*K


def solve_pair(problemset,problemset1):  
    solve(problemset,problemset1) 
    print('Answer:')
    if problemset[0][0] != None:   #check if there was no solution to the problem
      for item in problemset:
        print(item)
        
      print(" ")
      for item in problemset1:
        print(item)
    else:
      print('No solution')


#variables for the first cell
def v(i, j, d): 
    return T*T*(i - 1) + T* (j - 1) + d
#variables for the second cell    
def v1(i, j, d): 
    return T*T*T+T*T * (i - 1) + T* (j - 1) + d



#Will add clauses to list constraints

def sudoku_clauses(): 
    constraints = []
  
    for i in range(1, T+1):
        for j in range(1, T+1):
            # each cell must contain atleast one number in [1,T]
            constraints.append([v(i, j, d) for d in range(1, T+1)])
            constraints.append([v1(i, j, d) for d in range(1, T+1)])
            # must not contain two different digits at once 
            for d in range(1, T+1):
              #corconstraintsponding cells also must have different values
              constraints.append([-v(i,j,d),-v1(i,j,d)])
              for dp in range(d + 1, T+1):
                constraints.append([-v(i, j, d), -v(i, j, dp)])
                constraints.append([-v1(i, j, d), -v1(i, j, dp)])

    #this function cells for duplicate in same row or columns
    def valid(cells): 
        for i, xi in enumerate(cells):
            for j, xj in enumerate(cells):
                if i < j:
                    for d in range(1, T+1):
                        constraints.append([-v(xi[0], xi[1], d), -v(xj[0], xj[1], d)])
                        constraints.append([-v1(xi[0], xi[1], d), -v1(xj[0], xj[1], d)])

    # ensure rows and columns must have distinct values
    for i in range(1, T+1):
        valid([(i, j) for j in range(1, T+1)])
        valid([(j, i) for j in range(1, T+1)])
        
    # all KxK sub-grids must have distinct values
    lag1=[]
    lag2=[]
    for i in range (0,K):
      lag1.append(i*K+1)
      lag2.append(i*K+1)
    for i in lag1:
        for j in lag2:
            valid([(i + k % K, j + k // K) for k in range(T)])
      
    return constraints

def solve(grid,grid1):
  
    clauses = sudoku_clauses()
    # Add constranints for each cell value already known to us 
    for i in range(1, T+1):
        for j in range(1, T+1):
            d = grid[i - 1][j - 1]
            d1 = grid1[i - 1][j - 1] 
            if d:
                clauses.append([v(i, j, d)])
            if d1:
                clauses.append([v1(i, j, d1)])
            
    #print(pycosat.solve(clauses))
    sol = set(pycosat.solve(clauses))
    
    
    def readcell(i, j):
        # decode for the value of cell i, j according to the solution for first sudoku
        for d in range(1, T+1):
            if v(i, j, d) in sol:
                return d
    
    def readcell1(i, j):
        # decode for the value of cell i, j according to the solution for second sudoku
        for d in range(1, T+1):
            if v1(i, j, d) in sol:
                return d

    for i in range(1, T+1):
        for j in range(1, T+1):
            grid[i - 1][j - 1] = readcell(i, j)
            grid1[i - 1][j - 1] = readcell1(i, j);

if __name__ == '__main__':
    from pprint import pprint

    df = pd.read_csv('/content/sudoo4.csv', names = ['{}'.format(i) for i in range(T)]) #reading from csv file        
    mat1,mat2 = np.array(df.iloc[:T,:]).tolist(),np.array(df.iloc[T:,:]).tolist()#storing in matrix
    blank = []
    for i in mat1:
      blank.append(list(i))
    blank1 = []
    for i in mat2:
      blank1.append(list(i))
    print("problem")
    for item in blank:
      print(item)
    print(" ")  
    for item in blank1:
      print(item)
solve_pair(blank,blank1)
