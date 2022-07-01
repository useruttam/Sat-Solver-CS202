import pycosat
import random
K = int(input("Enter value of K:  "))
T = K*K
if(K==1):
  print("NO GENERATION")

#variables are assigned according to first code
# clause generation is also similar to first code

def v(i, j, d): 
    return T*T*(i - 1) + T* (j - 1) + d
def v1(i, j, d): 
    return T*T*T+T*T * (i - 1) + T* (j - 1) + d
 
def sudoku_clauses(): 
    constraints = []
    
    for i in range(1, T+1):
        for j in range(1, T+1):
            
            constraints.append([v(i, j, d) for d in range(1, T+1)])
            constraints.append([v1(i, j, d) for d in range(1, T+1)])
            
            for d in range(1, T+1):
              constraints.append([-v(i,j,d),-v1(i,j,d)])
              for dp in range(d + 1, T+1):
                constraints.append([-v(i, j, d), -v(i, j, dp)])
                constraints.append([-v1(i, j, d), -v1(i, j, dp)])

    def valid(cells): 
        for i, xi in enumerate(cells):
            for j, xj in enumerate(cells):
                if i < j:
                    for d in range(1, T+1):
                        constraints.append([-v(xi[0], xi[1], d), -v(xj[0], xj[1], d)])
                        constraints.append([-v1(xi[0], xi[1], d), -v1(xj[0], xj[1], d)])

    # ensure rows and columns have distinct values
    for i in range(1, T+1):
        valid([(i, j) for j in range(1, T+1)])
        valid([(j, i) for j in range(1, T+1)])
        
    lag1=[]
    lag2=[]
    for i in range (0,K):
      lag1.append(i*K+1)
      lag2.append(i*K+1)
    for i in lag1:
        for j in lag2:
            valid([(i + k % K, j + k // K) for k in range(T)])
      
    return constraints
import copy
clauses1=sudoku_clauses()

def solve1(grid,grid1):
    #solve a Sudoku problem
    clauses = copy.deepcopy(clauses1)
    for i in range(1, T+1):
        for j in range(1, T+1):
            d = grid[i - 1][j - 1]
            d1 = grid1[i - 1][j - 1]
            # constraints for already filled numbers 
            if d:
                clauses.append([v(i, j, d)])
            if d1:
                clauses.append([v1(i, j, d1)])
            
    
    
    sol = set(pycosat.solve(clauses))
    
    
    def read_cell(i, j):
        
        for d in range(1, T+1):
            if v(i, j, d) in sol:
                return d
    
    def read_cell1(i, j):
        
        for d in range(1, T+1):
            if v1(i, j, d) in sol:
                return d

    for i in range(1, T+1):
        for j in range(1, T+1):
            grid[i - 1][j - 1] = read_cell(i, j)
            grid1[i - 1][j - 1] = read_cell1(i,j);

clauses1=sudoku_clauses()
def solve(grid,grid1):
    
    clauses = copy.deepcopy(clauses1)
    for i in range(1, T+1):
        for j in range(1, T+1):
            d = grid[i - 1][j - 1]
            d1 = grid1[i - 1][j - 1]
            
            if d:
                clauses.append([v(i, j, d)])
            if d1:
                clauses.append([v1(i, j, d1)])
            
    
    
    
    #if number of solutions are greater than 1 then the removed number needs to be replaced back
    z=0
    for st in pycosat.itersolve(clauses):
      z=z+1
      if(z==2):
        break  
    if(z>1):
      return 0
    else :
      return 1  
    sol = set(pycosat.solve(clauses))
    
    
    def read_cell(i, j):
        
        for d in range(1, T+1):
            if v(i, j, d) in sol:
                return d
    
    def read_cell1(i, j):
        
        for d in range(1, T+1):
            if v1(i, j, d) in sol:
                return d

    for i in range(1, T+1):
        for j in range(1, T+1):
            grid[i - 1][j - 1] = read_cell(i, j)
            grid1[i-1][j-1] = read_cell1(i,j);

if __name__ == '__main__':
    from pprint import pprint
    blank=[]
    blank1=[]
    for i in range (0,T):
      lis1=[]
      lis2=[]
      for j in range (0,T):
        lis1.append(0)
        lis2.append(0)
      blank.append(lis1)
      blank1.append(lis2)

    


#This will initialize the blank sudoku with some values so that we get a different solution every time
for i in range (0,K):
  num = random.randint(1,T)
  col = random.randint(i*K,(i+1)*K-1)
  blank[i*K][col]=num
  
  



solve1(blank,blank1)

#The following code is for removing values from a blank sudoku
#This does the same thing as mentioned in the pdf

row = 0
col = 0
grid = 0 #this will keep track for the first or second sudoku
prev = 0 
eval = 0
remnums=[]
for i in range(2*T*T):
  remnums.append(i)

while( len(remnums)>0):
  curr = random.randint(0,len(remnums)-1)
  pos = remnums[curr]
  remnums.pop(curr)
  if(pos>T*T-1):
   grid = 1
   pos = pos - T*T
  else :
   grid = 0
  row = pos//T
  col = pos%T

  if(grid):
    prev = blank1[row][col]
    blank1[row][col]=0
  else:
    prev = blank[row][col]
    blank[row][col]=0
  if(solve(blank,blank1)!=1): #if after removing a number the number of solutions are greater than 1 then undo the removal
    if(grid):
     blank1[row][col]=prev
    else :
     blank[row][col]=prev
  

if K!=1:
  for item in blank:
    print(item)
  print("  ")
  for item in blank1:
    print(item)    
