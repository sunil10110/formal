#!/usr/bin/env python3

import z3 as z3
import numpy as np 
import time 

n = 7
k = 1
n_plus_k = n+k

entries = 2**n

# for printing code table routine 
def bool_to_int (b):
    if b==True:
        return 1
    return 0

s=z3.Solver()

def check_hamming(c1, c2,i,j):
    
    c_xor =[c1[i]!=c2[i] for i in range(len(c1))]

    # enforce unique codewords
    s.add(z3.Or(t))
    x1 = (bin(i)[2:].zfill(7))
    x2 = (bin(j)[2:].zfill(7))
    hdx = sum( d1 != d2 for d1,d2 in zip(x1,x2))
    
    if(hdx > 1):
        s.add(z3.PbGe([(x,1) for x in c_xor], hdx-1)) 
                   

code=[[z3.Bool('code_%d_%d' % (r,c)) for c in range(n_plus_k)] for r in range(entries)]



# generate code words for each input ranging 0 to 2**n-1
for i in range(entries):    
    
    # MTA properties -- assuming gray code so max transition is 10 to 00 and 00 to 10 
    s.add(z3.Not(z3.And(z3.And(z3.Not(code[i][0]),(code[i][1])),z3.And(z3.Not(code[i][2]),z3.Not(code[i][3])))))
    s.add(z3.Not(z3.And(z3.And(z3.Not(code[i][0]),z3.Not(code[i][1])),z3.And(z3.Not(code[i][2]),(code[i][3])))))    
    s.add(z3.Not(z3.And(z3.And(z3.Not(code[i][2]),(code[i][3])),z3.And(z3.Not(code[i][4]),z3.Not(code[i][5])))))
    s.add(z3.Not(z3.And(z3.And(z3.Not(code[i][2]),z3.Not(code[i][3])),z3.And(z3.Not(code[i][4]),(code[i][5])))))    
    s.add(z3.Not(z3.And(z3.And(z3.Not(code[i][4]),(code[i][5])),z3.And(z3.Not(code[i][6]),z3.Not(code[i][7])))))
    s.add(z3.Not(z3.And(z3.And(z3.Not(code[i][4]),z3.Not(code[i][5])),z3.And(z3.Not(code[i][6]),(code[i][7])))))
    s.add(z3.Or(code[i][7],code[i][6]))
  
    t = time.time()
     
    for j in range(i):
        c2=[code[i][bit] for bit in range(n_plus_k)]
        c2=[code[j][bit] for bit in range(n_plus_K)] 
        check_hamming(c1, c2,i,j)

# check model 
t = time.time()
result=s.check()
elapsed = time.time() - t
print(elapsed/60)

# print output 
if result==z3.unsat:
    print(("unsat"))
elif result==z3.unknown:
    print("unknown")
else:
    m=s.model()
    print(m)    
    print("code table:")    
    for i in range(entries):
        str_out =""
        for bit in range(n_plus_k):
            str_out =str_out +str(bool_to_int(z3.is_true(m[code[i][n_plus_k-1-bit]])))+" "
        print (str_out)

