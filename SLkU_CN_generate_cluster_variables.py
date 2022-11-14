'''Generating grassmannians tableaux'''
'''Note this is a sagemath script, generation parameters are set in the final section'''
#Import libraries
import sys
import numpy as np
import itertools
from numpy import matrix 
from itertools import combinations as comb
from operator import add
from typing import List
from sage.combinat.shuffle import ShuffleProduct
#from multiprocess import Pool
from sage.parallel.multiprocessing_sage import Pool
 
####################################################################
#Define relevant functions

def append(l,i):
    r=l
    r.append(i)
    return r

def UnionOfListsMany(l):
    r=[]
    for i in l:
        r=r+i
    return r

def TransposeTableauSLk(a): # a[i] are columns
    r=[]
    for j in [0..len(a[0])-1]:
        t1=[]
        for i in [0..len(a)-1]:
            if j<len(a[i]):
                t1.append(a[i][j])
        r.append(t1)

    return r

def ListAToN(a,n):
    r=list(range(a,n+1))
    return r

def IsPartition1GreaterThanOrEqualPartition2(p1,p2): # p1,p2 are partitions
    l1=p1
    l2=p2

    n=max(len(p1), len(p2))
    for i in [len(p1)..n]:
        l1.append(0) 
    for i in [len(p2)..n]: 
        l2.append(0) 

    r=1 # p1 >= p2

    for i in [1..n]: 
        t1=0
        t2=0
        for j in [0..i-1]:
            t1=t1+l1[j]
            t2=t2+l2[j] 
        if t1<t2: 
            r=0 # p1 is not greater or equal to p2
            break 
    return r

def comparePartitions(p1,p2): # p1,p2 are partitions
    t1=IsPartition1GreaterThanOrEqualPartition2(p1,p2)
    t2=IsPartition1GreaterThanOrEqualPartition2(p2,p1)

    if t1==1: 
        r=1  # p1>=p2
    elif t2==1: 
        r=-1 # p1<=p2
    else:
        r=0 # not comparable 
    return r

def IsTableauxP1GreaterEqualP2SLkU(P1,P2): # P1,P2 are tableaux

    n=-1000
    for i in UnionOfListsMany(P1):
        if n<i:
            n=i
    for i in UnionOfListsMany(P2):
        if n<i:
            n=i 

    r=1 # P1>=P2

    for a in [1..n]: 
        t1=TableauRestrictToElementsLessOrEqualAToPartition(P1,a)
        t2=TableauRestrictToElementsLessOrEqualAToPartition(P2,a)
        r1=comparePartitions(t1,t2)
        if r1==0 or r1==-1: 
            r=0 # P1 is not greater or equal to P2
            break 

    return r

def TableauToMatrixTakeRowsSLkMoreGeneral(a): # send a tableau to a matrix, a[i] are rows
    if a==[]:
        r=[]
    else:
        m=len(a)  # number of rows
        n=len(a[0])
        for i in [1..len(a)-1]:
            if n<len(a[i]):
                n=len(a[i])
        
        r=Matrix(m,n)
        for i in range(m):
            for j in range(n):
                if j<len(a[i]):
                    r[i,j]=a[i][j]
                else:
                    r[i,j]=-10000
    return r

def TableauToMatrixTakeColumnsSLkMoreGeneral(a): # send a tableau to a matrix, a[i] are columns
    
    if a==[]:
        r=[]
    else:
        n=len(a)  # number of columns
        m=len(a[0])
        for i in [1..len(a)-1]:
            if m<len(a[i]):
                m=len(a[i])
        
        r=Matrix(m,n)
        for i in range(m):
            for j in range(n):
                if i<len(a[j]):
                    r[i,j]=a[j][i]
                else:
                    r[i,j]=-10000
    return r 

def TableauToMatrixTakeRowsSLkListMoreGeneral(a): # SLk, a[i] are columns of tableau
    r=[]
    for i in a:
        r.append(TableauToMatrixTakeRowsSLkMoreGeneral(i))
    return r

def TableauToMatrixTakeColumnsSLkListMoreGeneral(a): # SLk, a[i] are columns of tableau
    r=[]
    for i in a:
        r.append(TableauToMatrixTakeColumnsSLkMoreGeneral(i))
    return r

def TableauToPartition(P):

    r=[]
    t1=TableauToMatrixTakeColumnsSLkMoreGeneral(P)
    for i in [0..t1.nrows()-1]: 
        t2=0
        for j in [0..t1.ncols()-1]: 
            if t1[i,j]!=-10000:
                t2=t2+1 
        r.append(t2) 
    return r

def TableauRestrictToElementsLessOrEqualAToPartition(P,a):

    t1=TableauRestrictToElementsLessOrEqualA(P,a)
    r=TableauToPartition(t1)

    return r

def compareWeightsTableauxSLkU(P1,P2): # P1,P2 are tableaux

    t1=IsTableauxP1GreaterEqualP2SLkU(P1,P2)
    t2=IsTableauxP1GreaterEqualP2SLkU(P2,P1)

    if t1==1:  
        r=1 # P1>=P2
    elif t2==1: 
        r=-1 # P1<=P2
    else:
        r=0 # P1, P2 not comparable
     
    return r

def TableauRestrictToElementsLessOrEqualA(P,a):

    r=[]
    for i in P: 
        t1=[]
        for j in i: 
            if j<=a:
                t1.append(j) 
        r.append(t1) 
    return r

# mutation for base affine space, C[SL_k]^U, and C[N]

def InitialCluster_SLk(kk): # initial cluster for SL_kk, only works for kk <= 10

    # quivers are from Keller's mutation app

    if kk==2: 
        mat=Matrix([[0,-1,1],[1,0,-1],[-1,1,0]]) # SL2
    elif kk==3: 
        mat=Matrix([[0,-1,1,0,0,0],[1,0,-1,-1,1,0],[-1,1,0,0,-1,1],[0,1,0,0,-1,0],[0,-1,1,1,0,-1],[0,0,-1,0,1,0]]) # SL3
    elif kk==4:
        mat=Matrix([[0,-1,1,0,0,0,0,0,0,0],[1,0,-1,-1,1,0,0,0,0,0],[-1,1,0,0,-1,1,0,0,0,0],[0,1,0,0,-1,0,-1,1,0,0],[0,-1,1,1,0,-1,0,-1,1,0],[0,0,-1,0,1,0,0,0,-1,1],[0,0,0,1,0,0,0,-1,0,0],[0,0,0,-1,1,0,1,0,-1,0],[0,0,0,0,-1,1,0,1,0,-1],[0,0,0,0,0,-1,0,0,1,0]]) # SL4
    elif kk==5: 
        mat=Matrix([[0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0],[1,0,-1,-1,1,0,0,0,0,0,0,0,0,0,0],[-1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0],[0,1,0,0,-1,0,-1,1,0,0,0,0,0,0,0],[0,-1,1,1,0,-1,0,-1,1,0,0,0,0,0,0],[0,0,-1,0,1,0,0,0,-1,1,0,0,0,0,0],[0,0,0,1,0,0,0,-1,0,0,-1,1,0,0,0],[0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0],[0,0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0],[0,0,0,0,0,-1,0,0,1,0,0,0,0,-1,1],[0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0],[0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0],[0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0],[0,0,0,0,0,0,0,0,-1,1,0,0,1,0,-1],[0,0,0,0,0,0,0,0,0,-1,0,0,0,1,0]]) # SL5
    elif kk==6: 
        mat=Matrix([[0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[1,0,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[-1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,1,1,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,-1,0,1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0],[0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0],[0,0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0],[0,0,0,0,0,-1,0,0,1,0,0,0,0,-1,1,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,-1,1,0,0,0,0],[0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0],[0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0],[0,0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0],[0,0,0,0,0,0,0,0,0,-1,0,0,0,1,0,0,0,0,0,-1,1],[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1,0]]) # SL6
    elif kk==7: 
        mat=Matrix([[0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[1,0,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[-1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,1,1,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,-1,0,1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,-1,0,0,1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,-1,0,0,0,1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0,-1,1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,0,-1,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,-1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,1,0]]) # SL7
    elif kk==8: 
        mat=Matrix([[0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[1,0,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[-1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,1,1,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,-1,0,1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,-1,0,0,1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,-1,0,0,0,1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,-1,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,1,0]]) # SL8
    elif kk==9: 
        mat=Matrix([[0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[1,0,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[-1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,1,1,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,-1,0,1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,-1,0,0,1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,-1,0,0,0,1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,-1,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,1,0]]) # SL9
    elif kk==10: 
        mat=Matrix([[0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[1,0,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[-1,1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,1,1,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,-1,0,1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,-1,1,0,1,0,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,-1,0,0,1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,-1,1,0,0,1,0,-1,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,-1,0,0,0,1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,1,0,-1,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,1,0,-1,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,-1,1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,-1,1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,-1,1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,-1,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,-1,1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,-1,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,1,0,-1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,1,0,-1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,1,0,-1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,1,0,-1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,1,0,-1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,1,0]]) # SL10

    vertices0=[]
    n=kk

    for i in [1..n]: 
        for j in [1..i]: 
            t3=ListAToN(j, j+n-i)
            vertices0.append(t3) 
            
    verticesTableaux=[] # Tableaux are represented by matrices
    for i in [0..len(vertices0)-1]:
        verticesTableaux.append([0, [vertices0[i]], i]) # [vertices0[i]] is an one column tableau
        
    mat1 = mat
    clusterVariables=[] 
    vertices1 = [verticesTableaux, clusterVariables] # vertices1[1] store cluster variables, vertices1[0] store variables on quiver
    r=[mat, vertices1]
    
    return r
    
def UnionOfTwoTableauxSLk(a,b): # a[i], b[i] are columns
    if a==[]:
        r=b
    elif b==[]:
        r=a
    else:
        r1=TransposeTableauSLk(a)
        r2=TransposeTableauSLk(b)
        
        m=max(len(r1), len(r2))
        #print('m,len(r1),len(r2)',m,len(r1),len(r2))
        r3=[]
        for i in [0..m-1]:
            #print(i,len(r1),len(r2))
            if i<len(r1) and i<len(r2):
                t2=r1[i]+r2[i]
                #print('t2',t2)
                t2=sorted(t2)
            elif i>=len(r1) and i<len(r2):
                    t2=sorted(r2[i])
            elif i<len(r1) and i>=len(r2):
                    t2=sorted(r1[i])
            r3.append(t2)
        #print('r3',r3)
        r=TransposeTableauSLk(r3)
    return r

def PowerOfTableaux_SLk(T, n): # T=[[1,2,3],[2,5]]
    if n==1:
        r=T
    elif n>1:
        r=T
        for i in range(n-1):
            r=UnionOfTwoTableauxSLk(r, T)
    return r
    
def computeEquationsForModulesTableaux_SLk(variable2, mat, k, kk): # variable2=(variables on quiver, cluster variables obtained so far)
    variable=variable2[0]
    clusterVariables=variable2[1] 
    size=mat.nrows() 
    newVariable=[]
    newVariable2=[]
    newVariableList=[]
    newVariable2List=[]

    for i in range(size):
        if mat[i, k]>0:
            newVariable=UnionOfTwoTableauxSLk(newVariable, PowerOfTableaux_SLk(variable[i][1], mat[i,k]) )
            for j in range(mat[i,k]):
                newVariableList.append(variable[i][1])
 
    for i in range(size): 
        if mat[i, k]<0:
            newVariable2= UnionOfTwoTableauxSLk( newVariable2, PowerOfTableaux_SLk(variable[i][1], -mat[i,k]) )
            for j in range(-mat[i,k]):
                newVariable2List.append(variable[i][1])
 
    variable[k][0]=variable[k][0]+1
    t1=compareWeightsTableauxSLkU(newVariable, newVariable2)
    
    if t1==1: 
        variable[k][1]=TableauDivisionSLk(newVariable, variable[k][1])
    else:
        variable[k][1]=TableauDivisionSLk(newVariable2, variable[k][1])  
    
    #print(variable[k][1])
    clusterVariables=TableauToMatrixTakeColumnsSLkMoreGeneral(variable[k][1])
    #print('new cluster variable', clusterVariables)
    
    r=[variable, clusterVariables]

    return r

def MatrixToTableauTakeColumnsSLk(a): 
 

    n=a.nrows()
    m=a.ncols()

    r=[]
    for i in [0..m-1]:
        t2=[]
        for j in [0..n-1]:
            if a[j,i]>=0:
                t2=append(t2,a[j,i])
        
        r=append(r, t2)
    
    #r=SemistandardTableau(r)
   
    return r

def ll_perms_SLk(lli, kk, max_column, repeat): # SL_kk
    b1=[]
    IC=InitialCluster_SLk(kk)
    mat1=IC[0]
    vertices1=IC[1]

    ll=list(map(lambda x: x - 1, lli))
    
    #print(IC)
    
    mutationSequence=[]
    for j1 in [1..repeat]: ###why do this?, just to repeat the same sequence of mutations, it will give more cluster variables, without this loop is also ok
        mutationSequence=mutationSequence+ll 
        
    for j in range(len(mutationSequence)): 
        vertices1 = computeEquationsForModulesTableaux_SLk(vertices1, mat1, mutationSequence[j], kk)
        mat1 = matrixMutation(mat1, mutationSequence[j]) 

        if vertices1[1].ncols()>max_column:
            vertices1 = computeEquationsForModulesTableaux_SLk(vertices1, mat1, mutationSequence[j], kk)
            mat1 = matrixMutation(mat1, mutationSequence[j]) 
        else:
            #print(vertices1[1])
            b1.append(MatrixToTableauTakeColumnsSLk(vertices1[1]))

    return b1

def TableauDivisionSLk(a,b): # a[i], b[i] are columns
    r1=TableauDivisionSLkResultInRows(a,b)
        
    r=TransposeTableauSLk(r1)
        
    return r

def TableauDivisionSLkResultInRows(a,b): # a[i], b[i] are columns
    r1=TransposeTableauSLk(a)
    r2=TransposeTableauSLk(b)
    
    r3=[]
    m=max(len(r1),len(r2))
    for i in range(m):
        if i<len(r1) and i<len(r2):
            r3.append(sorted(SetDifferenceListDifference(r1[i],r2[i])))
        elif i<len(r1) and i>=len(r2):
            r3.append(r1[i])
        elif i>=len(r1) and i<len(r2):
            r3=[]
            print('tableau not divisible')
            break
        
    r=r3
        
    return r

def TableauToMatrixTakeRows(a): 
    # a[i] are rows of the tableau a
    # transform a tableau to matrix form
    m=len(a)
    n=len(a[0])
    r=Matrix(m,n)
    for i in range(m):
        for j in range(n):
            r[i,j]=a[i][j]
    return r

def PromotionOfTableauNTimes(N,T1,n):
    # promotion of a tableau N times
    r=[T1]
    T=T1
    for i in range(N-1):
        T=T.promotion(n-1)
        r.append(T)
    return r 

def PromotionOfTableauNTimesInMatrix(N,T1,n):
    # promotion of tableau n times, T1 is in matrix form
    t1=MatrixTakeRows(T1)
    t2=SemistandardTableau(t1)
    r1=PromotionOfTableauNTimes(N,t2,n)
    r=[]
    for i in r1:
        r.append(TableauToMatrixTakeRows(i))
        
    return r 

def PluckerToMinimalAff(a1):
    # translate a Plucker coordinate to highest weight monomial
    r=[]
    a=sorted(a1)
    n=len(a)
    for i in range(n-1,0,-1):
        r.append(a[i]-a[i-1]-1)
    r.append(a[0]-1)

    return r

def InitialCluster(rank,n):  
    # initial cluster from Gr(rank, n)
    sizeColumn=n-rank
    k=sizeColumn    
    k1=rank
    p1=k*rank+1
    mat=Matrix(p1,p1)
    for i in range(p1): 
        i1=i+1
        if i1==1: 
            mat[i,i+k+1]=1
            mat[i, p1-1]=1
            mat[i,i+k]=-1
            mat[i, i+1]=-1
        elif i1>=2 and i1<=k-1: 
            mat[i,i+1]=-1
            mat[i,i+k]=-1
            mat[i,i-1]=1
            mat[i,i+k+1]=1
        elif i1==k: 
            mat[i,i-1]=1
            mat[i,i+k]=-1
        elif i1>k and i1<(rank-1)*k and i1 % k==1: 
            mat[i,i-k]=1
            mat[i,i+k+1]=1
            mat[i,i+1]=-1
            mat[i,i+k]=-1
        elif i1>k and i1<(rank-1)*k and i1 % k >=2 and i1 % k<=k-1:
            mat[i,i-k-1]=-1
            mat[i,i+1]=-1
            mat[i,i+k]=-1
            mat[i,i-k]=1
            mat[i,i-1]=1
            mat[i,i+k+1]=1
        elif i1>=2*k and i1<=(rank-1)*k and i1 % k==0:
            mat[i,i-k-1]=-1
            mat[i,i+k]=-1
            mat[i,i-k]=1
            mat[i,i-1]=1
        elif i1>(rank-1)*k and i1<p1 and i1 % k==1: 
            mat[i,i-k]=1
            mat[i,i+1]=-1
        elif i1>=(rank-1)*k+2 and i1<rank*k:
            mat[i,i-k-1]=-1
            mat[i,i+1]=-1
            mat[i,i-k]=1
            mat[i,i-1]=1
        elif i1==rank*k:
            mat[i,i-k-1]=-1
            mat[i,i-k]=1
            mat[i,i-1]=1
        elif i1==p1:
            mat[i,0]=-1

    vertices0=[]

    for j in range(k1-1,-1,-1):
        for i in range(k1,k1+k):
            t1=list(range(1,j+1))
            t2=list(range(i-k1+j+2,i+2))
            t3=t1+t2
            vertices0.append(t3)

    vertices0.append(list(range(1,k1+1)))  
    verticesTableaux = [] # Tableaux are represented by matrices
    for i in range(len(vertices0)):
        verticesTableaux.append([0, [vertices0[i]], i]) # [vertices0[i]] is an one column tableau
    mat1 = Matrix(p1,p1)
    for i in range(p1):
        for j in range(p1):
            mat1[i,j]=mat[i,j]
    clusterVariables=[] 
    vertices1 = [verticesTableaux, clusterVariables] # vertices1[1] store cluster variables, vertices1[0] store variables on quiver
    r=[mat, vertices1]
    
    return r


def TableauExpansionsInMatrixHalf(l,b,c): 
    # l is tableau in matrix form, b is the content of l, c is a list of numbers
    # replace a_1<...<a_m in l by c_1<...<c_m
    r=[]
    m=l.nrows()
    n=l.ncols()
    r=Matrix(m,n)
    for i in range(m):
        for j in range(n):
            t1=b.index(l[i,j])+1
            r[i,j]=c[t1-1]
    return r

def TableauExpansionsInMatrix(l,n): 
    # l is tableau in matrix form
    # replace a_1<...<a_m in l by c_1<...<c_m
    r1=ContentOfTableau(l)
    m=len(r1)
    r2=list(itertools.combinations(list(range(1,n+1)), m)) 
    r=[]
    for i in r2:
        t1=TableauExpansionsInMatrixHalf(l,r1,i)
        r.append(t1)
    return r

def TableauExpansionsInMatrixList(l,n): 
    # l is a list of tableaux in matrix form
    r=[]
    for i in l:
        r=r+TableauExpansionsInMatrix(i,n)
    r=removeDuplicates2(r)  
    
    return r

def ContentOfTableau(l): 
    # l is tableau
    # compute the content of l, with multiplicities
    r=[]
    for i in l:
        for j in i:
            r.append(j)
    #r=np.unique(r,axis=0)
    r=removeDuplicatesListOfLists(r)
    r=sorted(r)
    return r

def immutabilize(m):
    M = copy(m)
    M.set_immutable()
    return M

def ChangeListOfMatricesToSetOfMatrices(S):
    r={immutabilize(i) for i in S}
    return r

def removeAnElementInList(i, l):
    r=[]
    for j in range(len(l)):
        if (j!=i):
            r.append(l[j])
    
    return r

def removeDuplicates(l):
    # remove duplicates
    # it is slow whn l is large
    r=[]
    for i in l:
        if (i in r)==False:
            r.append(i)
    return r

def removeDuplicates2(l): 
    # remove duliplictes
    # vary fast, for matrices
    t1=ChangeListOfMatricesToSetOfMatrices(l)
    r=list(dict.fromkeys(t1))
    return r

def removeDuplicatesListOfLists(l): 
    # very fast
    l.sort()
    r=list(l for l,_ in itertools.groupby(l))

    return r

def SetDifference2(a,b):
    # take different of two lists a, b
    t1=ChangeListOfMatricesToSetOfMatrices(a)
    t2=ChangeListOfMatricesToSetOfMatrices(b)
    r=t1.difference(t2)
    return r

def SetDifferenceListDifference(A,B): 
    # A-B, can have duplicate elements
    # take different of two lists A, B, count multiplicites
    r=[]
    r1=list(set(A))
    for i in r1:
        t1=A.count(i)-B.count(i)
        #print(t1)
        for j in range(1,t1+1):
            r.append(i)
            
    return r

def TableauToMatrix(a):
    # transform a tableau to matrix form
    m=len(a)
    n=len(a[0])
    r=Matrix(n,m)
    for i in range(n):
        for j in range(m):
            r[i,j]=a[j][i]
    return r

def MatrixTakeRows(a):
    # take rows of a matrix to get a list
    n=a.nrows()
    m=a.ncols()
    r=[]
    for i in range(n):
        t1=a[[i],list(range(m))]
        t2=[]
        for j in range(m):
            t2.append(t1[0,j])
        r.append(t2)
    return r

def MatrixTakeRowsList(a):
    # function MatrixTakeRows for a list of matrices
    r=[]
    for i in a:
        r.append(MatrixTakeRows(i))
    return r

def TableauDivision(a,b):
    # division of two tableaux a, b, that is removing b from a
    t1=TableauToMatrix(a)
    t2=TableauToMatrix(b)  
    r1=MatrixTakeRows(t1)
    r2=MatrixTakeRows(t2)
    r3=[]
    for i in range(len(r1)):
        r3.append(sorted(SetDifferenceListDifference(r1[i],r2[i])))
    r=[]
    for i in range(len(r3[0])):
        t1=[]
        for j in range(len(r3)):
            t1.append(r3[j][i])
        r.append(t1)
        
    return r

def UnionOfTwoTableaux(a,b):
    t1=a+b
    t2=TableauToMatrix(t1)
    r=[]
    for i in range(t2.nrows()):
        r1=[]
        for j in range(t2.ncols()):
            r1.append(t2[i,j])
        r.append(sorted(r1))
        
    r2=TableauToMatrix(r);
    r=[]
    for i in range(r2.nrows()):
        r1=[]
        for j in range(r2.ncols()):
            r1.append(r2[i,j])
        r.append(sorted(r1))
    return r
        
def PowerOfTableaux(a,n):
    r=[]
    if a!=[] and a!=[[]]:
        for i in range(1,n+1):
            r=UnionOfTwoTableaux(r,a) 
    else:
        r=a 
    return r

def CartanMatrixSelfDefined(typ, rank):
    if typ=='E' and rank==6:
        r=Matrix([[2,0,-1,0,0,0],[0,2,0,-1,0,0],[-1,0,2,-1,0,0],[0,-1,-1,2,-1,0],[0,0,0,-1,2,-1],[0,0,0,0,-1,2]]) # this is the Cartan Matrix in Sage of type E6
    else:
    
        r = Matrix(rank, rank)
        n = rank
        for i in range(n):
            if i + 1 <= n-1:
                r[i, i + 1] = -1
            if 0 <= i - 1:
                r[i, i - 1] = -1
            r[i, i] = 2

        if typ == 'B' or typ == 2:
            r[n-1, n - 2] = -2
        elif typ == 'C' or typ == 3:
            r[n - 2, n-1] = -2
        elif typ == 'D' or typ == 4:
            if n == 2:
                r[0, 1] = 0
                r[1, 0] = 0
            elif 3 <= n:
                r[n - 3, n - 2] = -1
                r[n - 3, n-1] = -1
                r[n - 2, n - 3] = -1
                r[n-1, n - 3] = -1
                r[n - 2, n-1] = 0
                r[n-1, n - 2] = 0
        elif typ == 'E' or typ == 5:
            for k in [[2, 4], [4, 2]]:
                r[k[0], k[1]] = -1
            for k in [[3, 4], [4, 3]]:
                r[k[0], k[1]] = 0
        elif typ == 'F' or typ == 6:
            r[1, 2] = -2
        elif typ == 'G' or typ == 7:
            r[0, 1] = -3
     
    return r 

def compareWeightsTableaux(P1,P2,typ,rank): 
    # a,b are tableaux
    t1=WeightOfTableau(P1)
    t2=WeightOfTableau(P2)
    r=compareWeights2(t1,t2,typ, rank)

    return r

def WeightOfTableau(a): 
    # a[i] are columns of the tableau a
    m=len(a)
    n=len(a[0])
    r=[]
    for i in range(1,n+1):
        r.append(0)
    for i in range(m):
        t1=PluckerToMinimalAff(a[i])
        #r=list(np.array(r)+np.array(t1))
        r=list(map(add, r, t1))
        
    return r

def compareWeights(a, b, typ, rank): 
    # compare two weights
    r=1                             # r=1 means a>=b          
    l=a-b
    c=CartanMatrixSelfDefined(typ, rank)
    for i in range(rank): 
        p=0
        for j in range(rank):
            t1=(transpose(c)^(-1))[j,i]
            p=p+l[j,0]*t1
        if p<0: 
            r=-1              # r=-1 means a is not >= b, it is possible that a<b or a,b are not comparable
            break 
            
    if r==-1:
        for i in range(rank):
            p=0
            for j in range(rank):
                t1=(transpose(c)^(-1))[j,i]
                p=p+l[j,0]*t1
            if p>0: 
                r=0
                break
    return r

def compareWeights2(a,b,typ,rank): 
    # a,b are lists
    n=len(a)
    t1=Matrix(n,1)
    for i in range(n): 
        t1[i,0]=a[i] 
    t2=Matrix(n,1)
    for i in range(n): 
        t2[i,0]=b[i] 
    r=compareWeights(t1,t2,typ,rank)

    return r

def matrixMutation(mat,  k):  
    # matrix mutates at k
    size=mat.nrows()
    r=Matrix(size,size)
    for i in range(size):
        for j in range(size):
            r[i,j]=mat[i,j]
    
    for i in range(size): 
        for j in range(size): 
            
            if k==i or k==j:
                r[i,j]=-mat[i, j]    
            else: 
                r[i, j] = mat[i, j]+1/2*(abs(mat[i,k])*mat[k,j]+mat[i,k]*abs(mat[k,j]))
     
    return r

def ExtendSetOfTableauxToContainPromotions(l,n): 
    # l is a list of tableaux 
    # extend the set l to include their promotions
    r=[]
    for i in l:
        t1=PromotionOfTableauNTimes(n,i,n)
        r=r+t1 
    r=np.unique(r,axis=0)

    return r

def ExtendSetOfTableauxToContainPromotionsInMatrix(l,n): 
    # l is a list of tableaux in matrix form
    # extend the set l to include their promotions
    r=[]
    for i in l:
        t1=PromotionOfTableauNTimesInMatrix(n,i,n)
        r=r+t1 
    r=removeDuplicates2(r)
    
    return r

def TableauxToListOfTimesOfOccurrenceOfNumbers(a):
    # compute occurrences of numbers in tableau a
    r=[]
    n=a.nrows() 
    m=a.ncols() 
    r1=[]
    for i in range(n):  
        for j in range(m): 
            r1.append(a[i,j]) 
    for k in range(1,max(r1)+1):
        t1=0
        for i in r1:
            if i==k:
                t1=t1+1 
        r.append(t1)  
    return r

def TableauxToListOfTimesOfOccurrenceOfNumbersLengthN(a,N):
    r=[]
    n=a.nrows() 
    m=a.ncols() 
    r1=[]
    for i in range(n):  
        for j in range(m): 
            r1.append(a[i,j]) 
    for k in range(1,N):
        t1=0
        for i in r1:
            if i==k:
                t1=t1+1 
        r.append(t1)
    return r
    
def TableauxToListOfTimesOfOccurrenceOfNumbersLengthNWithContentLessOrEquN(a,N): 
    # compute the occurrences of numbers in i for those i in a such that the numbers in i is less or equal to N
    r=[]
    n=a.nrows() 
    m=a.ncols() 
    r1=[]
    for i in range(n):  
        for j in range(m): 
            r1.append(a[i,j])       
    if max(r1)<=N:
        for k in range(1,N):
            t1=0
            for i in r1:
                if i==k:
                    t1=t1+1 
            r.append(t1)
    return r
    
def TableauxToListOfTimesOfOccurrenceOfNumbersTableauIsList(a):
    t1=TableauToMatrix(a)
    r=TableauxToListOfTimesOfOccurrenceOfNumbers(t1)
 
    return r

def TableauxToListOfTimesOfOccurrenceOfNumbersLengthNTableauIsList(a,N):
    t1=TableauToMatrix(a)
    r=TableauxToListOfTimesOfOccurrenceOfNumbersLengthN(t1,N)
 
    return r


def computeEquationsForModulesTableaux(variable2, mat, k, typ, rank): 
    # mutation of Grassmannian cluster variables
    # variable2=(variables on quiver, cluster variables obtained so far)
    variable1=variable2[0]
    clusterVariables=variable2[1] 
    size=mat.nrows() 
    newVariable=[]
    newVariable2=[]
    variable=variable1

    for i in range(size):
        if mat[i, k]>0:
            newVariable=UnionOfTwoTableaux( newVariable, PowerOfTableaux(variable[i][1], mat[i,k]) )
 
    for i in range(size): 
        if mat[i, k]<0:
            newVariable2= UnionOfTwoTableaux( newVariable2, PowerOfTableaux(variable[i][1], -mat[i,k]) )
 
    variable[k][0]=variable[k][0]+1
    t1=compareWeightsTableaux(newVariable, newVariable2,typ,rank)
 
    if t1==1: 
        variable[k][1]=TableauDivision(newVariable, variable[k][1])
    else:
        variable[k][1]=TableauDivision(newVariable2, variable[k][1])  
        
    clusterVariables=TableauToMatrix(variable[k][1]) 
    
    r=[variable, clusterVariables]

    return r


def ll_perms(lli,typ,rank,max_column,n,repeat): 
    #Function for multiprocessing
    b1=[]
    IC=InitialCluster(rank,n)
    mat1=IC[0]
    vertices1=IC[1]
    ll=list(map(lambda x: x - 1, lli))
    
    mutationSequence=[]
    for j1 in [1..repeat]: # repeat the same sequence of mutations, it will give more cluster variables
        mutationSequence=mutationSequence+ll 
        
    for j in range(len(mutationSequence)): 
        vertices1 = computeEquationsForModulesTableaux(vertices1, mat1, mutationSequence[j],typ,rank)
        mat1 = matrixMutation(mat1, mutationSequence[j]) 

        if vertices1[1].ncols()>max_column:
            vertices1 = computeEquationsForModulesTableaux(vertices1, mat1, mutationSequence[j],typ,rank) # if encounter a cluster variable with too large number of columns, we mutate again to remove it
            mat1 = matrixMutation(mat1, mutationSequence[j]) 
        else:
            b1.append(vertices1[1]) 
            
    b1=removeDuplicates2(b1)
    b1=ExtendSetOfTableauxToContainPromotionsInMatrix(b1,n)
    b1=TableauExpansionsInMatrixList(b1, n)
    
    return b1

####################################################################
# compute only cluster variables, SLk
if __name__ == '__main__':
    kk = 5   #...for SL_kk
    max_column = 5 #...obtain only tableaux with number of columns less or equal to max_column
    max_step = 12     #...this number controls the length of random mutation sequence, in order to obtain all cluster variables with number of columns less or equal to a fixed number, we need to put the number max_step sufficiently large
    checkpoint = 3   #...if after check_point steps, the number elements in b2 is not increasing, then stop
    repeat=8
    
    b1=[]
    
    #Run generation 
    
    if kk==3:   # SL3
        ll0=[5]
    elif kk==4:
        ll0=[5,8,9]
    elif kk==5:
        ll0=[5,8,9,12,13,14]
    elif kk==6:
        ll0=[9, 18, 19, 13, 5, 17, 8, 20, 12, 14]
    elif kk==7:
        ll0=[5,8,9,12,13,14,17,18,19,20,23,24,25,26,27]
    elif kk==8:
        ll0=[5,8,9,12,13,14,17,18,19,20,23,24,25,26,27,30,31,32,33,34,35]
    elif kk==9:
        ll0=[5,8,9,12,13,14,17,18,19,20,23,24,25,26,27,30,31,32,33,34,35,38,39,40,41,42,43,44]
    elif kk==10:
        ll0=[5,8,9,12,13,14,17,18,19,20,23,24,25,26,27,30,31,32,33,34,35,38,39,40,41,42,43,44,47,48,49,50,51,52,53,54]

            
    sn=0
    num=0
    
    
    while (1):  #...have split the ComputeClusterVariablesInGrkn function up into part we wish to parallelise 'll_perms' and the remainder
        sn=sn+1

        lls = [np.random.permutation(ll0) for iii in range(max_step)]
        for i in lls:
            t1=ll_perms_SLk(i, kk, max_column, repeat)
            b1=b1+t1
        
        b1=removeDuplicatesListOfLists(b1)
        
        if sn%checkpoint==1:
            print('sn, len(b1)', sn, len(b1))
            if num==len(b1) and num!=0:
                break
            else:
                num=len(b1)

