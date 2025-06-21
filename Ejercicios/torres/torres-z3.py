#!/usr/bin/python3
from ast import Or
from pickletools import optimize
from z3 import *
import sys

# altura : altura de la torre
# disp : piezas disponibles
# Colores: Azul = 0, Rojo = 1 , Verde = 2;

#Espera entrada por consola
altura = int(input())
disp1 = input().split()
disp = []
for i in range(len(disp1)):
    disp.append(int(disp1[i]))

def ntorre (i):
    return "torre_"+str(i)

def bool2int(b):
    return If(b, 1, 0)

def addexists(a):
    if len(a) == 0:
        return False
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return Or(x,addexists(a)) 

def addsum(a):
    if len(a) == 0:
        return 0
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return x + addsum(a) 


################################
# generamos el problema 
################################

s = Optimize()

#declaración de variables de la solución
torre = [];
for i in range(altura):
    torre.append(Int(ntorre(i)))
# fin declaración

#constraint forall (i in 0..altura-1) (0 <= torre_i);
#constraint forall (i in 0..altura-1) (torre_i <= 2);
for i in range(altura): # es equivalente a range(0,altura)
    s.add(0 <= torre[i])
    s.add(torre[i] <= 2)
#end constraint

#No dos verdes consecutivas
#constraint forall (i in 0..altura-2) (torre_i!=2 \/ torre_i+1!=2);
for i in range(altura-1):
    c1 = not(torre[i] == 2)
    c2 = not(torre[i+1] == 2)
    s.add(Or(c1,c2)) #A->B = !A \/ B
#fin constraint

#Piezas azules >= Piezas verdes en todo momento
#constraint forall (i in 0..altura-1) (( sum (j in 0..i ) ( bool2int(torre_j=0) )) >=
#( sum (j in 0..i ) ( bool2int(torre_j=2) )));
for i in range(altura):
    suma = []
    sumv = []
    for j in range(i+1):
        suma.append(bool2int(torre[j] == 0))
        sumv.append(bool2int(torre[j] == 2))
    s.add(addsum(suma) >= addsum(sumv))
#fin constraint

#No mas piezas de las disponibles
#constraint forall (c in 0..2) (sum (i in 0..altura-1 ) ( bool2int(torre_i=c) ) <= disp[c]);
for c in range(3):
    sumc = []
    for i in range(altura):
        sumc.append(bool2int(torre[i] == c))
    s.add(addsum(sumc) <= disp[c])
#fin constraint

#Piezas rojas >= Piezas azules + Piezas verdes
#constraint ( sum (i in 0..altura-1 where (torre[i]=Rojo)) ( 1 )) >=
#           ( sum (i in 0..altura-1 ) ( bool2int(torre[i]=Azul \/ torre[i]=Verde) ));
#Lo expresamos como
#sum (i in 0..altura-1 ) ( bool2int(torre[i]!=Rojo) ) <= altura div 2
sumc = []
for i in range(altura):
    sumc.append(bool2int(Not(torre[i] == 1)))
s.add(addsum(sumc) <= altura//2)
#fin constraint

#Empieza con rojo
#constraint torre[0] = Rojo;
s.add(torre[0] == 1)

## preferimos las rojas
for i in range(altura):
    s.add_soft(torre[i] == 1)

# preferimos las rojas arriba o abajo
#for i in range(altura):
#    s.add_soft(torre[i] == 1,i+1)
#    s.add_soft(torre[i] == 1,altura-i)

## preferimos las rojas sobre las demás
#for i in range(altura):
#    s.add_soft(torre[i] == 1,1,"R")
## preferimos las azules a las verdes
#for i in range(altura):
#    s.add_soft(torre[i] == 0,1,"A")

print(s.check())

#print(s.model())
for i in reversed(range(altura)):
    print(s.model().eval(torre[i]))

#print(s.to_smt2())
exit(0)
