#!/usr/bin/python3

import sys
import io  

#Espera entrada por un archivo dado
filenameIn = sys.argv[1]
filenameOut = sys.argv[2]
myinput = "".join(open(filenameIn, "r").readlines())
sys.stdin = io.StringIO(myinput)
sys.stdout = open(filenameOut, mode='w')

# altura : altura de la torre
# disp : piezas disponibles
# Colores: Azul = 0, Rojo = 1 , Verde = 2;

#Lee de lo que viene del archivo no de la consola
altura = int(input())
disp1 = input().split()
disp = []
for i in range(len(disp1)):
    disp.append(int(disp1[i]))

#Prints por consola de lo que hacemos
def torre (i): #Torre dada
    return "torre_"+str(i)

def setlogic(l): #
    return "(set-logic "+ l +")"

def intvar(v): #Declaramos una variable entera, en este caso cada una de las torres
    return "(declare-fun "+v+" () Int)"

def bool2int(b):
    return "(ite "+b+" 1 0 )"

def addand(a1,a2):
    return "(and "+a1+" "+a2+" )"
def addor(a1,a2):
    return "(or "+a1+" "+a2+" )"
def addnot(a):
    return "(not "+a+" )"

def addexists(a):
    if len(a) == 0:
        return "false"
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return "(or " + x + " " + addexists(a) + " )" 

def addeq(a1,a2): #Comrpobamos igualdad
    return "(= "+a1+" "+a2+" )" 
def addle(a1,a2): #Comprobamos que una altura a1 sea siempre <= que una altura a2
    return "(<= "+a1+" "+a2+" )" 
def addge(a1,a2): #Comprobamos que una altura a1 sea siempre >= que una altura a2
    return "(>= "+a1+" "+a2+" )" 
# Lo mismo pero menor y mayor estricto
def addlt(a1,a2):
    return "(< "+a1+" "+a2+" )"
def addgt(a1,a2):
    return "(> "+a1+" "+a2+" )" 

#Adicion de piezas a la turra(añadir alturas)
def addplus(a1,a2):
    return "(+ "+a1+" "+a2+" )"

#Adicion de aserciones
def addassert(a):
    return "(assert "+a+" )"

def addsum(a):
    if len(a) == 0:
        return "0"
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return "(+ " + x + " " + addsum(a) + " )" 

def checksat(): #Comprobamos si es satisfactible
    print("(check-sat)")
def getmodel():
    print("(get-model)")
def getvalue(l):
    print("(get-value " + l + " )")

################################
# generamos un fichero smtlib2
################################

print("(set-option :produce-models true)")
print(setlogic("QF_LIA"))

#declaración de variables de la solución
for i in range(altura):
    print(intvar(torre(i)))
# fin declaración

#constraint forall (i in 0..altura-1) (0 <= torre_i);
#constraint forall (i in 0..altura-1) (torre_i <= 2);
for i in range(altura): # es equivalente a range(0,altura)
    print(addassert(addle("0",torre(i)))) #Comprobamos que la torre sea mayor o igual que 0 y si es asi añadimos la pieza a la torre
    print(addassert(addle(torre(i),"2"))) #Comprobamos que la torre sea menor o igual que 2 y si es asi añadimos la pieza a la torre
#end constraint

#No dos verdes consecutivas
#constraint forall (i in 0..altura-2) (torre_i!=2 \/ torre_i+1!=2);
for i in range(altura-1):
    c1 = addnot(addeq(torre(i),"2")) #Comprobamos que pieza uno no sea igual a verde
    c2 = addnot(addeq(torre(i+1),"2")) #Comprobamos que pieza dos no sea igual a verde
    print(addassert(addor(c1,c2))) #Comprobamos la disyuncion de la expresion logica obtenida de ambas piezas y añadimos el assert
#fin constraint

#Piezas azules >= Piezas verdes en todo momento
#constraint forall (i in 0..altura-1) (( sum (j in 0..i ) ( bool2int(torre_j=0) )) >=
#( sum (j in 0..i ) ( bool2int(torre_j=2) )));
for i in range(altura):
    suma = []
    sumv = []
    for j in range(i+1):
        suma.append(bool2int(addeq(torre(j),"0"))) #Añadimos a suma las pierzas azules
        sumv.append(bool2int(addeq(torre(j),"2"))) #Añadimos a sumv las piezas verdes
    print(addassert(addge(addsum(suma),addsum(sumv)))) #Comprobamos que la suma >= sumv y añadimos el assert
#fin constraint

#No mas piezas de las disponibles
#constraint forall (c in 0..2) (sum (i in 0..altura-1 ) ( bool2int(torre_i=c) ) <= disp[c]);
for c in range(3):
    sumc = []
    for i in range(altura):
        sumc.append(bool2int(addeq(torre(i),str(c))))
    print(addassert(addle(addsum(sumc),str(disp[c])))) #Suma de las pieas usadas es <= que las piezas disponibles
#fin constraint

#Piezas rojas >= Piezas azules + Piezas verdes
#constraint ( sum (i in 0..altura-1 where (torre[i]=Rojo)) ( 1 )) >=
#           ( sum (i in 0..altura-1 ) ( bool2int(torre[i]=Azul \/ torre[i]=Verde) ));
#Lo expresamos como
#sum (i in 0..altura-1 ) ( bool2int(torre[i]!=Rojo) ) <= altura div 2
sumc = [] #Suma de las piezas que no son rojas
for i in range(altura):
    sumc.append(bool2int(addnot(addeq(torre(i),"1")))) #Suma de las piezas que no son rojas
print(addassert(addle(addsum(sumc),str(altura//2))))  #Comprobamos que la suma de las piezas que no son rojas sea menor o igual a la mitad de la altura, asi asegruamos que las rojas siempre serán mas
#fin constraint

#Empieza con rojo
#constraint torre[0] = Rojo;
print(addassert(addeq(torre(0),"1")))

checksat() #Comprobamos si es satisfactible

#getmodel()
#Comprobamos el modelo
for i in reversed(range(altura)):
    getvalue("("+torre(i)+")")
exit(0)
