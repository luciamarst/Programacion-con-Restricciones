import sys
import io  
from pickletools import optimize
from z3 import *

#Espera entrada por un archivo dado


#Lee de lo que viene del archivo no de la consola
longitud = int(input()) #Leemos longitud
colores = int(input()) # Leemos colores
consumo_max = int(input()) #Leemos consumo maximo
#Leemos los consumos de cada tipo de bombilla
consumo1 = input().split()
consumo = []
for i in range(len(consumo1)):
    consumo.append(int(consumo1[i]))

#Prints por consola de lo que hacemos
def nluz(i): #Torre dada
    return "luz_"+str(i)

def setlogic(l): #
    return "(set-logic "+ l +")"

def intvar(v): #Declaramos una variable entera, en este caso cada una de las luces
    return "(declare-fun "+v+" () Int)"

def bool2int(b): #Convertimos booleano a entero
    return "(ite "+b+" 1 0 )"

def addand(luz1,luz2):
    return "(and "+luz1+" "+luz2+" )"
def addor(luz1,luz2):
    return "(or "+luz1+" "+luz2+" )"
def addnot(a):
    return "(not "+a+" )"

#def addexists(a): #Comprobamos si existe al menos una luz puesta    
def addexists(a):
    if len(a) == 0:
        return "false"
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return "(or " + x + " " + addexists(a) + " )" 

def addeq(luz1,luz2): #Comrpobamos igualdad
    return "(= "+ luz1+" "+luz2+" )" 
def addle(luz1,luz2): #Comprobamos que una altura a1 sea siempre <= que una altura a2
    return "(<= "+luz1+" "+luz2+" )" 
def addge(luz1,luz2): #Comprobamos que una altura a1 sea siempre >= que una altura a2
    return "(>= "+luz1+" "+luz2+" )" 
# Lo mismo pero menor y mayor estricto
def addlt(luz1,luz2):
    return "(< "+luz1+" "+luz2+" )"
def addgt(luz1,luz2):
    return "(> "+luz1+" "+luz2+" )" 

#Adicion de piezas a la turra(añadir alturas)
def addplus(luz1,luz2):
    return "(+ "+luz1+" "+luz2+" )"
def addminus(luz1,luz2):
    return "(- "+luz1+" "+luz2+" )"


#Adicion de aserciones
def addassert(a):
    return "(assert "+a+" )"

#Calculos recurvivos de sumas
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

s = Optimize()

print("(set-option :produce-models true)")
print(setlogic("QF_LIA"))


#declaración de variables de la solución
luz = []
for i in range(longitud):
    luz.append(Int(nluz(i)))
# fin declaración

#No haya ,mas de dos luces seguidas del mismo. Es decir, puede haber dos seguidas del mismo pero no mas de ahi
#constraint forall(i in 1..longitud-2) ((solucion[i] == solucion[i+1]) -> (solucion[i+2]!=solucion[i]));
for i in range(longitud - 2):
    c1 = (luz[i] == luz[i+1])  # Las dos primeras luces son del mismo color
    c2 = (luz[i+2] != luz[i])  # La tercera luz es de un color diferente
    s.add(Or(Not(c1), c2))  # Si c1 es verdadero, entonces c2 debe ser verdadero
#fin constraint

#En un momento i, la diferencia entre un color y los demas en ese momento 1 no puedde ser >= 1
#constraint forall(i in 1..longitud, j in 1..colores) ((sum(k in 1..i)(solucion[k]=j) - (sum(k in 1..i)(solucion[k]!=j)))<=1);
for i in range(longitud):
    for c in range(colores):
        sum1 = []  # Suma de luces del color c
        sum2 = []  # Suma de luces de otros colores
        for k in range(i):  # Consideramos todas las luces hasta el momento i
            sum1.append(If(luz[k] == c, 1, 0))  # Luces del color c
            sum2.append(If(luz[k] != c, 1, 0))  # Luces de otros colores

         # Generamos las sumas totales usando Z3
        suma_total_1 = Sum(*sum1)  # Suma de luces del color c
        suma_total_2 = Sum(*sum2)  # Suma de luces de otros colores

        abs_diff = If(suma_total_1 - suma_total_2 >= 0, suma_total_1 - suma_total_2, -(suma_total_1 - suma_total_2))
        # Añadimos ambas restricciones
        s.add(abs_diff <= 1)
#fin constraint

#Consumo 
#constraint sum(i in 1..longitud) (solucion[i]) <= consumo_max;
sum1 = []

for i in range(longitud):
   for c in range(colores):
       sum1.append(If(luz[i]== c,1,0) * consumo[c]) #Suma de las luces multiplicada por el consumo de cada color

s.add(Sum(*sum1) == consumo_max) #Comprobamos que la suma de las luces <= consumo maximo


print(s.check())

#print(s.model())
if s.check() == sat:
    for i in reversed(range(longitud)):
        print(s.model().eval(luz[i]))

    
#print(s.to_smt2())
exit(0)
