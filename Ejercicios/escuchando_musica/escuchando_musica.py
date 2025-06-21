import sys
import io  
from pickletools import optimize
from z3 import *

#Espera entrada por un archivo dado

# Abrimos el archivo en modo lectura
with open("input.txt", "r") as file:
    # Leemos todas las líneas y eliminamos las vacías
    lines = [line.strip() for line in file.readlines() if line.strip()]

# Procesamos las líneas
canciones = int(lines[0])  # Número de canciones
t1 = int(lines[1])  # Tiempo máximo de ida
t2 = int(lines[2])  # Tiempo máximo de vuelta

# Leemos las duraciones y satisfacciones de las canciones
par_duracion_satisfaccion = []
for line in lines[3:]:
    duracion, satisfaccion = map(int, line.split(","))  # Dividimos por la coma y convertimos a enteros
    par_duracion_satisfaccion.append((duracion, satisfaccion))

# Mostramos los datos leídos
print("Número de canciones:", canciones)
print("Tiempo máximo de ida:", t1)
print("Tiempo máximo de vuelta:", t2)
print("Duración y satisfacción de las canciones:", par_duracion_satisfaccion)

#Prints por consola de lo que hacemos
def ncancion(i): #Torre dada
    return "cancion_"+str(i)

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
cancion = []
for i in range(canciones):
    cancion.append(Int(ncancion(i)))
# fin declaración
#Los valores de las cancioens solo peuden ser 0(Ninguno),1(Ida) o 2(Vuelta). 
for i in range(canciones):
    s.add(Or(cancion[i] == 0, cancion[i] == 1, cancion[i] == 2))

#Restriccion 1. Si escojo una cancion en la ida, no puedo escogerla en la vuelta y viceversa
for j in range(canciones):
    for i in range(canciones):
        if i != j:
            s.add(Or(Not(cancion[i] == 1), Not(cancion[j] == 1))) #Niego porque si tenemos 1 y 1, pasamos a tener 0 y 0, que no es true

#Restriccion 2: No podemos exceder el tiempo de ida
tiempoIda = []
for j in range(canciones):
    tiempoIda.append(If(cancion[j] == 1, par_duracion_satisfaccion[j][0], 0))  # Tiempo de ida si la canción es seleccionada
s.add(Sum(*tiempoIda) <= t1)

#Restriccion 3: No podemos exceder el tiempo de vuelta
tiempoVuelta = []
for j in range(canciones):
    tiempoVuelta.append(If(cancion[j] == 2, par_duracion_satisfaccion[j][0], 0))  # Tiempo de vuelta si la canción es seleccionada
s.add(Sum(*tiempoVuelta) <= t2)

# Restricción 4: No puede haber ida sin canciones
s.add(Sum(*tiempoIda) > 0)

# Restricción 5: No puede haber vuelta sin canciones
s.add(Sum(*tiempoVuelta) > 0)

# Función objetivo: Maximizar la satisfacción total
satisfaccionTotal = Sum([
    If(cancion[j] > 0, par_duracion_satisfaccion[j][1], 0)  # Satisfacción si la canción es seleccionada
    for j in range(canciones)
])
s.maximize(satisfaccionTotal)

# Resolver el problema
if s.check() == sat:
    # Evaluar la satisfacción máxima
    satisfaccion_maxima = sum(
        par_duracion_satisfaccion[j][1] if s.model().eval(cancion[j]).as_long() > 0 else 0
        for j in range(canciones)
    )
    print("Satisfacción máxima:", satisfaccion_maxima)

    # Imprimir las canciones seleccionadas
    for i in range(canciones):
        print(f"Canción {i}: {s.model().eval(cancion[i]).as_long()}")
else:
    print("Imposible")
    
#print(s.to_smt2())
exit(0)