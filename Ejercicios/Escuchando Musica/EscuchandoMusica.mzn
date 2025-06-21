par int: n;
par int: tiempo1;
par int: tiempo2;

array[1..n] of tuple(int,int): canciones;%Duracion y Satisfaccion

array[1..2,1..n] of var bool: solucion;%1º Fila es la ida, 2º Fila es la vuelta. Las columnas son las canciones, escogiendo para cada las canciones que maximizan la solucion sin exceder el tiempo.

%Restricciones

%RESTRICCION 1: Si se ha escogido una cancion a la ida, no puede cogerse a la vuelta y viceversa
constraint forall(j in 1..n) (solucion[1,j]*solucion[2,j] = 0); 
                             
%RESTRICCION 2: No puede excederse el tiempo de ida
constraint sum(j in 1..n) (solucion[1,j] * canciones[j].1) <= tiempo1;

%RESTRICCION 3: No puede excederse el tiempo de la vuelta
constraint sum(j in 1..n) (solucion[2,j] * canciones[j].1) <= tiempo2;

%RESTRICCION 4: No puede haber una ida sin canciones
constraint sum(j in 1..n) (solucion[1,j] * canciones[j].1) > 0;

%RESTRICCION 5: No puede haber una vuelta sin canciones
constraint sum(j in 1..n) (solucion[2,j] * canciones[j].1) > 0;


solve maximize sum(j in 1..n) (solucion[1,j] * canciones[j].2 + solucion[2,j] * canciones[j].2);
