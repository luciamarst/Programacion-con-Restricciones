%Estructuras necesarias 

par int: n;
par int:presupuesto;

array[1..n] of tuple(int,int): adornos;%Coste y superficie

array[1..n] of var bool:solucion; %El indice indica que adornos se han cogido

%Restricciones

%RESTRICCIÓN Nº1: No se debe sobrepasar el presupuesto
%Si ese adorno ha sido cogido, será 1, entonces al multiplicarlo por su presupuesto se obtendrá el propio presupuesto de ese objeto i.

%Por tanto, de esta manera se está sumando cuando se haya cogido ese objeto.
constraint sum(i in 1..n) (solucion[i] * adornos[i].1) <= presupuesto;

%RESTRICCION Nº2
solve maximize sum(i in 1..n) (solucion[i] * adornos[i].2);

output ["\(sum(i in 1..n) (solucion[i] * adornos[i].2))"]