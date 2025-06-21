%Estructuras

par int: longitud;
par int: colores;
par int: consumo_max;

array[1..colores] of int: consumos;
array[1..longitud] of var 1..colores: solucion; 

%-------------------Requisitos-------------------

%No haya ,mas de dos luces seguidas del mismo. Es decir, puede haber dos seguidas del mismo pero no mas de ahi

constraint forall(i in 1..longitud-2) ((solucion[i] == solucion[i+1]) -> (solucion[i+2]!=solucion[i]));

%En un momento i, la diferencia entre un color y los demas en ese momento 1 no puedde ser >= 1

constraint forall(i in 1..longitud, j in 1..colores) (abs((sum(k in 1..i)(solucion[k]=j) - (sum(k in 1..i)(solucion[k]!=j))))<=1);

%Consumo 
constraint sum(i in 1..longitud) (consumos[solucion[i]]) <= consumo_max;

solve satisfy;


