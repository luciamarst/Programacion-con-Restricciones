%Papanoel

int: m; % Número de juguetes diferentes
int: n; % Número de niños
int: satisfaccion_minima; % Satisfacción mínima requerida

% Unidades disponibles de cada juguete
array[0..m-1] of int: disponibles; 

% Define los tipos posibles
enum TipoJuguete; 
% Almacena el tipo de cada juguete como un enum
array[0..m-1] of TipoJuguete: tipos; 

% Matriz de satisfacción de niños por juguete
array[0..n-1, 0..m-1] of int: satisfaccion;

%USADA PARA CONSTRUIR LA SOLUCION. Los valores enteros representan el indice del juguete seleccionado
% Variables de decisión: Cada niño recibe dos juguetes (se almacenan ordenados)
array[0..n-1, 0..1] of var 0..m-1: asignaciones; 

%-------------------------------------------------------CHEQUEO DE PARÁMETROS-------------------------------------------------------%
%Chequeo 1: Cantidad denjuguetes mayor que 0
constraint assert(m > 0, "La cantidad de juguetes debe ser mayor que cero");

%Chequeo 2: El numero de niños debe ser mayor que 0
constraint assert( n > 0, " El numero de niños debe ser mayor que cero");

%Chequeo 3: Satisfaccion minima mayor que 0
constraint assert(satisfaccion_minima > 0, "La satisfaccion minima debe ser mayor que cero");

%Chequeo 4: Disponibilidad de cada juguete
constraint assert (forall (i in 0..m-1) (disponibles[i] >= 0), "La disponibilidad de cada juguete debe ser mayor que 0");

%-----------------------------------------------------------RESTRICCIONES-----------------------------------------------------------%
% Restricción 1: Cada niño debe recibir juguetes de distinto tipo
constraint forall(i in 0..n-1) (asignaciones[i,0] != asignaciones[i,1]);

% Restricción 2: La satisfacción total de cada niño debe ser al menos "satisfaccion_minima"
constraint forall(i in 0..n-1) (satisfaccion[i, asignaciones[i,0]] + satisfaccion[i, asignaciones[i,1]] >= satisfaccion_minima);

% Restricción 3: No se puede superar la cantidad de juguetes disponibles
constraint forall (j in 0..m-1) (
  sum(i in 0..n-1, k in 0..1) (bool2int (asignaciones[i,k] == j)) <= disponibles[j]
);

% Restricción 4: Los dos juguetes asignados a cada niño deben estar en orden (para evitar repeticiones)
constraint forall(i in 0..n-1) (
    asignaciones[i,0] < asignaciones[i,1]
);

%Otra manera de ponerlo es
% constraint forall (i in 1..n) (ordered (asignaciones[i,j] | j in 1..ja));

solve satisfy;

output ["Asignaciones: \(asignaciones)"];