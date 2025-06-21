%Estruturas necesarias
par int: N;

array[1..N,1..N] of int: tiempos_por_funcionario;

array[1..N,1..N] of var bool: solucion;

%------------------------------------------CHEQUEOS--------------------------------------------------

%----------------------------------------RESTRICCIONES-----------------------------------------------

%Un funcionario solo puede tener un unico trabajo
constraint forall(i in 1..N)(
  sum(j in 1..N) (bool2int(solucion[i,j])) == 1
);

%Solo puedo coger un trabajo por columna
constraint forall(j in 1..N)(
  sum(i in 1..N) (bool2int(solucion[i,j])) == 1
);

%La suma de los trabajos realizados por cada funcionario ha de ser la mas optima posible
solve minimize sum(i, j in 1..N) (tiempos_por_funcionario[i, j] * bool2int(solucion[i, j])); %Minimiza las verdes, suma 1 cada vez que una pieza es verde (suma 1 por el (1))

output [ "\(sum(i,j in 1..N) (tiempos_por_funcionario[i, j] * bool2int(solucion[i, j])))"]

