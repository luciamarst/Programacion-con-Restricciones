
%Estructuras de datos

par int: N;
par int:misioneros;
par int:canibales;

array[0..N] of var tuple(int,int): orilla1; %Orilla de lz izuiqerda, donde tengo el numero de canibales(1) y el numero de misioneros(2)
array[0..N] of var tuple(int,int): orilla2; %Orilla de lz derecha, donde tengo el numero de canibales(1) y el numero de misioneros(2)

array[0..N] of var tuple(1..misioneros,1..canibales,1..2): solucion; %El N de canibales <= misioneros y la barca


%Restricciones

%Restriccion 1: No se puede dar que en una orilla haya mas numero de canibales que de misioneros. Si no, se comen
constraint forall(i in 1..N)(solucion[i].1 <= solucion[i].2 /\ solucion[i].3 <= 2);

%Una solucion es que en la orilla1 haya 0 personas y en la derecha 2 c y 3 c
constraint forall(i in 1..N) (
    i mod 2 == 1 ->(
        (orilla2[i].1 = canibales - orilla1[i-1].1) /\ 
        (orilla2[i].2 = misioneros - orilla1[i-1].2) /\ solucion[i].3 =(canibales - orilla1[i-1].1) + (misioneros - orilla1[i-1].2))
    /\ i mod 2 != 1 ->
    (
        (orilla1[i].1 = canibales - orilla2[i-1].1) /\ 
        (orilla1[i].2 = misioneros - orilla2[i-1].2) /\ solucion[i].3 =(canibales - orilla2[i-1].1) + (misioneros - orilla2[i-1].2))
);

constraint (orilla1[0].1 = canibales /\ orilla1[0].2 = misioneros) /\ (orilla2[0].1 = 0 /\ orilla2[0].2 = 0);

constraint (orilla1[N].1 = 0 /\ orilla1[N].2 = 0) /\ (orilla2[N].1 = canibales /\ orilla2[N].2 = misioneros);

solve satisfy;
