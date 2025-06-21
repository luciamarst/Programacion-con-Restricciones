int: N; % Número de movimientos (definido en el .dzn)
set of int: States = 0..N-1; % Estados en cada paso

array[States] of var 0..3: MI; % Misioneros en izquierda
array[States] of var 0..3: CI; % Caníbales en izquierda
array[States] of var 0..3: MD; % Misioneros en derecha
array[States] of var 0..3: CD; % Caníbales en derecha
array[States] of var 0..1: B; % Posición de la barca (0 = izq, 1 = der) y la gente que lleva dentro

% Estado inicial
constraint MI[0] = 3;
constraint CI[0] = 3;
constraint MD[0] = 0;
constraint CD[0] = 0;
constraint B[0]  = 0;

% Estado final
constraint MI[N-1] = 0;
constraint CI[N-1] = 0;
constraint MD[N-1] = 3;
constraint CD[N-1] = 3
;
constraint B[N-1] = 1;

%Restriccion 1: Transiciones válidas
constraint forall(s in 1..N-1) (
    % Si la barca está en la izquierda, se mueve hacia la derecha
    ((B[s-1] = 0 -> (
        (MI[s] = MI[s-1] - 1 /\ CI[s] = CI[s-1] /\ MD[s] = MD[s-1] + 1 /\ CD[s] = CD[s-1]) \/ % Mueve 1 misionero
        (MI[s] = MI[s-1] - 2 /\ CI[s] = CI[s-1] /\ MD[s] = MD[s-1] + 2 /\ CD[s] = CD[s-1]) \/ % Mueve 2 misioneros
        (MI[s] = MI[s-1] /\ CI[s] = CI[s-1] - 1 /\ MD[s] = MD[s-1] /\ CD[s] = CD[s-1] + 1) \/ % Mueve 1 caníbal
        (MI[s] = MI[s-1] /\ CI[s] = CI[s-1] - 2 /\ MD[s] = MD[s-1] /\ CD[s] = CD[s-1] + 2) \/ % Mueve 2 caníbales
        (MI[s] = MI[s-1] - 1 /\ CI[s] = CI[s-1] - 1 /\ MD[s] = MD[s-1] + 1 /\ CD[s] = CD[s-1] + 1) % Mueve 1 misionero y 1 caníbal
    )) /\

    % Si la barca está en la derecha, se mueve hacia la izquierda
    (B[s-1] == 1 -> (
        (MI[s] = MI[s-1] + 1 /\ CI[s] = CI[s-1] /\ MD[s] = MD[s-1] - 1 /\ CD[s] = CD[s-1]) \/ % Mueve 1 misionero
        (MI[s] = MI[s-1] + 2 /\ CI[s] = CI[s-1] /\ MD[s] = MD[s-1] - 2 /\ CD[s] = CD[s-1]) \/ % Mueve 2 misioneros
        (MI[s] = MI[s-1] /\ CI[s] = CI[s-1] + 1 /\ MD[s] = MD[s-1] /\ CD[s] = CD[s-1] - 1) \/ % Mueve 1 caníbal
        (MI[s] = MI[s-1] /\ CI[s] = CI[s-1] + 2 /\ MD[s] = MD[s-1] /\ CD[s] = CD[s-1] - 2) \/ % Mueve 2 caníbales
        (MI[s] = MI[s-1] + 1 /\ CI[s] = CI[s-1] + 1 /\ MD[s] = MD[s-1] - 1 /\ CD[s] = CD[s-1] - 1) % Mueve 1 misionero y 1 caníbal
    )))
    
);

%Restriccion 2: La orilla tiene que ir de izquierda a derecha y de derecha a izquierda alternamente
constraint forall(s in 0..N-2) (
    B[s+1] = 1 - B[s] % La barca cambia de lado en cada paso
);

%Restriccion 3: El barco siempre tiene que llevar como mínimo a una persona y como máximo a 2.
constraint forall(s in 0..N-2) (
    (B[s] = 0 -> 
        (abs(MI[s] - MI[s+1]) + abs(CI[s] - CI[s+1])) >= 1 
    ) 
    /\
    (B[s] = 1 -> 
        (abs(MD[s] - MD[s+1]) + abs(CD[s] - CD[s+1])) >= 1 
    )
);

%Restriccion 4: No podemos exceder el valor de caníbales en el de misioneros en ninguna de las orillas. (A no ser que M = 0)
constraint forall(s in 0..N-1)(
    % Validación de seguridad (misioneros >= caníbales, excepto si no hay misioneros)
    (MI[s] = 0 \/ MI[s] >= CI[s]) /\ (MD[s] = 0 \/ MD[s] >= CD[s])
);



solve satisfy;

