% Definir las dimensiones de la superficie
int: x_superficie;  % Ancho de la superficie
int: y_superficie;  % Alto de la superficie

% Definir el número de cajas
int: n_cuadrados;  % Número de cajas

% Definir las dimensiones de las cajas (tuplas de ancho y alto)
array[1..n_cuadrados] of tuple(int, int): cuadrados;  % array de n_cuadrados cajas con sus dimensiones (ancho, alto)

% Posiciones de las cajas (a determinar)
array[1..n_cuadrados] of var 0..x_superficie-1: pos_x;  % Coordenada x de la esquina superior izquierda de cada caja
array[1..n_cuadrados] of var 0..y_superficie-1: pos_y;  % Coordenada y de la esquina superior izquierda de cada caja
array[1..n_cuadrados] of var 0..1: orientacion; %Orientacion de cada pieza

% Superficie de la caja
array[0..x_superficie-1, 0..y_superficie-1] of var 0..n_cuadrados: matriz;  % Matr

% Restricción: Cada caja debe estar completamente dentro de la superficie
constraint forall(i in 1..n_cuadrados) (
    pos_x[i] + cuadrados[i].1 <= x_superficie /\  % La caja no debe sobresalir por el lado derecho
    pos_y[i] + cuadrados[i].2<= y_superficie    % La caja no debe sobresalir por el lado superior
);

% Restricción: No solapamiento de las cajas
constraint forall(i,j in 1..n_cuadrados where i < j) (
        
        (
            pos_x[i] + cuadrados[i].1 > pos_x[j] /\  % Si la caja i esta a la derecha de la caja j
            pos_y[i] + cuadrados[i].2 > pos_y[j] /\  % Si la caja i esta encima de la caja j
            pos_x[i] < pos_x[j] + cuadrados[j].1 /\  % Si la caja i esta a la izquierda de la caja j
            pos_y[i] < pos_y[j] + cuadrados[j].2    % Si la caja i esta debajo de la caja j
        ) -> (pos_x[i] != pos_x[j] \/ pos_y[i] != pos_y[j]) %Si se cumplen todas, entonces, i y j no pueden estar en la misma coordenada de inicio
    
);

% Restricción para que la matriz sea correctamente marcado
constraint forall(k in 1..n_cuadrados) (
    forall(dx in 0..cuadrados[k].1-1) (
        forall(dy in 0..cuadrados[k].2-1) (
            matriz[pos_x[k] + dx, pos_y[k] + dy] = k
        )
    )
);

%Restriccion para la orientacion


% Minimizar la cantidad de solapamientos
solve satisfy;

