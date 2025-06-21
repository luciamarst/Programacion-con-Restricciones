% Sudoku
array[1..9, 1..9] of 0..9: init;  % Array de inicialización que recibirá los valores del archivo .dzn
array[1..9, 1..9] of var 1..9: sol; % Solución

% Copiar los valores de `init` mayores que 0 en `sol`
constraint forall(i in 1..9, j in 1..9) (
    init[i, j] > 0 -> sol[i, j] = init[i, j]
);

constraint forall(i in 1..9, j in 1..9, k in j+1..9) (sol[i,j] != sol[i,k]);

constraint forall(i in 1..9, j in 1..9, k in j+1..9) (sol[j, i] != sol[k, i]);


% Restricciones para subcuadrículas 3x3: no puede haber valores repetidos en las subcuadrículas
constraint forall(i in {1, 4, 7}, j in {1, 4, 7}, k1,k2 in i..i+2, l1,l2 in j..j+2 where (k1<k2 \/ (k1=k2 /\ l1 <l2)))
             (sol[k1, l1] != sol[k2,l2]);
        
    

solve satisfy;

output [
    concat(
        [ 
          concat([show(sol[i,j]),
                  if j == 9 /\ i mod 3 == 0 then "|\n-----------------|\n" 
                  elseif j == 9 then "|\n"
                  elseif j mod 3 == 0 then "|"
                  else " " endif
                ])
          | i in 1..9, j in 1..9]
    )
];