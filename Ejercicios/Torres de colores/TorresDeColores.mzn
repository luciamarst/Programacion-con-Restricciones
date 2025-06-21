%Torres de Hanoi
%Para parametrizar , en lugar de definir la altura, dejamos las varibales como entrada, sin usar el dzn

par int: altura; 
enum Colores = {Azul, Rojo, Verde};
array [Colores] of int: disp;


%Piezas torre tamaño 10: Colores 0 azul / 1 rojo / 2 verde;
array[0..altura-1] of var Colores: torre; %

%cubos de color azul 3
%cubos de color rojo 5
%cubos de color verde 3

% 1º Restriccion. No dos verdes juntas
constraint forall(x in 0..altura-2) (torre[x] == Verde -> torre[x+1] != Verde);
 %Tambien como: torre[x] = Verde -> torre[x+1] != Verde
    

% 2º Restriccion: Piezas verdes <= piezas azules SIEMPRE
constraint forall(i in 0..altura-1) (sum(x in 0..i)(bool2int(torre[x] == Verde)) <= sum(x in 0..i)(bool2int(torre[x] == Azul))); 

% 3º Restriccion: No mas disponibles
constraint forall (c in Colores) (sum (i in 0..altura-1) (bool2int(torre[i]==c)) <= disp[c]);

% 4º Restrccion: Pieza roja primera
constraint torre[0] == Rojo;

% 5º Restriccion: Total de rojas mayor o igual que azules y verdes
constraint (sum (i in 0..altura-1 where (torre[i]==Rojo)) (1)) >= altura/2;

% 6º Restriccion: No haya 3 seguidas
%constraint forall (x in 0..altura-3) (not(torre[x] == torre[x+1] /\ torre[x] == torre[x+2]));
%exists
%Para una ventana de N
% constraint forall (x in 0..altura-v) (exists (i in x+1..x+v-1) (torre[i] != torre[x]));

%solve minimize (sum (i in 0..altura-1 where (torre[i]==Verde))(1)); %Minimiza las verdes, suma 1 cada vez que una pieza es verde (suma 1 por el (1))
solve satisfy;
