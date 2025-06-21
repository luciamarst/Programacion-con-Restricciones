% Use this editor as a MiniZinc scratch book
int : cant1 = 1000;
int : cant2 = 600;
int : cant3 = 3000;

var int : prod1;
var int : prod2;

constraint prod1 > 0;
constraint prod2 > 0;
constraint prod1*250+prod2*125 <= cant1;
constraint prod1*12+prod2*8 <= cant2;
constraint prod1*300+prod2*210 <= cant3;

solve maximize (prod1*10+prod2*15)