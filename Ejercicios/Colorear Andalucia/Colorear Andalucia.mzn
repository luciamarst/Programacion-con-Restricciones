int : nc = 2;

var 1..nc : hu;
var int : se;
var 1..nc : gr;
var 1..nc : ca;
var 1..nc : ma;
var 1..nc : co;
var 1..nc : ja;
var 1..nc : al;

constraint se >= 1 /\ se <= nc;

constraint hu != se /\ hu != ca;
constraint se != ca /\ se != ma /\ se != co;
constraint ca != ma;
constraint ma != co /\ ma != gr;
constraint co != ja /\ co != gr;
constraint gr != ja /\ gr != al;
constraint hu = 1;

solve satisfy;

output ["hu=\(hu)\t se=\(se)\t co=\(co)\t",
        "ja=\(ja)\t ca=\(ca)\t ma=\(ca)\t",
        "gr=\(gr)\t al=\(al)\t"];





 