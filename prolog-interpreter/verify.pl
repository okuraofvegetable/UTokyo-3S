rule nat(z).
rule nat(s(X)) :- nat(X).
query nat(X).

rule male(koji).
rule parent(kobo,koji).
rule father(X,Y) :- parent(X,Y),male(Y).
query father(kobo,Z).

rule add(z,Y,Y).
rule add(s(X),Y,s(Z)) :- add(X,Y,Z).
query add(s(z),X,X).

rule test :- q(X,X).
rule q(X,f(X)).
query test.
query q(X,X).

rule append([],Y,Y).
rule append([A|X],Y,[A|Z]) :- append(X,Y,Z).
rule concat([X|[]],X).
rule concat([X|Y],Z) :- concat(Y,W),append(X,W,Z).

query append([1,2,3],[4,5],Z).
query append(X,Y,[1,2,3,4,5]).
query concat([[1],[2,3,4]] ,X).


rule in(X,[X|Y]).
rule in(X,[Y|Z]) :- in(X,Z).
rule choose([X|Y],Y,X).
rule choose([A|X],[A|Y],Z) :- choose(X,Y,Z).
rule hamilton(V,E) :- choose(V,Rem,Start),hamiltonsub(Rem,E,Start).
rule hamiltonsub([],X,Y).
rule hamiltonsub(V,E,Now) :- choose(V,Rem,Next),in([Now|[Next|[]]],E),hamiltonsub(Rem,E,Next).

query hamilton([1,2,3,4],[[1,2],[2,3],[3,4],[4,1]]).

rule eq(a,b).
rule eq(c,b).
rule eq(X,Z) :- eq(X,Y),eq(Y,Z).
rule eq(X,Y) :- eq(Y,X).
query eq(a,c).