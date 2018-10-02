:- op(810,fy,-).
:- op(820,xfy,^).
:- op(830,xfy,/).
:- op(840,xfy,>).

convert(Inp,Res) :- imply(Inp,Z), Res=Z.
convert(Inp,Res) :- conjuntion(Inp,Z), Res=Z.
convert(Inp,Res) :- distribute(Inp,Z), Res=Z.
convert(Inp,Res) :- disjunction(Inp,Z), Res=Z.
convert(Inp,Res) :- negative(Inp,Z), Res=Z.
convert(Inp,Res) :- atomic(Inp,Z), Res=Z.

imply(-(A>B),Res) :- convert(A>B,Inter) , convert(-(Inter),Res).
imply(A>B,Res) :- convert(B,X),convert(-(A),Y), convert(Y/X,Res).

conjuntion(-(A^B),Res) :- convert(-(B),X),convert(-(A),Y)  , disjunction((Y/X),Res).
conjuntion(A^B,Res) :- convert(A,X) , convert(B,Y) , (X^Y) = Res.

distribute(A/(B^C),Res) :- distribute(A/B,X) , distribute(A/C,Y) , (X^Y) = Res.
distribute((A^B)/C,Res) :- distribute(A/B,X) , distribute(A/C,Y) , (X^Y) = Res.
distribute(A/(B^C),Res) :- disjunction(A/B,X) , distribute(A/C,Y) , (X^Y) = Res.
distribute((A^B)/C,Res) :- disjunction(A/B,X) , distribute(A/C,Y) , (X^Y) = Res.
distribute(A/(B^C),Res) :- disjunction(A/B,X) , disjunction(A/C,Y) , (X^Y) = Res.
distribute((A^B)/C,Res) :- disjunction(A/B,X) , disjunction(A/C,Y) , (X^Y) = Res.

disjunction(-(A/B),Res) :- convert(-(A),X) , convert(-(B),Y) , conjuntion((X^Y),Res).
disjunction(A/B,Res) :- convert(A,X) , convert(B,Y) , (X/Y) = Res.

negative(-(-X),Res) :- convert(X,Res).
negative(-A,Res) :- convert(A,Z), (-Z) = Res.

atomic(A,Res) :- A=Res.

get_clauses(Inp) :- convert(Inp,Res),write_clause(Res).

write_clause(A^B) :- writer(A,W),asserta(fact(W)),write_clause(B).
write_clause(A) :- writer(A,W),asserta(fact(W)).
append([], L, L).
append([X | L], M, [X | N])   :- append(L, M, N).
writer(A/B,W) :- !,writer(A,W1),writer(B,W2),append(W1,W2,W).
writer(A,W) :- W=[A].
resolution(nil,nil) :- writeln("nothing implies nothing case").
resolution(nil,Goal) :-cleardb,writeln("no antecedent"),(-Goal)=G,get_clauses(G),/*writeln("for resolution refutation negation of consequent is added to clauses and thus resulting clauses are"),display,*/start_resol.
resolution(Inp,nil) :- cleardb,get_clauses(Inp),/*writeln("antecedent is broken down into following clauses"),display,*/writeln("no consequent, applying resolution refutation on antecedent clauses"),start_resol.
resolution(Inp,Goal) :- basic_setup(Inp,Goal),start_resol.
basic_setup(Inp,Goal) :- cleardb,get_clauses(Inp),/*writeln("antecedent is broken down into following clauses"),display,*/(-Goal)=G,get_clauses(G)/*,writeln("for resolution refutation negation of consequent is added to clauses and thus resulting clauses are"),display*/.
start_resol :- resol(R,T),contra(R,T).
cleardb :- retractall(fact(_)).
cleardb.
display :- fact(C),writeln(C),fail.
display.
match(C1,C2,R):-literal_match(C1,C2,C1literal,C2literal),del(C1,C1literal,C1new),del(C2,C2literal,C2new),match(C1new,C2new,R).
match(C1,C2,R) :- union(C1,C2,R).
literal_match(C1,C2,C1literal,C2literal) :- mem_list(C1literal,C1),mem_list(C2literal,C2),(-C1literal) = (C2literal).
literal_match(C1,C2,C1literal,C2literal) :- mem_list(C1literal,C1),mem_list(C2literal,C2),(C1literal) = (-C2literal).
union([],Y,Y).
union(X,[],X).
union([X|T],T,U) :- mem_list(X,Y),union(T,Y,U).
union([X|T],Y,[X|U]) :- not(mem_list(X,Y)),union(T,Y,U).
mem_list(X,[X|_]).
mem_list(X,[_|T]) :- mem_list(X,T).
del([Y|X1],Y,Z) :- del(X1,Y,Z).
del([X|X1],Y,[X|Z]) :- not(X=Y),del(X1,Y,Z).
del([],_,[]).
resol(R,T):- fact(C1),fact(C2),not(C1=C2),match(C1,C2,R),retract(fact(C1)),retract(fact(C2)),asserta(fact(R)),/*nl,writeln("new status:"),display,*/T=0.
resol(_,T):- writeln("NO!!! no contradiction,so antecedent doesn't imply consequent"),T=1.
contra(R,_) :- not(R=[]),!,start_resol.
contra(_,0) :- writeln("YES!!! Since contradiction is derived, so antecedent implies consequent is proved").
contra(_,_).
start :- writeln("call resolution(antecedent,consequent) using following symbols"),writeln("nil for nothing"),writeln("> imply"),writeln("/ or"),writeln("^ and"),writeln("- not"),writeln("() braces").
