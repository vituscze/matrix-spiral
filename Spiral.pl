% Author: Vít Šefl
% Date: 19.3.2013

%   isEmpty(+M)
% Platí právě když M neobsahuje žádné prvky.
isEmpty([]).
isEmpty([[]|XS]) :- isEmpty(XS).

%   split(+M, Col, Rest)
% Rozdělí matici na první sloupec a zbytek.
split([], [], []).
split([[X|XS]|XSS], [X|C], [XS|R]) :-
    split(XSS, C, R).

%   splitRev(+M, RCol, Rest)
% Rozdělí matici na první sloupec (v opačném pořadí) a zbytek.
splitRev(M, C, R) :- splitRev(M, [], C, R).

splitRev([], A, A, []).
splitRev([[X|XS]|XSS], A, A2, [XS|R]) :-
    splitRev(XSS, [X|A], A2, R).

%   rotate(+M, RM)
% Otočí matici o 90° ve směru hodinových ručiček.
rotate(XS, []) :- isEmpty(XS).
rotate([X|XS], [C|MR]) :-
    splitRev([X|XS], C, R),
    rotate(R, MR).

%   spiral(+M, R)
% Nalezne všechny prvky na spirále matice.
spiral(M, []) :- isEmpty(M).
spiral([X|XS], FSp) :-
    split([X|XS], C, R),
    rotate(R, RR),
    spiral(RR, Sp),
    append(C, Sp, FSp).
