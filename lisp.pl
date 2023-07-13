symbol(X) :- atom(X).
%symbol(X) :- freeze(X, atom(X)).

symbols(X) :- symbol(X).

symbols([]).

symbols([H|T]) :-
    symbols(H),
    symbols(T).

% lookup(X, Env, Val).
%
% [quote-unbound(quote)] will be the empty environment
% when unbound(quote) is returned, this means that
% `quote` is unbound

lookup(X, [X-Val|_], Val) :- !.

lookup(X, [Y-_|Tail], Val) :-
    X \= Y,
    %dif(X, Y),
    lookup(X, Tail, Val).

% to avoid name clashing with `eval`
%
% evil(Expr, Env, Val).

evil([quote, X], Env, X) :-
    lookup(quote, Env, unbound(quote)),
    symbols(X).

evil(Expr, Env, Val) :-
    symbol(Expr),
    lookup(Expr, Env, Val),
    Val \= unbound(quote).
    %dif(Val, unbound(quote)).

evil([lambda, [X], Body], Env, closure(X, Body, Env)).

evil([list|Tail], Env, Val) :-
    evil_list(Tail, Env, Val).

evil([E1, E2], Env, Val) :-
    evil(E1, Env, closure(X, Body, Env1_Old)),
    evil(E2, Env, Arg),
    evil(Body, [X-Arg|Env1_Old], Val).

evil([cons, E1, E2], Env, Val) :-
    evil(E1, Env, E1E),
    evil(E2, Env, E2E),
    Val = [E1E | E2E].

evil_list([], _, []).
evil_list([H|T], Env, [H2|T2]) :-
    evil(H, Env, H2), evil_list(T, Env, T2).

% evaluate in the empty environment

evil(Expr, Val) :-
    evil(Expr, [quote-unbound(quote)], Val).










%evil(X, [i, love, you]), print(X).




%https://stackoverflow.com/questions/65446636/pure-prolog-scheme-quine
