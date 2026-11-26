/*  test_ocaso.pl testes do Ocaso com plunit

    Pra rodar  swipl -g run_tests -t halt backend/prolog/test_ocaso.pl
    ou make test-prolog na raiz do projeto

    Opções do test/2 que a gente usa
      true(Cond)  passa se Cond for verdade depois do teste
      fail        passa se o teste falhar
      all(...)    compara com todas as respostas
*/

:- use_module(ocaso).
:- use_module(library(plunit)).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).
:- use_module(library(yall)).
:- use_module(library(clpfd)).

example_solution([[2,0,0,3,0],
                  [2,0,0,0,0],
                  [0,0,0,0,1],
                  [0,0,0,0,2],
                  [3,0,0,0,0]]).

% Auxiliares usados em vários blocos
% Ficam aqui fora porque cada begin_tests/end_tests vira um módulo separado
at(Grid, L, C, V) :-
    nth0(L, Grid, Row),
    nth0(C, Row, V).

lake(puzzle(_, _, _, _, Lakes, _), Position) :-
    memberchk(Position, Lakes).



/* ---- Geometria da sombra ---------------------------------------------- */

:- begin_tests(sombra).

test(sol_a_oeste, S == [0,1,1,0,1]) :-
    row_shadows(west, [2,0,0,1,0], S).

test(sol_a_leste, S == [1,1,0,0,0]) :-
    row_shadows(east, [0,0,2,0,0], S).

% Esse é por causa de um bug  com a sombra livre o reverse entrava em
% loop no backtracking  agora tem que dar uma resposta só e parar
test(sol_a_leste_termina, all(S == [[1,1,0,0,0]])) :-
    row_shadows(east, [0,0,2,0,0], S).

test(sombra_cortada_na_borda, S == [0,0,0,0,0]) :-
    row_shadows(west, [0,0,0,0,3], S).

% Testando ao contrário  só a casa 3 tem sombra então quais alturas servem
% Quem faz sombra na casa 3 só pode ser a torre da casa 2 com altura 1
% A torre da casa 4 pode ter qualquer altura porque a sombra dela sai do
% tabuleiro
test(sombra_determina_torres,
     all(Hs == [[0,0,1,0,0], [0,0,1,0,1], [0,0,1,0,2], [0,0,1,0,3]])) :-
    length(Hs, 5),
    Hs ins 0..3,
    row_shadows(west, Hs, [0,0,0,1,0]),
    label(Hs).

:- end_tests(sombra).


/* ---- Resolvedor -------------------------------------------------------- */

:- begin_tests(resolver).

test(resolve_exemplo, T == S) :-
    example_puzzle(P),
    example_solution(S),
    solve(P, T).

test(exemplo_tem_solucao_unica, N == 1) :-
    example_puzzle(P),
    count_solutions(P, 5, N).

test(sem_as_reveladas_ha_varias_solucoes, true(N > 1)) :-
    example_puzzle(puzzle(Size, Suns, Rows, Cols, Lakes, _)),
    count_solutions(puzzle(Size, Suns, Rows, Cols, Lakes, []), 5, N).

test(pista_impossivel, fail) :-
    example_puzzle(puzzle(N, Suns, [_ | Rows], Cols, Lakes, Givens)),
    solve(puzzle(N, Suns, [5 | Rows], Cols, Lakes, Givens), _).

test(revelada_contraditoria, fail) :-
    example_puzzle(puzzle(N, Suns, Rows, Cols, Lakes, Givens)),
    solve(puzzle(N, Suns, Rows, Cols, Lakes, [cell(0, 0, 1) | Givens]), _).

:- end_tests(resolver).


/* ---- Gerador ----------------------------------------------------------- */

:- begin_tests(gerador).

% Pra cada nível o puzzle gerado tem que ter o tamanho certo solução
% única e pistas que batem com a solução
test(niveis) :-
    forall(member(Level-Size, [easy-5, medium-6, hard-7]),
           ( generate(Level, P),
             P = puzzle(Size, _, _, _, _, _),
             consistent(P) )).

test(varios_puzzles_dificeis) :-
    forall(between(1, 5, _),
           ( generate(hard, P), consistent(P) )).

test(nivel_desconhecido, error(type_error(_, impossible))) :-
    generate(impossible, _).

% Confere tudo  pistas de linha e coluna lagos na sombra e sem torre
% nenhuma torre na sombra reveladas certas e solução única
consistent(P) :-
    P = puzzle(_, Suns, Rows, Cols, Lakes, Givens),
    count_solutions(P, 2, 1),
    solve(P, T),
    maplist(row_shadows, Suns, T, Shade),
    maplist(sum_list, Shade, Rows),
    transpose(T, Columns),
    maplist(sum_list, Columns, Cols),
    forall(member(L-C, Lakes), ( at(Shade, L, C, 1), at(T, L, C, 0) )),
    forall(( at(T, L, C, H), H > 0 ), at(Shade, L, C, 0)),
    forall(member(cell(L, C, H), Givens), at(T, L, C, H)).

:- end_tests(gerador).


/* ---- Dicas ------------------------------------------------------------- */

:- begin_tests(dicas).

test(dica_bate_com_a_solucao) :-
    example_puzzle(P),
    example_solution(S),
    hint(P, [], cell(L, C, H, _How, Excluded)),
    at(S, L, C, H),
    pairs_keys(Excluded, Others),
    msort(Others, Sorted),
    subtract([0,1,2,3], [H], Sorted).

% Linha 3 com sol a leste  a torre de altura 2 já faz as duas casas de
% sombra que a pista pede  uma torre em (3,1) faria sombra a mais então o
% motivo é só a regra da linha 3
% why_not/5 não é exportado por isso chamamos com ocaso: na frente
test(motivo_da_linha, Reason == [row(3)]) :-
    example_puzzle(P),
    ocaso:why_not(P, [], 3-1, 1, Reason).

% A coluna 0 soma 7 e já tem 2 em (1,0) e 3 em (4,0)
% Se (0,0) ficasse vazia só olhando a coluna ainda dava pra fechar com uma
% torre 2 em (2,0) então a coluna sozinha não explica e precisa de outra regra
test(motivo_composto, true(Reason \== [col(0)])) :-
    example_puzzle(P),
    ocaso:why_not(P, [cell(1, 0, 2)], 0-0, 0, Reason).

test(casa_errada_e_apontada, Hint = wrong(0, 0, 1, _)) :-
    example_puzzle(P),
    hint(P, [cell(4, 4, 0), cell(0, 0, 1)], Hint).

% A torre 2 em (1,0) faz sombra em (1,1) e (1,2)
% Torre em (1,1) ficaria na sombra então só a regra do sol já basta
test(motivo_do_sol, Hint = wrong(1, 1, 1, [sun])) :-
    example_puzzle(P),
    hint(P, [cell(1, 0, 2), cell(1, 1, 1)], Hint).

test(tabuleiro_completo, Hint == complete) :-
    example_puzzle(P),
    example_solution(S),
    findall(cell(L, C, H),
            ( at(S, L, C, H), \+ lake(P, L-C) ),
            Placed),
    hint(P, Placed, Hint).

test(dica_nunca_aponta_casa_decidida) :-
    example_puzzle(P),
    Placed = [cell(0, 0, 2), cell(1, 0, 2), cell(4, 4, 0)],
    hint(P, Placed, cell(L, C, _, _, _)),
    \+ memberchk(cell(L, C, _), Placed),
    \+ lake(P, L-C).

:- end_tests(dicas).


/* ---- Fronteira com o Python -------------------------------------------- */

:- begin_tests(api).

test(dict_ida_e_volta) :-
    api_generate("medium", Dict),
    get_dict(size, Dict, 6),
    api_solve(Dict, Towers),
    length(Towers, 6).

test(dica_como_dict, Kind == wrong) :-
    example_puzzle(puzzle(N, _Suns, Rows, Cols, Lakes, Givens)),
    maplist([L-C, [L, C]] >> true, Lakes, LakeLists),
    maplist([cell(L, C, H), [L, C, H]] >> true, Givens, GivenLists),
    Dict = _{size: N, suns: ["west", "west", "east", "east", "west"],
             rows: Rows, cols: Cols, lakes: LakeLists, givens: GivenLists},
    api_hint(Dict, [[0, 0, 1]], Hint),
    get_dict(kind, Hint, Kind).

:- end_tests(api).
