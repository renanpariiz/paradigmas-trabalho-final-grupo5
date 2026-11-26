/*  ocaso.pl regras resolvedor gerador e dicas do Ocaso

    O jogo é um tabuleiro N x N e cada casa é lago ou terreno
    Terreno pode ficar vazio ou ter torre de altura 1 2 ou 3
    Em cada linha o sol vem do oeste ou do leste e uma torre de altura H
    faz sombra nas H casas seguintes pro lado contrário do sol
    A sombra para na borda

    Regras
      1 sol  torre não pode ficar na sombra de outra
      2 lagos  todo lago tem que estar na sombra e lago não tem torre
      3 linhas  a pista da linha é quantas casas dela estão na sombra
        contando os lagos
      4 colunas  a pista da coluna é a soma das alturas das torres dela

    Algumas casas já vêm reveladas pra só ter uma solução

    Como o puzzle fica guardado aqui dentro
        puzzle(Tamanho, Sois, PistasLinhas, PistasColunas, Lagos, Reveladas)
    Sois = [west, east, ...] um por linha
    Lagos = [L-C, ...]
    Reveladas = [cell(L, C, Altura), ...]  altura 0 é sem torre
    Linha e coluna começam do 0 e a solução é uma lista de linhas com a
    altura de cada casa de 0 a 3

    Tudo foi feito com restrição do CLP(FD)
    Cada casa tem uma variável de altura 0..3 e uma de sombra 0 ou 1 e as
    regras viram somas e implicações entre elas
    Com esse mesmo modelo dá pra resolver com labeling contar soluções
    parando na segunda gerar só com a parte da sombra e valores sorteados
    e explicar as dicas ligando uma regra por vez pra ver qual já proíbe
    o valor

    Pra testar no terminal
        $ swipl backend/prolog/ocaso.pl
        ?- example_puzzle(P), print_puzzle(P).
        ?- example_puzzle(P), solve(P, T), print_solution(P, T).
        ?- generate(hard, P), print_puzzle(P).
        ?- example_puzzle(P), hint(P, [], Dica).
*/

:- module(ocaso,
          [ solve/2,            % +Puzzle, -Towers
            count_solutions/3,  % +Puzzle, +Limit, -Count
            generate/2,         % +Difficulty, -Puzzle
            hint/3,             % +Puzzle, +Placed, -Hint
            row_shadows/3,      % ?Sun, ?Heights, ?Shade
            example_puzzle/1,   % -Puzzle
            print_puzzle/1,     % +Puzzle
            print_solution/2,   % +Puzzle, +Towers
            api_generate/2,     % +DifficultyName, -PuzzleDict
            api_solve/2,        % +PuzzleDict, -Towers
            api_hint/3          % +PuzzleDict, +Placed, -HintDict
          ]).

% + é entrada - é saída ? pode ser os dois

:- use_module(library(clpfd)).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(yall)).    % lambdas: [X] >> objetivo

% Obs no yall uma variável que aparece só no corpo do lambda vira local
% Isso deu bug aqui com linhas vazias e o programa travando então onde o
% lambda precisava de variável de fora trocamos por predicado auxiliar
:- use_module(library(pairs)).
:- use_module(library(random)).
:- use_module(library(solution_sequences)).


%% ---- 1 Sombra ------------------------------------------------------

% row_shadows(Sol, Alturas, Sombra)
% Liga as alturas de uma linha com as casas que ficam na sombra
% Funciona pros dois lados com as alturas ele calcula a sombra e com a
% sombra ele limita as alturas possíveis
%   ?- row_shadows(west, [2,0,0,1,0], S).    dá S = [0,1,1,0,1]
% Sol a leste é a mesma coisa com a linha invertida então a gente
% reaproveita o caso do oeste
row_shadows(west, Heights, Shade) :-
    cast(Heights, [], Shade).
row_shadows(east, Heights, Shade) :-
    % Sem o same_length o reverse entrava em loop no backtracking porque
    % Shade ainda não tinha tamanho
    same_length(Heights, Shade),
    reverse(Heights, ReversedHeights),
    reverse(Shade, ReversedShade),
    cast(ReversedHeights, [], ReversedShade).

% cast anda pela linha no sentido da sombra
% Behind guarda as alturas das 3 casas de antes com a mais perto primeiro
% Mais longe que isso nenhuma torre alcança já que a altura máxima é 3
cast([], _Behind, []).
cast([H | Hs], Behind, [S | Ss]) :-
    S in 0..1,
    reaches(Behind, 1, Reach),
    % S é 1 se e somente se Reach for verdade
    % Como é restrição e não conta funciona nos dois sentidos
    S #<==> Reach,
    nearest_three([H | Behind], Behind1),
    cast(Hs, Behind1, Ss).

% reaches monta torre a 1 casa tem altura >= 1 ou torre a 2 casas tem
% altura >= 2 ou etc
% Sem nada atrás vira 0 que é falso por isso a primeira casa da linha
% nunca fica na sombra
reaches([], _Distance, 0).
reaches([H | Hs], Distance, (H #>= Distance) #\/ Rest) :-
    Next is Distance + 1,
    reaches(Hs, Next, Rest).

nearest_three(List, Prefix) :-
    length(List, Length),
    (   Length > 3
    ->  length(Prefix, 3),
        append(Prefix, _, List)
    ;   Prefix = List
    ).


%% ---- 2 Modelo e regras ----------------------------------------------

% board_model(Puzzle, Conhecidas, Regras, Torres, Sombra)
% Cria as variáveis e coloca a sombra os lagos sem torre as casas que já
% sabemos e só as regras que estão em Regras
% Dá pra escolher as regras e a gente usa isso nas dicas
% Falha se já der contradição
board_model(puzzle(N, Suns, RowClues, ColClues, Lakes, Givens),
            Known, Rules, Towers, Shade) :-
    square(N, Towers),
    square(N, Shade),
    append(Towers, Heights),
    Heights ins 0..3,
    maplist(row_shadows, Suns, Towers, Shade),
    maplist(lake_has_no_tower(Towers), Lakes),
    append(Givens, Known, Fixed),
    maplist(fix_cell(Towers), Fixed),
    Board = board(Towers, Shade, RowClues, ColClues, Lakes),
    maplist(rule(Board), Rules).

all_rules([sun, lakes, rows, cols]).

% square(N, Linhas) faz uma matriz N x N de variáveis novas
square(N, Rows) :-
    length(Rows, N),
    maplist(length_of(N), Rows).

length_of(N, List) :-
    length(List, N).

lake_has_no_tower(Towers, L-C) :-
    cell_at(Towers, L, C, 0).

fix_cell(Towers, cell(L, C, Height)) :-
    cell_at(Towers, L, C, Var),
    Var #= Height.

cell_at(Grid, L, C, Value) :-
    nth0(L, Grid, Row),
    nth0(C, Row, Value).

% Uma cláusula pra cada regra
rule(board(Towers, Shade, _, _, _), sun) :-
    append(Towers, Heights),
    append(Shade, Shadows),
    maplist(in_sun, Heights, Shadows).
rule(board(_, Shade, _, _, Lakes), lakes) :-
    maplist(lake_in_shade(Shade), Lakes).
rule(board(_, Shade, RowClues, _, _), rows) :-
    maplist(sum_is, Shade, RowClues).
rule(board(Towers, _, _, ColClues, _), cols) :-
    transpose(Towers, Columns),
    maplist(sum_is, Columns, ColClues).
rule(board(_, Shade, RowClues, _, _), row(L)) :-
    nth0(L, Shade, Row),
    nth0(L, RowClues, Clue),
    sum_is(Row, Clue).
rule(board(Towers, _, _, ColClues, _), col(C)) :-
    transpose(Towers, Columns),
    nth0(C, Columns, Column),
    nth0(C, ColClues, Clue),
    sum_is(Column, Clue).

% Regra do sol se a casa tá na sombra a altura é 0
in_sun(Height, Shadow) :-
    Shadow #==> Height #= 0.

lake_in_shade(Shade, L-C) :-
    cell_at(Shade, L, C, 1).

sum_is(Vars, Total) :-
    sum(Vars, #=, Total).


%% ---- 3 Resolver -----------------------------------------------------

% solve pega a primeira solução e falha se não tiver nenhuma
solve(Puzzle, Towers) :-
    solution(Puzzle, [], Towers),
    !.

% solution devolve todas as soluções uma por backtracking
solution(Puzzle, Known, Towers) :-
    all_rules(Rules),
    board_model(Puzzle, Known, Rules, Towers, _Shade),
    append(Towers, Heights),
    labeling([ff], Heights).

% Conta as soluções até Limit
% Pra saber se é única basta Limit = 2 não precisa achar todas
count_solutions(Puzzle, Limit, Count) :-
    aggregate_all(count, limit(Limit, solution(Puzzle, [], _)), Count).

unique(Puzzle) :-
    count_solutions(Puzzle, 2, 1).


%% ---- 4 Gerador ------------------------------------------------------
%
% Passo a passo
%  - Sorteia o sol de cada linha e as torres só com a regra do sol
%    usando o mesmo modelo com labeling em ordem aleatória
%  - Escolhe uns lagos entre as casas que ficaram na sombra
%  - Calcula as pistas a partir dessa solução
%  - Enquanto tiver mais de uma solução revela uma casa onde duas
%    soluções são diferentes e depois tenta esconder de novo cada revelada
%  - No fácil e no médio revela mais algumas casas

% Nível tamanho do tabuleiro e casas extras reveladas
level(easy,   5, 3).
level(medium, 6, 1).
level(hard,   7, 0).

% generate(Nivel, Puzzle)
generate(Difficulty, Puzzle) :-
    must_be(oneof([easy, medium, hard]), Difficulty),
    level(Difficulty, N, Extra),
    repeat,
    random_layout(N, Suns, Towers, Shade),
    random_lakes(N, Shade, Lakes),
    !,
    maplist(sum_list, Shade, RowClues),
    transpose(Towers, Columns),
    maplist(sum_list, Columns, ColClues),
    Bare = puzzle(N, Suns, RowClues, ColClues, Lakes, []),
    make_unique(Bare, Towers, Unique),
    minimize_givens(Unique, Minimal),
    add_givens(Extra, Towers, Minimal, Puzzle).

% Torres aleatórias sem nenhuma na sombra
% Também exige pelo menos uma torre por linha mas isso é só pra não sair
% linha vazia não é regra do jogo
random_layout(N, Suns, Towers, Shade) :-
    length(Suns, N),
    maplist(random_member_of([west, east]), Suns),
    board_model(puzzle(N, Suns, _, _, [], []), [], [sun], Towers, Shade),
    maplist(has_tower, Towers),
    append(Towers, Heights),
    random_labeling(Heights),
    !.

random_member_of(Options, X) :-
    random_member(X, Options).

has_tower(Row) :-
    maplist(is_tower, Row, IsTower),
    sum(IsTower, #>=, 1).

is_tower(Height, Flag) :-
    Flag #<==> Height #> 0.

% Parecido com label/1 mas sorteando a ordem dos valores e com mais
% chance de tentar o 0 primeiro senão o tabuleiro enche de torre
random_labeling([]).
random_labeling([Var | Vars]) :-
    random_value_order(Order),
    member(Var, Order),
    random_labeling(Vars).

random_value_order(Order) :-
    random_permutation([1, 2, 3], Towers),
    (   random(X), X < 0.6
    ->  Order = [0 | Towers]
    ;   append(Towers, [0], Order)
    ).

% Cada casa na sombra tem 45% de chance de virar lago
% Se sair menos de N/2 lagos falha e o repeat do generate tenta outro
random_lakes(N, Shade, Lakes) :-
    findall(L-C,
            ( cell_at(Shade, L, C, 1),
              random(X), X < 0.45 ),
            Lakes),
    length(Lakes, Count),
    Count >= N // 2.

% Vai revelando casas até sobrar uma solução só
make_unique(Puzzle0, Towers, Puzzle) :-
    findall(T, limit(2, solution(Puzzle0, [], T)), Solutions),
    (   Solutions = [_]
    ->  Puzzle = Puzzle0
    ;   Solutions = [T1, T2],
        findall(L-C,
                ( cell_at(T1, L, C, V1),
                  cell_at(T2, L, C, V2),
                  V1 =\= V2 ),
                Disagreements),
        random_member(L-C, Disagreements),
        reveal(L-C, Towers, Puzzle0, Puzzle1),
        make_unique(Puzzle1, Towers, Puzzle)
    ).

reveal(L-C, Towers, puzzle(N, S, R, K, Lakes, Givens),
       puzzle(N, S, R, K, Lakes, [cell(L, C, H) | Givens])) :-
    cell_at(Towers, L, C, H).

% Tenta esconder cada casa revelada em ordem aleatória
% Se continuar com uma solução só ela fica escondida
minimize_givens(puzzle(N, S, R, K, Lakes, Givens), Puzzle) :-
    random_permutation(Givens, Order),
    foldl(try_hide, Order, puzzle(N, S, R, K, Lakes, Givens), Puzzle).

try_hide(Given, puzzle(N, S, R, K, Lakes, Givens), Puzzle) :-
    selectchk(Given, Givens, Fewer),
    Candidate = puzzle(N, S, R, K, Lakes, Fewer),
    (   unique(Candidate)
    ->  Puzzle = Candidate
    ;   Puzzle = puzzle(N, S, R, K, Lakes, Givens)
    ).

% Revela mais Count casas que não sejam lago nem já estejam reveladas
add_givens(Count, Towers, puzzle(N, S, R, K, Lakes, Givens), Puzzle) :-
    findall(L-C,
            ( cell_at(Towers, L, C, _),
              \+ memberchk(L-C, Lakes),
              \+ memberchk(cell(L, C, _), Givens) ),
            Hidden),
    random_permutation(Hidden, Shuffled),
    length(Shuffled, Available),
    Take is min(Count, Available),
    length(Chosen, Take),
    append(Chosen, _, Shuffled),
    foldl(reveal_in(Towers), Chosen, puzzle(N, S, R, K, Lakes, Givens), Puzzle).

reveal_in(Towers, Position, Puzzle0, Puzzle) :-
    reveal(Position, Towers, Puzzle0, Puzzle).


%% ---- 5 Dicas --------------------------------------------------------
%
% Placed são as casas que o jogador já preencheu no formato cell(L, C, Altura)
% A dica pode ser
%   wrong(L, C, Altura, Motivo)          uma casa do jogador tá errada
%   cell(L, C, Altura, Como, Excluidos)  a próxima casa pra preencher
%       Como é propagation quando as regras já decidem a casa direto
%       ou search quando precisa testar
%       Excluidos = [Valor-Motivo, ...] fala por que cada outro valor não
%       serve
%   complete                             não falta nenhuma casa
%
% Motivo é a menor lista de regras que já impede o valor
% Primeiro tenta uma regra só tipo [row(2)] depois pares tipo
% [lakes, col(3)] e se nada disso basta vem [] que quer dizer que precisa
% de todas juntas
% As regras testadas são sun lakes e a linha e a coluna da casa

% hint(Puzzle, Placed, Dica)
hint(Puzzle, Placed, Hint) :-
    solve(Puzzle, Solution),
    partition(agrees_with(Solution), Placed, Correct, Wrong),
    (   Wrong = [cell(L, C, Height) | _]
    ->  why_not(Puzzle, Correct, L-C, Height, Reason),
        Hint = wrong(L, C, Height, Reason)
    ;   undecided(Puzzle, Placed, Open),
        (   Open == []
        ->  Hint = complete
        ;   easiest_cell(Puzzle, Correct, Open, L-C, How),
            cell_at(Solution, L, C, Height),
            exclusions(Puzzle, Correct, L-C, Height, Excluded),
            Hint = cell(L, C, Height, How, Excluded)
        )
    ).

agrees_with(Solution, cell(L, C, Height)) :-
    cell_at(Solution, L, C, Height).

% Casas que ainda faltam nem lago nem revelada nem preenchida
undecided(puzzle(N, _, _, _, Lakes, Givens), Placed, Open) :-
    Last is N - 1,
    findall(L-C,
            ( between(0, Last, L),
              between(0, Last, C),
              \+ memberchk(L-C, Lakes),
              \+ memberchk(cell(L, C, _), Givens),
              \+ memberchk(cell(L, C, _), Placed) ),
            Open).

% Aplica as regras sem labeling e pega a casa que ficou com menos valores
% possíveis
% Se sobrou um valor só dá pra deduzir direto e empate vai no sorteio
easiest_cell(Puzzle, Known, Open, Position, How) :-
    all_rules(Rules),
    board_model(Puzzle, Known, Rules, Towers, _Shade),
    random_permutation(Open, Shuffled),
    map_list_to_pairs(domain_size(Towers), Shuffled, Pairs),
    keysort(Pairs, [Size-Position | _]),
    (   Size =:= 1
    ->  How = propagation
    ;   How = search
    ).

domain_size(Towers, L-C, Size) :-
    cell_at(Towers, L, C, Var),
    fd_size(Var, Size).

% Pra cada valor diferente do certo o motivo dele não servir
exclusions(Puzzle, Known, Position, Height, Excluded) :-
    findall(Other-Reason,
            ( between(0, 3, Other),
              Other =\= Height,
              why_not(Puzzle, Known, Position, Other, Reason) ),
            Excluded).

% why_not procura o menor grupo de regras uma e depois duas que deixa o
% tabuleiro sem solução com esse valor na casa
% O rule_subset gera os grupos no backtracking e o primeiro que funciona
% é a resposta
why_not(Puzzle, Known, L-C, Height, Reason) :-
    Candidates = [sun, lakes, row(L), col(C)],
    (   between(1, 2, Size),
        rule_subset(Size, Candidates, Rules),
        \+ satisfiable(Puzzle, [cell(L, C, Height) | Known], Rules)
    ->  Reason = Rules
    ;   Reason = []
    ).

% Subconjuntos de List com Size elementos na ordem da lista
rule_subset(0, _, []) :- !.
rule_subset(Size, [X | Xs], [X | Subset]) :-
    Rest is Size - 1,
    rule_subset(Rest, Xs, Subset).
rule_subset(Size, [_ | Xs], Subset) :-
    Size > 0,
    rule_subset(Size, Xs, Subset).

satisfiable(Puzzle, Known, Rules) :-
    board_model(Puzzle, Known, Rules, Towers, _Shade),
    append(Towers, Heights),
    once(labeling([ff], Heights)).


%% ---- 6 Ponte com o Python ------------------------------------------
%
% O Janus converte dict do Python em dict do Prolog mas não converte termo
% composto tipo cell(1, 2, 3) então esses predicados fazem a tradução
% São só esses que o Python chama

% api_generate(NomeDoNivel, Dict)
api_generate(Name, Dict) :-
    atom_string(Difficulty, Name),
    generate(Difficulty, Puzzle),
    puzzle_dict(Puzzle, Dict).

% api_solve(Dict, Torres)
api_solve(Dict, Towers) :-
    puzzle_dict(Puzzle, Dict),
    solve(Puzzle, Towers).

% Placed chega como [[Linha, Coluna, Altura], ...]
% Se o puzzle não tiver solução só se alguém mexer nele volta
% _{kind: unsolvable}
api_hint(Dict, PlacedLists, HintDict) :-
    puzzle_dict(Puzzle, Dict),
    maplist([[L, C, H], cell(L, C, H)] >> true, PlacedLists, Placed),
    (   hint(Puzzle, Placed, Hint)
    ->  hint_dict(Hint, HintDict)
    ;   HintDict = _{kind: unsolvable}
    ).

% Funciona nos dois sentidos
% O sol sai como átomo e pode voltar como átomo ou string e o atom_string
% aceita os dois
puzzle_dict(puzzle(N, Suns, Rows, Cols, Lakes, Givens),
            _{size: N, suns: SunNames, rows: Rows, cols: Cols,
              lakes: LakeLists, givens: GivenLists}) :-
    maplist(sun_name, Suns, SunNames),
    maplist([L-C, [L, C]] >> true, Lakes, LakeLists),
    maplist([cell(L, C, H), [L, C, H]] >> true, Givens, GivenLists).

sun_name(Sun, Name) :-
    (   var(Sun)
    ->  atom_string(Sun, Name),
        must_be(oneof([west, east]), Sun)
    ;   Name = Sun
    ).

hint_dict(complete, _{kind: complete}).
hint_dict(wrong(L, C, H, Reason),
          _{kind: wrong, row: L, col: C, value: H, rules: RuleDicts}) :-
    maplist(rule_dict, Reason, RuleDicts).
hint_dict(cell(L, C, H, How, Excluded),
          _{kind: cell, row: L, col: C, value: H, method: How,
            excluded: ExcludedDicts}) :-
    maplist(excluded_dict, Excluded, ExcludedDicts).

excluded_dict(Value-Reason, _{value: Value, rules: RuleDicts}) :-
    maplist(rule_dict, Reason, RuleDicts).

rule_dict(row(L), _{rule: row, index: L}) :- !.
rule_dict(col(C), _{rule: col, index: C}) :- !.
rule_dict(Rule, _{rule: Rule}).


%% ---- 7 Terminal ----------------------------------------------------

% Puzzle 5x5 dos testes com solução única
% [[2,0,0,3,0], [2,0,0,0,0], [0,0,0,0,1], [0,0,0,0,2], [3,0,0,0,0]]
example_puzzle(puzzle(5,
                      [west, west, east, east, west],
                      [3, 2, 1, 2, 3],
                      [7, 0, 0, 3, 3],
                      [0-1, 3-2, 3-3, 4-3],
                      [cell(3, 0, 0), cell(4, 0, 3), cell(3, 4, 2),
                       cell(2, 4, 1), cell(1, 3, 0)])).

% Desenha o puzzle  ~ é lago  . é casa em aberto e número é revelada
% O * mostra de que lado vem o sol e a pista fica do outro lado
print_puzzle(Puzzle) :-
    Puzzle = puzzle(N, _, _, _, Lakes, Givens),
    square(N, Grid),
    fill_grid(Grid, Lakes, Givens),
    print_grid(Puzzle, Grid).

% Desenha a solução com as alturas  ~ nos lagos  # no terreno na sombra
% e . no terreno no sol
print_solution(Puzzle, Towers) :-
    Puzzle = puzzle(_, Suns, _, _, Lakes, _),
    maplist(row_shadows, Suns, Towers, Shade),
    maplist(maplist(solution_symbol), Towers, Shade, Symbols0),
    foldl(mark_lake, Lakes, Symbols0, Symbols),
    print_grid(Puzzle, Symbols).

mark_lake(Position, Grid0, Grid) :-
    replace_cell(Position, '~', Grid0, Grid).

solution_symbol(0, 1, '#') :- !.
solution_symbol(0, 0, '.') :- !.
solution_symbol(H, _, H).

% Usamos maplist e não forall porque o forall desfaz as ligações e aqui a gente
% quer justamente ligar as casas
fill_grid(Grid, Lakes, Givens) :-
    maplist(put_lake(Grid), Lakes),
    maplist(put_given(Grid), Givens),
    maplist(maplist(unknown_dot), Grid).

put_lake(Grid, L-C) :- cell_at(Grid, L, C, '~').
put_given(Grid, cell(L, C, H)) :- cell_at(Grid, L, C, H).
unknown_dot(X) :- ( var(X) -> X = '.' ; true ).

replace_cell(L-C, Symbol, Grid0, Grid) :-
    nth0(L, Grid0, Row0, OtherRows),
    nth0(C, Row0, _, OtherCells),
    nth0(C, Row, Symbol, OtherCells),
    nth0(L, Grid, Row, OtherRows).

print_grid(puzzle(_, Suns, RowClues, ColClues, _, _), Grid) :-
    format("    "), forall(member(K, ColClues), format(" ~w", [K])), nl,
    forall(nth0(L, Grid, Row),
           ( nth0(L, Suns, Sun),
             nth0(L, RowClues, Clue),
             print_row(Sun, Clue, Row) )).

print_row(west, Clue, Row) :-
    format(" * |"), forall(member(X, Row), format(" ~w", [X])), format(" | ~w~n", [Clue]).
print_row(east, Clue, Row) :-
    format(" ~w |", [Clue]), forall(member(X, Row), format(" ~w", [X])), format(" | *~n").
