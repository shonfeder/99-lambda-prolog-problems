namespace util {

pred flip i:(A -> B -> prop), o:A, o:B.
flip P A B :- P B A.

pred repeat i:int, i:A, o:list A.
repeat 0 _ [].
repeat N X [X|Xs] :- N > 0
                  &  repeat {calc (N - 1)} X Xs
                  .

pred is-some o:option A.
is-some (some _).

pred succ o:int, o:int.
succ N N' :- not (var N), N' is N + 1, !.
succ N N' :- not (var N'), N is N' - 1, !.
succ N N' :- var N, var N', declare_constraint (succ N N') [N, N'].
}

namespace list {

% 1.01
pred last o:list A, o:option A.
last []    none.
last [H]   (some H) :- !.
last [_|T] H        :- last T H.

% 1.02
pred second-last o:list A, o:option A.
second-last []     none.
second-last [_]    none.
second-last [H, _] (some H) :- !.
second-last [_|T]  H        :- second-last T H.

% 1.03
pred nth i:list A, i:int, o:option A.
nth []     _ none.
nth [X|_ ] N (some X) :- N = 0, !.
nth [_|Xs] N X        :- N > 0
                       & nth Xs {calc (N - 1)} X.

% 1.04
pred len o:list A, o:int.
% `len Ls N` is true when `N` is the length of `Ls`.
pred len.aux o:list A, o:int.
% When `N` is bound, we count down from `N` to `0`, removing one element of
% `Ls` with each unit of `N` removed. If we arrive at `[]` and `0` at the
% same time, we are done, and cannot possibly have more conclusions (thus the cut).
len Ls N :-
        if (var N)
          ( ( len.aux Ls N
            & pi L M M'\
              len.aux L M :- M' is M + 1, len.aux [_|L] M'
             ) => len.aux [] 0 )
          ( ( len.aux [] 0
            & pi T M M'\ len.aux [_|T] M :- M' is M - 1, len.aux T M'
            ) => len.aux Ls N, ! ).

% When `N` is free, then we count up, starting from `0` to `N`, constructing
% a list by adding a free variable to our list each time a unit is added to
% `N`. When the list we're constructing can be unified with the input `Ls`
% then we're at our `N`. If `Ls` is left partial in the tail, then we can
% keep generating longer lists for `Ls` on backtracking.
% len Ls N :- var N,


% 1.05
pred rev o:list A, o:list A.
pred reverse o:list A, o:list B.
reverse L K :-
        ( rev [] Rev
        & pi X L K\ rev [X|L] K :- rev L [X|K] )
        => ( not (var L)
           & rev L []
           & K = Rev
           ; var L & not (var K)
           & rev K []
           & L = Rev
           ).

% 1.06
pred is-palindrome i:list A.
is-palindrome L :- reverse L L.

% 1.07.1
kind nlist type -> type.
type el A -> nlist A.
type ls (list (nlist A)) -> nlist A.

% 1.07.2
pred flatten i:nlist A, o:list A.
flatten (ls []) [].
flatten (el X) [X].
flatten (ls [H|LS]) Flat :- flatten H LS'
                         &  flatten (ls LS) LS''
                         &  std.append LS' LS'' Flat
                         .

% 1.08
pred compress i:list A, o:list A.
compress []       [].
compress [X]      [X].
compress [X,X|Xs] Rs     :- compress [X|Xs] Rs
                         .
compress [X,Y|Xs] [X|Rs] :- not (X = Y)
                         &  compress [Y|Xs] Rs
                         .

% 1.09
pred pack i:list A, o:list (list A).
pack [] [].
pack Xs Packed :- pack.aux Xs [] Packed.

pred pack.aux i:list A, i:list A, o:list (list A).
pack.aux []  Ls [Ls].
pack.aux [X] Ls [[X|Ls]].
pack.aux [X,X|Xs] Packing Packed :- pack.aux [X|Xs] [X|Packing] Packed.
pack.aux [X,Y|Xs] Packing Packed :- not (X = Y)
                                 &  Packed = [[X|Packing]|ToPack]
                                 &  pack.aux [Y|Xs] [] ToPack
                                 .

% 1.10
pred encode i:list A, o:list (pair int A).
encode Xs Encoded :- pack Xs Packed
                  &  std.map Packed encode.code Encoded
                  .

pred encode.code i:list A, o:pair int A.
encode.code ([X|_] as Ls) (pr N X) :- std.length Ls N.

% 1.11
kind encoded type -> type.
type one A -> encoded A.
type many int -> A -> encoded A.

pred encoded.of-pair o:pair int A, o:encoded A.
encoded.of-pair (pr 1 X) (one X).
encoded.of-pair (pr N X) (many N X) :- N > 1.

pred encode-compact i:list A, o:list (encoded A).
encode-compact Ls Encoded :- std.map {encode Ls} encoded.of-pair Encoded.

% 1.12
pred decode i:list (encoded A), o:list A.
decode []                [].
decode [one X|Enc]       [X|Dec] :- decode Enc Dec.
decode [many N X|Enc]    Dec     :- util.repeat N X Xs
                                 &  std.append Xs Dec' Dec
                                 &  decode Enc Dec'
                                 .

% 1.13
pred encode-direct i:list A, o:list (encoded A).
encode-direct Xs Encoded :- encode-direct.aux Xs 0 Encoded.

pred encode-direct.aux i:list A, i:int, o:list (encoded A).
encode-direct.aux [] _ [].
encode-direct.aux [X] Count [Enc] :- encode-direct.aux.enc X {calc (Count + 1)} Enc
                                  .
encode-direct.aux [X,X|Xs] Count Encoded :- encode-direct.aux [X|Xs] {calc (Count + 1)} Encoded
                                         .
encode-direct.aux [X,Y|Xs] Count Encoded :- not (X = Y)
                                         & Count' is Count + 1
                                         & encode-direct.aux.enc X Count' Enc
                                         & Encoded = [Enc | Encoding]
                                         & encode-direct.aux [Y|Xs] 0 Encoding
                                         .

pred encode-direct.aux.enc i:int, i:A, o:encoded A.
encode-direct.aux.enc A 1 (one A).
encode-direct.aux.enc A N (many N A) :- N > 1
                                     .
% 1.14
pred duplicate i:list A, o:list A.
duplicate [] [].
duplicate Xs Dups :- duplicate-n 2 Xs Dups.

% 1.15
pred repeat i:int, o:A, o:list A.
pred rep i:int, o:list A.
repeat N X Reps :-
       ( rep N Reps
       & pi M M' Xs\
         rep M Xs :- M' is M + 1, rep M' [X|Xs]
       ) => rep 0 []
       .

pred concat i:list (list A), i:list A.
concat Xs Concat :- std.fold Xs [] (a\b\c\ std.append b a c) Concat.

pred duplicate-n i:int, o:list A, o:list A.
pred dup i:int, o:list A.
duplicate-n N Xs Dups :- std.map Xs (repeat N) Dups' & concat Dups' Dups.

% 1.16
pred drop-nth i:int, i:list A, o:list A.
pred drop i:int, i:A, o:option A.
drop-nth N Xs Dropped :-
         ( pi M X Res\
           drop M X Res :- if (0 is (M + 1) mod N) (Res = none) (Res = some X)
         ) => std.map-i Xs drop Opt,
              std.map-filter Opt (a\b\some b = a) Dropped.

% 1.17
% `split N Ls Front Back` is true when Front is a prefix
% of Ls of length N, and Back is the remaining suffix of
% Ls. It is a fatal error if N is a negative number.
pred split i:int, i:list A, o:list A, o:list A.
% split N Ls Front Back :- print "split > " N Ls Front Back, fail.
split N _ _ _ :- N < 0, std.fatal-error "split with negative number".
split 0 Xs _ Xs.
split N [X|Xs] [X|Front] Back :- split {calc (N - 1)} Xs Front Back.

% 1.18
pred slice i:int, i:int, i:list A, o:list A.
% slice I J Xs Slice :- print "slice > " I J Xs Slice, fail.
slice I J _ _ :- J < I, std.fatal-error "slice with second index < first".
slice I J Xs Slice :- split I Xs _ Xs'
                   & M is (J - I)
                   & split M Xs' Slice _
                   .

% 1.19
pred rotate i:list A, i:int, o:list A.
rotate Ls N Ls' :- if (N > 0)
                    ( ( split N Ls Front Back
                      & std.append Back Front Ls' ) )
                    ( ( M is N + {len Ls}
                      & split M Ls Front Back
                      & std.append Back Front Ls' ) ).

% 1.20
pred select-nth i:int, i:list A, o:A, o:list A.
select-nth N Ls X Rest :- len Prefix {calc (N - 1)}
                       &  std.append Prefix [X|Suffix] Ls
                       &  std.append Prefix Suffix Rest
                       .

% 1.21
pred insert-at i:A, i:int, i:list A, o:list A.
insert-at X N Ls Ls' :- len Prefix {calc N}
                     &  std.append Prefix Suffix Ls
                     &  std.append Prefix [X|Suffix] Ls'
                     .

% 1.22
pred range i:int, i:int, o:List A.
range N N' _ :- N' < N, std.fatal-error "`range` with second index smaller than first".
range N N  [N].
range N N' [N|Ns] :- range {util.succ N} N' Ns.

% 1.23
% FIXME: Sometimes gets stuck at random.int. Report bug?
pred select-rnd i:int, i:list A, o:list A.
pred select-rnd.aux i:int, i:int, i:list A, o:list A.
select-rnd N Ls Xs :-
    random.self_init,
    ( select-rnd.aux N _ _ Xs
    & select-rnd.aux _ 0 _ Xs
    & pi M M' Len Len' Opts Acc X Rest Idx\
        select-rnd.aux M Len Opts Acc :-
            random.int Len Idx,
            select-nth Idx Opts X Rest,
            util.succ M M',
            util.succ Len' Len,
            select-rnd.aux M' Len' Rest [X|Acc]
    ) => select-rnd.aux 0 {len Ls} Ls []
    .

}


pred test i:prop.
test P :-  P & !.
test P :- Msg is "Test '" ^ {term_to_string P} ^ "' FAILED!"
       &  print Msg
       &  !
       &  fail
       .

shorten list.{ ls, el, one, many }.

pred tests.
tests :- test (list.last [1, 2, 3, 4] (some 4))
      & test (list.second-last [1,2,3,4] (some 3))
      & test (list.nth [1,2,3,4] 2 (some 3))
      & test (list.len [1,2,3,4] 4)
      & test (list.len L 4 & L = [_, _, _, _])
      & test (not (list.len [1,2,3,4,5] 4))
      & test (list.reverse [1,2,3,4] [4,3,2,1])
      & test (list.reverse X [4,3,2,1] & X = [1,2,3,4])
      & test (list.is-palindrome ["x","a","m","a","x"])
      & test (list.flatten (ls [el 1, ls [el 2, ls [el 3, el 4], el 5]]) [1,2,3,4,5])
      & test (list.compress [1,1,1,1,2,3,3,1,1,4,5,5,5,5] [1,2,3,1,4,5])
      & test (list.pack [1,1,1,1,2,3,3,1,1,4,5,5,5,5] [[1,1,1,1],[2],[3,3],[1,1],[4],[5,5,5,5]])
      & test (list.encode
                    ["a","a","a","a","b","c","c","a","a","d","e","e","e","e"]
                    [pr 4 "a", pr 1 "b", pr 2 "c", pr 2 "a", pr 1 "d", pr 4 "e"])
      & test (list.encode-compact
                    ["a","a","a","a","b","c","c","a","a","d","e","e","e","e"]
                    [many 4 "a", one "b", many 2 "c", many 2 "a", one "d", many 4 "e"])
      & test (list.decode
                    [many 4 "a", one "b", many 2 "c", many 2 "a", one "d", many 4 "e"]
                    ["a","a","a","a","b","c","c","a","a","d","e","e","e","e"])
      & test (list.encode-direct
                    ["a","a","a","a","b","c","c","a","a","d","e","e","e","e"]
                    [many 4 "a", one "b", many 2 "c", many 2 "a", one "d", many 4 "e"])
      & test (list.duplicate [1,2,3,4,5] [1,1,2,2,3,3,4,4,5,5])
      & test (list.repeat 4 "a" ["a", "a", "a", "a"])
      & test (list.concat [[1,2,3], [4,5,6], [7,8]] [1,2,3,4,5,6,7,8])
      & test (list.duplicate-n 3 [1,2,3] [1,1,1,2,2,2,3,3,3])
      & test (list.drop-nth 3 [1,2,3,4,5,6,7,8] [1,2,4,5,7,8])
      & test (list.split 3 [1,2,3,4,5,6,7,8,9,10] [1,2,3] [4,5,6,7,8,9,10])
      & test (list.slice 4 8 [1,2,3,4,5,6,7,8,9,10] [5,6,7,8,9])
      & test (list.rotate [1,2,3,4,5,6,7,8] 3 [4,5,6,7,8,1,2,3])
      & test (list.rotate [1,2,3,4,5,6,7,8] -2 [7,8,1,2,3,4,5,6])
      & test (list.select-nth 2 [1,2,3,4] 2 [1,3,4])
      & test (list.insert-at 10 2 [1,2,3,4] [1,2,10,3,4])
      & test (list.range 4 9 [4,5,6,7,8,9])
      % FIXME
      % & test (list.select-rnd 3 [1,2,3,4,5,6,7,8] [_, _, _])
      .

pred main.
main :- tests & print "ALL TESTS PASSED".
