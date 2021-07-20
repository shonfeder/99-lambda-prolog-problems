namespace list {

pred last o:list A, o:option A.
last []    none.
last [H]   (some H) :- !.
last [_|T] H        :- last T H.

pred second-last o:list A, o:option A.
second-last []     none.
second-last [_]    none.
second-last [H, _] (some H) :- !.
second-last [_|T]  H        :- second-last T H.

pred nth i:list A, i:int, o:option A.
nth []     _ none.
nth [X|_ ] N (some X) :- N = 0, !.
nth [_|Xs] N X        :- N > 0
                       & nth Xs {calc (N - 1)} X.


pred len o:list A, o: Int.
len []    0.
len [_|T] N :- N is {len T} + 1.

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

pred is-palindrome i:list A.
is-palindrome L :- reverse L L.
}

pred test i:prop.
test P :- ( P
          & !
          )
        ; ( Msg is "Test '" ^ {term_to_string P} ^ "' FAILED!"
          & print Msg
          & !
          & false
          )
          .

pred main.
main :- test (list.last [1, 2, 3, 4] (some 4))
      & test (list.second-last [1,2,3,4] (some 3))
      & test (list.nth [1,2,3,4] 2 (some 3))
      & test (list.len [1,2,3,4] 4)
      & test (list.len L 4 & L = [_, _, _, _])
      & test (list.reverse [1,2,3,4] [4,3,2,1])
      & test (list.reverse X [4,3,2,1] & X = [1,2,3,4])
      & test (list.is-palindrome ["x","a","m","a","x"])
      & print "ALL TESTS PASSED"
      .
