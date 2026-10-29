s=Path('/tmp/dp-ls-controls.py').read_text()
exec(s[:s.index('\nrows=[]')])
controls['three-copy-fixed-tag']='''example :
    (BlockedDisjBoth.block (.bot : NormalForm Empty) .top [.disj .bot .top] [] [] []).route.get
      (.here (.disj .bot .top) [.disj .bot .top,.disj .bot .top,.disj .bot .top]) =
        (BlockedDisjBoth.block .bot .top [.disj .bot .top] [] [] []).keep := by rfl
'''
controls['three-copy-original-tags']='''example (C : NormalForm Empty) :
    (selectedCopies C [[C],[C,C],[C]] []).map At.index = [1,1,6] := by rfl
'''
controls['missing-third-copy-repair']='''example {P : Type} (C : NormalForm P) (Y F H D E I R : List (NormalForm P))
    (p : Route Y F) (q : Route Y H)
    (l : G P (((F++I)++(H++I))++I) (((D++R)++(E++R))++R)) :
    G P (Y++I) ((D++E)++R) := l
'''
exec(s[s.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==30'))
