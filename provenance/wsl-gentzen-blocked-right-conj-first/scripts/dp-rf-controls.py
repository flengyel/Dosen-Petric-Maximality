rf_controls_source=Path('/tmp/dp-ls-controls.py').read_text()
# Reuse the corrected complete thirty-control definition prefix.
rf_both_source=Path('/tmp/dp-lb-controls.py').read_text()
exec(rf_both_source[:rf_both_source.index('\nexec(lb_controls_source[lb_controls_source.index(')])
controls['right-first-fixed-tail']='''example :
    (BlockedConjFirst.block (.bot : NormalForm Empty) .top [] [] [.conj .bot .top]).route.get
      (.there (.there (.here (.conj .bot .top) []))) =
        (BlockedConjFirst.block .bot .top [] [] [.conj .bot .top]).keep := by rfl
'''
controls['fresh-conjunction-returned-rank']='''example :
    (SequentialConjFirst.fresh (P:=Empty) (Γ:=[.bot]) (Θ:=[]) (I:=[]) (J:=[]) (F:=[.top]) (U:=[])
      (G.thinR [.bot] [] [.top] .top (G.thinR [.bot] [] [] .top G.botE)) G.topI).rho
      .right (.here (.conj .top .top) [.top]) = 2 := by
  have hf : (SequentialConjFirst.fresh (P:=Empty) (Γ:=[.bot]) (Θ:=[]) (I:=[]) (J:=[]) (F:=[.top]) (U:=[])
      (G.thinR [.bot] [] [.top] .top (G.thinR [.bot] [] [] .top G.botE)) G.topI).rho
      .right (.here (.conj .top .top) [.top]) = 1 := G.rho_conjR_principal _ _
  rw [hf]
  rfl
'''
exec(rf_controls_source[rf_controls_source.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==32'))
