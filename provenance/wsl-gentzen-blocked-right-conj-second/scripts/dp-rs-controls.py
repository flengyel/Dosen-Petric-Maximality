rs_controls_source=Path('/tmp/dp-ls-controls.py').read_text()
rs_prior_source=Path('/tmp/dp-rf-controls.py').read_text()
exec(rs_prior_source[:rs_prior_source.index('\nexec(rf_controls_source[rf_controls_source.index(')])
controls['right-second-fixed-first']='''example :
    (BlockedConjSecond.block (.bot : NormalForm Empty) .top [.conj .bot .top] [] []).route.get
      (.there (.here (.conj .bot .top) [.conj .bot .top])) =
        (BlockedConjSecond.block .bot .top [.conj .bot .top] [] []).keep := by rfl
'''
exec(rs_controls_source[rs_controls_source.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==33'))
