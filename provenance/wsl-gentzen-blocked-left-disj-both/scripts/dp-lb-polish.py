attempt=local/'attempts';attempt.mkdir(exist_ok=True)
for p in sorted(local.glob('*.lean')):
 for q in [p,p.with_suffix('.log')]:
  if q.exists():(attempt/q.name).write_bytes(q.read_bytes())
(attempt/'dp-lb-controls-failed-dispatch.py').write_bytes(Path('/tmp/dp-lb-controls-failed-dispatch.py').read_bytes())
(attempt/'STATUS.json').write_text(json.dumps(dict(
 failed_control_harness_dispatch=True,
 reason='Nested exec changed the generic script variable, selecting an older expected-diagnostic classifier for newly inherited controls.',
 counted_as_expected_rejection=False,
 resolution='Save the intended full runner source under a phase-specific variable before evaluating inherited control definitions; rerun every focused control.'),indent=2)+'\n')
print('Preserved interrupted control-harness attempt; semantic production proofs unaffected')
