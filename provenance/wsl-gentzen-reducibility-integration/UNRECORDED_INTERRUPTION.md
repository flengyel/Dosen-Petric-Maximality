# Interrupted exploratory build

The length-copy exploratory run was interrupted by Ctrl-C (process exit 130); its Python runner then raised KeyboardInterrupt before saving a JSON receipt. Elapsed time was not captured. This is a failed/interrupted attempt, not a successful check. No final verification was interrupted. Logs without a JSON receipt:

- build-GentzenLengthCopyIndices-20261025T203911658324.log
