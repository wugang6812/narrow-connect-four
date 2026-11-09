# Auxiliary mathematical checks

These finite tests support the papers; they do not replace parameterized proofs.
Run each script with Python 3.10+ from any working directory.

- independent_lower_bounds.py: independent coordinate checks of the zero-active traps.
- a2_interval_scan.py: interval-scan implementation against cellwise enumeration.
- replay_upper_and_segments.py: supplied reference checker with segment instrumentation.
- segment_nine_witness.py: a concrete nine-segment trajectory with coordinate replay.

reference/check_uniform.py is the supplied independently implemented reference
checker, retained without byte changes. Reusing it is not a new independent
implementation. The first two scripts and the segment instrumentation are
separate additions. Output JSON files are local generated results.
