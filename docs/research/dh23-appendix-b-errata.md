# APPB source errata for the final handoff

- DH23 Revision_Submit.tex L2183 (`brprop`): statement says Delta nu=2;
  its proof L2185 computes 2-4=-2. Use -2 (already campaign F4).
- DH23 L2238, final sentence of 3D3-3G proof: “same direction” contradicts
  the operation's applicable internal-pair condition; use “opposite
  direction,” as in the operation definition (recorded in TRANSCRIPTIONS).
- DH23 L2110, proof of `basiccount` (4), displays
  `|k1|^2-|k2|^2+|k3|^2-|k|^2 = 2(k1-k) dot (k3-k)` under
  `k1-k2+k3=k`. The sign must be negative, or the second factor must be
  `k-k3`, exactly as the paper correctly states at L435 (`defomega`).
  Counterexample in dimension 3: k1=k3=(1,0,0), k2=(2,0,0), k=0;
  left side -2, displayed right side +2. The absolute energy-window
  counting bounds survive by reversing the fixed energy center. Use the
  correct negative sign in actual transformations. No frozen file changed.

Typographical “Ds/Df”, “bond/bound”, and “tall bonds” occurrences do not
change statements. See TRANSCRIPTIONS.md for figure readings.

- DH23 L2238, 3D3-3G proof, says “we have C_pre ≲
  delta^{-1} L^{d-gamma-2 gamma0/3}” with no C_pos factor.
  Read this as the relative counting bound C_pre ≲
  delta^{-1} L^{d-gamma-2 gamma0/3} C_pos, as in the immediately
  preceding 3S3-3G proof L2211 and as required for the deviation estimate.
  The implemented theorem proves the relative bound on the actual
  reinserted output. This is a missing factor in the prose proof;
  the operation and proposition statements are unchanged.
