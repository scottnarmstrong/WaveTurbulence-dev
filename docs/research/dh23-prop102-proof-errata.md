# APPB-ALG source errata and readings

- DH23 Revision_Submit.tex L1904, equation (increv3), prints the upper
  bound `-V_30 - C r_2`. The good-operation contribution is bounded in
  absolute value, so the required upper bound is `-V_30 + C r_2`.
  This is also the sign needed for the subsequent subtraction yielding
  an O(r_2) upper bound. We will derive the signed remainder from the
  actual finite sequence, rather than assume the displayed inequality.
  No frozen statement is involved.
- The connected-component qualification at L1902 is not an erratum:
  DH23 §10.1 L1829 explicitly assumes connected molecules in Props
  10.1–10.4. This resolves the initial question about nu_0.
- DH23 Revision_Submit.tex L1912 (Conclusion) says, for E=2V-2>0,
  "the total number of operations is <= C(r_1+r_2) as shown above".
  This drops the exclusion of 3D3-1N stated at L1911 and contradicts
  L1912's preceding sentence that 3D3-1N's count is not controlled.
  Long double-rung ladders have arbitrarily many such normal removals.
  The required argument is that a nonempty terminating run has a step
  different from normal 3D3: normal 3D3 leaves degree-three boundary
  survivors, hence cannot be the last step. Bound that step count (or
  the count of chains plus other steps), not the total number of steps.
  We use the actual terminal-step argument, without a new source premise.
- DH23 Revision_Submit.tex L1834 (Prop 10.2, third bound) writes "the number of atoms not of degree 4 is `w`, and we also allow at most
  `w` atoms to be SG". The proof (L1913) fixes "the w SG atoms" and removes them one by one; but SG-ness (L553) is a property of the
  decoration, so the set varies with the decoration. Not an error: handled by a union bound over the at most (w+1) n^w exceptional
  sets, which needs the size bound n <= (log L)^C (see the GraphOk deviation).
- L1913-L1917: "L^{-eta^2 rho + C(w+1)}" with rho <= C(r1+r2)+C(w+1): the passage to `L^{-(r1+r2) eta/3}` vs `L^{-eta^2 rho}` needs
  eta <= 1/(4 C0) for the absolute constant C0 of rho <= C0 (r1+r2) (here 1440061); the source treats this as part of "eta small".
