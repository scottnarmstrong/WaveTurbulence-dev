# wt-orch Task 10 — statement review 3 (high-stakes new results)

`git merge main` first. Refute-first statement review (statements, not proofs; normalizations, hypotheses that would
not be dischargeable at the use site, junk values, exact types), priority order:
1. **The 27/41 circle result** (`Foundations/VdCB/**`, wt-ansob, NT-BPROC; resolves FINDINGS F3): the circle discrepancy
   and annulus bounds — uniform in the centre, the exact exponent, the annulus statement in the form DH23 Lemma A.2
   (L2028–L2050, F31) needs; and wt-nt's elementary annulus/estcross (`Foundations/Counting/**`).
2. **`MainGlue.main_of_propansatz_nlsAkBridge`** (scratch `/home/scott/wt-scratch/main-assembly/`, wt-cumul): its
   conclusion is *exactly* the frozen type of `WaveTurbulence.main` (byte comparison of the elaborated types, e.g. via
   `#check` output), its two hypotheses are *exactly* the drafted `propansatz` and `nlsAkBridge` of
   `/home/scott/wt-scratch/waveb-snap-5/` (no extra hypotheses, no weakening), and it does not import any quarantined
   module. Also the MainGlue lemmas G1–G11 (landed + `/home/scott/wt-scratch/main-glue2/`).
3. `Foundations/NormBridge*`/`Fourier/Norm00V*` (norm bridges, wt-cumul), `Foundations/NTSP/**` (TARGET Lemma 5.2, DH23
   Lemmas 6.5, 6.7), `Foundations/ClassJR/**` (DH21 Def 5.2, Lemmas 5.3–5.8), `Foundations/WeylSums/**` minor arcs (DH23 6.6,
   lemlayer2/lemcubic in drafted form — compare with snapshot 5's `quadExpSum2/3` exactly).
File `docs/campaign/orch/audits/Infra-review-3.md`; commit; `READY task10`.
