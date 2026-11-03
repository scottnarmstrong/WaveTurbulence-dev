# Packets I1 INDUCT-A + I2 INDUCT-B (pre-freeze, conditional) — the inductive step: propansatz from the three gates

Read `COMMON.md` first. You just proved `main_of_propansatz_nlsAkBridge` (main from the two gates). Now the layer below:
TARGET's proof of Prop `propansatz` (L795–L816, steps S1–S7) from `layergarden`, `fixedpoint`, `wkeTaylor`.
Blueprint rows (packets I1, I2): `T.cmattr`, `GAP.cmattrBij`, `T.step.S1`–`S7`, `T.ansatzBase`, `PROB.condCS`.

Work in untracked scratch `/home/scott/wt-scratch/induct/` against `/home/scott/wt-scratch/waveb-snap-5/` (the freeze
candidate), importing the landed `Foundations/{Cumulant,Gaussian,NLS,MainGlue,Probability}` modules and the scratch APIs
of wt-gauss-hc (CANON: `/home/scott/wt-scratch/canon/` — `canonicalCharacterization` proved, construction-data
uniqueness, finiteness of 𝒢_q; SYS-DEFS API / Duhamel identity in progress: ask the orchestrator for paths).

Goals (do not end your turn at milestones):
1. **T.ansatzBase** (p = 0, L708–L709): F₀ = Ω, R₀ = E₀ = Ẽ₀ = 0, Gaussian cumulants of order ≥ 3 vanish, the two-point
   function is 1_{k=ℓ} φin(k) — from the landed Gaussian/cumulant API.
2. **T.cmattr** (L727–L730, L798–L801; the unfrozen target formerly called `cumulantExpansion`, corrected order range in
   DESIGN CL-9): 𝕂_p(a^tr(t)^{ζ₁},…,a^tr(t)^{ζ_{2R}}) = Σ_{G ∈ 𝒢^tr_{p+1}} K_G(t,…) + terms containing E_p or Ẽ_p, by
   multilinearity, Lemma `propertycm` (landed), the canonical-garden bijection (`GAP.cmattrBij`, via CANON), and the
   time-domain factorization.
3. **S3–S4** (errors E^{(1)}, E^{(2)}), **S6–S7** (the b-contributions E^{(4)} and the event change E^{(5)}; Cauchy–
   Schwarz, cumulant↔moment conversions — `PROB.condCS` landed in MISC-A).
4. **The conditional assembly** `propansatz_of_gates`: hypotheses exactly the propositions of the drafted `layergarden`,
   `fixedpoint`, `wkeTaylor` (copied verbatim from snapshot 5 as Prop-valued hypotheses), conclusion exactly the drafted
   `propansatz`. Report precisely anything that does not fit (a missing gate clause would be a statement defect).
Done: `READY induct`.
