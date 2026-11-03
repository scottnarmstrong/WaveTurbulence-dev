# Packet WKE-TAYLOR — WKE existence by power series, τ_max characterization, Taylor bound (follow-on to WKE)

Read `COMMON.md` first. Same worktree/branch (`/home/scott/WaveTurbulence-worktrees/wke`, `w/wke`); run `git merge main`.
Files: `WaveTurbulence/Foundations/WKE/**`.

Your STOPPED report is accepted. The frozen `wkelwp` conjunct 3 (L²_s blow-up for d ≥ 4) is a pending author decision
(FINDINGS F32; options: versioned successor of `wkelwp`, or a proof of the general-d L²_s trilinear estimate, which a
separate research agent is investigating). Do not work on conjunct 3. Work on everything else, via your power-series
route:

1. **Local existence** of Schwartz-class solutions by the power series `𝒰ₙ(t) = (δ(t−p))ⁿ aₙ` / its WKE analogue, with
   lifespan controlled by the low weighted-sup norm; continuation; uniqueness (you have it).
2. **The τ_max characterization**: define τ_max := sup{τ★ : a Schwartz solution exists on [0,τ★]} (∈ (0,∞]) and prove
   `wkelwp` conjuncts 1–2 exactly as frozen (`0 < τmax`, and `ofReal τ★ < τmax ↔ ∃ φ, IsWKESolution φin τ★ φ`; note the
   ← direction needs "a solution on the closed [0,τ★] extends past τ★"), plus the uniqueness conjunct (done).
   Provide them as separate theorems under the Provider-free names `WaveTurbulence.WKE.*` (not in the Provider module,
   which is quarantined; the orchestrator assembles the anchor later).
3. **Goal 5 / F10**: the WKE Taylor expansion (wketaylor)–(taylorbound) with the base independent of Λ, via your
   Jensen + multinomial induction, in the 𝔖^{Λ,Λ}-type sup norms (state the norm you use; the frozen 𝔖 norm comes in
   Wave B — make the statement easy to transfer).
4. Optional, if quick: Lemma 4.3(ii)-type L²_s bounds that do transfer for 2s > d − 2 (report what is and is not proved
   in L²_s for d ≥ 4).
Commit after each. Done: `READY wke-taylor`.
