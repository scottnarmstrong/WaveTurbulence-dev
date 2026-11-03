# Packet WKE-L2S — the general-d L²_s trilinear estimate (Theorem 7) and the blow-up conjunct of `wkelwp`

Read `COMMON.md` first. Worktree `/home/scott/WaveTurbulence-worktrees/wke-l2s`, branch `w/wke-l2s`.
Files: `WaveTurbulence/Foundations/WKEL2/**` (import, never edit, wt-wke's `Foundations/WKE/**`).

## Sources

- The proof to formalize: `/home/scott/WaveTurbulence-dev/docs/research/git20-general-d.md` (Theorem 7, Lemmas 1–4,
  Props 5–7, §10 blow-up passage; §12 lists the Lean dependencies), audited CORRECT in
  `docs/campaign/orch/audits/GIT20-general-d.md` (which also lists three supporting lemmas, §3).
- TARGET Appendix C (`/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex` L2487–L2528).
- Frozen: `collisionOp`, `IsWKESolution`, `weightedL2Norm` (`WaveTurbulence/Frozen/Defs/`), statement
  `WaveTurbulence.wkelwp` (read-only; conjunct 3 is this packet's target).
- Landed infrastructure: `Foundations/WKE/{DeltaReading,Hyperplane,CollisionOp,...}` (hyperplane slicing,
  `collisionOp = 𝒦₀ − 𝒦₁ + 𝒦₂ − 𝒦₃`).

## Goals (commit after each)

1. Lemma 1 (symmetry of the resonant measure under ℓ₁ ↔ ℓ₃), Corollary 2 (polar form).
2. Lemmas 3–4 (the radial quantity A_k, the uniform bounds M₁, M₂ via Hölder).
3. Props 5–7 and **Theorem 7**: ‖𝒦_j(φ₁,φ₂,φ₃)‖_{Z_s} ≤ C(d,s) ∏‖φ_i‖_{Z_s} for d ≥ 3, s > d/2 − 1, j = 0..3, with
   `‖·‖_{Z_s} = weightedL2Norm s` (frozen), for nonnegative measurable inputs and then signed ones.
4. The three supporting lemmas of the audit §3 and the **blow-up conjunct** of `wkelwp` (Picard LWP in Z_s with
   existence time ≳ (C‖φ₀‖²)⁻¹, the Z_{s,m} bounds, Gronwall (schappend10), equality of all τ_max^{(s,m)}, full limit):
   prove it as a separate theorem `WaveTurbulence.WKEL2.wkelwp_blowup` stated exactly as conjunct 3, relative to the
   τ_max of wt-wke's WKE-TAYLOR packet (coordinate the name of τ_max with wt-wke via the orchestrator; if theirs is not
   landed yet, state it relative to `sSup {τ★ | ∃ φ, IsWKESolution φin τ★ φ}`).
Done: `READY wke-l2s`.
