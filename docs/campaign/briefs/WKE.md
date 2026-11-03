# Packet WKE — the collision operator, local theory, Prop `wkelwp`, Taylor expansion

Read `COMMON.md` (same directory) first.
Worktree: `/home/scott/WaveTurbulence-worktrees/wke`, branch `w/wke`.
Files you own: `WaveTurbulence/Foundations/WKE/**`.

## Sources

TARGET `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`: (WKE), (COL) L294–L310;
Prop `wkelwp` L598–L606; Appendix C L2487–L2528; WKE Taylor expansion (wketaylor), (wketaylor2), (taylorbound)
L749–L760; norms 𝔖^{Λ₁,Λ₂} (normX2) L586–L590. GIT20 `/home/scott/wave-turbulence/references/src-1711.05587/Kin8.tex`
(Lemmas 4.1–4.3, Remark 2.6; note GIT20 is written in d = 3 — TARGET uses it for all d ≥ 3, see
`/home/scott/WaveTurbulence-dev/docs/FINDINGS.md` F18). Map: `/home/scott/wave-turbulence/maps/T-part1.md`
(entries wkelwp, Appendix C stages, wketaylor/taylorbound; open question Q6 = FINDINGS F10).

## DRAFT definitions (verbatim; namespace `WaveTurbulence`;
`open MeasureTheory Set`, `open scoped InnerProductSpace SchwartzMap`)

```lean
/-- Momentum space `ℝ^d` with the Euclidean inner product `⟨k, ℓ⟩ = ∑ kʲ ℓʲ` (DH (COL), §1.1). -/
abbrev Mom (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The cubic collision operator `𝒦(φ₁, φ₂, φ₃)(k)` of (COL), written after the change of
variables `k₁ = k + ℓ₁`, `k₃ = k + ℓ₃`, `k₂ = k + ℓ₁ + ℓ₃` of (C.5) (which removes the first
delta and turns the second into `δ(-2⟨ℓ₁, ℓ₃⟩)`), with `∫ g(ℓ₃) δ(2⟨ℓ₁, ℓ₃⟩) dℓ₃ =
(2|ℓ₁|)⁻¹ ∫_{ℓ₁^⊥} g`, the integral over the hyperplane `ℓ₁^⊥` taken against its
`(d-1)`-dimensional Lebesgue measure. -/
def collisionOp {d : ℕ} (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d) : ℝ :=
  ∫ ℓ₁ : Mom d, (2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ,
    (φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + w) * φ₃ (k + w)
      - φ₁ k * φ₂ (k + ℓ₁ + w) * φ₃ (k + w)
      + φ₁ (k + ℓ₁) * φ₂ k * φ₃ (k + w)
      - φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + w) * φ₃ k)

/-- `φ` is a Schwartz-class solution of (WKE) on `[0, τ★]` with initial data `φin`:
`τ ↦ φ τ` is continuous on `[0, τ★]` into the Schwartz space, `φ 0 = φin`, and
`∂_τ φ(τ, k) = 𝒦(φ(τ), φ(τ), φ(τ))(k)` for every `τ ∈ [0, τ★]` and `k ∈ ℝ^d`
(one-sided at the endpoints). -/
def IsWKESolution {d : ℕ} (φin : 𝓢(Mom d, ℝ)) (τstar : ℝ) (φ : ℝ → 𝓢(Mom d, ℝ)) : Prop :=
  ContinuousOn φ (Icc 0 τstar) ∧ φ 0 = φin ∧
    ∀ τ ∈ Icc 0 τstar, ∀ k : Mom d,
      HasDerivWithinAt (fun s => φ s k) (collisionOp (φ τ) (φ τ) (φ τ) k) (Icc 0 τstar) τ
```

## Goal (in this order; commit after each)

1. **Well-definedness and the delta reading.** For Schwartz (or `⟨k⟩^{-N}`-bounded measurable) inputs and `d ≥ 3`:
   integrability of every integrand (so no Bochner junk), the decomposition `𝒦 = 𝒦₀ − 𝒦₁ + 𝒦₂ − 𝒦₃` of
   (schappend1)–(schappend4), and a **characterization theorem** confirming the delta reading:
   `𝒦(φ₁,φ₂,φ₃)(k) = lim_{ε→0} ∫∫ [integrand](ℓ₁,ℓ₃) ψ_ε(2⟨ℓ₁,ℓ₃⟩) dℓ₁ dℓ₃` for a standard mollifier
   `ψ_ε = ε⁻¹ψ(·/ε)`, `∫ψ = 1` (the GIT20 convention, Kin8.tex L981). Also the symmetric form in `(k₁,k₂,k₃)` if cheap.
2. **Trilinear estimate** (TARGET (schappend8), GIT20 Lemmas 4.1–4.3): `‖𝒦_j(φ₁,φ₂,φ₃)‖_{Z_s} ≤ C₀(s) ∏ ‖φ_i‖_{Z_s}`,
   `‖φ‖_{Z_s} = ‖⟨k⟩^s φ‖_{L²}`, for `d ≥ 3`, `s > d/2 − 1`. If GIT20's d = 3 proof does not transfer, find the
   general-d argument (or the weaker range of `s` that suffices for the uses) and report.
3. Leibniz rule (schappend6) and weight identity (schappend7) and their multi-index iterates; the `Z_{s,m}` estimate.
4. Local well-posedness in `Z_{s,m}`, the a priori estimate (schappend10), and **Prop `wkelwp`**: maximal Schwartz
   solution on `[0, τ_max)`, uniqueness, blowup criterion (blowuptest). Relate to `IsWKESolution`: for `τ★ < τ_max`
   the maximal solution restricted to `[0, τ★]` satisfies `IsWKESolution`, and any `IsWKESolution` on `[0, τ★]`
   coincides with it on `[0, τ★]` (so `τ★ < τ_max`).
5. **Taylor expansion** (wketaylor)–(taylorbound): for `δ` small depending on `sup_{[0,τ★]} ‖φ‖_{𝔖^{40d,40d}}`, the
   power series in `𝒰_n` converges and `sup_t ‖𝒰_n(t)‖_{𝔖^{Λ,Λ}} ≤ C₂ (C₁δ)^n` with the base `C₁δ` independent of
   `Λ` (FINDINGS F10: the paper asserts this; it needs a tame estimate for `𝒦` in the sup-based weighted norms
   `𝔖^{Λ₁,Λ₂}` (normX2)). Work out and prove the tame estimate.

## Stop conditions

Done: `READY wke`. Blocked > ~1 hour on one ingredient: `STOPPED wke: <reason>` with a proposed route.
