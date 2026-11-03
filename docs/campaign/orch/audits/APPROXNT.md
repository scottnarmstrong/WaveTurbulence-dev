# APPROXNT audit (Task 14b): DH23 Prop 6.4, its added conditions, and the large-order range

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03.

**Subject.** Landed `f154af6` ("Land w/approxnt"), `WaveTurbulence/Foundations/ApproxNT/**`. The packaged export is
`ApproxNT.dh23_prop_6_4` (`Prop64.lean`), assembled from `approxnt_conclusion1` and `approxnt_conclusion2`.

**Sources.**
- DH23 `Revision_Submit.tex` L984–L1010 (Prop `approxnt`) and L438 (standing parameters).
- Snapshot 5's `WTPrefix` (Π) and `WTParams.{R, N}` (`WaveB1-Core.lean` L75–L109).
- FINDINGS F33 (route R14(a)).

## Verdict: PASS

The added conditions are satisfiable inside Π in the order Π fixes the parameters. The order range `n ≤ (log L)^A`
for **every** real `A` covers `n ≤ N_{p+1}^4` (F33).

## The exported statement (binders)

```
dh23_prop_6_4 (hd : 3 ≤ d) (hγ : γ ∈ Ioo 0 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
  (hηγ : η ≤ (d-1)(1-γ)) (hηγ' : η ≤ γ) (hC₀ : 1 ≤ C₀) :
  ∃ C₁ > 0, ∀ A, ∃ L₀, ∀ L ≥ L₀, ∀ δ, L^{-η/2} ≤ δ → δ ≤ 1 → ∀ n, (n:ℝ) ≤ (log L)^A → ∀ C⁺ ≥ 0, …
  (propertyw1), (propertyw2) with arbitrary λ_j ≥ 1, (propertypsi1), (propertypsi2) with constant C₀ …
  → conclusion (1) ∧ |I_app| ≤ B ∧ |I − I_app| ≤ B L^{-γ₁+η}
```

Here `B = (∏λ_j)^{2d} (C₁ C⁺ L^{2d−2γ} δ⁻¹)^n`.

**Relative to DH23.** The box sizes `1 ≤ λ_j ≤ (log L)^4` become `λ_j ≥ 1` (stronger), and the order bound
`n ≤ (log L)³` becomes `n ≤ (log L)^A` for every `A` (stronger; this is the F33 extension). The added conditions are
D3/D4 below.

## The added conditions inside Π

**Π's order** (snapshot 5 `WTPrefix`): `d ≥ 3, γ` → `∃η₀ ∀η ≤ η₀` → data `(φin, τ★, φ)` → `C₁^Π` → `ν` → `δ` (with
`𝔇 = τ★/δ`) → `C₂` → `∃L₀ ∀L ≥ L₀`.

| Condition | Depends on | Where Π can discharge it |
|---|---|---|
| `η ≤ 1/20`, `η ≤ (d−1)(1−γ)`, `η ≤ γ` (D3) | `d, γ` | Choose `η₀ ≤ min(1/20, (d−1)(1−γ), γ)`, which is positive since `d ≥ 3` and `0 < γ < 1`. This is the quantitative form of DH23 L438's "η ≪_{d,γ} 1", and TARGET's other upper bounds on η are of the same type, so the intersection is a positive `η₀`. ✓ |
| `1 ≤ C₀`, the Ψ constant of (propertypsi2) | DH23 L438: "`C` depending on `(d, γ)` and `η`" | APPROXNT's `C₁` is chosen after `(d, γ, η, C₀)` and before `A, L, δ, n, C⁺`. It can be absorbed into `C₁^Π`, which comes after the data, so this works even if a consumer's `C₀` depends on the data. ✓ |
| `C⁺` | universally quantified (`∀ C⁺ ≥ 0`) | Any later choice (DH23: depending on `C` and the data). ✓ |
| `δ ≤ 1` (D4) | — | `δ₀ ≤ 1` is the prover's choice in Π. ✓ |
| `L^{−η/2} ≤ δ` (D4) | `δ, η` | `L₀` comes after `δ`. For `L ≥ δ^{−2/η}` it holds (`rpow_neg_half_le`, proved). This is DH23's "δ fixed, then L large". ✓ |
| `A` in `n ≤ (log L)^A` | see below | `A = A(d, 𝔇)` is fixed after `𝔇` and before `L₀`. `dh23_prop_6_4` gives `L₀(A)` after `A`. ✓ |

**Quantifier order.** In the export, `∃ C₁ ∀ A ∃ L₀ ∀ L ≥ L₀ ∀ δ`: `L₀` precedes `δ`, but `δ` then enters only
through `L^{−η/2} ≤ δ ≤ 1`. So at the use site the consumer takes `L₀^Π ≥ max(L₀(A), δ^{−2/η})`. The bound `B`
retains `δ⁻ⁿ`, exactly as DH23's (conclusion1)/(conclusion2).

## The large-order range covers `n ≤ N_{p+1}^4` (F33)

In snapshot 5:
- `R_q = Rdown(𝔇 − q)` with `Rdown 0 = ⌊(log L)^{40d}⌋` and `Rdown (k+1) = (Rdown k^{40d})^{40d}`;
- `N_q = R_q^{40d}`.

**Bound.** For `x = log L ≥ 1`, induction on `k` gives `Rdown k ≤ x^{40d·(40d)^{2k}}`. Hence, for `p + 1 ≤ 𝔇`,

  `N_{p+1}^4 = R_{p+1}^{160d} ≤ (log L)^{A}` with `A := 160d · 40d · (40d)^{2𝔇}`.

`A` depends only on `(d, 𝔇)`, both fixed before `L₀`. Since the export holds for every real `A`, it covers every order
`n ≤ N_{p+1}^4` that regref1 (F33) needs, provided `L₀ ≥ e`. **The F33 extension is available at the
`approxnt` level.** It does not by itself close F33 for the regular-couple asymptotics (B2.1's other ingredients), as
recorded in my stage-2/3 B2 audit.

## Notes

- The η conditions are hypotheses of the Foundations theorem, not of any frozen statement. The frozen anchors keep
  the source's prefix Π, and the provers discharge them as above.
- `I_app` uses the p.v. as the limit of `χ_∞(ν⟨x,y⟩)` truncations and `δ(⟨x,y⟩)` in the hyperplane reading of ruling
  D6, integrated backwards from `j = n−1` as in DH21 L1636 (commit `a6db6ef`). This matches the `deltaInner`
  convention of NTSP (Task 10).
