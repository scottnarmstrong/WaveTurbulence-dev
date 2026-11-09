/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmCountAlg
/-! **L6E GHOST, part 20: the specification (f′) and Theorem 7.1 (exact telescoping)** (M1-R2 §6, §7; REF-M1R2 §4.8–4.9).

* `GhostSpec`: the data of (f′) on a run: the critical group-D pairs (a finset of an index type), the steps
  `tri(P)` (the triangle step) and `s(P)` (`cre`, the creation step of the later ghost), and one bit per pair
  (`true` = TR, `false` = NC); `ncPairs` the NC pairs.
* `nuTri s`, `nuCre s`: `ν^tri_s = #{NC P : tri(P) = s}`, `ν^cre_s = #{NC P : s(P) = s}`.
* **Theorem 7.1** (`telescoping`): `∏_s L^{τ₀(ν^tri_s - ν^cre_s)} = 1` over any finite set of steps containing every
  `tri(P)` and `s(P)`; `telescoping_prod`: the charged per-step bounds (★) multiply to exactly R38's product.
* `nuTri_le_one`, `nuCre_le_two`: the step counts (each ghost lies in one triangle; a step creates `≤ 2` `α`-atoms).
* **The cost of (f′)** (`countA_spec_le`): splitting the decorations of a class by the TR/NC bits of `n` pairs costs
  `2^n` (main's `countA_union_le`): `𝔄(Adm) ≤ 2^n · max_T 𝔄(Adm_T)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

/-- **The specification (f′)** (M1-R2 §6): critical pairs, their triangle step `tri(P)`, the creation step `s(P)` of
the later ghost (`cre`), and the class bit (`true` = TR, `false` = NC). -/
structure GhostSpec (ι σ : Type*) where
  pairs : Finset ι
  tri : ι → σ
  cre : ι → σ
  spec : ι → Bool

namespace GhostSpec
variable {ι σ : Type*} (G : GhostSpec ι σ)

/-- The NC critical pairs. -/
noncomputable def ncPairs : Finset ι := G.pairs.filter fun P => G.spec P = false

/-- `ν^tri_s`: the NC pairs whose triangle step is `s`. -/
noncomputable def nuTri (s : σ) : ℕ := (G.ncPairs.filter fun P => G.tri P = s).card

/-- `ν^cre_s`: the NC pairs whose later ghost is created at `s`. -/
noncomputable def nuCre (s : σ) : ℕ := (G.ncPairs.filter fun P => G.cre P = s).card

theorem sum_nuTri (steps : Finset σ) (h : ∀ P ∈ G.ncPairs, G.tri P ∈ steps) :
    ∑ s ∈ steps, G.nuTri s = G.ncPairs.card :=
  (Finset.card_eq_sum_card_fiberwise h).symm

theorem sum_nuCre (steps : Finset σ) (h : ∀ P ∈ G.ncPairs, G.cre P ∈ steps) :
    ∑ s ∈ steps, G.nuCre s = G.ncPairs.card :=
  (Finset.card_eq_sum_card_fiberwise h).symm

/-- **Theorem 7.1 (telescoping).** The transfers cancel pair by pair: `∏_s L^{τ₀(ν^tri_s - ν^cre_s)} = 1`. -/
theorem telescoping (steps : Finset σ) (htri : ∀ P ∈ G.ncPairs, G.tri P ∈ steps)
    (hcre : ∀ P ∈ G.ncPairs, G.cre P ∈ steps) {L : ℝ} (hL : 0 < L) (τ : ℝ) :
    ∏ s ∈ steps, L ^ (τ * ((G.nuTri s : ℝ) - G.nuCre s)) = 1 := by
  rw [← Real.rpow_sum_of_pos hL]
  have h1 : ∑ s ∈ steps, τ * ((G.nuTri s : ℝ) - G.nuCre s) =
      τ * ((∑ s ∈ steps, (G.nuTri s : ℝ)) - ∑ s ∈ steps, (G.nuCre s : ℝ)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  have h2 : ∑ s ∈ steps, (G.nuTri s : ℝ) = G.ncPairs.card := by exact_mod_cast G.sum_nuTri steps htri
  have h3 : ∑ s ∈ steps, (G.nuCre s : ℝ) = G.ncPairs.card := by exact_mod_cast G.sum_nuCre steps hcre
  rw [h1, h2, h3, sub_self, mul_zero, Real.rpow_zero]

/-- **The charged per-step bounds multiply to R38's product** (Theorem 7.1, consequence): for any per-step factors
`B_s`, `∏_s (B_s · L^{τ₀(ν^tri_s - ν^cre_s)}) = ∏_s B_s`. -/
theorem telescoping_prod (steps : Finset σ) (htri : ∀ P ∈ G.ncPairs, G.tri P ∈ steps)
    (hcre : ∀ P ∈ G.ncPairs, G.cre P ∈ steps) {L : ℝ} (hL : 0 < L) (τ : ℝ) (B : σ → ℝ) :
    ∏ s ∈ steps, (B s * L ^ (τ * ((G.nuTri s : ℝ) - G.nuCre s))) = ∏ s ∈ steps, B s := by
  rw [Finset.prod_mul_distrib, G.telescoping steps htri hcre hL τ, mul_one]

/-- The per-step factor in the form of the two step bounds: `L^{τ₀ν^tri} · L^{-τ₀ν^cre}`. -/
theorem transfer_split (s : σ) {L : ℝ} (hL : 0 < L) (τ : ℝ) :
    L ^ (τ * ((G.nuTri s : ℝ) - G.nuCre s)) = L ^ (τ * (G.nuTri s : ℝ)) * L ^ (-τ * (G.nuCre s : ℝ)) := by
  rw [← Real.rpow_add hL]; congr 1; ring

/-- Each NC pair has one triangle step: `ν^tri_s ≤ 1` when distinct NC pairs have distinct triangle steps. -/
theorem nuTri_le_one (hinj : Set.InjOn G.tri G.ncPairs) (s : σ) : G.nuTri s ≤ 1 := by
  unfold nuTri
  rw [Finset.card_le_one]
  intro P hP P' hP'
  rw [Finset.mem_filter] at hP hP'
  exact hinj hP.1 hP'.1 (hP.2.trans hP'.2.symm)

/-- A step creates at most two later ghosts: `ν^cre_s ≤ 2` when each step is `s(P)` of at most two NC pairs. -/
theorem nuCre_le_two (s : σ) (h : (G.ncPairs.filter fun P => G.cre P = s).card ≤ 2) : G.nuCre s ≤ 2 := h

end GhostSpec

/-- **The cost of (f′)**: splitting the decorations of a class by the TR/NC bits of the pairs `Ps` (`TR P κ`: the pair
`P` is transverse in the decoration `κ`) costs the factor `2^{#Ps}` (TARGET's `C₀^{n_sb}`, M1-R2 §6). -/
theorem countA_spec_le {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ} {ι : Type*}
    (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (Ps : Finset ι) (TR : ι → (D → (Fin d → ℤ)) → Prop) (B : ℝ≥0∞)
    (hB : ∀ T ∈ Ps.powerset, M.countA L γ δ C₁ w (fun κ => Adm κ ∧ ∀ p ∈ Ps, (TR p κ ↔ p ∈ T)) P ≤ B) :
    M.countA L γ δ C₁ w Adm P ≤ 2 ^ Ps.card * B := by
  have h := FinalCountAsm.countA_union_le M L γ δ C₁ w Ps.powerset
    (fun T => fun κ => Adm κ ∧ ∀ p ∈ Ps, (TR p κ ↔ p ∈ T)) (fun κ hκ => by
      refine ⟨Ps.filter fun p => TR p κ, Finset.mem_powerset.2 (Finset.filter_subset _ _), hκ, fun p hp => ?_⟩
      rw [Finset.mem_filter]; exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩) P
  refine h.trans ?_
  calc ∑ T ∈ Ps.powerset, M.countA L γ δ C₁ w (fun κ => Adm κ ∧ ∀ p ∈ Ps, (TR p κ ↔ p ∈ T)) P
      ≤ ∑ _T ∈ Ps.powerset, B := Finset.sum_le_sum hB
    _ = 2 ^ Ps.card * B := by rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]; push_cast; ring

end WaveTurbulence.GammaLow.FinalCount.Ghost
