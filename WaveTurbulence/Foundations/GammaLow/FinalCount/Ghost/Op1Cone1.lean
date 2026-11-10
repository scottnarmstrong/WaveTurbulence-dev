/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone8
/-! **L6E2, part 1: the creation cone at an Operation-1 removal — splitting by the joint gap**
(M1-R2 Theorem 6.1 (e) at Op 1/1E; Lemma 5.2; NOTES §10.2).

An Op-1 removal with `ΔF = 0` (L6-STEP1's `Step1.VineCut`) creates the two joints as `α`-atoms with the common gap `±r`
(`r = κ x₁ - κ x₂`, `Step1.rint`). Every Step-1 label count of L6-STEP1 (`vine_count_main`, `hyper_count_main`,
`DoubleShape.labelSet_le_vineG`) is uniform in the admissible class and in the ball `‖r - r₀‖ ≤ ρ` (`ρL ≥ 1`), and is
linear in `(ρL)^d`. So the cone count follows from these counts as black boxes:
* split the class by the exact joint gap (`AdmFix`; `labelSet_le_split`: `#labels ≤ #G · max_r #labels_r`);
* each piece has its gap fixed: the ball of radius `1/L` around it;
* the joint gaps of a class with the cone hypothesis `JointCone` lie in `coneSet` (`rint_mem_coneSet`), whose size is
  `≤ 3·5^{d-1} θ₀^{d-1} (ρL)^d` (`card_coneSet_le_rho`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {d : ℕ}

/-- **The creation cone at an Op-1 removal** (the (f′) class NC at `s(P)` when the later ghost is a joint of the removed
object; Lemma 6.2): in each parameter class the joint gap lies in the cone of aperture `θ₀ = L^{-6η}` around a fixed
nonzero centre. (Both joints have the gap `±r`, and `InCone` is even in `r` (`inCone_neg`), so one cone covers both
joints: `k ≤ 2`, NOTES §6 (e).) -/
def JointCone {g : ℝ} {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (K : Step1.VineCut g M) (L γ δ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    ∃ ctr : Mom d, ctr ≠ 0 ∧ ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      InCone (L ^ (-6 * η)) (Molecule.gapAt L w κ K.x₁ K.x₂) ctr

/-- The class restricted to decorations with the joint gap `r`. -/
def AdmFix {g : ℝ} {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (K : Step1.VineCut g M) (Adm : (D → (Fin d → ℤ)) → Prop) (r : Fin d → ℤ) : (D → (Fin d → ℤ)) → Prop :=
  fun κ => Adm κ ∧ Step1.rint K κ = r

section
variable {g : ℝ} {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
  (K : Step1.VineCut g M)

/-- **Splitting by the joint gap.** -/
theorem labelSet_le_split (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (G : Finset (Fin d → ℤ))
    (hG : ∀ κ ∈ decSet M L γ δ w Adm c β k0, Step1.rint K κ ∈ G) (B : ℝ≥0∞)
    (hB : ∀ r ∈ G, ((K.labelSet L γ δ w (AdmFix K Adm r) c β k0).encard : ℝ≥0∞) ≤ B) :
    ((K.labelSet L γ δ w Adm c β k0).encard : ℝ≥0∞) ≤ (G.card : ℝ≥0∞) * B := by
  have hsub : K.labelSet L γ δ w Adm c β k0 ⊆ ⋃ r ∈ G, K.labelSet L γ δ w (AdmFix K Adm r) c β k0 := by
    rintro _ ⟨κ, hκ, rfl⟩
    refine Set.mem_iUnion₂.2 ⟨Step1.rint K κ, hG κ hκ, κ, ?_, rfl⟩
    exact ⟨hκ.1, hκ.2.1, hκ.2.2, rfl⟩
  have h1 := (Set.encard_le_encard hsub).trans (Finset.set_encard_biUnion_le G _)
  calc ((K.labelSet L γ δ w Adm c β k0).encard : ℝ≥0∞)
      ≤ ((∑ r ∈ G, (K.labelSet L γ δ w (AdmFix K Adm r) c β k0).encard : ℕ∞) : ℝ≥0∞) := by exact_mod_cast h1
    _ = ∑ r ∈ G, ((K.labelSet L γ δ w (AdmFix K Adm r) c β k0).encard : ℝ≥0∞) :=
        map_sum ENat.toENNRealRingHom _ _
    _ ≤ ∑ _r ∈ G, B := Finset.sum_le_sum hB
    _ = (G.card : ℝ≥0∞) * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- In a piece of the split, the joint gap is fixed: the ball of radius `L⁻¹` (any `ρ ≥ 0`) around it. -/
theorem ball_of_fix (L : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (r : Fin d → ℤ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (γ δ : ℝ) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) :
    ∃ r₀ : Mom d, ∀ κ ∈ decSet M L γ δ w (AdmFix K Adm r) c β k0,
      ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ ρ := by
  refine ⟨latticePoint L r, fun κ hκ => ?_⟩
  rw [Step1.gapAt_eq_lattice K L w κ, hκ.2.2.2, sub_self, norm_zero]
  exact hρ

/-- `DecScale` passes to a sub-class. -/
theorem decScale_fix (L : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (Q : (D → (Fin d → ℤ)) → Prop)
    (h : VineCount.DecScale M L w Adm Q) (r : Fin d → ℤ) : VineCount.DecScale M L w (AdmFix K Adm r) Q :=
  fun c κ hd hc hk => h c κ hd hc hk.1

/-- **The joint gaps of a class with the creation cone lie in `coneSet`.** -/
theorem rint_mem_coneSet (L : ℝ) (hL : 0 < L) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (γ δ η ρ : ℝ)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (ctr : Mom d)
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ ρ)
    (hc : ∀ κ ∈ decSet M L γ δ w Adm c β k0, InCone (L ^ (-6 * η)) (Molecule.gapAt L w κ K.x₁ K.x₂) ctr) :
    ∀ κ ∈ decSet M L γ δ w Adm c β k0, Step1.rint K κ ∈ coneSet d L ρ (L ^ (-6 * η)) ctr := by
  intro κ hκ
  have hg := Step1.gapAt_eq_lattice K L w κ
  refine mem_coneSet_of L hL _ _ ctr _ ?_ ?_
  · rw [← hg]; exact hgap κ hκ.2.2
  · rw [← hg]; exact hc κ hκ

end

/-- **The cone count in units of `(ρL)^d`**: `#coneSet ≤ 3·5^{d-1} θ^{d-1} (ρL)^d` when `ρL ≥ 1`, `θρL ≥ 1`. -/
theorem card_coneSet_le_rho (L ρ θ : ℝ) (hL : 0 < L) (hρL : 1 ≤ ρ * L) (hθρ : 1 ≤ θ * (ρ * L)) (hθ0 : 0 ≤ θ)
    (hd : 1 ≤ d) (ctr : Mom d) (hctr : ctr ≠ 0) :
    ((coneSet d L ρ θ ctr).card : ℝ) ≤ 3 * 5 ^ (d - 1) * θ ^ (d - 1) * (ρ * L) ^ d := by
  have hρ0 : 0 ≤ ρ := by
    by_contra h; push Not at h; nlinarith
  have hc := card_coneSet L hL ρ θ hρ0 hθ0 ctr hctr
  have hρL0 : 0 ≤ ρ * L := by linarith
  have h1 : ((2 * ⌊ρ * L⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * (ρ * L) := by
    push_cast; have := Nat.floor_le hρL0; linarith
  have h2 : ((⌊4 * θ * (ρ * L)⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * (θ * (ρ * L)) := by
    push_cast
    have := Nat.floor_le (show 0 ≤ 4 * θ * (ρ * L) by positivity)
    nlinarith
  calc ((coneSet d L ρ θ ctr).card : ℝ)
      ≤ (((2 * ⌊ρ * L⌋₊ + 1) * (⌊4 * θ * (ρ * L)⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast hc
    _ = ((2 * ⌊ρ * L⌋₊ + 1 : ℕ) : ℝ) * (((⌊4 * θ * (ρ * L)⌋₊ + 1 : ℕ) : ℝ)) ^ (d - 1) := by push_cast; ring
    _ ≤ (3 * (ρ * L)) * (5 * (θ * (ρ * L))) ^ (d - 1) := by gcongr
    _ = 3 * 5 ^ (d - 1) * θ ^ (d - 1) * (ρ * L) ^ (1 + (d - 1)) := by rw [pow_add, mul_pow, mul_pow]; ring
    _ = 3 * 5 ^ (d - 1) * θ ^ (d - 1) * (ρ * L) ^ d := by congr 2; omega

end WaveTurbulence.GammaLow.FinalCount.Ghost
