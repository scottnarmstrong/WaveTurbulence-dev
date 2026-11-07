/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Step5b
public import WaveTurbulence.Foundations.FinalCount.VCNew13
/-! **FINALCOUNT-G3 (step 5b, part 1): the flux identity through a bridge and `NewCompFixedUp`** (TARGET L2174).

`atoms_flux`: for an atom set `A` and an antisymmetric dart function `g` (`g (mate x) = - g x`), the sum of `g` over all darts at atoms of `A`
equals the sum over the boundary darts (atom in `A`, mate atom outside `A`).  If the boundary of `A` is exactly the two darts `x₁, x₂` of a
vine cut (the new component hanging at the upper joint), the decoration identity gives `k_{x₂} - k_{x₁} = Σ_A c_v` and the energy window gives
`| |k_{x₂}|² - |k_{x₁}|² - Σ_A β_v | ≤ |A| δ⁻¹ L^{-2γ}`: `NewCompFixedUp M K L γ δ |A| w Adm` (VINE-COUNT's form), with `n₀ ≠ 0` from the gap. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem atoms_flux {E : Type*} [AddCommGroup E] (M : Molecule V D) (A : Finset V) (g : D → E)
    (hg : ∀ x, g (M.mate x) = - g x) :
    ∑ v ∈ A, ∑ x ∈ M.dartsAt v, g x =
      ∑ x ∈ Finset.univ.filter (fun x => M.atom x ∈ A ∧ M.atom (M.mate x) ∉ A), g x := by
  have h2 : ∑ b ∈ A, ∑ x ∈ M.dartsAt b, g x = ∑ x ∈ Finset.univ.filter (fun x => M.atom x ∈ A), g x := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => M.atom x ∈ A)) (t := A)
      (g := M.atom) (fun x hx => (Finset.mem_filter.1 hx).2)]
    refine Finset.sum_congr rfl fun b hb => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hb, h⟩
    · intro h; exact h.2
  have h3 := Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun x => M.atom x ∈ A))
    (fun x => M.atom (M.mate x) ∈ A) g
  have h4 : ∑ x ∈ (Finset.univ.filter (fun x => M.atom x ∈ A)).filter (fun x => M.atom (M.mate x) ∈ A), g x = 0 := by
    refine Finset.sum_involution (fun x _ => M.mate x) (fun x hx => ?_) (fun x hx hne => ?_) (fun x hx => ?_)
      (fun x hx => M.mate_mate x)
    · rw [hg x]; abel
    · exact fun e => M.mate_ne x e
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.2, by rw [M.mate_mate]; exact hx.1⟩
  have h5 : (Finset.univ.filter (fun x => M.atom x ∈ A)).filter (fun x => ¬ M.atom (M.mate x) ∈ A) =
      Finset.univ.filter (fun x => M.atom x ∈ A ∧ M.atom (M.mate x) ∉ A) := by
    ext x; simp [Finset.mem_filter]
  rw [h2, ← h3, h4, zero_add, h5]

variable {M : Molecule V D}

/-- If the boundary of `A` is `{x₁, x₂}` (a new component hanging at the upper joint), `NewCompFixedUp` with `ν = |A|`. -/
theorem newCompFixedUp_of_boundary (hd : 0 < d) (K : VineCut M) {L γ δ : ℝ} (hL : L ≠ 0) {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} (A : Finset V) (hA : A ⊆ M.atoms)
    (hbd : ∀ x, M.atom x ∈ A → M.atom (M.mate x) ∉ A → x = K.x₁ ∨ x = K.x₂)
    (h1 : M.atom K.x₁ ∈ A ∧ M.atom (M.mate K.x₁) ∉ A) (h2 : M.atom K.x₂ ∈ A ∧ M.atom (M.mate K.x₂) ∉ A)
    (hgap : ∀ κ, Adm κ → κ K.x₁ ≠ κ K.x₂) :
    NewCompFixedUp M K L γ δ (A.card : ℝ) w Adm := by
  intro c β k0 _
  have hbdry : Finset.univ.filter (fun x => M.atom x ∈ A ∧ M.atom (M.mate x) ∉ A) = {K.x₁, K.x₂} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h; exact hbd x h.1 h.2
    · rintro (rfl | rfl)
      · exact h1
      · exact h2
  have hx12 : K.x₁ ≠ K.x₂ := K.x₁_ne_x₂
  have hflux : ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      Molecule.kvec L w κ K.x₂ - Molecule.kvec L w κ K.x₁ = ∑ v ∈ A, c v := by
    intro κ hκ
    have hdec := hκ.1
    have hg : ∀ x, (fun x => M.dartSign x • Molecule.kvec L w κ x) (M.mate x) =
        - (fun x => M.dartSign x • Molecule.kvec L w κ x) x := by
      intro x
      simp only [Molecule.kvec, hdec.1 x, dartSign_mate, neg_smul]
    have := atoms_flux M A (fun x => M.dartSign x • Molecule.kvec L w κ x) hg
    rw [hbdry, Finset.sum_pair hx12] at this
    have e1 : ∑ v ∈ A, ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x = ∑ v ∈ A, c v :=
      Finset.sum_congr rfl fun v hv => hdec.2 v (hA hv)
    rw [e1] at this
    rw [this]
    simp only [Molecule.dartSign, K.Mout₁, K.Mout₂]
    simp; abel
  have henergy : ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      ‖Molecule.kvec L w κ K.x₂‖ ^ 2 - ‖Molecule.kvec L w κ K.x₁‖ ^ 2 = ∑ v ∈ A, M.Gamma L w κ v := by
    intro κ hκ
    have hdec := hκ.1
    have hg : ∀ x, (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) (M.mate x) =
        - (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) x := by
      intro x
      simp only [Molecule.kvec, hdec.1 x, dartSign_mate]; ring
    have := atoms_flux M A (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) hg
    rw [hbdry, Finset.sum_pair hx12] at this
    unfold Molecule.Gamma
    rw [this]
    simp only [Molecule.dartSign, K.Mout₁, K.Mout₂]
    simp; ring
  have hlat : ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      latticePoint L (κ K.x₁ - κ K.x₂) = - ∑ v ∈ A, c v := by
    intro κ hκ
    have := hflux κ hκ
    rw [FinalCount.latticePoint_sub]
    simp only [Molecule.kvec] at this
    rw [← neg_sub, ← this]
    abel
  by_cases hex : ∃ κ₀, κ₀ ∈ decSet M L γ δ w Adm c β k0
  · obtain ⟨κ₀, hκ₀⟩ := hex
    refine ⟨κ₀ K.x₁ - κ₀ K.x₂, sub_ne_zero.2 (hgap κ₀ hκ₀.2.2), ∑ v ∈ A, β v, fun κ hκ => ⟨?_, ?_⟩⟩
    · exact latticePoint_injective L hL ((hlat κ hκ).trans (hlat κ₀ hκ₀).symm)
    · rw [henergy κ hκ, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ v ∈ A, |M.Gamma L w κ v - β v| ≤ ∑ _v ∈ A, δ⁻¹ * L ^ (-2 * γ) :=
            Finset.sum_le_sum fun v hv => hκ.2.1.1 v (hA hv)
        _ = (A.card : ℝ) * δ⁻¹ * L ^ (-2 * γ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
  · push Not at hex
    refine ⟨fun _ => 1, ?_, 0, fun κ hκ => absurd hκ (hex κ)⟩
    intro h
    have := congrFun h ⟨0, hd⟩
    simp at this

end WaveTurbulence.FinalCountG3
