/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew11
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCNew12`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 34 (session 4): the fixed-set fact at the UPPER joint implies it at the lower joint.

`NewCompFixed` is stated with the lower-joint energy `|k_{y₂}|² - |k_{y₁}|²`. If the new component is attached to the vine
at the upper joint, the natural fact is the same statement for `|k_{x₂}|² - |k_{x₁}|²`; the energies of the `m` atoms of the
vine sum to zero (every bond of the block is internal) and the interior windows give
`lowerG + upperG + ∑_{interior} β_v = O((m-2)τ)`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The energy of the two bonds of the removed vine at its upper joint: `|k_{x₂}|² - |k_{x₁}|²`. -/
noncomputable def upperG {M : Molecule V D} (K : VineCut g M) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) : ℝ :=
  ‖Molecule.kvec L w κ K.x₂‖ ^ 2 - ‖Molecule.kvec L w κ K.x₁‖ ^ 2

section Sum
variable {M : Molecule V D} (K : VineCut g M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower)
include hB

theorem energy_upper_eq (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) :
    energy M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1) K.C.upper = - upperG K L w κ := by
  have hk : ∀ x, ‖Molecule.kvec L w κ (M.mate x)‖ ^ 2 = ‖Molecule.kvec L w κ x‖ ^ 2 := by
    intro x; simp [Molecule.kvec, hκ x]
  have h := sum_bond_incidence M K.C.atoms K.C.upper (fun x => ‖Molecule.kvec L w κ x‖ ^ 2) hk
  rw [group_at_a K hB, Finset.sum_pair (x₁_ne_x₂ K hB)] at h
  simp only [smul_eq_mul, Molecule.dartSign, x₁_out K, x₂_out K] at h
  unfold energy upperG
  simp only [Bool.false_eq_true, ite_false, ite_true] at h
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [h]; ring

omit hB in
/-- The energies of all atoms of a block sum to zero (each bond of the block is internal). -/
theorem sum_energy_zero (S : Finset V) (k : Bond M S → Mom d) :
    ∑ v ∈ S, energy M S k v = 0 := by
  unfold energy
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hin : e.1 ∈ internalBondSet M S := e.2
  unfold internalBondSet at hin
  obtain ⟨-, hg⟩ := Finset.mem_filter.mp hin
  obtain ⟨h1, h2⟩ := hg
  have hs : ∑ v ∈ S, (incidence M v e.1 : ℝ) = 0 := by
    unfold incidence
    push_cast
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq, h1, h2]
  calc ∑ v ∈ S, -(incidence M v e.1 : ℝ) * ‖k e‖ ^ 2 = -(∑ v ∈ S, (incidence M v e.1 : ℝ)) * ‖k e‖ ^ 2 := by
        rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    _ = 0 := by rw [hs]; simp

theorem lower_upper_sum (hM : ∀ v ∈ M.atoms, M.deg v ≤ 4) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (hκ : ∀ x, κ (M.mate x) = κ x) :
    lowerG K L w κ + upperG K L w κ + ∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, M.Gamma L w κ v = 0 := by
  have h0 := sum_energy_zero (M := M) K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1)
  have hb : K.C.lower ∈ K.C.atoms.erase K.C.upper := Finset.mem_erase.mpr ⟨K.ab_ne.symm, K.b_mem⟩
  rw [← Finset.add_sum_erase K.C.atoms _ K.a_mem, ← Finset.add_sum_erase _ _ hb] at h0
  rw [energy_upper_eq K hB L w κ hκ, energy_lower_eq K hB L w κ hκ] at h0
  have hint : ∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower,
      energy M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1) v =
      - ∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, M.Gamma L w κ v := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨hvb, hv'⟩ := Finset.mem_erase.mp hv
    obtain ⟨hva, hvS⟩ := Finset.mem_erase.mp hv'
    exact energy_interior_eq hB hM hvS hva hvb L w κ hκ
  rw [hint] at h0
  linarith

end Sum


/-- The fixed-set fact at the UPPER joint (the new component is attached at `a`): as `NewCompFixed`, with the upper-joint
energy `|k_{x₂}|² - |k_{x₁}|²` in an interval of radius `ν' δ⁻¹ L^{-2γ}`. -/
def NewCompFixedUp (M : Molecule V D) (K : VineCut g M) (L γ δ ν : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    ∃ n₀ : Fin d → ℤ, n₀ ≠ 0 ∧ ∃ e₀ : ℝ, ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      κ K.x₁ - κ K.x₂ = n₀ ∧
      |‖Molecule.kvec L w κ K.x₂‖ ^ 2 - ‖Molecule.kvec L w κ K.x₁‖ ^ 2 - e₀| ≤ ν * δ⁻¹ * L ^ (-2 * γ)

/-- **Upper joint to lower joint**: `NewCompFixedUp` with radius `ν'` gives `NewCompFixed` with radius `ν' + (m-2)`. -/
theorem newCompFixed_of_upper {M : Molecule V D} (K : VineCut g M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower)
    (hM : ∀ v ∈ M.atoms, M.deg v ≤ 4) {L γ δ ν' : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop}
    (h : NewCompFixedUp M K L γ δ ν' w Adm) :
    NewCompFixed M K L γ δ (ν' + (((K.C.atoms.erase K.C.upper).erase K.C.lower).card : ℝ)) w Adm := by
  intro c β k0 hP
  obtain ⟨n₀, hn₀, e₀', hne⟩ := h c β k0 hP
  refine ⟨n₀, hn₀, -e₀' - ∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, β v, fun κ hκ => ⟨(hne κ hκ).1, ?_⟩⟩
  have hsum := lower_upper_sum K hB hM L w κ hκ.1.1
  have hu := (hne κ hκ).2
  have hwin : ∀ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, |M.Gamma L w κ v - β v| ≤ δ⁻¹ * L ^ (-2 * γ) :=
    fun v hv => hκ.2.1.1 v (hB.1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv)))
  have hSum : |∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, (M.Gamma L w κ v - β v)| ≤
      (((K.C.atoms.erase K.C.upper).erase K.C.lower).card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hwin).trans ?_
    simp
  rw [Finset.sum_sub_distrib] at hSum
  have e : lowerG K L w κ - (-e₀' - ∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, β v) =
      -(∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, M.Gamma L w κ v -
        ∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, β v) - (upperG K L w κ - e₀') := by
    linarith
  show |lowerG K L w κ - (-e₀' - ∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, β v)| ≤ _
  rw [e]
  unfold upperG at hu
  have h1 := abs_sub (-(∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, M.Gamma L w κ v -
        ∑ v ∈ (K.C.atoms.erase K.C.upper).erase K.C.lower, β v)) (‖Molecule.kvec L w κ K.x₂‖ ^ 2 -
        ‖Molecule.kvec L w κ K.x₁‖ ^ 2 - e₀')
  rw [abs_neg] at h1
  calc _ ≤ _ := h1
    _ ≤ _ := by nlinarith [hSum, hu]

end WaveTurbulence.GammaLow.FinalCount.Step1
