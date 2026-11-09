/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmVN12`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (VineNodeExists, part 12): the shape part of `VHard.hcls`.**
`doubleShape_of_card_three`: any vine cut of a loop-free molecule of degrees `<= 4` along an object with exactly three atoms is a
`DoubleShape` (the four darts at the middle atom are the mates of the joint darts).  So `hcls` only needs a classification of the
objects with `<> 3` atoms as single vines. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

section ds
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {N : Molecule V D}

theorem doubleShape_of_card_three (hnl : ∀ x, N.atom x ≠ N.atom (N.mate x)) (hdeg : ∀ b ∈ N.atoms, N.deg b ≤ 4)
    (K : Step1.VineCut Src.γL N) (hc : K.C.atoms.card = 3) : Nonempty (Step1.DoubleShape K) := by
  have hb := (object_oh K.C).basic
  obtain ⟨x, hx, hx1, hx2⟩ : ∃ x ∈ K.C.atoms, x ≠ K.C.upper ∧ x ≠ K.C.lower := by
    by_contra hcon
    push Not at hcon
    have hsub : K.C.atoms ⊆ {K.C.upper, K.C.lower} := fun v hv => by
      by_cases h1 : v = K.C.upper
      · simp [h1]
      · by_cases h2 : v = K.C.lower
        · simp [h2]
        · exact absurd (hcon v hv h1) h2
    have := Finset.card_le_card hsub
    have h2 := Finset.card_le_two (a := K.C.upper) (b := K.C.lower)
    omega
  have hatoms : K.C.atoms = {K.C.upper, x, K.C.lower} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact hb.2.1
      · exact hx
      · exact hb.2.2.1
    · rw [hc]
      have : ({K.C.upper, x, K.C.lower} : Finset V).card = 3 := by
        rw [Finset.card_eq_three]
        exact ⟨_, _, _, hx1.symm, K.ab_ne, hx2, rfl⟩
      omega
  have hxdeg : N.degIn K.C.atoms x = 4 := hb.2.2.2.2.2.2 x hx hx1 hx2
  have hxm : x ∈ N.atoms := hb.1 hx
  have hdx : (N.dartsAt x).card ≥ 4 := by
    have := Mole.degIn_le_deg N K.C.atoms x
    unfold Molecule.deg at this
    omega
  have hsub : N.dartsAt x ⊆ {N.mate K.x₁, N.mate K.x₂, N.mate K.y₁, N.mate K.y₂} := by
    intro z hz
    have hza : N.atom z = x := by simpa [Molecule.dartsAt] using hz
    have hcz : K.C.ContainsDart z := containsDart_of_interior K.C hdeg hb.2.2.2.2.2.2 (by rw [hza]; exact hx)
      (by rw [hza]; exact hx1) (by rw [hza]; exact hx2)
    have hcm : K.C.ContainsDart (N.mate z) := containsDart_mate K.C hcz
    have hmem : N.atom (N.mate z) ∈ K.C.atoms := (containsDart_inGroup K.C hcm).1
    have hne : N.atom (N.mate z) ≠ x := fun e => hnl z (by rw [hza, e])
    rw [hatoms] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · have := cd_at_joint_eq K.C (Or.inl rfl) (p := K.x₂) (q := K.x₁) K.Mx₂ K.Mx₁ K.in_a.2 K.in_a.1 K.Mout₂ K.Mout₁ h hcm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with e | e
      · right; left; rw [← e, N.mate_mate]
      · left; rw [← e, N.mate_mate]
    · exact absurd h hne
    · have := cd_at_joint_eq K.C (Or.inr rfl) (p := K.y₂) (q := K.y₁) K.My₂ K.My₁ K.in_b.2 K.in_b.1 K.Mouty₂ K.Mouty₁ h hcm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with e | e
      · right; right; right; rw [← e, N.mate_mate]
      · right; right; left; rw [← e, N.mate_mate]
  have hcard : ({N.mate K.x₁, N.mate K.x₂, N.mate K.y₁, N.mate K.y₂} : Finset D).card ≤ 4 := Finset.card_le_four
  exact ⟨⟨x, hxm, hx1, hx2, hatoms, Finset.eq_of_subset_of_card_le hsub (by omega)⟩⟩

end ds
end WaveTurbulence.GammaLow.FinalCount.H
