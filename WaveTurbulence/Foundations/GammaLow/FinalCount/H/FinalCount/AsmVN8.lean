/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmVN8`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (VineNodeExists, part 8): the cut data of an intact collected object in the state.**  `vineData_of_intact`:
for an intact object `U` with `κ`-gap kind `SG`, there is a `VineCut K` of the state along the transported copy of `U` with fresh
`fa = fresh3 h 0`, `fb = fresh3 h 1`, whose four darts lie over the `ContainsDart` darts of `U`, with the twin gaps and the
`SG`-gap of the first pair. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **Cut data of an intact object.** -/
theorem vineData_of_intact [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hM₀ : M₀.IsMolecule) (hS : SubHyp Rn M₀) {L γ η : ℝ} {w : Mom d}
    {κ : D₀ → (Fin d → ℤ)} (hmate : ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h : HSt V D₀) (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) (hdeg : ∀ b ∈ h.s.M.atoms, h.s.M.deg b ≤ 4)
    (U : Src.Object Src.γL M₀) (hint : UIntact U h) (hsg : U.HasGapKind L γ η w κ .SG) :
    ∃ K : Step1.VineCut Src.γL h.s.M, K.C.atoms = U.atoms ∧ K.C.upper = U.upper ∧ K.C.lower = U.lower ∧ K.fa = fresh3 h 0 ∧
      K.fb = fresh3 h 1 ∧
      (U.ContainsDart (h.s.down K.x₁) ∧ U.ContainsDart (h.s.down K.x₂) ∧ U.ContainsDart (h.s.down K.y₁) ∧
        U.ContainsDart (h.s.down K.y₂)) ∧
      (M₀.atom (h.s.down K.x₁) = U.upper ∧ M₀.atom (h.s.down K.y₁) = U.lower) ∧
      SourceObjectJointPair U U.upper (h.s.down K.x₂) (h.s.down K.x₁) ∧
      SourceObjectJointPair U U.lower (h.s.down K.y₂) (h.s.down K.y₁) ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG ∧
      pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂) := by
  have hnl : ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := by
    intro x e
    apply hS.noloop (h.s.down x)
    have e1 := hA.atom x
    have e2 := hA.atom (h.s.M.mate x)
    rw [← hD.mate] at e2
    rw [e1, e2, e]
  obtain ⟨hf0, hf1⟩ := fresh3_spec h
  have hfab : fresh3 h 0 ≠ fresh3 h 1 := fun e => by have := hf0 e; simp at this
  obtain ⟨Ũ, hatoms, hup, hlo, hcd, -⟩ := stateObj_spec hA hD U hint
  obtain ⟨K, hKC, hKfa, hKfb⟩ := exists_vineCut_of_object Ũ hdeg hnl (fresh3 h 0) (fresh3 h 1) (hf1 0) (hf1 1) hfab
  have hUup : U.upper ∈ U.atoms := object_mem_of_joint U (Or.inl rfl)
  have hUlo : U.lower ∈ U.atoms := object_mem_of_joint U (Or.inr rfl)
  have hKup : K.C.upper = U.upper := by rw [hKC]; exact hup
  have hKlo : K.C.lower = U.lower := by rw [hKC]; exact hlo
  have hCD : ∀ z, K.C.ContainsDart z ↔ U.ContainsDart (h.s.down z) := fun z => by rw [hKC]; exact hcd z
  have hMx₁ : M₀.atom (h.s.down K.x₁) = U.upper := by
    rw [hA.atom, K.Mx₁, hKup]; exact hA.eps _ (hint _ hUup).1 (hint _ hUup).2
  have hMx₂ : M₀.atom (h.s.down K.x₂) = U.upper := by
    rw [hA.atom, K.Mx₂, hKup]; exact hA.eps _ (hint _ hUup).1 (hint _ hUup).2
  have hMy₁ : M₀.atom (h.s.down K.y₁) = U.lower := by
    rw [hA.atom, K.My₁, hKlo]; exact hA.eps _ (hint _ hUlo).1 (hint _ hUlo).2
  have hMy₂ : M₀.atom (h.s.down K.y₂) = U.lower := by
    rw [hA.atom, K.My₂, hKlo]; exact hA.eps _ (hint _ hUlo).1 (hint _ hUlo).2
  have PU : SourceObjectJointPair U U.upper (h.s.down K.x₂) (h.s.down K.x₁) :=
    ⟨hMx₂, hMx₁, (hCD _).mp K.in_a.2, (hCD _).mp K.in_a.1, by rw [hD.out]; exact K.Mout₂, by rw [hD.out]; exact K.Mout₁⟩
  have PL : SourceObjectJointPair U U.lower (h.s.down K.y₂) (h.s.down K.y₁) :=
    ⟨hMy₂, hMy₁, (hCD _).mp K.in_b.2, (hCD _).mp K.in_b.1, by rw [hD.out]; exact K.Mouty₂, by rw [hD.out]; exact K.Mouty₁⟩
  refine ⟨K, by rw [hKC, hatoms], hKup, hKlo, hKfa, hKfb, ⟨(hCD _).mp K.in_a.1, (hCD _).mp K.in_a.2, (hCD _).mp K.in_b.1,
    (hCD _).mp K.in_b.2⟩, ⟨hMx₁, hMy₁⟩, PU, PL, ?_, ?_⟩
  · have := object_gapKind_pair U L γ η w κ .SG hsg PU
    rw [gapAt_comp_down]
    have e : Molecule.gapAt L w κ (h.s.down K.x₁) (h.s.down K.x₂) = -Molecule.gapAt L w κ (h.s.down K.x₂) (h.s.down K.x₁) := by
      simp [Molecule.gapAt]
    rw [e, gapKind_neg]; exact this
  · have htw := object_gap_twin U (fun b hb => Mole.deg_le_four M₀ hM₀ hb) (Molecule.kvec L w κ)
      (fun x => by simp [Molecule.kvec, hmate]) h0 PU PL
    unfold pgap
    simp only [St.pr, Molecule.gapAt]
    rw [eq_neg_iff_add_eq_zero]
    calc _ = -((Molecule.kvec L w κ (h.s.down K.x₂) - Molecule.kvec L w κ (h.s.down K.x₁)) +
          (Molecule.kvec L w κ (h.s.down K.y₂) - Molecule.kvec L w κ (h.s.down K.y₁))) := by abel
      _ = 0 := by rw [htw, neg_zero]

end WaveTurbulence.GammaLow.FinalCount.H
