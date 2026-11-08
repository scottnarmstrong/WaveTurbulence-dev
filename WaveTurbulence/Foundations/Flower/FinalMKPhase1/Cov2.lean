/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov1

/-! # C1b1 MK-PHASE1 (13): cut data of a matched object (coverage, part 2)

`vineDataA`: main's `vineDataL_of_intact` (LowChain22) for an object present through a renaming `π` (`MatchA`): a vine
cut `K` of the state along the transported object with the fresh names `fresh3 h 0, 1`, node darts in `U`, joints
`π U.upper`, `π U.lower` (so `anc` of the joints are the joints of `U`), the joint pairs, the `SG` gap of the first pair
and the twin relation; every cut with these atoms is a single vine when `U` is one. Copied by source. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **Cut data of a matched object** (main's `vineDataL_of_intact` with the renaming `π`). -/
theorem vineDataA [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hM₀ : M₀.IsMolecule) (hS : SubHypL Rn M₀)
    {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} (hmate : ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h : HSt V D₀) (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    (hinj : ∀ c ∈ h.s.M.atoms, ∀ e ∈ h.s.M.atoms, h.anc c = h.anc e → c = e)
    (hdeg : ∀ b ∈ h.s.M.atoms, h.s.M.deg b ≤ 4) (U : Object M₀) {π : V → V} (hm : MatchA h U π)
    (hsg : U.HasGapKind L γ η w κ .SG) :
    ∃ K : VineCut h.s.M, K.C.atoms = U.atoms.image π ∧ K.C.upper = π U.upper ∧ K.C.lower = π U.lower ∧
      K.fa = fresh3 h 0 ∧ K.fb = fresh3 h 1 ∧
      (U.ContainsDart (h.s.down K.x₁) ∧ U.ContainsDart (h.s.down K.x₂) ∧ U.ContainsDart (h.s.down K.y₁) ∧
        U.ContainsDart (h.s.down K.y₂)) ∧
      (M₀.atom (h.s.down K.x₁) = U.upper ∧ M₀.atom (h.s.down K.y₁) = U.lower) ∧
      SourceObjectJointPair U U.upper (h.s.down K.x₂) (h.s.down K.x₁) ∧
      SourceObjectJointPair U U.lower (h.s.down K.y₂) (h.s.down K.y₁) ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG ∧
      pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂) ∧
      (ObjVine M₀ U → ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → SingleVineVC K') := by
  have hnl : ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := by
    intro x e
    apply hS.noloop (h.s.down x)
    have e1 := hA.atom x
    have e2 := hA.atom (h.s.M.mate x)
    rw [← hD.mate] at e2
    rw [e1, e2, e]
  obtain ⟨hf0, hf1⟩ := fresh3_spec h
  have hfab : fresh3 h 0 ≠ fresh3 h 1 := fun e => by have := hf0 e; simp at this
  obtain ⟨Ũ, hatoms, hup, hlo, hcd, hsv⟩ := stateObjA_spec hA hD hinj hm
  obtain ⟨K, hKC, hKfa, hKfb⟩ := exists_vineCut_of_object Ũ hdeg hnl (fresh3 h 0) (fresh3 h 1) (hf1 0) (hf1 1) hfab
  have hUup : U.upper ∈ U.atoms := object_mem_of_joint U (Or.inl rfl)
  have hUlo : U.lower ∈ U.atoms := object_mem_of_joint U (Or.inr rfl)
  have hKup : K.C.upper = π U.upper := by rw [hKC]; exact hup
  have hKlo : K.C.lower = π U.lower := by rw [hKC]; exact hlo
  have hCD : ∀ z, K.C.ContainsDart z ↔ U.ContainsDart (h.s.down z) := fun z => by rw [hKC]; exact hcd z
  have hMx₁ : M₀.atom (h.s.down K.x₁) = U.upper := by rw [hA.atom, K.Mx₁, hKup]; exact hm.anc _ hUup
  have hMx₂ : M₀.atom (h.s.down K.x₂) = U.upper := by rw [hA.atom, K.Mx₂, hKup]; exact hm.anc _ hUup
  have hMy₁ : M₀.atom (h.s.down K.y₁) = U.lower := by rw [hA.atom, K.My₁, hKlo]; exact hm.anc _ hUlo
  have hMy₂ : M₀.atom (h.s.down K.y₂) = U.lower := by rw [hA.atom, K.My₂, hKlo]; exact hm.anc _ hUlo
  have PU : SourceObjectJointPair U U.upper (h.s.down K.x₂) (h.s.down K.x₁) :=
    ⟨hMx₂, hMx₁, (hCD _).mp K.in_a.2, (hCD _).mp K.in_a.1, by rw [hD.out]; exact K.Mout₂, by rw [hD.out]; exact K.Mout₁⟩
  have PL : SourceObjectJointPair U U.lower (h.s.down K.y₂) (h.s.down K.y₁) :=
    ⟨hMy₂, hMy₁, (hCD _).mp K.in_b.2, (hCD _).mp K.in_b.1, by rw [hD.out]; exact K.Mouty₂,
      by rw [hD.out]; exact K.Mouty₁⟩
  refine ⟨K, by rw [hKC, hatoms], hKup, hKlo, hKfa, hKfb, ⟨(hCD _).mp K.in_a.1, (hCD _).mp K.in_a.2,
    (hCD _).mp K.in_b.1, (hCD _).mp K.in_b.2⟩, ⟨hMx₁, hMy₁⟩, PU, PL, ?_, ?_, ?_⟩
  · have := object_gapKind_pair U L γ η w κ .SG hsg PU
    rw [gapAt_comp_down]
    have e : Molecule.gapAt L w κ (h.s.down K.x₁) (h.s.down K.x₂) =
        -Molecule.gapAt L w κ (h.s.down K.x₂) (h.s.down K.x₁) := by
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
  · intro hov K' hK'
    exact hsv K' (hK'.trans (by rw [hKC, hatoms])) hov

end WaveTurbulence.Flower.FinalMKPhase1
