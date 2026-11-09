/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper2
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCHyper3`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 28: the label count `𝔉` for a hyper object whose adjoint is a single vine.

DH23 L1796 ("`𝕍ℂ` ... is `𝕌` or `𝕌` minus a bond in case of HV or HVC") and L1799--L1801: the labels counted are those of the
bonds of the removed VC, i.e. of the adjoint; the deleted bond between the joints carries a label that is not counted
(it stays in `𝕄_pos` between the two new `α`-atoms).  The restricted labels of `K` are the restrictions of the labels of
the adjoint `eraseBond M R.added`; there the interior atoms keep their dart sets, so the facts used by the count
(`GoodLabel`) hold (only degree-`4` atoms enter, and the joints have degree `≤ 3` after the deletion). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
  {M : Molecule V D} (K : VineCut g M) (R : Src.HyperLikeRealization g M K.C.atoms K.C.upper K.C.lower)
  (h : K.C.shape = .hyper R)

include h in
theorem added_nonloop : M.atom R.added ≠ M.atom (M.mate R.added) := by
  intro e
  have e2 := R.ends_eq
  unfold Molecule.ends at e2
  rw [← e] at e2
  rcases Sym2.eq_iff.mp e2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact K.ab_ne (h1.symm.trans h2)
  · exact K.ab_ne (h2.symm.trans h1)

include h in
/-- A restricted label of `M` restricts to a label of the adjoint to which the count applies. -/
theorem good_of_hyper (hMol : M.IsMolecule) (L γ δ : ℝ) (w : Mom d) (P : Finset V → ℝ) (β : V → ℝ)
    (k0 : D → Mom d) (r₀ : Mom d) (ρ : ℝ) {κ : D → (Fin d → ℤ)} {c : V → Mom d}
    (hdec : M.IsDecoration L w c κ) (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0)
    (hres : M.IsRestricted L γ δ w β k0 κ) (hs : VCLadderScale K L w P κ)
    (hb : ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ ρ) :
    GoodLabel (Molecule.eraseBond M R.added) (adjointCut K R h) L γ δ w P β (fun y => k0 y.1) r₀ ρ
      (fun y => κ y.1) := by
  have hne := added_nonloop K R h
  obtain ⟨c', hd', hc'⟩ := Vine.eraseBond_decoration_exists M hMol R.added hne L w c κ hdec hc
  have hend := Vine.eraseBond_endpoint_degree_le_three M hMol R.added hne
  refine ⟨c', hd', hc', ?_, fun x => hres.2 x.1, adj_vcLadderScale K R h L w P hs, hb⟩
  intro v hv hdeg
  have hv1 : M.atom R.added ≠ v := by
    intro he; have hh := he ▸ hend.1; change (Mole.eraseBond M R.added).deg v ≤ 3 at hh
    change (Mole.eraseBond M R.added).deg v = 4 at hdeg; omega
  have hv2 : M.atom (M.mate R.added) ≠ v := by
    intro he; have hh := he ▸ hend.2; change (Mole.eraseBond M R.added).deg v ≤ 3 at hh
    change (Mole.eraseBond M R.added).deg v = 4 at hdeg; omega
  have hsum := Vine.eraseBond_local_sum (W := ℝ) M R.added v hv1 hv2 (fun x => ‖Molecule.kvec L w κ x‖ ^ 2)
  have hG : (Molecule.eraseBond M R.added).Gamma L w (fun y => κ y.1) v = M.Gamma L w κ v := by
    unfold Molecule.Gamma
    simp only [smul_eq_mul] at hsum
    exact hsum
  rw [hG]
  exact hres.1 v hv

end WaveTurbulence.GammaLow.FinalCount.Step1
