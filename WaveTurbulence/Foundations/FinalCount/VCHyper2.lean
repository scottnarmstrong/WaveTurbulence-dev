/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCHyper1
/-! # VINE-COUNT part 27: the removed vine of a hyper object, in `M` and in its adjoint.

`adjEquiv` is the bijection of darts between the removed vine of the adjoint cut and the removed vine of `K`; with
`VCIso` it gives equal maximal ladders (hence equal `ladderProdVC`), ladder gaps, atoms and bond counts. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
  {M : Molecule V D} (K : VineCut M) (R : HyperLikeRealization M K.C.atoms K.C.upper K.C.lower)
  (h : K.C.shape = .hyper R)

include h in
theorem pdart_ne_added (x : PDart K.cutMol (fun a => ¬ (a ∉ K.C.atoms))) :
    x.1 ≠ R.added ∧ x.1 ≠ M.mate R.added := by
  constructor
  · intro e
    have := x.2
    rw [e] at this
    exact cutMol_atom_added K R h (not_not.mp this)
  · intro e
    have := x.2
    rw [e] at this
    exact cutMol_atom_added_mate K R h (not_not.mp this)

include h in
/-- The darts of the removed vine of the adjoint cut are the darts of the removed vine of `K`. -/
def adjEquiv : PDart (adjointCut K R h).cutMol (fun a => ¬ (a ∉ K.C.atoms)) ≃
    PDart K.cutMol (fun a => ¬ (a ∉ K.C.atoms)) where
  toFun y := ⟨y.1.1, by have := y.2; rwa [adj_cutMol_atom K R h] at this⟩
  invFun x := ⟨⟨x.1, (pdart_ne_added K R h x)⟩, by
      rw [adj_cutMol_atom K R h]; exact x.2⟩
  left_inv y := rfl
  right_inv x := rfl


section IsoFacts
include h

theorem adj_iso_atom (x : PDart (adjointCut K R h).cutMol (fun a => ¬ (a ∉ K.C.atoms))) :
    K.vc.atom (adjEquiv K R h x) = (adjointCut K R h).vc.atom x :=
  (adj_cutMol_atom K R h x.1).symm

theorem adj_iso_mate (x : PDart (adjointCut K R h).cutMol (fun a => ¬ (a ∉ K.C.atoms))) :
    K.vc.mate (adjEquiv K R h x) = adjEquiv K R h ((adjointCut K R h).vc.mate x) := rfl

theorem adj_iso_out (x : PDart (adjointCut K R h).cutMol (fun a => ¬ (a ∉ K.C.atoms))) :
    K.vc.out (adjEquiv K R h x) = (adjointCut K R h).vc.out x := rfl

theorem adj_iso_atoms : (adjointCut K R h).vc.atoms = K.vc.atoms := rfl

/-- The removed vine of the adjoint cut has the same maximal ladders. -/
theorem adj_maximalLadders : (adjointCut K R h).vc.maximalLadders = K.vc.maximalLadders :=
  (iso_maximalLadders (adjEquiv K R h) (adj_iso_atom K R h) (adj_iso_mate K R h) (adj_iso_out K R h)
    (adj_iso_atoms K R h)).symm

theorem adj_ladderProdVC (L γ δ : ℝ) (P : Finset V → ℝ) :
    (adjointCut K R h).ladderProdVC L γ δ P = K.ladderProdVC L γ δ P := by
  unfold VineCut.ladderProdVC
  rw [adj_maximalLadders K R h]

theorem adj_bonds_card : (adjointCut K R h).vc.bonds.card = K.vc.bonds.card :=
  (iso_bonds_card (adjEquiv K R h) (adj_iso_atom K R h) (adj_iso_mate K R h) (adj_iso_out K R h)).symm

/-- The ladder-scale restriction passes from the hyper cut to its adjoint cut. -/
theorem adj_vcLadderScale (L : ℝ) (w : Mom d) (P : Finset V → ℝ) {κ : D → (Fin d → ℤ)}
    (hs : VCLadderScale K L w P κ) :
    VCLadderScale (adjointCut K R h) L w P (fun y => κ y.1) := by
  intro S' hS' m u v hlad hat r hr
  rw [adj_maximalLadders K R h] at hS'
  have hlad' : K.vc.IsLadder u v :=
    (iso_isLadder (adjEquiv K R h) (adj_iso_atom K R h) (adj_iso_mate K R h) (adj_iso_out K R h)
      (adj_iso_atoms K R h) u v).2 hlad
  have hr' : K.vc.IsLadderGap L w (fun x => κ x.1) u v hlad'.1 r :=
    (iso_ladderGap (adjEquiv K R h) (adj_iso_atom K R h) (adj_iso_mate K R h) (adj_iso_out K R h) (adj_iso_atoms K R h) u v hlad.1 L w
      (fun x => κ x.1.1) (fun x => κ x.1) (fun x => rfl) r).2 hr
  exact hs S' hS' m u v hlad' hat r hr'

end IsoFacts

end WaveTurbulence.VineCount
