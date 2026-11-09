/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.S1Erase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Basic
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.Invariance
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.S1Erase`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# Stage 1 combinatorics: deleting a bond outside a group, and unions at one joint

Deleting a bond that is not internal to an atomic group `S` does not change `S` as a block, a vine
or a vine chain.  This transports ordinary chains into the adjoint molecule, and gives the union
of two chains meeting in one joint as a designated vine-like object (a VC, or an HVC when the outer
joints are joined by a bond).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- Low-family form of main's `isVine_eraseBond` (L6-HG3): erasing a bond outside the group keeps a member of the
family (T-vines: L6-HTV's `isTVine_map_of_groupBonds` along `id`). -/
theorem isSomeVine_eraseBond {S : Finset V} {a b : V} (e : D) (hV : Src.IsSomeVine Src.γL M S a b)
    (he : ¬ M.InGroup S e) : Src.IsSomeVine Src.γL (Molecule.eraseBond M e) S a b := by
  rcases hV.cases with h | h | h
  · exact Src.isSomeVine_of_I (isVine_eraseBond e h he)
  · exact Src.isSomeVine_of_II (isVine_eraseBond e h he)
  · refine Src.isSomeVine_of_T ?_
    exact TV.isTVine_map_of_groupBonds (φ := id) (M' := Molecule.eraseBond M e) (Set.injOn_id _)
      Finset.image_id.symm (by rw [eraseBond_groupBonds_eq e he, Sym2.map_id, Multiset.map_id])
      (isBlock_eraseBond e h.1 he) h

theorem chain_eraseBond {S : Finset V} {a b : V} {n : ℕ} (e : D) (h : Src.Chain Src.γL M S a b n)
    (he : ¬ M.InGroup S e) : Src.Chain Src.γL (Molecule.eraseBond M e) S a b n := by
  induction h with
  | single hv =>
    have hX := hv
    exact Src.Chain.single (isSomeVine_eraseBond e hX he)
  | @append S' T a b c n hS hT hi hne ih =>
    have hX := hT
    refine Src.Chain.append (ih (fun h' => he (inGroup_mono subset_union_left h'))) (isSomeVine_eraseBond e hX
      (fun h' => he (inGroup_mono subset_union_right h'))) hi hne

/-- A chain `P` from `a` to `c` and a chain `Q` from `c` to `b` meeting exactly in `c`, both
ordinary blocks: the union is a designated vine-like object (a VC, or an HVC if the outer joints
are joined by a further bond). -/
theorem exists_object_union (hM : M.IsMolecule) {P Q : Finset V} {a b c : V} {n m : ℕ}
    (hP : Src.Chain Src.γL M P a c n) (hQ : Src.Chain Src.γL M Q c b m) (hPQ : P ∩ Q = {c})
    (hPB : M.IsBlock P a c) (hQB : M.IsBlock Q c b) :
    ∃ W : Src.Object Src.γL M, W.atoms = P ∪ Q ∧ W.upper = a ∧ W.lower = b := by
  have hcon := Mole.blocks_concatenate M hM hPB (Mole.block_swap_joints M hQB) (groupConnected_of_block hPB) hPQ
  rcases hcon with hU | ⟨e, he, hBe⟩
  · exact ⟨⟨P ∪ Q, a, b, .vc ⟨hU, n + m, chain_append_chain hP hQ hPQ⟩⟩, rfl, rfl, rfl⟩
  · have hbP : b ∉ P := by
      intro hb
      have : b ∈ P ∩ Q := mem_inter.mpr ⟨hb, (chain_ends hQ).2.1⟩
      rw [hPQ] at this
      exact (chain_ends hQ).2.2 (mem_singleton.mp this).symm
    have haQ : a ∉ Q := by
      intro ha
      have : a ∈ P ∩ Q := mem_inter.mpr ⟨(chain_ends hP).1, ha⟩
      rw [hPQ] at this
      exact (chain_ends hP).2.2 (mem_singleton.mp this)
    have hend := Sym2.eq_iff.mp he
    change (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) at hend
    have hnP : ¬ M.InGroup P e := by
      rintro ⟨h1, h2⟩
      rcases hend with ⟨_, h4⟩ | ⟨h3, _⟩
      · exact hbP (h4 ▸ h2)
      · exact hbP (h3 ▸ h1)
    have hnQ : ¬ M.InGroup Q e := by
      rintro ⟨h1, h2⟩
      rcases hend with ⟨h3, _⟩ | ⟨_, h4⟩
      · exact haQ (h3 ▸ h1)
      · exact haQ (h4 ▸ h2)
    have hP' := chain_eraseBond e hP hnP
    have hQ' := chain_eraseBond e hQ hnQ
    exact ⟨⟨P ∪ Q, a, b, .hyper ⟨e, he, ⟨hBe, n + m, chain_append_chain hP' hQ' hPQ⟩⟩⟩, rfl, rfl, rfl⟩

end WaveTurbulence.GammaLow.FinalCount.H
