/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceHyperDiamond
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondClosed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceHyperDiamond`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Same-joints overlap involving a hyper block: either one block is just its two joints
(nested), or the union is a saturated component. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- If all group darts of a block at the joint `a` end at `b`, the block is `{a, b}`. -/
theorem block_eq_pair_of_all_to_b {N : Molecule V D} {A : Finset V} {a b : V}
    (hA : N.IsBlock A a b)
    (h : ∀ x, N.atom x = a → N.InGroup A x → N.atom (N.mate x) = b) : A = {a, b} := by
  have hdeg := Mole.block_joint_degrees N hA
  -- darts at b in the group are exactly the mates of those at a
  have hsub : ((N.dartsAt a).filter fun x => N.InGroup A x).image N.mate ⊆
      (N.dartsAt b).filter fun x => N.InGroup A x := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and] at hx ⊢
    exact ⟨h x hx.1 hx.2, inGroup_mate hx.2⟩
  have hcard : (((N.dartsAt a).filter fun x => N.InGroup A x).image N.mate).card =
      ((N.dartsAt b).filter fun x => N.InGroup A x).card := by
    rw [Finset.card_image_of_injective _ (fun x y hxy => by
      simpa only [N.mate_mate] using congrArg N.mate hxy)]
    exact hdeg.1.trans hdeg.2.symm
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hb : ∀ y, N.atom y = b → N.InGroup A y → N.atom (N.mate y) = a := by
    intro y hy hyg
    have : y ∈ (N.dartsAt b).filter fun x => N.InGroup A x := by simp [Molecule.dartsAt, hy, hyg]
    rw [← heq] at this
    obtain ⟨x, hx, rfl⟩ := mem_image.mp this
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and] at hx
    rw [N.mate_mate]; exact hx.1
  have key : ∀ p q, Relation.EqvGen (fun u v => ∃ y, N.InGroup A y ∧ N.atom y = u ∧
      N.atom (N.mate y) = v) p q → ((p = a ∨ p = b) ↔ (q = a ∨ q = b)) := by
    intro p q hpq
    induction hpq with
    | rel u v huv =>
      obtain ⟨y, hy, hyu, hyv⟩ := huv
      have fwd : ∀ y, N.InGroup A y → (N.atom y = a ∨ N.atom y = b) →
          (N.atom (N.mate y) = a ∨ N.atom (N.mate y) = b) := by
        intro y hy h'
        rcases h' with h' | h'
        · exact Or.inr (h y h' hy)
        · exact Or.inl (hb y h' hy)
      constructor
      · intro hu; rw [← hyv]; exact fwd y hy (hyu ▸ hu)
      · intro hv
        have := fwd (N.mate y) (inGroup_mate hy) (by rw [hyv]; exact hv)
        rw [N.mate_mate, hyu] at this; exact this
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
  apply Finset.Subset.antisymm
  · intro u hu
    have hconn := hA.2.2.2.2.2.2.2.2.2 a hA.2.1 u hu
    have := (key a u hconn).mp (Or.inl rfl)
    simpa using this
  · intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact hA.2.1
    · rw [mem_singleton.mp hu]; exact hA.2.2.1


theorem OH.eq_pairL {M : Molecule V D} {A : Finset V} {a b : V} (h : OH M A a b)
    (hs : ∀ x, M.atom x = a → M.InGroup A x → M.atom (M.mate x) = b) : A = {a, b} := by
  rcases h with h | ⟨e, he, hB⟩
  · exact block_eq_pair_of_all_to_b h hs
  · exact block_eq_pair_of_all_to_b hB (fun x hx hg => hs x.1 hx hg)


alias _root_.WaveTurbulence.LGSpine.OH.eq_pairL := _root_.WaveTurbulence.GammaLow.FinalCount.H.OH.eq_pairL
end WaveTurbulence.GammaLow.FinalCount.H
