/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceTripleDesig` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceTripleDesig


/-!
# REDSPLICE-DEF (S2a), R37: the chosen hinge pair lies in a triple bond at the hinge

TARGET Operation 1 (L2140) and DH23 L1775: a triple bond of `M_sb` has a hinge endpoint `v`; the unit of `v` has four external
bonds, two at each joint, so three of them leave the unit at one joint twice.  `hingeOrigPair` (`HingeBest`) is chosen so
that its pair is that external pair of the joint, independently of `σ` (tiers `PairSameAtom`, `PairSameUnit`).

* `tripleDarts γ G σ v c`: the original darts underlying the bonds of `G_sb` from `v` to `c`.
* `whole_pair_in_triple`, `skip_pair_in_triple`: the pair lies in them (whole-group unit / unit of a skipped vine).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem card_aux {α : Type*} [DecidableEq α] (X E' : Finset α) (c : α) (hX : X.card = 3)
    (hsub : X ⊆ insert c E') (hE' : E'.card ≤ 2) : E'.card = 2 ∧ E' ⊆ X := by
  have h1 : (insert c E').card ≤ E'.card + 1 := Finset.card_insert_le _ _
  have h2 : X.card ≤ (insert c E').card := Finset.card_le_card hsub
  have hc : E'.card = 2 := by omega
  have heq : X = insert c E' := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact ⟨hc, by rw [heq]; exact Finset.subset_insert _ _⟩

theorem comb3 {α : Type*} [DecidableEq α] (X E E' : Finset α) (hX : X.card = 3) (hsub : X ⊆ E ∪ E')
    (hE' : E'.card ≤ 2) (a b : α) (hE : E ⊆ {a, b}) :
    (a ∈ X ∧ b ∈ X) ∨ (E'.card = 2 ∧ E' ⊆ X ∧ (a ∈ X ∨ b ∈ X) ∧ (a ∉ X ∨ b ∉ X)) := by
  by_cases ha : a ∈ X
  · by_cases hb : b ∈ X
    · exact Or.inl ⟨ha, hb⟩
    · right
      have hs : X ⊆ insert a E' := by
        intro x hx
        rcases Finset.mem_union.mp (hsub hx) with h | h
        · have h' := Finset.mem_insert.mp (hE h)
          rcases h' with h' | h'
          · rw [h']; exact Finset.mem_insert_self _ _
          · rw [Finset.mem_singleton] at h'; rw [h'] at hx; exact absurd hx hb
        · exact Finset.mem_insert_of_mem h
      obtain ⟨hc, hs'⟩ := card_aux X E' a hX hs hE'
      exact ⟨hc, hs', Or.inl ha, Or.inr hb⟩
  · right
    by_cases hb : b ∈ X
    · have hs : X ⊆ insert b E' := by
        intro x hx
        rcases Finset.mem_union.mp (hsub hx) with h | h
        · have h' := Finset.mem_insert.mp (hE h)
          rcases h' with h' | h'
          · rw [h'] at hx; exact absurd hx ha
          · rw [Finset.mem_singleton] at h'; rw [h']; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem h
      obtain ⟨hc, hs'⟩ := card_aux X E' b hX hs hE'
      exact ⟨hc, hs', Or.inr hb, Or.inl ha⟩
    · exfalso
      have hs : X ⊆ E' := by
        intro x hx
        rcases Finset.mem_union.mp (hsub hx) with h | h
        · have h' := Finset.mem_insert.mp (hE h)
          rcases h' with h' | h'
          · rw [h'] at hx; exact absurd hx ha
          · rw [Finset.mem_singleton] at h'; rw [h'] at hx; exact absurd hx hb
        · exact h
      have := Finset.card_le_card hs
      omega

/-- The external darts of the block `u` at the joint `j`. -/
@[expose] noncomputable def extAt (G : Garden w) (u : CLBlock G) (j : GBranch G.tree) : Finset (GardenDart G) :=
  (G.molecule.dartsAt j).filter (fun d => ¬ G.molecule.InGroup u.atoms d)

theorem mem_extAt {u : CLBlock G} {j : GBranch G.tree} {d : GardenDart G} :
    d ∈ extAt G u j ↔ G.molecule.atom d = j ∧ ¬ G.molecule.InGroup u.atoms d := by
  unfold extAt
  rw [Finset.mem_filter, Mole.mem_dartsAt]

section core
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

theorem ext_joint {u : CLBlock G} {d : GardenDart G} (hd : G.molecule.atom d ∈ u.atoms)
    (hn : ¬ G.molecule.InGroup u.atoms d) : G.molecule.atom d = u.upper ∨ G.molecule.atom d = u.lower := by
  by_contra hcon
  push Not at hcon
  exact hn (allInt hM u.isBlock hd hcon.1 hcon.2 rfl)

theorem card_extAt_le {u : CLBlock G} {j : GBranch G.tree} (hj : j = u.upper ∨ j = u.lower) :
    (extAt G u j).card ≤ 2 := by
  have hjm : j ∈ G.molecule.atoms := by
    rcases hj with rfl | rfl
    · exact u.isBlock.1 u.isBlock.2.1
    · exact u.isBlock.1 u.isBlock.2.2.1
  have hdeg := deg_le_four G.molecule hM hjm
  have hdi : G.molecule.degIn u.atoms j = 2 := by
    rcases hj with rfl | rfl
    · exact (block_joint_degrees G.molecule u.isBlock).1
    · exact (block_joint_degrees G.molecule u.isBlock).2
  have h : ((G.molecule.dartsAt j).filter (fun x => G.molecule.InGroup u.atoms x)).card +
      ((G.molecule.dartsAt j).filter (fun x => ¬ G.molecule.InGroup u.atoms x)).card =
      (G.molecule.dartsAt j).card := Finset.card_filter_add_card_filter_not _
  have h' : G.molecule.deg j = (G.molecule.dartsAt j).card := rfl
  have hdi' : ((G.molecule.dartsAt j).filter (fun x => G.molecule.InGroup u.atoms x)).card = 2 := hdi
  show ((G.molecule.dartsAt j).filter (fun x => ¬ G.molecule.InGroup u.atoms x)).card ≤ 2
  omega

theorem deg_eq_four_of_ext {u : CLBlock G} {j : GBranch G.tree} (hj : j = u.upper ∨ j = u.lower)
    (hc : (extAt G u j).card = 2) : G.molecule.deg j = 4 := by
  have hdi : G.molecule.degIn u.atoms j = 2 := by
    rcases hj with rfl | rfl
    · exact (block_joint_degrees G.molecule u.isBlock).1
    · exact (block_joint_degrees G.molecule u.isBlock).2
  have h : ((G.molecule.dartsAt j).filter (fun x => G.molecule.InGroup u.atoms x)).card +
      ((G.molecule.dartsAt j).filter (fun x => ¬ G.molecule.InGroup u.atoms x)).card =
      (G.molecule.dartsAt j).card := Finset.card_filter_add_card_filter_not _
  have hdi' : ((G.molecule.dartsAt j).filter (fun x => G.molecule.InGroup u.atoms x)).card = 2 := hdi
  have hc' : ((G.molecule.dartsAt j).filter (fun x => ¬ G.molecule.InGroup u.atoms x)).card = 2 := hc
  show (G.molecule.dartsAt j).card = 4
  omega

end core

section whole
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

end whole

theorem two_not_erased {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) {e0 : D} {a b : V}
    (hends : M.ends e0 = s(a, b)) (hab : a ≠ b) {j' : V} (hj' : j' = a ∨ j' = b) {e1 e2 : D} (hne : e1 ≠ e2)
    (h1 : M.atom e1 = j') (h2 : M.atom e2 = j') :
    (e1 ≠ e0 ∧ e1 ≠ M.mate e0) ∨ (e2 ≠ e0 ∧ e2 ≠ M.mate e0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c3⟩ := hcon
  unfold Molecule.ends at hends
  have key : M.atom e0 ≠ M.atom (M.mate e0) := by
    intro h
    rw [h] at hends
    rcases Sym2.eq_iff.mp hends with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · exact hab (h5.symm.trans h6)
    · exact hab (h6.symm.trans h5)
  by_cases d1 : e1 = e0
  · by_cases d2 : e2 = e0
    · exact hne (d1.trans d2.symm)
    · have d2' := c3 d2
      exact key ((congrArg M.atom d1.symm).trans (h1.trans (h2.symm.trans (congrArg M.atom d2'))))
  · have d1' := c1 d1
    by_cases d2 : e2 = e0
    · exact key ((congrArg M.atom d2.symm).trans (h2.trans (h1.symm.trans (congrArg M.atom d1'))))
    · exact hne (d1'.trans (c3 d2).symm)

theorem ext_sub_gen {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}
    {X Y : Finset V} {j j1 j2 : V} (hX : N.IsBlock X j j1) (hY : N.IsBlock Y j j2) (hXY : X ⊆ Y) {d : D}
    (hd : N.atom d = j) (hg : N.InGroup Y d) : N.InGroup X d :=
  subEq hXY ((block_joint_degrees N hX).1.trans (block_joint_degrees N hY).1.symm) hd hg

section skipcase
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

end skipcase

end WaveTurbulence.GammaLow.Fama
