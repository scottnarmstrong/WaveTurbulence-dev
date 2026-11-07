/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceIter
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): garden-level consequences of a simultaneous splice

For every `SpMap G0 G cls`: the order does not increase, a nonempty garden stays nonempty, and the
molecule stays connected (TARGET `subpro` (1) for the spliced garden, together with the counts of
`propcplmol` which hold for every irreducible plain garden).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {w : ℕ} {G0 G : Garden w} {cls : GBranch G0.tree → Option (GBranch G0.tree)}

theorem Garden_order_eq_card (G : Garden w) : G.order = Fintype.card (GBranch G.tree) :=
  (card_gbranch G.tree).symm

theorem SpMap.order_le (M : SpMap G0 G cls) : G.order ≤ G0.order := by
  rw [Garden_order_eq_card, Garden_order_eq_card]
  exact Fintype.card_le_of_injective M.ob M.ob_inj

theorem SpMap.repC_mem_range (M : SpMap G0 G cls) (hcls : ClsOK cls) (v : GBranch G0.tree) :
    ∃ c, M.ob c = repC cls v := by
  apply (M.ob_range _).mpr
  unfold repC
  cases h : cls v with
  | none => simpa using Or.inl h
  | some a => simpa using Or.inr (hcls v a h)

theorem SpMap.order_pos (M : SpMap G0 G cls) (hcls : ClsOK cls) (h : 1 ≤ G0.order) : 1 ≤ G.order := by
  rw [Garden_order_eq_card] at h ⊢
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp h
  obtain ⟨c, -⟩ := M.repC_mem_range hcls v
  exact Fintype.card_pos_iff.mpr ⟨c⟩

theorem SpMap.repC_ob (M : SpMap G0 G cls) (c : GBranch G.tree) : repC cls (M.ob c) = M.ob c := by
  unfold repC
  rcases (M.ob_range (M.ob c)).mp ⟨c, rfl⟩ with h | h <;> simp [h]

/-- Path lifting: the molecule of the spliced garden is connected when the original one is. -/
theorem SpMap.connected (M : SpMap G0 G cls) (hcls : ClsOK cls) (h : G0.molecule.IsConnected) :
    G.molecule.IsConnected := by
  have key : ∀ u v : GBranch G0.tree, Relation.EqvGen G0.molecule.Adj u v →
      ∀ c d : GBranch G.tree, M.ob c = repC cls u → M.ob d = repC cls v →
        Relation.EqvGen G.molecule.Adj c d := by
    intro u v huv
    induction huv with
    | rel u v hx =>
      obtain ⟨x, hxu, hxv⟩ := hx
      intro c d hc hd
      by_cases hr : ∃ y, M.od y = x
      · obtain ⟨y, hy⟩ := hr
        have h1 : G.molecule.atom y = c := by
          apply M.ob_inj; rw [M.ob_atom, hy, hxu, hc]
        have h2 : G.molecule.atom (G.molecule.mate y) = d := by
          apply M.ob_inj; rw [M.ob_atom, M.od_mate, hy, hxv, hd]
        exact Relation.EqvGen.rel _ _ ⟨y, h1, h2⟩
      · have hcl : ∃ a, cls (G0.molecule.atom x) = some a ∧ cls (G0.molecule.atom (G0.molecule.mate x)) = some a := by
          by_contra hn
          exact hr ((M.od_range x).mpr hn)
        obtain ⟨a, h1, h2⟩ := hcl
        have : c = d := by
          apply M.ob_inj
          rw [hc, hd]
          unfold repC
          rw [← hxu, ← hxv, h1, h2]
          rfl
        exact this ▸ Relation.EqvGen.refl _
    | refl u =>
      intro c d hc hd
      have : c = d := M.ob_inj (hc.trans hd.symm)
      exact this ▸ Relation.EqvGen.refl _
    | symm u v _ ih =>
      intro c d hc hd
      exact (ih d c hd hc).symm
    | trans u v z _ _ ih1 ih2 =>
      intro c d hc hd
      obtain ⟨e, he⟩ := M.repC_mem_range hcls v
      exact Relation.EqvGen.trans _ _ _ (ih1 c e hc he) (ih2 e d he hd)
  intro c _ d _
  exact key (M.ob c) (M.ob d) (h _ (mem_univ _) _ (mem_univ _)) c d (M.repC_ob c).symm (M.repC_ob d).symm

end WaveTurbulence.RedSplice
