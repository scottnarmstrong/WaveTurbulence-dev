/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftCanonCriterion
public import WaveTurbulence.Foundations.XChain.GardenGraftIrreducible
/-! The explicit graft construction belongs to the canonical garden class. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem isCanonG_layer_le {w p : ℕ} {LG : LayeredGarden w} (h : IsCanonG p LG)
    (a : GNode LG.garden.tree) : LG.layer a ≤ p := by
  cases p with
  | zero => exact False.elim h
  | succ q => exact (h.2.2.2.1 a).trans (Nat.le_succ q)

theorem isCanonG_irreducible {w p : ℕ} {LG : LayeredGarden w} (h : IsCanonG p LG) :
    LG.garden.Irreducible := by
  cases p with
  | zero => exact False.elim h
  | succ q => exact h.2.2.1

theorem garden_irreducible_of_width_eq_two {w : ℕ} (G : Garden w) (hw : w = 2) :
    G.Irreducible := by
  subst w
  exact garden_two_irreducible G

theorem layeredGardenGraft_isCanonG {w : ℕ} (hw : 4 ≤ w) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hplain : ∀ B, (low B).garden.IsPlain)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hP : TopPartitionIrreducible top P)
    (hcomponent : ∀ B, IsCanonG p (low B) ∨
      B.1.card = 2 ∧ ∀ a, (low B).layer a = p) :
    IsCanonG (p + 1) (layeredGardenGraft sig top P low p hplain hsig
      (fun B a => (hcomponent B).elim (fun h => isCanonG_layer_le h a)
        (fun h => (h.2 a).le))) := by
  refine ⟨hw, ?_, ?_, ?_⟩
  · exact fun _ => rfl
  · exact gardenGraft_irreducible sig top P (fun B => (low B).garden) hplain hsig hP
      (fun B => (hcomponent B).elim isCanonG_irreducible
        (fun h => garden_irreducible_of_width_eq_two (low B).garden h.1))
  · exact layeredGardenGraft_criterion sig top P low p hplain hsig _
      (fun B => (hcomponent B).imp_right And.right)

end WaveTurbulence.Induct
