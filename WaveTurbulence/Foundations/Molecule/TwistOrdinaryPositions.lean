/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistBlockTransport

/-! # Every ordinary atom retains its actual incidence position codes

TARGET twistexplain: ordered ports change only at the lower atom. This
stronger form feeds the source splicing and distinct-vine commutation.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- The last slot of an actual child address is its ordered child index. -/
theorem last_eq_of_child {w : ℕ} {F : Fin w → TTree} {n : GNode F} {p : GBranch F}
    {i : Fin 3} (hn : n.1.2 ≠ []) (hc : n = p.child i) : n.1.2.getLast hn = i := by
  have hv : n.1.2 = p.1.2 ++ [i] := congrArg (fun n : GNode F => n.1.2) hc
  simp [hv]

/-- Last slots agree when actual nonroot address paths agree. -/
theorem getLast_congr {p q : Path} (hp : p ≠ []) (hq : q ≠ []) (he : p = q) :
    p.getLast hp = q.getLast hq := by
  subst q
  rfl

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Every incidence at an atom other than u2 keeps its actual ordered position. -/
theorem twistDartEquiv_position_other (x : GardenDart G) (hx : G.molecule.atom x ≠ P.lower) :
    Mole.dartPosition (unitTwistGarden G P) (twistDartEquiv G P x) = Mole.dartPosition G x := by
  change Mole.dartPosition (unitTwistGarden G P) (naiveDartEquiv G P (exceptionalDartSwap G P x)) = _
  cases x with
  | inl c =>
    obtain ⟨c,side⟩ := c
    by_cases hc : c.1 = P.lower
    · have he : c = ⟨P.lower,P.nonroot⟩ := Subtype.ext hc
      subst c
      change Mole.dartPosition (unitTwistGarden G P)
        (naiveDartEquiv G P (exceptionalDartSwap G P (lowerPC G P side))) = _
      rw [exceptionalDartSwap_lowerPC]
      cases side
      · exact (hx rfl).elim
      · change ((coreLeafEquiv G P (G.pair P.retained)).1.2.getLast
          ((coreLeafEquiv_nonroot G P (G.pair P.retained)).mpr P.paired_nonroot)).succ =
          (P.lower.1.2.getLast P.nonroot).succ
        exact congrArg Fin.succ (getLast_congr _ _ (congrArg Prod.snd (coreLeafEquiv_paired_val G P)))
    · rw [exceptionalDartSwap_otherPC G P c hc side]
      cases side
      · rfl
      · let p := GNode.parent c.1.toNode c.2
        have hp : p.1 ≠ P.lower.1 := fun he => hx (Subtype.ext he)
        dsimp only [p] at hp
        have ht := branch_child_transport G P (Mole.parent_child_eq_node c.1.toNode c.2).symm hc
        simp only [exchangeChildSlot,hp,ite_false] at ht
        change ((coreBranchEquiv G P c.1).1.2.getLast ((coreBranchEquiv_nonroot G P c.1).mpr c.2)).succ =
          (c.1.1.2.getLast c.2).succ
        exact congrArg Fin.succ (last_eq_of_child _ ht)
  | inr l =>
    by_cases hl : l.1 = P.retained
    · have he : l = ⟨P.retained,P.unmarked,retained_nonroot G P,P.paired_nonroot⟩ := Subtype.ext hl
      subst l
      exact (hx (retained_parent G P)).elim
    · by_cases hpair : l.1 = G.pair P.retained
      · have he : (.inr l : GardenDart G) = G.molecule.mate (retainedLP G P) := by
          apply congrArg Sum.inr
          exact Subtype.ext hpair
        rw [he,exceptionalDartSwap_pairedLP]
        change ((coreBranchEquiv G P P.lower).1.2.getLast
          ((coreBranchEquiv_nonroot G P P.lower).mpr P.nonroot)).succ =
          ((G.pair P.retained).1.2.getLast P.paired_nonroot).succ
        exact congrArg Fin.succ (getLast_congr _ _ (congrArg Prod.snd (coreBranchEquiv_lower_val G P)))
      · rw [exceptionalDartSwap_otherLP G P l hl hpair]
        let p := GNode.parent l.1.toNode l.2.2.1
        have hp : p.1 ≠ P.lower.1 := fun he => hx (Subtype.ext he)
        dsimp only [p] at hp
        have ht := leaf_child_transport G P (Mole.parent_child_eq_node l.1.toNode l.2.2.1).symm hpair
        simp only [exchangeChildSlot,hp,ite_false] at ht
        change ((coreLeafEquiv G P l.1).1.2.getLast ((coreLeafEquiv_nonroot G P l.1).mpr l.2.2.1)).succ =
          (l.1.1.2.getLast l.2.2.1).succ
        exact congrArg Fin.succ (last_eq_of_child _ ht)

end WaveTurbulence.Twist
