/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR32IndirectCrossing
public import WaveTurbulence.Foundations.FinalCount.AppBCutSignAt
public import WaveTurbulence.Foundations.FinalCount.AppBCutExternalSign
public import WaveTurbulence.Foundations.FinalCount.AppBFrameSignCap
public import WaveTurbulence.Foundations.FinalCount.AppBTripleOrdering
import Mathlib.Tactic

/-! # The indirect cut's signs inherit the old special atom's degree caps -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_r32_indirect_cut_sign_cap {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms) (hM : M.IsMolecule)
    (S : Finset V) (hS : S ⊆ r.post.atoms) (j : Fin 3) (which : Bool)
    (hcross : appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val})
    (ha : s.specialAtom which ∈ S) (hc : s.specialCompanion which ∈ S) (ho : s.specialAtom (!which) ∉ S)
    (hstar : appbIncidence M (s.specialAtom which) (r.edge j).val = 0)
    (hopp : appbCutSign M S (r.edge j).val ≠ appbCutSign M S (s.edge ⟨0,by decide⟩).val.val) :
    ∀ u : ℤˣ,¬∀ k,appbCutSign M (S \ {s.specialAtom which})
      ((r.combinedRemoval s v0).edge ((appbR32IndirectCut r s v0 S hS j which hcross ha hc ho hstar).index k)).val = u := by
  let b := r.combinedRemoval s v0
  let a := s.specialAtom which
  let T := S \ {a}
  let cut := appbR32IndirectCut r s v0 S hS j which hcross ha hc ho hstar
  have hleft := appb_r32_all_star_incidence_zero r s S hS j hcross a ha hstar
  let t := (s.specialFrame which).combinedRight r s v0 hleft
  have hindices := s.specialFrame_indices which
  have he0 : (b.edge (t.index 0)).val = (s.edge ⟨0,by decide⟩).val.val := by
    change (b.edge (r.combinedRightIndex s ((s.specialFrame which).index 0))).val = _
    rw [hindices.1]
    exact r.combined_edge_right s v0 _
  have he1 : (b.edge (t.index 1)).val = (s.edge (s.specialFirst which)).val.val := by
    change (b.edge (r.combinedRightIndex s ((s.specialFrame which).index 1))).val = _
    rw [hindices.2.1]
    exact r.combined_edge_right s v0 _
  have he2 : (b.edge (t.index 2)).val = (s.edge (s.specialSecond which)).val.val := by
    change (b.edge (r.combinedRightIndex s ((s.specialFrame which).index 2))).val = _
    rw [hindices.2.2]
    exact r.combined_edge_right s v0 _
  have hiB : appbIncidence M a (s.edge ⟨0,by decide⟩).val.val = 1 := by
    have hh := (s.specialFrame which).incidence 0
    rw [hindices.1] at hh
    exact hh
  have hBcross : (M.atom (s.edge ⟨0,by decide⟩).val.val ∈ S ∧
      M.atom (M.mate (s.edge ⟨0,by decide⟩).val.val) ∉ S) ∨
      (M.atom (s.edge ⟨0,by decide⟩).val.val ∉ S ∧ M.atom (M.mate (s.edge ⟨0,by decide⟩).val.val) ∈ S) := by
    have hh : (s.edge ⟨0,by decide⟩).val.val ∈ appbCrossingBonds M S :=
      hcross.symm ▸ mem_insert_of_mem (mem_singleton_self _)
    exact (mem_filter.mp hh).2
  have hBsign := appb_cutSign_eq_incidence_at M S _ a ha hiB hBcross
  have hXsign : appbCutSign M S (r.edge j).val = -appbIncidenceSign M a (s.edge ⟨0,by decide⟩).val.val :=
    appb_units_eq_neg_of_ne _ _ (Ne.symm (by simpa only [hBsign] using hopp))
  have haN : a ∉ T := fun h => (mem_sdiff.mp h).2 (mem_singleton_self _)
  have hcN : s.specialCompanion which ∈ T := mem_sdiff.mpr ⟨hc,by
    simpa only [mem_singleton] using (s.special_atom_ne_companion which).symm⟩
  have hd1 : M.ends (s.edge (s.specialFirst which)).val.val = s(a,s.specialCompanion which) := s.special_first_ends which
  have hd2 : M.ends (s.edge (s.specialSecond which)).val.val = s(a,s.specialCompanion which) := s.special_second_ends which
  have hD1 := appb_cutSign_eq_neg_external M T _ (s.specialCompanion which) a
    (hd1.trans Sym2.eq_swap) hcN haN
  have hD2 := appb_cutSign_eq_neg_external M T _ (s.specialCompanion which) a
    (hd2.trans Sym2.eq_swap) hcN haN
  have hXsame : appbCutSign M T (r.edge j).val = appbCutSign M S (r.edge j).val := by
    have hn := (appb_incidence_zero_iff M a _).mp hstar
    simp only [appbCutSign,T,mem_sdiff,mem_singleton,hn.1,not_false_eq_true,and_true]
  have hi := appb_r32_triple_indices r s j which
  have hL : (b.edge (r.combinedLeftIndex s j)).val = (r.edge j).val := r.combined_edge_left s v0 j
  have hR1 : (b.edge (r.combinedRightIndex s (s.specialFirst which))).val = (s.edge (s.specialFirst which)).val.val :=
    r.combined_edge_right s v0 _
  have hR2 : (b.edge (r.combinedRightIndex s (s.specialSecond which))).val = (s.edge (s.specialSecond which)).val.val :=
    r.combined_edge_right s v0 _
  have hsign (k : Fin 3) : appbCutSign M T (b.edge (cut.index k)).val =
      -appbIncidenceSign M a (b.edge (t.index k)).val := by
    change appbCutSign M T (b.edge (appbR32TripleIndices r s j which k)).val = _
    fin_cases k
    · change appbCutSign M T (b.edge (appbR32TripleIndices r s j which ⟨0,by decide⟩)).val =
        -appbIncidenceSign M a (b.edge (t.index ⟨0,by decide⟩)).val
      have hfin : (⟨0,by decide⟩ : Fin 3) = 0 := by decide
      rw [hfin,hi.1,hL,he0,hXsame,hXsign]
    · change appbCutSign M T (b.edge (appbR32TripleIndices r s j which ⟨1,by decide⟩)).val =
        -appbIncidenceSign M a (b.edge (t.index ⟨1,by decide⟩)).val
      have hfin : (⟨1,by decide⟩ : Fin 3) = 1 := by decide
      rw [hfin,hi.2.1,hR1,he1,hD1]
    · change appbCutSign M T (b.edge (appbR32TripleIndices r s j which ⟨2,by decide⟩)).val =
        -appbIncidenceSign M a (b.edge (t.index ⟨2,by decide⟩)).val
      have hfin : (⟨2,by decide⟩ : Fin 3) = 2 := by decide
      rw [hfin,hi.2.2,hR2,he2,hD2]
  intro u hall
  apply appb_not_all_frame_signs b hM a (mem_sdiff.mp (hS ha)).1 t.index t.incidence (-u)
  intro k
  have hh := hsign k
  rw [hall k] at hh
  have hh' := congrArg Neg.neg hh
  simpa only [neg_neg] using hh'.symm

end WaveTurbulence.Mole
