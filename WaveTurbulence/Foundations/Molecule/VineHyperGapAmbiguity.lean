/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.Molecule.VineGapKinds
import Mathlib.Tactic

/-! # Audit example: one triple-bond group has different designated-adjoint gaps

TARGET defblock and defdiff. This does not change any pinned definition.
It records why the designation must be part of a hyper-block object and why
the owner requires compatible designations in containment for equal atom groups.
-/

public section
namespace WaveTurbulence.Vine.HyperGapAudit
open Finset

/-- Two bonds point from atom0 to atom1 and the third points back. -/
@[expose] def triple : Molecule (Fin 2) (Fin 6) where
  atoms := univ
  atom := ![0,1,0,1,1,0]
  mate := ![1,0,3,2,5,4]
  out := ![true,false,true,false,true,false]
  atom_mem := fun _ => mem_univ _
  mate_mate := by intro d; fin_cases d <;> decide
  mate_ne := by intro d; fin_cases d <;> decide
  out_mate := by intro d; fin_cases d <;> decide

/-- The degree-three molecule has no saturated component. -/
theorem triple_isMolecule : triple.IsMolecule := by
  constructor
  · decide
  · intro v hv
    refine ⟨v,hv,Relation.EqvGen.refl _,?_⟩
    fin_cases v <;> decide

/-- Either of the first two equally directed bonds leaves a connected block (the degree clauses are decidable;
the connectedness conjunct of the canonical `IsBlock` is proved by the two bonds of the remaining two-atom graph). -/
theorem triple_adjoint_block (e : Fin 6) (he : e=0 ∨ e=2) :
    (Mole.eraseBond triple e).IsBlock univ 0 1 := by
  have hc : (Mole.eraseBond triple e).GroupConnected univ := by
    intro u _ v _
    have hadj : ∀ x : Fin 6, x ≠ e → x ≠ triple.mate e → triple.atom x = 0 → triple.atom (triple.mate x) = 1 →
        Relation.EqvGen (fun a b => ∃ y, (Mole.eraseBond triple e).InGroup univ y ∧
          (Mole.eraseBond triple e).atom y = a ∧ (Mole.eraseBond triple e).atom ((Mole.eraseBond triple e).mate y) = b)
          0 1 := by
      intro x hx1 hx2 ha hb
      exact Relation.EqvGen.rel _ _ ⟨⟨x, hx1, hx2⟩, ⟨mem_univ _, mem_univ _⟩, ha, hb⟩
    rcases he with he | he <;> subst e <;> fin_cases u <;> fin_cases v
    all_goals first
      | exact Relation.EqvGen.refl _
      | exact hadj 2 (by decide) (by decide) (by decide) (by decide)
      | exact Relation.EqvGen.symm _ _ (hadj 2 (by decide) (by decide) (by decide) (by decide))
      | exact hadj 0 (by decide) (by decide) (by decide) (by decide)
      | exact Relation.EqvGen.symm _ _ (hadj 0 (by decide) (by decide) (by decide) (by decide))
  rcases he with he | he <;> subst e <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, hc⟩

/-- Either of the first two equally directed bonds can be designated. -/
theorem triple_adjoint_I (e : Fin 6) (he : e=0 ∨ e=2) :
    (Mole.eraseBond triple e).IsVine .I univ 0 1 := by
  rcases he with he | he <;> subst e
  · refine ⟨triple_adjoint_block _ (Or.inl rfl),[],rfl,Fin.val,(fun _ _ _ _ h => Fin.val_injective h),by decide,by decide,?_⟩
    decide
  · refine ⟨triple_adjoint_block _ (Or.inr rfl),[],rfl,Fin.val,(fun _ _ _ _ h => Fin.val_injective h),by decide,by decide,?_⟩
    decide

/-- Each designation is a valid actual HV, with a type-I adjoint. -/
theorem triple_isHV : IsHV triple univ 0 1 :=
  ⟨0,by decide,.I,triple_adjoint_I 0 (Or.inl rfl)⟩

/-- Integer lattice labels: the two equally directed bonds have labels
1 and32, and the oppositely directed bond has label0. -/
@[expose] def labels (d : Fin 6) : Fin 1 → ℤ := fun _ => ![1,1,32,32,0,0] d

/-- A one-coordinate momentum vector with specified real coordinate. -/
@[expose] noncomputable def vector (t : ℝ) : Mom 1 := PiLp.single 2 0 t

/-- The defect vector is the actual signed local sum; all degree-four
constraints are vacuous because both atoms have degree three. -/
@[expose] noncomputable def defects (v : Fin 2) : Mom 1 :=
  ∑ d ∈ triple.dartsAt v,triple.dartSign d • Molecule.kvec 16 0 labels d

/-- This is an exact source lattice decoration. -/
theorem decorated : triple.IsDecoration 16 0 defects labels := by
  constructor
  · intro d
    fin_cases d <;> rfl
  · intro _v _hv
    rfl

/-- The source's standing zero-defect condition at full atoms is satisfied. -/
theorem defects_at_full : ∀ v ∈ triple.atoms,triple.deg v=4 → defects v=0 := by
  intro v _hv hd
  have h3 : triple.deg v=3 := by fin_cases v <;> decide
  omega

/-- Deleting bond0 gives gap2 between the remaining outgoing and incoming bonds. -/
theorem outer_gap : (Mole.eraseBond triple 0).IsBlockGap 16 0
    (fun d => labels d.1) univ 0 (vector 2) := by
  refine ⟨⟨2,by decide,by decide⟩,⟨5,by decide,by decide⟩,
    by decide,by decide,by decide,by decide,by decide,by decide,?_⟩
  ext j
  fin_cases j
  norm_num [Molecule.gapAt,Molecule.kvec,latticePoint,labels,vector,PiLp.single_apply]

/-- Deleting bond2 gives gap1/16 on the same decorated atom group. -/
theorem inner_gap : (Mole.eraseBond triple 2).IsBlockGap 16 0
    (fun d => labels d.1) univ 0 (vector (1/16)) := by
  refine ⟨⟨0,by decide,by decide⟩,⟨5,by decide,by decide⟩,
    by decide,by decide,by decide,by decide,by decide,by decide,?_⟩
  ext j
  fin_cases j
  norm_num [Molecule.gapAt,Molecule.kvec,latticePoint,labels,vector,PiLp.single_apply]

/-- The two gaps straddle the source threshold for every sufficiently
small nonnegative eta; the example does not rely on a zero threshold. -/
theorem different_gap_kinds (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/4) :
    Molecule.gapKind 16 (1/2) η (vector 2)=.LG ∧
      Molecule.gapKind 16 (1/2) η (vector (1/16))=.SG := by
  have hlo := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 16 by norm_num)
    (show (-1 : ℝ) ≤ -(1/2)+η by linarith)
  have hhi := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 16 by norm_num)
    (show -(1/2)+η ≤ (0 : ℝ) by linarith)
  norm_num only [Real.rpow_neg_one,Real.rpow_zero] at hlo hhi
  have hn (t : ℝ) : ‖vector t‖=|t| := by simp only [vector,PiLp.norm_single,Real.norm_eq_abs]
  constructor
  · apply (gapKind_eq_LG_iff 16 (1/2) η (by norm_num) _).mpr
    rw [hn,abs_of_nonneg (by norm_num)]
    linarith
  · apply (gapKind_eq_SG_iff 16 (1/2) η _).mpr
    refine ⟨?_,?_⟩
    · intro he
      have hh := congrArg norm he
      rw [hn,norm_zero] at hh
      norm_num at hh
    · rw [hn,abs_of_nonneg (by norm_num)]
      exact hlo

/-- The proposed subsetvc list has no hyper-adjoint of this atom size:
two double bonds need three atoms and Vine V needs at least nine. -/
theorem no_listed_adjoint : ¬∃ e : Fin 6,triple.ends e=s((0 : Fin 2),1) ∧
    (DoubleChain (Mole.eraseBond triple e) univ 0 1 2 ∨
      (Mole.eraseBond triple e).IsVine .V univ 0 1) := by
  rintro ⟨e,_he,hD | hV⟩
  · have hc := doubleChain_card hD
    norm_num at hc
  · have hx := isVine_typeI_of_card_lt_four hV (by decide)
    cases hx

end WaveTurbulence.Vine.HyperGapAudit
