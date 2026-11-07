/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp7Comb
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Canon

/-! # The twist class as a product over `Zp(A)` and `Y(A)` (V5 Step 4b, step 4, WP-A)

`ST` is the type of (state, split) pairs.  `canonSpFinset` is the finite set of canonical representatives carrying the split;
`zpFinset` the states reached by one operation at `pstar` (or skipping it); `yFinset G` the states of the class reached from
`G ∈ Zp` by a batch over the other members; `yA = yFinset` of the start.  `sum_canon_eq`: the sum over the class is the sum over
`G ∈ Zp(A)` of the sums over `yFinset G`.  `sum_yG_eq_sum_yA`: the bijection `yFinset G ≃ yA` (`x = (operation at pstar)(y)`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

/-- States together with a split. -/
abbrev ST (w : ℕ) (ι : Type*) (pstar : ι) (J : Set ι) := Σ X : FamilyReconstruction w ι, SplitAt X.skeleton X.family pstar J

theorem ReachSp.append {L1 L2 : List ι} {A B C : FamilyReconstruction w ι} {sp : SplitAt A.skeleton A.family pstar J}
    {sb : SplitAt B.skeleton B.family pstar J} {sc : SplitAt C.skeleton C.family pstar J}
    (h1 : ReachSp p kind pstar J L1 A sp B sb) (h2 : ReachSp p kind pstar J L2 B sb C sc) :
    ReachSp p kind pstar J (L1 ++ L2) A sp C sc := by
  induction h1 with
  | nil A sp => exact h2
  | skip i h ih => exact .skip i (ih h2)
  | apply op h ih => exact .apply op (ih h2)

theorem ReachSp.skips {X : FamilyReconstruction w ι} (sx : SplitAt X.skeleton X.family pstar J) :
    ∀ L : List ι, ReachSp p kind pstar J L X sx X sx
  | [] => .nil X sx
  | i :: L => .skip i (ReachSp.skips sx L)

section Fib
variable [Fintype ι] [DecidableEq ι]

theorem st_ext {A : FamilyReconstruction w ι} {sp : SplitAt A.skeleton A.family pstar J} {x x' : ST w ι pstar J}
    (hs : x.1 = x'.1) {M M' : List ι} (hM : M.Nodup) (hM' : M'.Nodup)
    (h : ReachSp p kind pstar J M A sp x.1 x.2) (h' : ReachSp p kind pstar J M' A sp x'.1 x'.2) : x = x' := by
  obtain ⟨X, s⟩ := x
  obtain ⟨X', s'⟩ := x'
  simp only at hs h h'
  subst hs
  rw [ReachSp.unique hM hM' h h']

theorem perm_cons_erase (pstar : ι) :
    ([pstar] ++ (Finset.univ.erase pstar).toList).Perm (Finset.univ : Finset ι).toList := by
  refine List.perm_of_nodup_nodup_toFinset_eq ?_ (Finset.nodup_toList _) ?_
  · refine List.nodup_append.mpr ⟨List.nodup_singleton _, Finset.nodup_toList _, ?_⟩
    intro a ha b hb hab
    simp at ha
    subst ha
    have := (Finset.mem_toList.mp hb)
    simp at this
    exact this hab.symm
  · ext y
    simp only [List.mem_toFinset, Finset.toList_toFinset, List.mem_append, List.mem_singleton, Finset.mem_toList,
      Finset.mem_erase, Finset.mem_univ, and_true]
    by_cases h : y = pstar <;> simp [h]

theorem perm_erase_cons (pstar : ι) :
    ((Finset.univ.erase pstar).toList ++ [pstar]).Perm (Finset.univ : Finset ι).toList := by
  refine List.Perm.trans List.perm_append_comm (perm_cons_erase pstar)

theorem not_mem_erase {M : List ι} (hM : M.Perm (Finset.univ.erase pstar).toList) : pstar ∉ M := by
  intro h
  have := hM.mem_iff.mp h
  simp at this

theorem nodup_pre {M : List ι} (hM : M.Perm (Finset.univ.erase pstar).toList) : ([pstar] ++ M).Nodup := by
  refine List.nodup_append.mpr ⟨List.nodup_singleton _, hM.nodup_iff.mpr (Finset.nodup_toList _), ?_⟩
  intro a ha b hb hab
  simp at ha
  subst ha
  have := hM.mem_iff.mp hb
  simp at this
  exact this hab.symm

theorem nodup_erase {M : List ι} (hM : M.Perm (Finset.univ.erase pstar).toList) : M.Nodup :=
  hM.nodup_iff.mpr (Finset.nodup_toList _)

variable (p kind pstar J) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)

/-- The canonical representatives with their splits. -/
@[expose] def canonSpSet : Set (ST w ι pstar J) :=
  {x | ∃ M : List ι, M.Perm Finset.univ.toList ∧ ReachSp p kind pstar J M A sp0 x.1 x.2}

theorem canonSpSet_finite (hA : IsPrimeGarden A.skeleton) : (canonSpSet p kind pstar J A sp0).Finite := by
  refine Set.Finite.of_injOn (f := fun x : ST w ι pstar J => (⟨x.1, x.2.c⟩ : Σ Bs : FamilyReconstruction w ι,
    ChainAt Bs.skeleton Bs.family)) (t := CanonRepsK p kind A sp0.c) ?_ ?_ (canonReps_finite p kind hA sp0.c)
  · intro x ⟨M, hM, h⟩
    exact ⟨M, hM, h.reach⟩
  · intro x ⟨M, hM, h⟩ x' ⟨M', hM', h'⟩ hxx
    have hs : x.1 = x'.1 := by
      have := hxx
      simp only [Sigma.mk.injEq] at this
      exact this.1
    exact st_ext hs (perm_univ_nodup hM) (perm_univ_nodup hM') h h'

/-- The finite set of canonical representatives with their splits. -/
@[expose] noncomputable def canonSpFinset (hA : IsPrimeGarden A.skeleton) : Finset (ST w ι pstar J) :=
  (canonSpSet_finite p kind pstar J A sp0 hA).toFinset

theorem mem_canonSpFinset (hA : IsPrimeGarden A.skeleton) {x : ST w ι pstar J} :
    x ∈ canonSpFinset p kind pstar J A sp0 hA ↔ x ∈ canonSpSet p kind pstar J A sp0 :=
  Set.Finite.mem_toFinset _

end Fib

end WaveTurbulence.VineEstS4
