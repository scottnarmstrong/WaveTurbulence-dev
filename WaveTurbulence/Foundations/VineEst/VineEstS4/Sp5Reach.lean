/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp4Rigid
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls2Comb

/-! # The S-side along a batch below the split (V5 Step 4b, step 4, WP-D)

`noop_batch`: a member without an operation at `A0` has none at any state reached by a batch avoiding it (`OpsCommute`).
`sSumAt_reachBelow`: along a `ReachSp` whose operations are all at members of `J` (guaranteed when the members outside
`J ∪ {pstar}` carry no operation at the start `A0`), `sSumAt κ _ _ Φ` is constant, for every lower factor `Φ`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

theorem noop_batch (hc : Stage1.OpsCommute p kind w ι) {L : List ι} {A X : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A X) {j : ι} (hj : j ∉ L) (hA : IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) :
    IsEmpty (FamilyOperation (p := p) (kind := kind) X j) := by
  induction h with
  | nil => exact hA
  | skip i h ih => exact ih (fun hh => hj (List.mem_cons_of_mem _ hh)) hA
  | @apply L A B i op h ih =>
    have hji : i ≠ j := fun e => hj (e ▸ List.mem_cons_self)
    refine ih (fun hh => hj (List.mem_cons_of_mem _ hh)) ⟨fun op2 => ?_⟩
    obtain ⟨op2', _, _⟩ := hc A i j hji op op2
    exact hA.false op2'

theorem sSumAt_reachBelow [DecidableEq ι] (hc : Stage1.OpsCommute p kind w ι) (κ : KPar d) {A0 : FamilyReconstruction w ι}
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A0 j))
    {M : List ι} {G x : FamilyReconstruction w ι} {sp : SplitAt G.skeleton G.family pstar J}
    {sx : SplitAt x.skeleton x.family pstar J} (h : ReachSp p kind pstar J M G sp x sx) :
    ∀ {Lpre : List ι}, FamilyBatch p kind Lpre A0 G → (Lpre ++ M).Nodup → pstar ∈ Lpre →
      ∀ Φ : ℝ → Mom d → Mom d → ℂ, sSumAt κ x sx Φ = sSumAt κ G sp Φ := by
  induction h with
  | nil A sp => intros; rfl
  | skip i h ih =>
    intro Lpre hpre hnd hp Φ
    exact ih hpre (hnd.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)) hp Φ
  | @apply L A sp B sp' i op h ih =>
    intro Lpre hpre hnd hp Φ
    have hnd' : (Lpre ++ i :: L).Nodup := hnd
    have hiL : i ∉ Lpre := fun hi => by
      have := List.nodup_append.mp hnd'
      exact this.2.2 i hi i List.mem_cons_self rfl
    have hij : i ∈ J := by
      by_contra hnJ
      have hne : i ≠ pstar := fun e => hiL (e ▸ hp)
      exact (noop_batch hc hpre hiL (hA0 i hnJ hne)).false op
    have h1 := ih (Lpre := Lpre ++ [i]) (Stage1.familyBatch_append hpre (.apply op (.nil _)))
      (by simpa using hnd') (List.mem_append_left _ hp) Φ
    exact h1.trans (sSumAt_op κ A sp hij op Φ)

end WaveTurbulence.VineEstS4
