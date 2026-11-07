/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFamilyRestriction
public import WaveTurbulence.Foundations.Vine.A.VineGardenOrbits
/-! Every actual subfamily output is an actual output of the full LF family. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 LFTwist
variable {w p : ℕ} {kind : Bool} {ι κ : Type*}

/-- Lift every actual subfamily batch, retaining the complete original output data. -/
theorem batch_restrict_lift (e : κ → ι) (he : Function.Injective e)
    {L : List κ} {B C : FamilyReconstruction w κ} (h : FamilyBatch p kind L B C)
    (A : FamilyReconstruction w ι) (hA : stateRestrict A e he = B) :
    ∃ D, FamilyBatch p kind (L.map e) A D ∧ stateRestrict D e he = C := by
  induction h generalizing A with
  | nil B =>
    exact ⟨A, .nil A, hA⟩
  | skip i _ ih =>
    obtain ⟨D, hD, hd⟩ := ih A hA
    exact ⟨D, .skip (e i) hD, hd⟩
  | @apply L B C i op h ih =>
    subst B
    let op' := operationLiftAt e he i op
    obtain ⟨D, hD, hd⟩ := ih op'.output (operationLiftAt_output e he i op)
    exact ⟨D, .apply op' hD, hd⟩

/-- Complete an injective subfamily's processing order by skipping the complementary coordinates. -/
theorem complete_injective_list [Fintype ι] [Fintype κ] [DecidableEq ι] (e : κ → ι) (he : Function.Injective e)
    (L : List κ) (hL : L.Perm Finset.univ.toList) :
    ((Finset.univ.toList.filter (fun i => decide (i ∉ L.map e))) ++ L.map e).Perm Finset.univ.toList := by
  classical
  have hn : (L.map e).Nodup := (hL.nodup_iff.mpr (Finset.nodup_toList _)).map he
  have hd : List.Disjoint (Finset.univ.toList.filter (fun i => decide (i ∉ L.map e))) (L.map e) := by
    intro i hi hm
    exact (of_decide_eq_true (List.mem_filter.mp hi).2) hm
  apply (List.perm_ext_iff_of_nodup
    (((Finset.nodup_toList _).filter _).append hn hd) (Finset.nodup_toList _)).mpr
  intro i
  constructor
  · intro _
    exact Finset.mem_toList.mpr (Finset.mem_univ i)
  · intro _
    by_cases hm : i ∈ L.map e
    · exact List.mem_append.mpr (Or.inr hm)
    · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr
        ⟨Finset.mem_toList.mpr (Finset.mem_univ i), by simpa using hm⟩))

/-- Actual once-per-member subfamily outputs refine the full family's garden outputs. -/
theorem allCoreOutputs_restrict_subset [Fintype ι] [Fintype κ]
    (A : FamilyReconstruction w ι) (e : κ → ι) (he : Function.Injective e) :
    (stateRestrict A e he).allCoreOutputs (p := p) (kind := kind) ⊆
      A.allCoreOutputs (p := p) (kind := kind) := by
  classical
  intro LG hLG
  obtain ⟨B, ⟨L, hL, hb⟩, hB⟩ := (congruent_layered_iff p kind _ LG).mp hLG
  obtain ⟨C, hC, hc⟩ := batch_restrict_lift e he hb A rfl
  let K := Finset.univ.toList.filter (fun i => decide (i ∉ L.map e))
  have hskip : FamilyBatch p kind (K ++ L.map e) A C := by
    induction K with
    | nil => exact hC
    | cons i K ih => exact .skip i ih
  apply (congruent_layered_iff p kind A LG).mpr
  refine ⟨C, ⟨K ++ L.map e, complete_injective_list e he L hL, hskip⟩, ?_⟩
  exact (congrArg FamilyReconstruction.layered hc).trans hB

end WaveTurbulence.VineA
