/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Final
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Canon

/-! # Class combinatorics, part 1: moving an operation to the front (V5 Step 4b, step 4, WP-A)

`familyBatch_moveLeft`: the converse of Stage 1's `familyBatch_moveRight`.  An operation at `i` performed LAST in a batch over a
list `K ++ [i]` with `i ∉ K` can be performed FIRST: `FamilyBatch (i :: K)` (uses `Stage1.opsCommute_all`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.LFTwist

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}

theorem familyBatch_moveLeft (hc : Stage1.OpsCommute p kind w ι) (i : ι) :
    ∀ (K : List ι), i ∉ K → ∀ {X Y : FamilyReconstruction w ι},
      FamilyBatch p kind (K ++ [i]) X Y → FamilyBatch p kind (i :: K) X Y := by
  intro K
  induction K with
  | nil =>
    intro _ X Y h
    exact h
  | cons k K ih =>
    intro hi X Y h
    have hik : k ≠ i := fun e => hi (by simp [e])
    have hiK : i ∉ K := fun e => hi (List.mem_cons_of_mem _ e)
    cases h with
    | skip _ h1 =>
      have h2 := ih hiK h1
      cases h2 with
      | skip _ h3 => exact .skip i (.skip k h3)
      | apply op h3 => exact .apply op (.skip k h3)
    | apply op1 h1 =>
      have h2 := ih hiK h1
      cases h2 with
      | skip _ h3 => exact .skip i (.apply op1 h3)
      | apply op2 h3 =>
        obtain ⟨op2', op1', hop⟩ := hc X k i hik op1 op2
        refine .apply op2' (.apply op1' ?_)
        rw [hop]
        exact h3

/-- Concatenation of two reached regions. -/
theorem Reach.append {L1 L2 : List ι} {A B C : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    {c' : ChainAt B.skeleton B.family} {c'' : ChainAt C.skeleton C.family}
    (h1 : Reach p kind L1 A c B c') (h2 : Reach p kind L2 B c' C c'') : Reach p kind (L1 ++ L2) A c C c'' := by
  induction h1 with
  | nil A c => exact h2
  | skip i h ih => exact .skip i (ih h2)
  | apply op h ih => exact .apply op (ih h2)

section Decomp
variable [Fintype ι] [DecidableEq ι] {A : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}

/-- **The class decomposes along an operation at `pstar` performed first.**  Every canonical representative is reached from a
state `y` obtained by (at most) one operation at `pstar` by a batch over the other members. -/
theorem canonReps_decomp (hc : Stage1.OpsCommute p kind w ι) (pstar : ι)
    {x : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family} (hx : x ∈ CanonRepsK p kind A c) :
    ∃ y : (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family),
      Reach p kind [pstar] A c y.1 y.2 ∧
        ∃ M : List ι, M.Perm (Finset.univ.erase pstar).toList ∧ Reach p kind M y.1 y.2 x.1 x.2 := by
  obtain ⟨M0, hM0, hr⟩ := hx
  have hnd := perm_univ_nodup hM0
  have hmem : pstar ∈ M0 := hM0.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ _))
  obtain ⟨K1, K2, hK⟩ := List.append_of_mem hmem
  have hb : FamilyBatch p kind (K1 ++ pstar :: K2) A x.1 := by rw [← hK]; exact hr.batch
  have hnd' : (pstar :: (K1 ++ K2)).Nodup := by
    have := hnd; rw [hK] at this
    exact List.nodup_middle.mp this
  obtain ⟨hn1, hn2⟩ := List.nodup_cons.mp hnd'
  obtain ⟨B1, h1, h2⟩ := Stage1.familyBatch_split (L1 := K1 ++ [pstar]) (L2 := K2) (by simpa using hb)
  have h1' : FamilyBatch p kind (pstar :: K1) A B1 :=
    familyBatch_moveLeft hc pstar K1 (fun h => hn1 (List.mem_append_left _ h)) h1
  have hb' : FamilyBatch p kind ([pstar] ++ (K1 ++ K2)) A x.1 := by
    have := Stage1.familyBatch_append h1' h2
    simpa using this
  obtain ⟨G, hG1, hG2⟩ := Stage1.familyBatch_split hb'
  obtain ⟨cG, hrG⟩ := batch_reach hG1 c
  obtain ⟨cx, hrx⟩ := batch_reach hG2 cG
  have hperm : (K1 ++ K2).Perm (Finset.univ.erase pstar).toList := by
    refine List.perm_of_nodup_nodup_toFinset_eq hn2 (Finset.nodup_toList _) ?_
    ext y
    simp only [List.mem_toFinset, Finset.toList_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hy hyp
      exact hn1 (hyp ▸ hy)
    · intro hyp
      have : y ∈ M0 := hM0.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ _))
      rw [hK] at this
      simp only [List.mem_append, List.mem_cons] at this ⊢
      rcases this with h | h | h
      · exact Or.inl h
      · exact absurd h hyp
      · exact Or.inr h
  have hcx : cx = x.2 := by
    have hall := Reach.append hrG hrx
    exact Reach.region_unique (perm_univ_nodup (M := [pstar] ++ (K1 ++ K2)) (by
      refine List.Perm.trans ?_ hM0
      rw [hK]; simpa using List.perm_middle.symm)) hnd hall hr
  exact ⟨⟨G, cG⟩, hrG, K1 ++ K2, hperm, hcx ▸ hrx⟩

/-- Conversely, the batch over the other members from a state reached by one operation at `pstar` is canonical. -/
theorem mem_canonReps_of_decomp (pstar : ι) {y : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family}
    (hy : Reach p kind [pstar] A c y.1 y.2) {M : List ι} (hM : M.Perm (Finset.univ.erase pstar).toList)
    {x : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family} (hx : Reach p kind M y.1 y.2 x.1 x.2) :
    x ∈ CanonRepsK p kind A c := by
  refine ⟨[pstar] ++ M, ?_, Reach.append hy hx⟩
  have hnd : (pstar :: M).Nodup := by
    refine List.nodup_cons.mpr ⟨fun h => ?_, hM.nodup_iff.mpr (Finset.nodup_toList _)⟩
    have := hM.mem_iff.mp h
    simp at this
  refine List.perm_of_nodup_nodup_toFinset_eq (by simpa using hnd) (Finset.nodup_toList _) ?_
  ext z
  simp only [List.mem_toFinset, Finset.toList_toFinset, Finset.mem_univ, iff_true, List.mem_append,
    List.mem_singleton]
  by_cases hz : z = pstar
  · exact Or.inl hz
  · exact Or.inr (hM.mem_iff.mpr (by simpa using hz))

end Decomp

end WaveTurbulence.VineEstS4
