/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp5Reach
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp8Fib
public import WaveTurbulence.Foundations.VineEst.VineEstS4.BaseCase

/-! # The case `p*` = bottom piece (V5 Step 4b, step 4)

If every member other than `pstar` carries no operation at the start `A` (this is the situation of TARGET (tildeJ2) when `p*`
is the bottom piece: there is no lower block, `K̃^{U<p}` is trivial and `Y(A) = {A}`), the canonical representatives are exactly the
states reached from `A` by one operation at `pstar` or by skipping it (`Zp(A)`): `mem_canonFinset_iff_bottom`.  Hence the class
sum is the sum over `Zp(A)` of the kernels `K^U_G` itself (the Step 3 form).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} [Fintype ι] [DecidableEq ι]

theorem reach_only_pstar (hc : Stage1.OpsCommute p kind w ι) {A0 : FamilyReconstruction w ι}
    (hA0 : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A0 j))
    {M : List ι} {A B : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family} {cB : ChainAt B.skeleton B.family}
    (h : Reach p kind M A c B cB) :
    ∀ {Lpre : List ι}, FamilyBatch p kind Lpre A0 A → (Lpre ++ M).Nodup →
      Reach p kind (M.filter (fun i => i == pstar)) A c B cB := by
  induction h with
  | nil A c => intros; exact .nil A c
  | @skip L A c B c' i h ih =>
    intro Lpre hpre hnd
    have hnd' : (Lpre ++ L).Nodup := hnd.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
    have := ih hpre hnd'
    by_cases hi : i = pstar
    · subst hi
      rw [List.filter_cons_of_pos (by simp)]
      exact .skip i this
    · rw [List.filter_cons_of_neg (by simpa using hi)]
      exact this
  | @apply L A c B c' i op h ih =>
    intro Lpre hpre hnd
    have hnd' : (Lpre ++ i :: L).Nodup := hnd
    have hiL : i ∉ Lpre := by
      intro hh
      have := List.nodup_append.mp hnd'
      exact this.2.2 i hh i (List.mem_cons_self) rfl
    have hip : i = pstar := by
      by_contra hne
      exact (noop_batch hc hpre hiL (hA0 i hne)).false op
    subst hip
    have h1 := ih (Lpre := Lpre ++ [i]) (Stage1.familyBatch_append hpre (.apply op (.nil _))) (by simpa using hnd')
    rw [List.filter_cons_of_pos (by simp)]
    exact .apply op h1

theorem filter_perm_univ {M : List ι} (hM : M.Perm Finset.univ.toList) :
    M.filter (fun i => i == pstar) = [pstar] := by
  have h1 : M.count pstar = 1 := by
    rw [hM.count_eq]
    exact List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)
  rw [List.filter_beq, h1]
  rfl

theorem mem_canonFinset_iff_bottom {A0 : FamilyReconstruction w ι} (hA : IsPrimeGarden A0.skeleton)
    (hA0 : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A0 j))
    {c : ChainAt A0.skeleton A0.family} {x : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family} :
    x ∈ canonFinsetK p kind A0 c ↔ Reach p kind [pstar] A0 c x.1 x.2 := by
  rw [mem_canonFinset hA]
  constructor
  · rintro ⟨M, hM, h⟩
    have := reach_only_pstar Stage1.opsCommute_all hA0 h (Lpre := []) (FamilyBatch.nil A0) (by simpa using perm_univ_nodup hM)
    rwa [filter_perm_univ hM] at this
  · intro h
    exact ⟨[pstar] ++ (Finset.univ.erase pstar).toList, perm_cons_erase pstar,
      Reach.append h (reach_skips x.2 _)⟩

end WaveTurbulence.VineEstS4
