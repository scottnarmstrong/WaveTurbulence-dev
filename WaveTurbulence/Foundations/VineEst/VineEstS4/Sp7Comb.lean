/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp6KT
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls7Inj
public import WaveTurbulence.Foundations.Stage1.Shared.S1Final

/-! # Class combinatorics at the level of states (V5 Step 4b, step 4, WP-A)

* `diamond_ind`: an operation at `pstar` out of the start of a batch avoiding `pstar` can be transported along the batch
  (Stage 1's `diamond_all`).
* `decomp_state`: every once-per-member batch is an operation at `pstar` first, then a batch over the other members.
* `zp_rev`: a `[pstar]`-batch can be reversed (`FamilyOperation.exists_rev`).
* `y_unique`, `x_unique`, `g_unique`: uniqueness statements from `zp_eq_of_sigStar` and `sigStar_batch`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}

section Comb
variable {pstar : ι}

/-- Transport of an operation at `pstar` along a batch avoiding `pstar` (the Diamond). -/
theorem diamond_ind {M : List ι} {y0 y : FamilyReconstruction w ι} (h : FamilyBatch p kind M y0 y) (hp : pstar ∉ M)
    {x0 : FamilyReconstruction w ι} (hx : FamilyBatch p kind [pstar] y0 x0) :
    ∃ x, FamilyBatch p kind M x0 x ∧ FamilyBatch p kind [pstar] y x := by
  induction h generalizing x0 with
  | nil A => exact ⟨x0, .nil _, hx⟩
  | skip i h ih =>
    obtain ⟨x, h1, h2⟩ := ih (fun e => hp (List.mem_cons_of_mem _ e)) hx
    exact ⟨x, .skip i h1, h2⟩
  | @apply L A B i op h ih =>
    have hip : i ≠ pstar := fun e => hp (e ▸ List.mem_cons_self)
    have hL : pstar ∉ L := fun e => hp (List.mem_cons_of_mem _ e)
    cases hx with
    | skip _ hx' =>
      cases hx'
      obtain ⟨x, h1, h2⟩ := ih hL (.skip pstar (.nil op.output))
      exact ⟨x, .apply op h1, h2⟩
    | apply opp hx' =>
      cases hx'
      let P : Stage1.PairCtx p kind A pstar i :=
        ⟨hip.symm, opp.canonical, opp.eligible, opp.treeCoherent, opp.coupleCoherent, op.eligible, op.treeCoherent,
          op.coupleCoherent⟩
      obtain ⟨opj, opi, hdia⟩ : ∃ (opj : FamilyOperation (p := p) (kind := kind)
          (FamilyOperation.output (⟨P.c, P.el, P.tc, P.cc, opp.choice, opp.construction⟩ :
            FamilyOperation (p := p) (kind := kind) A pstar)) i)
          (opi : FamilyOperation (p := p) (kind := kind)
          (FamilyOperation.output (⟨P.c, P.elJ, P.tcJ, P.ccJ, op.choice, op.construction⟩ :
            FamilyOperation (p := p) (kind := kind) A i)) pstar), opj.output = opi.output := by
        obtain ⟨c1, e1, t1, q1, ε1, k1⟩ := opp
        obtain ⟨c2, e2, t2, q2, ε2, k2⟩ := op
        cases ε1 <;> cases ε2
        · exact P.diamond_FF k1 k2
        · exact P.diamond_FT k1 k2
        · exact P.diamond_TF k1 k2
        · exact P.diamond_TT k1 k2
      obtain ⟨x, h1, h2⟩ := ih hL (.apply opi (.nil _))
      refine ⟨x, .apply opj ?_, h2⟩
      rw [hdia]
      exact h1

/-- A `[i]`-batch can be reversed. -/
theorem zp_rev {i : ι} {y x : FamilyReconstruction w ι} (h : FamilyBatch p kind [i] y x) :
    FamilyBatch p kind [i] x y := by
  cases h with
  | skip _ h1 => cases h1; exact .skip i (.nil _)
  | apply op h1 =>
    cases h1
    obtain ⟨r, hr⟩ := Stage1.FamilyOperation.exists_rev op
    have := FamilyBatch.apply r (FamilyBatch.nil r.output)
    rw [hr] at this
    exact this

variable [DecidableEq ι] [Fintype ι]

/-- Every batch over a permutation of all members is an operation at `pstar` first, then a batch over the others. -/
theorem decomp_state (hc : Stage1.OpsCommute p kind w ι) {A x : FamilyReconstruction w ι} {M0 : List ι}
    (hM0 : M0.Perm Finset.univ.toList) (h : FamilyBatch p kind M0 A x) (pstar : ι) :
    ∃ G : FamilyReconstruction w ι, ∃ M : List ι, FamilyBatch p kind [pstar] A G ∧
      M.Perm (Finset.univ.erase pstar).toList ∧ FamilyBatch p kind M G x := by
  have hnd := perm_univ_nodup hM0
  have hmem : pstar ∈ M0 := hM0.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ _))
  obtain ⟨K1, K2, hK⟩ := List.append_of_mem hmem
  have hb : FamilyBatch p kind (K1 ++ pstar :: K2) A x := by rw [← hK]; exact h
  have hnd' : (pstar :: (K1 ++ K2)).Nodup := by
    have := hnd; rw [hK] at this
    exact List.nodup_middle.mp this
  obtain ⟨hn1, hn2⟩ := List.nodup_cons.mp hnd'
  obtain ⟨B1, h1, h2⟩ := Stage1.familyBatch_split (L1 := K1 ++ [pstar]) (L2 := K2) (by simpa using hb)
  have h1' : FamilyBatch p kind (pstar :: K1) A B1 :=
    familyBatch_moveLeft hc pstar K1 (fun h => hn1 (List.mem_append_left _ h)) h1
  have hb' : FamilyBatch p kind ([pstar] ++ (K1 ++ K2)) A x := by
    have := Stage1.familyBatch_append h1' h2
    simpa using this
  obtain ⟨G, hG1, hG2⟩ := Stage1.familyBatch_split hb'
  refine ⟨G, K1 ++ K2, hG1, ?_, hG2⟩
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

/-- Moving the operation at `pstar` from first to last. -/
theorem move_last (hc : Stage1.OpsCommute p kind w ι) {A G x : FamilyReconstruction w ι} {M : List ι} {pstar : ι}
    (hp : pstar ∉ M) (h1 : FamilyBatch p kind [pstar] A G) (h2 : FamilyBatch p kind M G x) :
    ∃ y, FamilyBatch p kind M A y ∧ FamilyBatch p kind [pstar] y x := by
  have h := Stage1.familyBatch_append h1 h2
  have h' := Stage1.familyBatch_moveRight hc pstar M hp (by simpa using h)
  exact Stage1.familyBatch_split h'

end Comb

section Uniq
variable [DecidableEq ι] {A : FamilyReconstruction w ι} {pstar : ι}

theorem sigStar_of_batch {M : List ι} {A y : FamilyReconstruction w ι} (hp : pstar ∉ M)
    (h : FamilyBatch p kind M A y) : sigStar y pstar = sigStar A pstar := sigStar_batch h hp

/-- Two states reached from `A` by batches avoiding `pstar`, with the same successor under `[pstar]`, coincide. -/
theorem y_unique (hA : IsPrimeGarden A.skeleton) {M1 M2 : List ι} (h1 : pstar ∉ M1) (h2 : pstar ∉ M2)
    {y1 y2 x : FamilyReconstruction w ι} (hy1 : FamilyBatch p kind M1 A y1) (hy2 : FamilyBatch p kind M2 A y2)
    (hx1 : FamilyBatch p kind [pstar] y1 x) (hx2 : FamilyBatch p kind [pstar] y2 x) : y1 = y2 := by
  have hxp : IsPrimeGarden x.skeleton :=
    batch_prime (Stage1.familyBatch_append hy1 hx1) hA
  exact zp_eq_of_sigStar hxp (zp_rev hx1) (zp_rev hx2)
    ((sigStar_batch hy1 h1).trans (sigStar_batch hy2 h2).symm)

/-- Two states reached from `G` by batches avoiding `pstar`, with a common predecessor under `[pstar]`, coincide. -/
theorem x_unique {G y : FamilyReconstruction w ι} (hy : IsPrimeGarden y.skeleton) {M1 M2 : List ι} (h1 : pstar ∉ M1)
    (h2 : pstar ∉ M2) {x1 x2 : FamilyReconstruction w ι} (hx1 : FamilyBatch p kind M1 G x1)
    (hx2 : FamilyBatch p kind M2 G x2) (hy1 : FamilyBatch p kind [pstar] y x1) (hy2 : FamilyBatch p kind [pstar] y x2) :
    x1 = x2 :=
  zp_eq_of_sigStar hy hy1 hy2 ((sigStar_batch hx1 h1).trans (sigStar_batch hx2 h2).symm)

/-- Two operations at `pstar` from `A` whose outputs have a common descendant by batches avoiding `pstar` coincide. -/
theorem g_unique (hA : IsPrimeGarden A.skeleton) {M1 M2 : List ι} (h1 : pstar ∉ M1) (h2 : pstar ∉ M2)
    {G1 G2 x : FamilyReconstruction w ι} (hG1 : FamilyBatch p kind [pstar] A G1) (hG2 : FamilyBatch p kind [pstar] A G2)
    (hx1 : FamilyBatch p kind M1 G1 x) (hx2 : FamilyBatch p kind M2 G2 x) : G1 = G2 :=
  zp_eq_of_sigStar hA hG1 hG2 ((sigStar_batch hx1 h1).symm.trans (sigStar_batch hx2 h2))

end Uniq

end WaveTurbulence.VineEstS4
