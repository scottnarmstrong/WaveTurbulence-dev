/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.CanonStatement
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Final3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.RestrictState
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp17Suffix
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp18Geom

/-! # Interval blocks of a chain assembly and the nested splits (V5 Step 4d part C, WP-I)

`iregion B i j` is the union of the atoms of the pieces `i ≤ l < j` (pieces numbered from the bottom), `jointAt B l` the joint between
pieces `l - 1` and `l` (`jointAt B 0 = b`, `jointAt B n = a`).  `iregion_chain`: pieces `[i, j)` form a vine chain from
`jointAt j` to `jointAt i`; `iregion_upper_block`, `lower_block`, `interval_block`: the regions above/below/between joints
are blocks; `mkSplitAt`: the `SplitAt` of the chain region `iregion B 0 k0` of a restricted family at the member of piece
index `k < k0` (upper block `[k, k0)`, lower block `[0, k)`).  With `RestrictState` this makes `tildeJ2_canon` /
`tildeJ2_bundle` available at every level of the induction on the number of core vines (TARGET Step 4).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.Twist
  WaveTurbulence.RegRed TTree Finset

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

open Classical in
/-- The atoms of the pieces `i ≤ l < j` of a chain assembly (pieces numbered from the bottom). -/
noncomputable def iregion {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (i j : ℕ) : Finset (GBranch G.tree) :=
  match B with
  | .single (U := U) _ _ => if i = 0 ∧ 0 < j then U else ∅
  | .append (T := T) B _ _ _ _ => (if i = 0 ∧ 0 < j then T else ∅) ∪ iregion B (i - 1) (j - 1)

/-- The joint between the pieces `l - 1` and `l` (`0`: the bottom `b`; `n`: the top `a`). -/
noncomputable def jointAt {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (l : ℕ) : GBranch G.tree :=
  match B with
  | .single (a := a) (b := b) _ _ => if l = 0 then b else a
  | .append (c := c) B _ _ _ _ => if l = 0 then c else jointAt B (l - 1)

theorem iregion_append {S T : Finset (GBranch G.tree)} {a' b' c' : GBranch G.tree} {n' : ℕ} {RP : CLRegionData G S a' b'}
    (B : CLChainAssembly G RP n') {X : VineType} (hT : G.molecule.IsVine X T b' c') (hi : S ∩ T = {b'})
    (hU : G.molecule.IsBlock (S ∪ T) a' c') (R : CLRegionData G (S ∪ T) a' c') (i j : ℕ) :
    iregion (CLChainAssembly.append B hT hi hU R) i j =
      (open Classical in (if i = 0 ∧ 0 < j then T else ∅)) ∪ iregion B (i - 1) (j - 1) := rfl

theorem iregion_full (B : CLChainAssembly G R n) : iregion B 0 n = U := by
  induction B with
  | single hV R => simp [iregion]
  | append B hT hi hU R ih =>
    simp [iregion, ih]
    exact union_comm _ _

theorem iregion_subset (B : CLChainAssembly G R n) (i j : ℕ) : iregion B i j ⊆ U := by
  induction B generalizing i j with
  | single hV R => unfold iregion; split_ifs <;> simp
  | append B hT hi hU R ih =>
    unfold iregion
    refine Finset.union_subset ?_ ((ih _ _).trans Finset.subset_union_left)
    split_ifs
    · exact Finset.subset_union_right
    · exact Finset.empty_subset _

theorem iregion_zero_right (B : CLChainAssembly G R n) (i : ℕ) : iregion B i 0 = ∅ := by
  induction B generalizing i with
  | single hV R => simp [iregion]
  | append B hT hi hU R ih => simp [iregion, ih]

theorem jointAt_zero (B : CLChainAssembly G R n) : jointAt B 0 = b := by
  cases B <;> simp [jointAt]

theorem jointAt_top (B : CLChainAssembly G R n) : jointAt B n = a := by
  induction B with
  | single hV R => simp [jointAt]
  | append B hT hi hU R ih => simp [jointAt, ih]

/-- **The pieces `i ≤ l < j` of an assembly form a vine chain from the joint `j` to the joint `i`.** -/
theorem iregion_chain (B : CLChainAssembly G R n) :
    ∀ i j : ℕ, i < j → j ≤ n → Vine.Chain G.molecule (iregion B i j) (jointAt B j) (jointAt B i) (j - i) := by
  induction B with
  | single hV R =>
    intro i j hij hj
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 1 := by omega
    simp only [iregion, jointAt]
    simpa using Vine.Chain.single ⟨_, hV⟩
  | @append S T a' b' c' n' RP B X hT hi hU R ih =>
    intro i j hij hj
    have hj0 : j ≠ 0 := by omega
    by_cases hi0 : i = 0
    · subst hi0
      simp only [iregion, jointAt, hj0, ite_true, true_and, Nat.pos_of_ne_zero hj0, and_self, ite_false]
      rcases Nat.lt_or_ge 1 j with h2 | h2
      · have hch := ih 0 (j - 1) (by omega) (by omega)
        rw [jointAt_zero] at hch
        have hSsub := iregion_subset B 0 (j - 1)
        have hjoint := Vine.chain_joints_mem hch
        have hbc : b' ≠ c' := by
          have hch1 : Vine.Chain G.molecule T b' c' 1 := Vine.Chain.single ⟨X, hT⟩
          exact chain_joints_ne hch1
        have hi' : iregion B 0 (j - 1) ∩ T = {b'} := by
          ext x
          constructor
          · intro hx
            have : x ∈ S ∩ T := mem_inter.mpr ⟨hSsub (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩
            rwa [hi] at this
          · intro hx
            rw [mem_singleton] at hx; subst hx
            exact mem_inter.mpr ⟨hjoint.2, (Vine.chain_joints_mem (Vine.Chain.single ⟨X, hT⟩)).1⟩
        have hne : jointAt B (j - 1) ≠ c' := by
          intro h
          have h1 : c' ∈ S := hSsub (h ▸ hjoint.1)
          have h2 : c' ∈ S ∩ T := mem_inter.mpr ⟨h1, (Vine.chain_joints_mem (Vine.Chain.single ⟨X, hT⟩)).2⟩
          rw [hi] at h2
          exact hbc (mem_singleton.mp h2).symm
        have := Vine.Chain.append hch ⟨X, hT⟩ hi' hne
        rw [union_comm] at this
        have e : j - 1 - 0 + 1 = j - 0 := by omega
        have h01 : (0 : ℕ) - 1 = 0 := rfl
        rw [h01]
        exact (congrArg (fun m => Vine.Chain G.molecule (T ∪ iregion B 0 (j - 1)) (jointAt B (j - 1)) c' m) e).mp this
      · obtain rfl : j = 1 := by omega
        have h01 : (0 : ℕ) - 1 = 0 := rfl
        rw [iregion_zero_right, union_empty, jointAt_zero]
        exact Vine.Chain.single ⟨X, hT⟩
    · simp only [iregion, jointAt, hi0, hj0, ite_false, false_and, empty_union]
      have := ih (i - 1) (j - 1) (by omega) (by omega)
      have e : (j - 1) - (i - 1) = j - i := by omega
      exact (congrArg (fun m => Vine.Chain G.molecule (iregion B (i - 1) (j - 1)) (jointAt B (j - 1)) (jointAt B (i - 1)) m) e).mp this


theorem piece_lower_eq_jointAt (B : CLChainAssembly G R n) (l : ℕ) (h : l < n) :
    (assemblyPieceAt B ⟨l, h⟩).lower = jointAt B l := by
  induction B generalizing l with
  | single hV R =>
    obtain rfl : l = 0 := by omega
    simp [assemblyPieceAt, jointAt]
  | append B hT hi hU R ih =>
    cases l with
    | zero => simp [assemblyPieceAt, jointAt]
    | succ l' =>
      have := ih l' (by omega)
      simpa [assemblyPieceAt, jointAt] using this

theorem piece_atoms_sub_iregion (B : CLChainAssembly G R n) (i j l : ℕ) (hil : i ≤ l) (hlj : l < j) (h : l < n) :
    (assemblyPieceAt B ⟨l, h⟩).atoms ⊆ iregion B i j := by
  induction B generalizing i j l with
  | single hV R =>
    obtain rfl : l = 0 := by omega
    obtain rfl : i = 0 := by omega
    simp [assemblyPieceAt, iregion]
    have : 0 < j := by omega
    simp [this]
  | append B hT hi hU R ih =>
    cases l with
    | zero =>
      obtain rfl : i = 0 := by omega
      have : 0 < j := by omega
      simp [assemblyPieceAt, iregion, this]
    | succ l' =>
      have := ih (i - 1) (j - 1) l' (by omega) (by omega) (by omega)
      simp only [assemblyPieceAt]
      have hs : iregion B (i - 1) (j - 1) ⊆ iregion (CLChainAssembly.append B hT hi hU R) i j := by
        rw [iregion_append]; exact Finset.subset_union_right
      exact this.trans hs

theorem iregion_union_zero (B : CLChainAssembly G R n) (j l : ℕ) (hjl : j ≤ l) :
    iregion B 0 j ∪ iregion B j l = iregion B 0 l := by
  induction B generalizing j l with
  | single hV R =>
    unfold iregion
    by_cases hj : j = 0
    · subst hj; simp
    · have : 0 < j := Nat.pos_of_ne_zero hj
      have hl : 0 < l := by omega
      simp [hj, this, hl]
  | append B hT hi hU R ih =>
    unfold iregion
    by_cases hj : j = 0
    · subst hj; simp [iregion_zero_right]
    · have h1 : 0 < j := Nat.pos_of_ne_zero hj
      have hl : 0 < l := by omega
      have := ih (j - 1) (l - 1) (by omega)
      simp only [true_and, h1, hl, hj, and_false, if_true, if_false, ite_true, ite_false, empty_union, true_and]
      rw [← this]
      simp only [Nat.zero_sub]
      ext x; simp only [mem_union]; tauto

theorem iregion_upper_block (B : CLChainAssembly G R n) :
    ∀ k : ℕ, 1 ≤ k → k < n → G.molecule.IsBlock (iregion B k n) a (jointAt B k) := by
  induction B with
  | single hV R => intro k h1 h2; omega
  | @append S T a' b' c' n' RP B X hT hi hU R ih =>
    intro k h1 h2
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      have h := iregion_full B
      simp only [iregion, jointAt]
      simp only [one_ne_zero, ite_false, false_and, empty_union, Nat.add_sub_cancel, Nat.sub_self]
      rw [h, jointAt_zero]
      exact B.isBlock
    · have := ih (k - 1) (by omega) (by omega)
      have hk0 : k ≠ 0 := by omega
      simp only [iregion, jointAt, hk0, ite_false, false_and, empty_union]
      simpa using this


theorem jointAt_mem_lower (B : CLChainAssembly G R n) (i j : ℕ) (hij : i < j) (hj : j ≤ n) :
    jointAt B j ∈ iregion B i j ∧ jointAt B i ∈ iregion B i j :=
  Vine.chain_joints_mem (iregion_chain B i j hij hj)

theorem jointAt_ne (B : CLChainAssembly G R n) (i j : ℕ) (hij : i < j) (hj : j ≤ n) :
    jointAt B j ≠ jointAt B i :=
  chain_joints_ne (iregion_chain B i j hij hj)

theorem iregion_inter (B : CLChainAssembly G R n) :
    ∀ k : ℕ, 1 ≤ k → k < n → iregion B k n ∩ iregion B 0 k = {jointAt B k} := by
  induction B with
  | single hV R => intro k h1 h2; omega
  | @append S T a' b' c' n' RP B X hT hi hU R ih =>
    intro k h1 h2
    have hch1 : Vine.Chain G.molecule T b' c' 1 := Vine.Chain.single ⟨X, hT⟩
    have hjT := Vine.chain_joints_mem hch1
    have hfull := iregion_full B
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      have e1 : iregion (CLChainAssembly.append B hT hi hU R) 1 (n' + 1) = S := by
        rw [iregion_append]; simp [hfull]
      have e2 : iregion (CLChainAssembly.append B hT hi hU R) 0 1 = T := by
        rw [iregion_append]; simp [iregion_zero_right]
      have e3 : jointAt (CLChainAssembly.append B hT hi hU R) 1 = b' := by
        simp [jointAt, jointAt_zero]
      rw [e1, e2, e3, hi]
    · have hk0 : k ≠ 0 := by omega
      have hSsub := iregion_subset B (k - 1) n'
      have e1 : iregion (CLChainAssembly.append B hT hi hU R) k (n' + 1) = iregion B (k - 1) n' := by
        rw [iregion_append]; simp [hk0]
      have e2 : iregion (CLChainAssembly.append B hT hi hU R) 0 k = T ∪ iregion B 0 (k - 1) := by
        rw [iregion_append]; simp [Nat.pos_of_ne_zero hk0]
      have e3 : jointAt (CLChainAssembly.append B hT hi hU R) k = jointAt B (k - 1) := by
        simp [jointAt, hk0]
      rw [e1, e2, e3]
      have IH := ih (k - 1) (by omega) (by omega)
      have hb0 : b' ∈ iregion B 0 (k - 1) := by
        have := (jointAt_mem_lower B 0 (k - 1) (by omega) (by omega)).2
        rwa [jointAt_zero] at this
      ext x
      simp only [mem_inter, mem_union, mem_singleton]
      constructor
      · rintro ⟨hx1, hx2 | hx2⟩
        · exfalso
          have hxb : x = b' := by
            have : x ∈ S ∩ T := mem_inter.mpr ⟨hSsub hx1, hx2⟩
            rwa [hi, mem_singleton] at this
          subst hxb
          have hh : x ∈ iregion B (k - 1) n' ∩ iregion B 0 (k - 1) := mem_inter.mpr ⟨hx1, hb0⟩
          rw [IH, mem_singleton] at hh
          have hne := jointAt_ne B 0 (k - 1) (by omega) (by omega)
          rw [jointAt_zero] at hne
          exact hne hh.symm
        · have hh : x ∈ iregion B (k - 1) n' ∩ iregion B 0 (k - 1) := mem_inter.mpr ⟨hx1, hx2⟩
          rwa [IH, mem_singleton] at hh
      · intro hx
        subst hx
        have hh : jointAt B (k - 1) ∈ iregion B (k - 1) n' ∩ iregion B 0 (k - 1) := by
          rw [IH]; exact mem_singleton_self _
        exact ⟨(mem_inter.mp hh).1, Or.inr (mem_inter.mp hh).2⟩


theorem iregion_union (B : CLChainAssembly G R n) (i j l : ℕ) (hij : i ≤ j) (hjl : j ≤ l) :
    iregion B i j ∪ iregion B j l = iregion B i l := by
  induction B generalizing i j l with
  | single hV R =>
    unfold iregion
    by_cases hj : j = 0
    · subst hj
      obtain rfl : i = 0 := by omega
      simp
    · have h1 : 0 < j := Nat.pos_of_ne_zero hj
      have hl : 0 < l := by omega
      by_cases hi : i = 0
      · subst hi; simp [hj, h1, hl]
      · simp [hj, hi, h1, hl]
  | append B hT hi hU R ih =>
    rw [iregion_append, iregion_append, iregion_append]
    by_cases hj : j = 0
    · subst hj
      obtain rfl : i = 0 := by omega
      simp [iregion_zero_right]
    · have h1 : 0 < j := Nat.pos_of_ne_zero hj
      have hl : 0 < l := by omega
      have := ih (i - 1) (j - 1) (l - 1) (by omega) (by omega)
      rw [← this]
      by_cases hi0 : i = 0
      · subst hi0
        simp only [true_and, h1, hl, hj, ite_true, and_false, ite_false, empty_union]
        try (ext x; simp only [mem_union]; tauto)
      · simp only [hi0, hj, false_and, and_false, ite_false, empty_union]
        try (ext x; simp only [mem_union]; tauto)


theorem iregion_mono_right (B : CLChainAssembly G R n) (i j l : ℕ) (hij : i ≤ j) (hjl : j ≤ l) :
    iregion B i j ⊆ iregion B i l := by
  rw [← iregion_union B i j l hij hjl]; exact Finset.subset_union_left

theorem iregion_mono_left (B : CLChainAssembly G R n) (i j l : ℕ) (hij : i ≤ j) (hjl : j ≤ l) :
    iregion B j l ⊆ iregion B i l := by
  rw [← iregion_union B i j l hij hjl]; exact Finset.subset_union_right

theorem lower_block (B : CLChainAssembly G R n) (k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    G.molecule.IsBlock (iregion B 0 k) (jointAt B k) b := by
  have hS := iregion_upper_block B k hk hkn
  have hch := iregion_chain B 0 k (by omega) (by omega)
  rw [jointAt_zero] at hch
  have hi := iregion_inter B k hk hkn
  have hU : G.molecule.IsBlock (iregion B k n ∪ iregion B 0 k) a b := by
    rw [union_comm, iregion_union B 0 k n (by omega) (by omega), iregion_full]
    exact B.isBlock
  exact chain_suffix_currentBlock G.molecule (Mole.garden_isMolecule G) hS hch hi hU

theorem interval_block (B : CLChainAssembly G R n) (k k0 : ℕ) (hk : 1 ≤ k) (hkk0 : k < k0) (hk0 : k0 ≤ n) :
    G.molecule.IsBlock (iregion B k k0) (jointAt B k0) (jointAt B k) := by
  rcases Nat.lt_or_ge k0 n with h | h
  · have hS := iregion_upper_block B k0 (by omega) h
    have hch := iregion_chain B k k0 hkk0 hk0
    have hi : iregion B k0 n ∩ iregion B k k0 = {jointAt B k0} := by
      have h1 := iregion_inter B k0 (by omega) h
      refine Finset.Subset.antisymm ?_ ?_
      · rw [← h1]
        exact Finset.inter_subset_inter (Finset.Subset.refl _) (iregion_mono_left B 0 k k0 (by omega) hkk0.le)
      · intro x hx
        rw [mem_singleton] at hx; subst hx
        exact mem_inter.mpr ⟨(jointAt_mem_lower B k0 n h (le_refl _)).2, (jointAt_mem_lower B k k0 hkk0 hk0).1⟩
    have hU : G.molecule.IsBlock (iregion B k0 n ∪ iregion B k k0) a (jointAt B k) := by
      rw [union_comm, iregion_union B k k0 n hkk0.le h.le]
      exact iregion_upper_block B k hk (by omega)
    exact chain_suffix_currentBlock G.molecule (Mole.garden_isMolecule G) hS hch hi hU
  · obtain rfl : k0 = n := le_antisymm hk0 h
    rw [jointAt_top]
    exact iregion_upper_block B k hk hkk0


/-- **The split of the chain region `iregion B 0 k0` (a chain region of the restricted family) at the lower joint of the member with
piece index `k`** (`1 ≤ k < k0 ≤ n`): upper block = pieces `[k, k0)`, lower block = pieces `< k`. -/
noncomputable def mkSplitAt (B : CLChainAssembly G R n) {ι' : Type*} (e : ι' → (assemblySourceFamily B).CoreIndex)
    (he : Function.Injective e) (k k0 : ℕ) (hk : 1 ≤ k) (hkk0 : k < k0) (hk0 : k0 ≤ n) (pstar : ι')
    (hp : (e pstar).1.val = k)
    (c : ChainAt G (restrictFamily (assemblySourceFamily B).coreFamily e he))
    (hcU : c.U = iregion B 0 k0) (hca : c.a = jointAt B k0) (hcb : c.b = b) :
    SplitAt G (restrictFamily (assemblySourceFamily B).coreFamily e he) pstar {j | (e j).1.val < k} where
  c := c
  sb := ⟨iregion B k k0, jointAt B k0, jointAt B k, interval_block B k k0 hk hkk0 hk0⟩
  tb := ⟨iregion B 0 k, jointAt B k, b, by
    have := lower_block B k hk (by omega); exact this⟩
  sa := hca.symm
  tbb := hcb.symm
  joint := rfl
  bk := by
    have h1 := ((assemblySourceFamily B).corePlacement_at (e pstar)).1
    change jointAt B k = ((assemblySourceFamily B).corePlacement (e pstar)).lower
    rw [h1]
    have := piece_lower_eq_jointAt B k (by omega)
    have e1 : (e pstar).1 = ⟨k, by omega⟩ := Fin.ext hp
    change jointAt B k = (assemblyPieceAt B (e pstar).1).lower
    rw [e1]; exact this.symm
  inter := by
    have h1 := iregion_inter B k hk (by omega)
    show iregion B k k0 ∩ iregion B 0 k = {jointAt B k}
    refine Finset.Subset.antisymm ?_ ?_
    · rw [← h1]
      exact Finset.inter_subset_inter (iregion_mono_right B k k0 n hkk0.le hk0) (Finset.Subset.refl _)
    · intro x hx
      rw [mem_singleton] at hx; subst hx
      exact mem_inter.mpr ⟨(jointAt_mem_lower B k k0 hkk0 hk0).2, (jointAt_mem_lower B 0 k (by omega) (by omega)).1⟩
  union := by
    show c.U = iregion B k k0 ∪ iregion B 0 k
    rw [hcU, union_comm, iregion_union B 0 k k0 (by omega) hkk0.le]
  atomsJ := fun j hj => by
    have hj' : (e j).1.val < k := hj
    show (assemblyPieceAt B (e j).1).atoms ⊆ iregion B 0 k
    exact piece_atoms_sub_iregion B 0 k (e j).1.val (by omega) hj' (e j).1.2
  lowJ := fun j hj => by
    have hj' : (e j).1.val < k := hj
    have h1 := ((assemblySourceFamily B).corePlacement_at (e j)).1
    change ((assemblySourceFamily B).corePlacement (e j)).lower ≠ jointAt B k
    rw [h1]
    change (assemblyPieceAt B (e j).1).lower ≠ jointAt B k
    have := piece_lower_eq_jointAt B (e j).1.val (e j).1.2
    rw [show (⟨(e j).1.val, (e j).1.2⟩ : Fin n) = (e j).1 from rfl] at this
    rw [this]
    exact (jointAt_ne B (e j).1.val k hj' (by omega)).symm

end WaveTurbulence.VineEstS5C
