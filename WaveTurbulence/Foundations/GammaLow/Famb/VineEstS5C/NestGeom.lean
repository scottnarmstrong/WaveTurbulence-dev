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
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainPrefixBlocks
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.NestGeom
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowSum
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.NestGeom` (sha256 3ed800c415010233…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

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
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.Twist WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.RegRed TTree Finset

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

open Classical in
/-- The atoms of the pieces `i ≤ l < j` of a chain assembly (pieces numbered from the bottom). -/
noncomputable def iregionΓ {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) (i j : ℕ) : Finset (GBranch G.tree) :=
  match B with
  | .single (U := U) _ _ => if i = 0 ∧ 0 < j then U else ∅
  | .append (T := T) B _ _ _ _ => (if i = 0 ∧ 0 < j then T else ∅) ∪ iregionΓ B (i - 1) (j - 1)

/-- The joint between the pieces `l - 1` and `l` (`0`: the bottom `b`; `n`: the top `a`). -/
noncomputable def jointAtΓ {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) (l : ℕ) : GBranch G.tree :=
  match B with
  | .single (a := a) (b := b) _ _ => if l = 0 then b else a
  | .append (c := c) B _ _ _ _ => if l = 0 then c else jointAtΓ B (l - 1)

theorem iregion_appendΓ {S T : Finset (GBranch G.tree)} {a' b' c' : GBranch G.tree} {n' : ℕ} {RP : CLRegionData G S a' b'}
    (B : CLChainAssemblyΓ γF G RP n') (hT : FinalCount.Src.IsSomeVine γF G.molecule T b' c') (hi : S ∩ T = {b'})
    (hU : G.molecule.IsBlock (S ∪ T) a' c') (R : CLRegionData G (S ∪ T) a' c') (i j : ℕ) :
    iregionΓ (CLChainAssemblyΓ.append B hT hi hU R) i j =
      (open Classical in (if i = 0 ∧ 0 < j then T else ∅)) ∪ iregionΓ B (i - 1) (j - 1) := rfl

theorem iregion_fullΓ (B : CLChainAssemblyΓ γF G R n) : iregionΓ B 0 n = U := by
  induction B with
  | single hV R => simp [iregionΓ]
  | append B hT hi hU R ih =>
    simp [iregionΓ, ih]
    exact union_comm _ _

theorem iregion_subsetΓ (B : CLChainAssemblyΓ γF G R n) (i j : ℕ) : iregionΓ B i j ⊆ U := by
  induction B generalizing i j with
  | single hV R => unfold iregionΓ; split_ifs <;> simp
  | append B hT hi hU R ih =>
    unfold iregionΓ
    refine Finset.union_subset ?_ ((ih _ _).trans Finset.subset_union_left)
    split_ifs
    · exact Finset.subset_union_right
    · exact Finset.empty_subset _

theorem iregion_zero_rightΓ (B : CLChainAssemblyΓ γF G R n) (i : ℕ) : iregionΓ B i 0 = ∅ := by
  induction B generalizing i with
  | single hV R => simp [iregionΓ]
  | append B hT hi hU R ih => simp [iregionΓ, ih]

theorem jointAt_zeroΓ (B : CLChainAssemblyΓ γF G R n) : jointAtΓ B 0 = b := by
  cases B <;> simp [jointAtΓ]

theorem jointAt_topΓ (B : CLChainAssemblyΓ γF G R n) : jointAtΓ B n = a := by
  induction B with
  | single hV R => simp [jointAtΓ]
  | append B hT hi hU R ih => simp [jointAtΓ, ih]

/-- **The pieces `i ≤ l < j` of an assembly form a vine chain from the joint `j` to the joint `i`.** -/
theorem iregion_chainΓ (B : CLChainAssemblyΓ γF G R n) :
    ∀ i j : ℕ, i < j → j ≤ n → FinalCount.Src.Chain γF G.molecule (iregionΓ B i j) (jointAtΓ B j) (jointAtΓ B i) (j - i) := by
  induction B with
  | single hV R =>
    intro i j hij hj
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 1 := by omega
    simp only [iregionΓ, jointAtΓ]
    simpa using FinalCount.Src.Chain.single hV
  | @append S T a' b' c' n' RP B hT hi hU R ih =>
    intro i j hij hj
    have hj0 : j ≠ 0 := by omega
    by_cases hi0 : i = 0
    · subst hi0
      simp only [iregionΓ, jointAtΓ, hj0, ite_true, true_and, Nat.pos_of_ne_zero hj0, and_self, ite_false]
      rcases Nat.lt_or_ge 1 j with h2 | h2
      · have hch := ih 0 (j - 1) (by omega) (by omega)
        rw [jointAt_zeroΓ] at hch
        have hSsub := iregion_subsetΓ B 0 (j - 1)
        have hjoint := chain_joints_memΓ hch
        have hbc : b' ≠ c' := by
          have hch1 : FinalCount.Src.Chain γF G.molecule T b' c' 1 := FinalCount.Src.Chain.single hT
          exact chain_joints_neΓ hch1
        have hi' : iregionΓ B 0 (j - 1) ∩ T = {b'} := by
          ext x
          constructor
          · intro hx
            have : x ∈ S ∩ T := mem_inter.mpr ⟨hSsub (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩
            rwa [hi] at this
          · intro hx
            rw [mem_singleton] at hx; subst hx
            exact mem_inter.mpr ⟨hjoint.2, (chain_joints_memΓ (FinalCount.Src.Chain.single hT)).1⟩
        have hne : jointAtΓ B (j - 1) ≠ c' := by
          intro h
          have h1 : c' ∈ S := hSsub (h ▸ hjoint.1)
          have h2 : c' ∈ S ∩ T := mem_inter.mpr ⟨h1, (chain_joints_memΓ (FinalCount.Src.Chain.single hT)).2⟩
          rw [hi] at h2
          exact hbc (mem_singleton.mp h2).symm
        have := FinalCount.Src.Chain.append hch hT hi' hne
        rw [union_comm] at this
        have e : j - 1 - 0 + 1 = j - 0 := by omega
        have h01 : (0 : ℕ) - 1 = 0 := rfl
        rw [h01]
        exact (congrArg (fun m => FinalCount.Src.Chain γF G.molecule (T ∪ iregionΓ B 0 (j - 1)) (jointAtΓ B (j - 1)) c' m) e).mp this
      · obtain rfl : j = 1 := by omega
        have h01 : (0 : ℕ) - 1 = 0 := rfl
        rw [iregion_zero_rightΓ, union_empty, jointAt_zeroΓ]
        exact FinalCount.Src.Chain.single hT
    · simp only [iregionΓ, jointAtΓ, hi0, hj0, ite_false, false_and, empty_union]
      have := ih (i - 1) (j - 1) (by omega) (by omega)
      have e : (j - 1) - (i - 1) = j - i := by omega
      exact (congrArg (fun m => FinalCount.Src.Chain γF G.molecule (iregionΓ B (i - 1) (j - 1)) (jointAtΓ B (j - 1)) (jointAtΓ B (i - 1)) m) e).mp this

theorem piece_lower_eq_jointAtΓ (B : CLChainAssemblyΓ γF G R n) (l : ℕ) (h : l < n) :
    (assemblyPieceAtΓ B ⟨l, h⟩).lower = jointAtΓ B l := by
  induction B generalizing l with
  | single hV R =>
    obtain rfl : l = 0 := by omega
    simp [assemblyPieceAtΓ, jointAtΓ]
  | append B hT hi hU R ih =>
    cases l with
    | zero => simp [assemblyPieceAtΓ, jointAtΓ]
    | succ l' =>
      have := ih l' (by omega)
      simpa [assemblyPieceAtΓ, jointAtΓ] using this

theorem piece_atoms_sub_iregionΓ (B : CLChainAssemblyΓ γF G R n) (i j l : ℕ) (hil : i ≤ l) (hlj : l < j) (h : l < n) :
    (assemblyPieceAtΓ B ⟨l, h⟩).atoms ⊆ iregionΓ B i j := by
  induction B generalizing i j l with
  | single hV R =>
    obtain rfl : l = 0 := by omega
    obtain rfl : i = 0 := by omega
    simp [assemblyPieceAtΓ, iregionΓ]
    have : 0 < j := by omega
    simp [this]
  | append B hT hi hU R ih =>
    cases l with
    | zero =>
      obtain rfl : i = 0 := by omega
      have : 0 < j := by omega
      simp [assemblyPieceAtΓ, iregionΓ, this]
    | succ l' =>
      have := ih (i - 1) (j - 1) l' (by omega) (by omega) (by omega)
      simp only [assemblyPieceAtΓ]
      have hs : iregionΓ B (i - 1) (j - 1) ⊆ iregionΓ (CLChainAssemblyΓ.append B hT hi hU R) i j := by
        rw [iregion_appendΓ]; exact Finset.subset_union_right
      exact this.trans hs

theorem iregion_upper_blockΓ (B : CLChainAssemblyΓ γF G R n) :
    ∀ k : ℕ, 1 ≤ k → k < n → G.molecule.IsBlock (iregionΓ B k n) a (jointAtΓ B k) := by
  induction B with
  | single hV R => intro k h1 h2; omega
  | @append S T a' b' c' n' RP B hT hi hU R ih =>
    intro k h1 h2
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      have h := iregion_fullΓ B
      simp only [iregionΓ, jointAtΓ]
      simp only [one_ne_zero, ite_false, false_and, empty_union, Nat.add_sub_cancel, Nat.sub_self]
      rw [h, jointAt_zeroΓ]
      exact B.isBlock
    · have := ih (k - 1) (by omega) (by omega)
      have hk0 : k ≠ 0 := by omega
      simp only [iregionΓ, jointAtΓ, hk0, ite_false, false_and, empty_union]
      simpa using this

theorem jointAt_mem_lowerΓ (B : CLChainAssemblyΓ γF G R n) (i j : ℕ) (hij : i < j) (hj : j ≤ n) :
    jointAtΓ B j ∈ iregionΓ B i j ∧ jointAtΓ B i ∈ iregionΓ B i j :=
  chain_joints_memΓ (iregion_chainΓ B i j hij hj)

theorem jointAt_neΓ (B : CLChainAssemblyΓ γF G R n) (i j : ℕ) (hij : i < j) (hj : j ≤ n) :
    jointAtΓ B j ≠ jointAtΓ B i :=
  chain_joints_neΓ (iregion_chainΓ B i j hij hj)

theorem iregion_interΓ (B : CLChainAssemblyΓ γF G R n) :
    ∀ k : ℕ, 1 ≤ k → k < n → iregionΓ B k n ∩ iregionΓ B 0 k = {jointAtΓ B k} := by
  induction B with
  | single hV R => intro k h1 h2; omega
  | @append S T a' b' c' n' RP B hT hi hU R ih =>
    intro k h1 h2
    have hch1 : FinalCount.Src.Chain γF G.molecule T b' c' 1 := FinalCount.Src.Chain.single hT
    have hjT := chain_joints_memΓ hch1
    have hfull := iregion_fullΓ B
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      have e1 : iregionΓ (CLChainAssemblyΓ.append B hT hi hU R) 1 (n' + 1) = S := by
        rw [iregion_appendΓ]; simp [hfull]
      have e2 : iregionΓ (CLChainAssemblyΓ.append B hT hi hU R) 0 1 = T := by
        rw [iregion_appendΓ]; simp [iregion_zero_rightΓ]
      have e3 : jointAtΓ (CLChainAssemblyΓ.append B hT hi hU R) 1 = b' := by
        simp [jointAtΓ, jointAt_zeroΓ]
      rw [e1, e2, e3, hi]
    · have hk0 : k ≠ 0 := by omega
      have hSsub := iregion_subsetΓ B (k - 1) n'
      have e1 : iregionΓ (CLChainAssemblyΓ.append B hT hi hU R) k (n' + 1) = iregionΓ B (k - 1) n' := by
        rw [iregion_appendΓ]; simp [hk0]
      have e2 : iregionΓ (CLChainAssemblyΓ.append B hT hi hU R) 0 k = T ∪ iregionΓ B 0 (k - 1) := by
        rw [iregion_appendΓ]; simp [Nat.pos_of_ne_zero hk0]
      have e3 : jointAtΓ (CLChainAssemblyΓ.append B hT hi hU R) k = jointAtΓ B (k - 1) := by
        simp [jointAtΓ, hk0]
      rw [e1, e2, e3]
      have IH := ih (k - 1) (by omega) (by omega)
      have hb0 : b' ∈ iregionΓ B 0 (k - 1) := by
        have := (jointAt_mem_lowerΓ B 0 (k - 1) (by omega) (by omega)).2
        rwa [jointAt_zeroΓ] at this
      ext x
      simp only [mem_inter, mem_union, mem_singleton]
      constructor
      · rintro ⟨hx1, hx2 | hx2⟩
        · exfalso
          have hxb : x = b' := by
            have : x ∈ S ∩ T := mem_inter.mpr ⟨hSsub hx1, hx2⟩
            rwa [hi, mem_singleton] at this
          subst hxb
          have hh : x ∈ iregionΓ B (k - 1) n' ∩ iregionΓ B 0 (k - 1) := mem_inter.mpr ⟨hx1, hb0⟩
          rw [IH, mem_singleton] at hh
          have hne := jointAt_neΓ B 0 (k - 1) (by omega) (by omega)
          rw [jointAt_zeroΓ] at hne
          exact hne hh.symm
        · have hh : x ∈ iregionΓ B (k - 1) n' ∩ iregionΓ B 0 (k - 1) := mem_inter.mpr ⟨hx1, hx2⟩
          rwa [IH, mem_singleton] at hh
      · intro hx
        subst hx
        have hh : jointAtΓ B (k - 1) ∈ iregionΓ B (k - 1) n' ∩ iregionΓ B 0 (k - 1) := by
          rw [IH]; exact mem_singleton_self _
        exact ⟨(mem_inter.mp hh).1, Or.inr (mem_inter.mp hh).2⟩

theorem iregion_unionΓ (B : CLChainAssemblyΓ γF G R n) (i j l : ℕ) (hij : i ≤ j) (hjl : j ≤ l) :
    iregionΓ B i j ∪ iregionΓ B j l = iregionΓ B i l := by
  induction B generalizing i j l with
  | single hV R =>
    unfold iregionΓ
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
    rw [iregion_appendΓ, iregion_appendΓ, iregion_appendΓ]
    by_cases hj : j = 0
    · subst hj
      obtain rfl : i = 0 := by omega
      simp [iregion_zero_rightΓ]
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

theorem iregion_mono_rightΓ (B : CLChainAssemblyΓ γF G R n) (i j l : ℕ) (hij : i ≤ j) (hjl : j ≤ l) :
    iregionΓ B i j ⊆ iregionΓ B i l := by
  rw [← iregion_unionΓ B i j l hij hjl]; exact Finset.subset_union_left

theorem iregion_mono_leftΓ (B : CLChainAssemblyΓ γF G R n) (i j l : ℕ) (hij : i ≤ j) (hjl : j ≤ l) :
    iregionΓ B j l ⊆ iregionΓ B i l := by
  rw [← iregion_unionΓ B i j l hij hjl]; exact Finset.subset_union_right

theorem lower_blockΓ (B : CLChainAssemblyΓ γF G R n) (k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    G.molecule.IsBlock (iregionΓ B 0 k) (jointAtΓ B k) b := by
  have hS := iregion_upper_blockΓ B k hk hkn
  have hch := iregion_chainΓ B 0 k (by omega) (by omega)
  rw [jointAt_zeroΓ] at hch
  have hi := iregion_interΓ B k hk hkn
  have hU : G.molecule.IsBlock (iregionΓ B k n ∪ iregionΓ B 0 k) a b := by
    rw [union_comm, iregion_unionΓ B 0 k n (by omega) (by omega), iregion_fullΓ]
    exact B.isBlock
  exact chain_suffix_currentBlockΓ G.molecule (Mole.garden_isMolecule G) hS hch hi hU

theorem interval_blockΓ (B : CLChainAssemblyΓ γF G R n) (k k0 : ℕ) (hk : 1 ≤ k) (hkk0 : k < k0) (hk0 : k0 ≤ n) :
    G.molecule.IsBlock (iregionΓ B k k0) (jointAtΓ B k0) (jointAtΓ B k) := by
  rcases Nat.lt_or_ge k0 n with h | h
  · have hS := iregion_upper_blockΓ B k0 (by omega) h
    have hch := iregion_chainΓ B k k0 hkk0 hk0
    have hi : iregionΓ B k0 n ∩ iregionΓ B k k0 = {jointAtΓ B k0} := by
      have h1 := iregion_interΓ B k0 (by omega) h
      refine Finset.Subset.antisymm ?_ ?_
      · rw [← h1]
        exact Finset.inter_subset_inter (Finset.Subset.refl _) (iregion_mono_leftΓ B 0 k k0 (by omega) hkk0.le)
      · intro x hx
        rw [mem_singleton] at hx; subst hx
        exact mem_inter.mpr ⟨(jointAt_mem_lowerΓ B k0 n h (le_refl _)).2, (jointAt_mem_lowerΓ B k k0 hkk0 hk0).1⟩
    have hU : G.molecule.IsBlock (iregionΓ B k0 n ∪ iregionΓ B k k0) a (jointAtΓ B k) := by
      rw [union_comm, iregion_unionΓ B k k0 n hkk0.le h.le]
      exact iregion_upper_blockΓ B k hk (by omega)
    exact chain_suffix_currentBlockΓ G.molecule (Mole.garden_isMolecule G) hS hch hi hU
  · obtain rfl : k0 = n := le_antisymm hk0 h
    rw [jointAt_topΓ]
    exact iregion_upper_blockΓ B k hk hkk0

/-- **The split of the chain region `iregion B 0 k0` (a chain region of the restricted family) at the lower joint of the member with
piece index `k`** (`1 ≤ k < k0 ≤ n`): upper block = pieces `[k, k0)`, lower block = pieces `< k`. -/
noncomputable def mkSplitAtΓ (B : CLChainAssemblyΓ γF G R n) {ι' : Type*} (e : ι' → (assemblySourceFamilyΓ B).CoreIndex)
    (he : Function.Injective e) (k k0 : ℕ) (hk : 1 ≤ k) (hkk0 : k < k0) (hk0 : k0 ≤ n) (pstar : ι')
    (hp : (e pstar).1.val = k)
    (c : ChainAt G (restrictFamily (assemblySourceFamilyΓ B).coreFamily e he))
    (hcU : c.U = iregionΓ B 0 k0) (hca : c.a = jointAtΓ B k0) (hcb : c.b = b) :
    SplitAt G (restrictFamily (assemblySourceFamilyΓ B).coreFamily e he) pstar {j | (e j).1.val < k} where
  c := c
  sb := ⟨iregionΓ B k k0, jointAtΓ B k0, jointAtΓ B k, interval_blockΓ B k k0 hk hkk0 hk0⟩
  tb := ⟨iregionΓ B 0 k, jointAtΓ B k, b, by
    have := lower_blockΓ B k hk (by omega); exact this⟩
  sa := hca.symm
  tbb := hcb.symm
  joint := rfl
  bk := by
    have h1 := ((assemblySourceFamilyΓ B).corePlacement_at (e pstar)).1
    change jointAtΓ B k = ((assemblySourceFamilyΓ B).corePlacement (e pstar)).lower
    rw [h1]
    have := piece_lower_eq_jointAtΓ B k (by omega)
    have e1 : (e pstar).1 = ⟨k, by omega⟩ := Fin.ext hp
    change jointAtΓ B k = (assemblyPieceAtΓ B (e pstar).1).lower
    rw [e1]; exact this.symm
  inter := by
    have h1 := iregion_interΓ B k hk (by omega)
    show iregionΓ B k k0 ∩ iregionΓ B 0 k = {jointAtΓ B k}
    refine Finset.Subset.antisymm ?_ ?_
    · rw [← h1]
      exact Finset.inter_subset_inter (iregion_mono_rightΓ B k k0 n hkk0.le hk0) (Finset.Subset.refl _)
    · intro x hx
      rw [mem_singleton] at hx; subst hx
      exact mem_inter.mpr ⟨(jointAt_mem_lowerΓ B k k0 hkk0 hk0).2, (jointAt_mem_lowerΓ B 0 k (by omega) (by omega)).1⟩
  union := by
    show c.U = iregionΓ B k k0 ∪ iregionΓ B 0 k
    rw [hcU, union_comm, iregion_unionΓ B 0 k k0 (by omega) hkk0.le]
  atomsJ := fun j hj => by
    have hj' : (e j).1.val < k := hj
    show (assemblyPieceAtΓ B (e j).1).atoms ⊆ iregionΓ B 0 k
    exact piece_atoms_sub_iregionΓ B 0 k (e j).1.val (by omega) hj' (e j).1.2
  lowJ := fun j hj => by
    have hj' : (e j).1.val < k := hj
    have h1 := ((assemblySourceFamilyΓ B).corePlacement_at (e j)).1
    change ((assemblySourceFamilyΓ B).corePlacement (e j)).lower ≠ jointAtΓ B k
    rw [h1]
    change (assemblyPieceAtΓ B (e j).1).lower ≠ jointAtΓ B k
    have := piece_lower_eq_jointAtΓ B (e j).1.val (e j).1.2
    rw [show (⟨(e j).1.val, (e j).1.2⟩ : Fin n) = (e j).1 from rfl] at this
    rw [this]
    exact (jointAt_neΓ B (e j).1.val k hj' (by omega)).symm

end WaveTurbulence.GammaLow.Famb.VineEstS5C
