/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCMember
public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Spine.VineDelObjects

/-!
# Lemma 8.1′ (packet L3D): vine chains over `𝒱_γ`

Main's chain lemmas (`Spine/SourceObjectUnion`, `Spine/SourceChainSwap`, `Molecule/VineChainConnected`,
`Molecule/VineChainBlock`, `Molecule/VineChainEraseEndpoints`, `Molecule/VineChainInteriorConnected`,
`Spine/VineDelObjects`; sha256 in `COPIED-SHA256SUMS`) restated for L6's carrier `Src.Chain γ`. The proofs are main's,
with each use of a drawn vine's block, connectivity and one-atom-deletion facts replaced by the per-member facts of
`VCMember` (N2 N6: DH23's proof holds verbatim for `𝒱_γ`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Drawn.VC

open Finset WaveTurbulence.GammaLow.FinalCount WaveTurbulence.Vine

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {γ : ℝ}

/-! ## Ends, concatenation, reversal (main `SourceObjectUnion`, `SourceChainSwap`) -/

theorem chain_ends {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  induction h with
  | single h => exact member_ends h
  | append _ hT _ hac ih => exact ⟨mem_union_left _ ih.1, mem_union_right _ (member_ends hT).2.1, hac⟩

theorem chain_pos {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : 1 ≤ n := by
  induction h with
  | single => exact le_rfl
  | append _ _ _ _ _ => omega

/-- Concatenation of chains sharing exactly the joining joint. -/
theorem chain_append_chain {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Src.Chain γ M S a b n) (hT : Src.Chain γ M T b c m) (hST : S ∩ T = {b}) :
    Src.Chain γ M (S ∪ T) a c (n + m) := by
  induction hT generalizing S n with
  | @single T0 b0 c0 hv =>
    refine Src.Chain.append hS hv hST ?_
    intro hac
    have hcS : c0 ∈ S := hac ▸ (chain_ends hS).1
    have : c0 ∈ S ∩ T0 := mem_inter.mpr ⟨hcS, (member_ends hv).2.1⟩
    rw [hST] at this
    exact (member_ends hv).2.2 (mem_singleton.mp this).symm
  | @append T1 T2 b0 p c0 k hT1 hv hT12 hbc ih =>
    have hbS := (chain_ends hS).2.1
    have hb1 := (chain_ends hT1).1
    have hsub1 : S ∩ T1 ⊆ S ∩ (T1 ∪ T2) := inter_subset_inter_left subset_union_left
    have hsub2 : S ∩ T2 ⊆ S ∩ (T1 ∪ T2) := inter_subset_inter_left subset_union_right
    rw [hST] at hsub1 hsub2
    have hS1 : S ∩ T1 = {b0} :=
      Subset.antisymm hsub1 (singleton_subset_iff.mpr (mem_inter.mpr ⟨hbS, hb1⟩))
    have hS2 : S ∩ T2 ⊆ {p} := by
      intro x hx
      have hxb : x = b0 := mem_singleton.mp (hsub2 hx)
      have hxT2 := (mem_inter.mp hx).2
      have : x ∈ T1 ∩ T2 := mem_inter.mpr ⟨hxb ▸ hb1, hxT2⟩
      rw [hT12] at this
      exact this
    have h1 := ih hS hS1
    have hne : a ≠ c0 := by
      intro hac
      have hcS : c0 ∈ S := hac ▸ (chain_ends hS).1
      have : c0 ∈ S ∩ (T1 ∪ T2) :=
        mem_inter.mpr ⟨hcS, mem_union_right _ (member_ends hv).2.1⟩
      rw [hST] at this
      exact hbc (mem_singleton.mp this).symm
    have h2 := Src.Chain.append h1 hv (by
      rw [union_inter_distrib_right, hT12]
      exact Subset.antisymm (union_subset hS2 (Subset.refl _))
        (subset_union_right)) hne
    rw [union_assoc] at h2
    exact h2

theorem chain_swap {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : Src.Chain γ M S b a n := by
  induction h with
  | single h => exact Src.Chain.single (GammaLow.Fama.isSomeVine_swap h)
  | @append S T a b c n hS hT hi hne ih =>
    have h1 : Src.Chain γ M T c b 1 := Src.Chain.single (GammaLow.Fama.isSomeVine_swap hT)
    have h2 := chain_append_chain h1 ih (by rw [Finset.inter_comm]; exact hi)
    rw [Finset.union_comm] at h2
    rwa [Nat.add_comm] at h2

/-! ## Connectivity and blocks (main `VineChainConnected`, `VineChainBlock`) -/

theorem chain_joints_mem {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : a ∈ S ∧ b ∈ S :=
  ⟨(chain_ends h).1, (chain_ends h).2.1⟩

theorem chain_joints_ne {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : a ≠ b :=
  (chain_ends h).2.2

theorem chain_connected {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    Vine.GroupConnected M S := by
  induction h with
  | single h => exact member_connected h
  | append hS hT _ _ ih =>
    exact groupConnected_union M ih (member_connected hT) (chain_joints_mem hS).2 (member_ends hT).1

theorem chain_atoms_subset {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : S ⊆ M.atoms := by
  induction h with
  | single h => exact (member_block h).1
  | append _ hT _ _ ih => exact union_subset ih (member_block hT).1

theorem chain_endpoint_lower {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    1 ≤ M.outIn S a ∧ 1 ≤ M.inIn S a ∧ 1 ≤ M.outIn S b ∧ 1 ≤ M.inIn S b := by
  induction h with
  | single h =>
    obtain ⟨_hS, _ha, _hb, _hne, hoa, hia, hob, hib, _hint⟩ := member_block h
    omega
  | @append S T a b c n _hS hT _hi _hne ih =>
    obtain ⟨_hT, _hb, _hc, _hbc, _hob, _hib, hoc, hic, _hint⟩ := member_block hT
    have hl := oriented_degree_mono (M := M) (show S ⊆ S ∪ T from subset_union_left) a
    have hr := oriented_degree_mono (M := M) (show T ⊆ S ∪ T from subset_union_right) c
    omega

theorem chain_interior_degree (hM : M.IsMolecule) {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ M S a b n) : ∀ v ∈ S, v ≠ a → v ≠ b → M.degIn S v = 4 := by
  induction h with
  | single h => exact (member_block h).2.2.2.2.2.2.2.2.1
  | @append S T a b c n hS hT hi _hne ih =>
    have hX := member_block hT
    have hloop := connected_degree_two_no_loop M (member_connected hT)
      hX.2.1 hX.2.2.1 hX.2.2.2.1 (Mole.block_joint_degrees M hX).1
    intro v hv hva hvc
    have hvM : v ∈ M.atoms := (union_subset (chain_atoms_subset hS) hX.1) hv
    have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvM)
    by_cases hvb : v = b
    · subst v
      have hlo := chain_endpoint_lower hS
      have hsum := Mole.outIn_add_inIn M S b
      have hTdeg := (Mole.block_joint_degrees M hX).1
      have hle := degIn_add_le_union M hi hloop b
      omega
    · rcases mem_union.mp hv with hv | hv
      · have hd := ih v hv hva hvb
        have hle := degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
        omega
      · have hd := hX.2.2.2.2.2.2.2.2.1 v hv hvb hvc
        have hle := degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
        omega

/-- In an actual block, removing the terminal ingredient of a chain leaves an actual prefix block. -/
theorem chain_prefix_isBlock (hM : M.IsMolecule) {S T : Finset V} {a b c : V} {n : ℕ}
    (hS : Src.Chain γ M S a b n) (hT : Src.IsSomeVine γ M T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) : M.IsBlock S a b := by
  have hTB := member_block hT
  have hmem := chain_joints_mem hS
  have hlo := chain_endpoint_lower hS
  have hla := oriented_degree_mono M (show S ⊆ S ∪ T from subset_union_left) a
  have hloop := connected_degree_two_no_loop M (member_connected hT)
    hTB.2.1 hTB.2.2.1 hTB.2.2.2.1 (Mole.block_joint_degrees M hTB).1
  have hob := group_filtered_card_union_le M hi hloop b (fun d => M.out d = true)
  have hib := group_filtered_card_union_le M hi hloop b (fun d => M.out d = false)
  change M.outIn S b + M.outIn T b ≤ M.outIn (S ∪ T) b at hob
  change M.inIn S b + M.inIn T b ≤ M.inIn (S ∪ T) b at hib
  have hbo := (outIn_le_outdeg M (S ∪ T) b).trans (hM.1 b (hTB.1 hTB.2.1)).1
  have hbi := (inIn_le_indeg M (S ∪ T) b).trans (hM.1 b (hTB.1 hTB.2.1)).2
  obtain ⟨_hTU, _ha, _hc, _hac, hoa, hia, _hoc, _hic, _hint⟩ := hU
  obtain ⟨_hT, _hb, _hc, _hbc, hot, hit, _hot', _hit', _hint'⟩ := hTB
  refine ⟨chain_atoms_subset hS, hmem.1, hmem.2, chain_joints_ne hS,
    by omega, by omega, by omega, by omega, chain_interior_degree hM hS, ?_⟩
  intro u hu w hw
  have hmono : (Mole.induced M S).Adj ≤
      fun x y => ∃ z, M.InGroup S z ∧ M.atom z = x ∧ M.atom (M.mate z) = y := by
    intro x y hxy
    obtain ⟨z, hx, hy⟩ := hxy
    exact ⟨z.1, z.2, hx, hy⟩
  exact Relation.EqvGen.mono hmono u w (chain_connected hS u hu w hw)

/-! ## Deleting one atom (main `VineChainEraseEndpoints`, `VineChainInteriorConnected`, `VineDelObjects`) -/

section F1

variable (hF1 : TVineF1Input.{u, v})
include hF1

/-- Deleting a single atom from a chain leaves every remaining atom connected to a surviving outer endpoint. -/
theorem chain_erase_endpoint_reach {S : Finset V} {a b z : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    ∀ w ∈ S.erase z,
      (a ≠ z ∧ (Mole.induced M (S.erase z)).SameComponent a w) ∨
      (b ≠ z ∧ (Mole.induced M (S.erase z)).SameComponent b w) := by
  induction h with
  | @single S a b h =>
    have hX := member_block h
    intro w hw
    by_cases haz : a = z
    · have hbz : b ≠ z := by intro he; exact hX.2.2.2.1 (haz.trans he.symm)
      exact Or.inr ⟨hbz, member_erase_connected hF1 h z b (mem_erase.mpr ⟨hbz, hX.2.2.1⟩) w hw⟩
    · exact Or.inl ⟨haz, member_erase_connected hF1 h z a (mem_erase.mpr ⟨haz, hX.2.1⟩) w hw⟩
  | @append S T a b c n hS hT hi _hne ih =>
    have hs := chain_joints_mem hS
    have ht := member_block hT
    have liftS : S.erase z ⊆ (S ∪ T).erase z := by
      intro x hx
      obtain ⟨hxz, hxS⟩ := mem_erase.mp hx
      exact mem_erase.mpr ⟨hxz, mem_union_left _ hxS⟩
    have liftT : T.erase z ⊆ (S ∪ T).erase z := by
      intro x hx
      obtain ⟨hxz, hxT⟩ := mem_erase.mp hx
      exact mem_erase.mpr ⟨hxz, mem_union_right _ hxT⟩
    intro w hw
    obtain ⟨hwz, hwU⟩ := mem_erase.mp hw
    by_cases hcz : c = z
    · have hcS : c ∉ S := by
        intro hcS
        have he : c = b := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hcS, ht.2.2.1⟩)
        exact ht.2.2.2.1 he.symm
      have hSz : ∀ x ∈ S, x ≠ z := by
        intro x hx he
        exact hcS (hcz.symm ▸ he ▸ hx)
      have hbz := hSz b hs.2
      have haz := hSz a hs.1
      have liftS' : S ⊆ (S ∪ T).erase z := fun x hx => mem_erase.mpr ⟨hSz x hx, mem_union_left _ hx⟩
      refine Or.inl ⟨haz, ?_⟩
      rcases mem_union.mp hwU with hwS | hwT
      · exact induced_path_mono M liftS' (chain_connected hS a hs.1 w hwS)
      · exact Relation.EqvGen.trans _ _ _
          (induced_path_mono M liftS' (chain_connected hS a hs.1 b hs.2))
          (induced_path_mono M liftT (member_erase_connected hF1 hT z b (mem_erase.mpr ⟨hbz, ht.2.1⟩) w
            (mem_erase.mpr ⟨hwz, hwT⟩)))
    · rcases mem_union.mp hwU with hwS | hwT
      · rcases ih w (mem_erase.mpr ⟨hwz, hwS⟩) with ⟨haz, hp⟩ | ⟨hbz, hp⟩
        · exact Or.inl ⟨haz, induced_path_mono M liftS hp⟩
        · refine Or.inr ⟨hcz, Relation.EqvGen.trans _ _ _ ?_ (induced_path_mono M liftS hp)⟩
          exact induced_path_mono M liftT
            (member_erase_connected hF1 hT z c (mem_erase.mpr ⟨hcz, ht.2.2.1⟩) b (mem_erase.mpr ⟨hbz, ht.2.1⟩))
      · exact Or.inr ⟨hcz, induced_path_mono M liftT
          (member_erase_connected hF1 hT z c (mem_erase.mpr ⟨hcz, ht.2.2.1⟩) w (mem_erase.mpr ⟨hwz, hwT⟩))⟩

/-- Removing the first endpoint of a chain leaves it connected. -/
theorem chain_erase_first_connected {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    Vine.GroupConnected M (S.erase a) := by
  have reach (w : V) (hw : w ∈ S.erase a) : (Mole.induced M (S.erase a)).SameComponent b w := by
    rcases chain_erase_endpoint_reach hF1 (z := a) h w hw with ⟨hne, _hp⟩ | ⟨_hne, hp⟩
    · exact False.elim (hne rfl)
    · exact hp
  intro x hx y hy
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach x hx)) (reach y hy)

/-- The atoms of a chain other than its two outer joints form a connected region. -/
theorem chain_interior_connected {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    Vine.GroupConnected M (S \ {a, b}) := by
  cases h with
  | single h => exact member_interior_connected hF1 h
  | @append S T a b c n hS hT hi _hne =>
    rename_i c
    have hX := member_block hT
    have hs := chain_joints_mem hS
    have hab := chain_joints_ne hS
    have hbc := hX.2.2.2.1
    have hcS : c ∉ S := by
      intro hcS
      have he : c = b := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hcS, hX.2.2.1⟩)
      exact hbc he.symm
    have haT : a ∉ T := by
      intro haT
      exact hab (mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hs.1, haT⟩))
    have liftS : S.erase a ⊆ (S ∪ T) \ {a, c} := by
      intro x hx
      obtain ⟨hxa, hxS⟩ := mem_erase.mp hx
      refine mem_sdiff.mpr ⟨mem_union_left _ hxS, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hxa, fun he => hcS (he ▸ hxS)⟩
    have liftT : T.erase c ⊆ (S ∪ T) \ {a, c} := by
      intro x hx
      obtain ⟨hxc, hxT⟩ := mem_erase.mp hx
      refine mem_sdiff.mpr ⟨mem_union_right _ hxT, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun he => haT (he ▸ hxT), hxc⟩
    have reach (w : V) (hw : w ∈ (S ∪ T) \ {a, c}) :
        (Mole.induced M ((S ∪ T) \ {a, c})).SameComponent b w := by
      obtain ⟨hwU, hwj⟩ := mem_sdiff.mp hw
      have hwne : w ≠ a ∧ w ≠ c := by simpa only [mem_insert, mem_singleton, not_or] using hwj
      rcases mem_union.mp hwU with hwS | hwT
      · exact induced_path_mono M liftS
          (chain_erase_first_connected hF1 hS b (mem_erase.mpr ⟨hab.symm, hs.2⟩) w (mem_erase.mpr ⟨hwne.1, hwS⟩))
      · exact induced_path_mono M liftT
          (member_erase_connected hF1 hT c b (mem_erase.mpr ⟨hbc, hX.2.1⟩) w (mem_erase.mpr ⟨hwne.2, hwT⟩))
    intro x hx y hy
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach x hx)) (reach y hy)

/-- DH23 Lemma 4.11 premise for vine chains: deleting an interior atom leaves the chain connected or splits it into
two connected pieces containing the joints. -/
theorem chain_interior_deletion {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ M S a b n) {x : V} (_hx : x ∈ S) (hxa : x ≠ a) (hxb : x ≠ b) :
    Mole.GroupConnected M (S.erase x) ∨ Mole.TwoComponents M (S.erase x) a b := by
  classical
  obtain ⟨haS, hbS⟩ := chain_joints_mem h
  have haS' : a ∈ S.erase x := mem_erase.mpr ⟨hxa.symm, haS⟩
  have hbS' : b ∈ S.erase x := mem_erase.mpr ⟨hxb.symm, hbS⟩
  have reach := chain_erase_endpoint_reach hF1 (z := x) h
  by_cases hab : (Mole.induced M (S.erase x)).SameComponent a b
  · left
    have hall : ∀ w ∈ S.erase x, (Mole.induced M (S.erase x)).SameComponent a w := by
      intro w hw
      rcases reach w hw with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact hp
      · exact Relation.EqvGen.trans _ _ _ hab hp
    refine ⟨⟨a, haS'⟩, fun w hw y hy => ?_⟩
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall w hw)) (hall y hy)
  · right
    let U := (S.erase x).filter (fun y => (Mole.induced M (S.erase x)).SameComponent a y)
    let W := (S.erase x).filter (fun y => (Mole.induced M (S.erase x)).SameComponent b y)
    have hclosed : ∀ (c : V), (Mole.induced M (S.erase x)).SameComponent c c →
        ∀ y ∈ (S.erase x).filter (fun y => (Mole.induced M (S.erase x)).SameComponent c y),
        ∀ z ∈ S.erase x, M.Adj y z →
        z ∈ (S.erase x).filter (fun y => (Mole.induced M (S.erase x)).SameComponent c y) := by
      intro c _ y hy z hz hadj
      refine mem_filter.mpr ⟨hz, Relation.EqvGen.trans _ _ _ (mem_filter.mp hy).2
        (Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M _ y z).mpr ⟨hadj, (mem_filter.mp hy).1, hz⟩))⟩
    have gc : ∀ (c : V), c ∈ S.erase x →
        Mole.GroupConnected M ((S.erase x).filter
          (fun y => (Mole.induced M (S.erase x)).SameComponent c y)) := by
      intro c hc
      refine ⟨⟨c, mem_filter.mpr ⟨hc, Relation.EqvGen.refl _⟩⟩, fun y hy w hw => ?_⟩
      have hcl := hclosed c (Relation.EqvGen.refl _)
      have hp : (Mole.induced M (S.erase x)).SameComponent y w :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (mem_filter.mp hy).2)
          (mem_filter.mp hw).2
      exact (LGSpine.induced_restrict M hcl hp).2 hy
    refine ⟨U, W, ?_, ?_, gc a haS', gc b hbS',
      mem_filter.mpr ⟨haS', Relation.EqvGen.refl _⟩,
      mem_filter.mpr ⟨hbS', Relation.EqvGen.refl _⟩, ?_⟩
    · ext w
      simp only [mem_union, U, W, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hw
        rcases reach w hw with ⟨_, hp⟩ | ⟨_, hp⟩
        · exact Or.inl ⟨hw, hp⟩
        · exact Or.inr ⟨hw, hp⟩
    · rw [Finset.disjoint_left]
      intro w hw hw'
      exact hab (Relation.EqvGen.trans _ _ _ (mem_filter.mp hw).2
        (Relation.EqvGen.symm _ _ (mem_filter.mp hw').2))
    · intro w hw y hy hadj
      have hp := Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M (S.erase x) w y).mpr
        ⟨hadj, (mem_filter.mp hw).1, (mem_filter.mp hy).1⟩)
      exact hab (Relation.EqvGen.trans _ _ _ (mem_filter.mp hw).2
        (Relation.EqvGen.trans _ _ _ hp (Relation.EqvGen.symm _ _ (mem_filter.mp hy).2)))

end F1

end WaveTurbulence.TVine.Struct.Drawn.VC
