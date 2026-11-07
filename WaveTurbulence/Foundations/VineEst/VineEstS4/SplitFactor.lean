/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitDec
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalKernel

/-! # Factorization of the CL-local summand at the joint `b` (V5 Step 4b, P2.3)

Index-set and clock identities for `U = S ∪ T`: `U = S.erase b ⊔ T`, the interior branches of `U` are those of `S` and of `T`, the
regional pairs of `U` are those of `S` and of `T`; the clock of `T` with upper time `u b` is the clock of `U` on `T`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

theorem mem_pairs_split {hG : G.IsPlain} {U : Finset (GBranch G.tree)} {q : SourcePair G} :
    q ∈ clRegionalPairs hG U ↔ Mole.IsInternalLeaf G U (q.firstLeaf hG) := by
  classical
  unfold clRegionalPairs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

section Index
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)
include hS hT hi hU

theorem split_union_erase : S ∪ T = S.erase b ∪ T := by
  ext v
  simp only [Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (h | h)
    · by_cases hvb : v = b
      · exact Or.inr (hvb ▸ hT.2.1)
      · exact Or.inl ⟨hvb, h⟩
    · exact Or.inr h
  · rintro (⟨_, h⟩ | h)
    · exact Or.inl h
    · exact Or.inr h

theorem split_disjoint_erase : Disjoint (S.erase b) T := by
  rw [Finset.disjoint_left]
  intro v hv hvT
  obtain ⟨hvb, hvS⟩ := Finset.mem_erase.mp hv
  have := Finset.mem_inter.mpr ⟨hvS, hvT⟩
  rw [hi, Finset.mem_singleton] at this
  exact hvb this

theorem split_interior : (S ∪ T).erase a = S.erase a ∪ T.erase b := by
  have hab : a ≠ b := hS.2.2.2.1
  have haT := split_a_not_mem hS hT hi hU
  ext v
  simp only [Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro ⟨hva, h | h⟩
    · exact Or.inl ⟨hva, h⟩
    · by_cases hvb : v = b
      · exact Or.inl ⟨hva, hvb ▸ hS.2.2.1⟩
      · exact Or.inr ⟨hvb, h⟩
  · rintro (⟨hva, h⟩ | ⟨hvb, h⟩)
    · exact ⟨hva, Or.inl h⟩
    · exact ⟨fun h' => haT (h' ▸ h), Or.inr h⟩

theorem split_interior_disjoint : Disjoint (S.erase a) (T.erase b) := by
  rw [Finset.disjoint_left]
  intro v hv hvT
  obtain ⟨hva, hvS⟩ := Finset.mem_erase.mp hv
  obtain ⟨hvb, hvT'⟩ := Finset.mem_erase.mp hvT
  have := Finset.mem_inter.mpr ⟨hvS, hvT'⟩
  rw [hi, Finset.mem_singleton] at this
  exact hvb this

theorem split_pairs (hG : G.IsPlain) : clRegionalPairs hG (S ∪ T) = clRegionalPairs hG S ∪ clRegionalPairs hG T := by
  ext p
  simp only [Finset.mem_union, mem_pairs_split]
  exact split_internalLeaf hS hT hi hU _

theorem split_pairs_disjoint (hG : G.IsPlain) : Disjoint (clRegionalPairs hG S) (clRegionalPairs hG T) := by
  rw [Finset.disjoint_left]
  intro p hp hpT
  rw [mem_pairs_split] at hp hpT
  exact split_not_internalLeaf_both hS hT hi hU _ ⟨hp, hpT⟩

theorem mem_interior_of_T {v : GBranch G.tree} (hv : v ∈ T.erase b) : v ∈ (S ∪ T).erase a := by
  rw [split_interior hS hT hi hU]
  exact Finset.mem_union_right _ hv

theorem mem_interior_of_S {v : GBranch G.tree} (hv : v ∈ S.erase a) : v ∈ (S ∪ T).erase a := by
  rw [split_interior hS hT hi hU]
  exact Finset.mem_union_left _ hv

end Index

/-! ## Clocks and the time domain -/

section Clock
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RT : CLRegionData G T b c)

/-- The restriction of the internal times of `U` to the interior branches of `T`. -/
@[expose] noncomputable def restrT (τ : CLInternalTime RU) : CLInternalTime RT :=
  fun v => τ ⟨v.1, mem_interior_of_T hS hT hi hU v.2⟩

/-- The exterior times of `T`: its upper time is the time of `b` in `U`. -/
@[expose] noncomputable def tT (b : GBranch G.tree) {a c : GBranch G.tree} {S T : Finset (GBranch G.tree)}
    (RU : CLRegionData G (S ∪ T) a c) (t : Fin 3 → ℝ) (τ : CLInternalTime RU) : Fin 3 → ℝ :=
  ![clLocalClock RU t τ b, t 1, t 2]

include hS hT hi hU

theorem clockT (t : Fin 3 → ℝ) (τ : CLInternalTime RU) {v : GBranch G.tree} (hv : v ∈ T) :
    clLocalClock RT (tT b RU t τ) (restrT hS hT hi hU RU RT τ) v = clLocalClock RU t τ v := by
  by_cases hvb : v = b
  · subst hvb
    rw [clLocalClock_upper]
    rfl
  · have h1 : v ∈ T.erase b := Finset.mem_erase.mpr ⟨hvb, hv⟩
    have h2 := mem_interior_of_T hS hT hi hU h1
    have := clLocalClock_internal RT (tT b RU t τ) (restrT hS hT hi hU RU RT τ) ⟨v, h1⟩
    rw [this]
    exact (clLocalClock_internal RU t τ ⟨v, h2⟩).symm

theorem pclockT (t : Fin 3 → ℝ) (τ : CLInternalTime RU) {x : GNode G.tree}
    (hx : x ∈ clRealizationNodes G T) (hne : x ≠ b.toNode) :
    parentClock ((tT b RU t τ) 0) (clLocalClock RT (tT b RU t τ) (restrT hS hT hi hU RU RT τ)) x =
      parentClock (t 0) (clLocalClock RU t τ) x := by
  obtain ⟨hn, hp⟩ := cl_realization_parent hT RT x hx hne
  rw [parentClock_nonroot _ _ x hn, parentClock_nonroot _ _ x hn]
  exact clockT hS hT hi hU RU RT t τ hp

/-- The time condition of the upper block `S`. -/
@[expose] def DomS (lay : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree)) (a : GBranch G.tree)
    (u : GBranch G.tree → ℝ) : Prop :=
  ∀ v ∈ S.erase a, (lay v : ℝ) < u v ∧ u v < lay v + 1 ∧ 0 < u v ∧ u v < parentClock (u a) u v.toNode

theorem domain_iff (lay : GBranch G.tree → ℕ) (t : Fin 3 → ℝ) (τ : CLInternalTime RU) :
    τ ∈ clLocalTimeDomain RU lay t ↔
      DomS lay S a (clLocalClock RU t τ) ∧
        restrT hS hT hi hU RU RT τ ∈ clLocalTimeDomain RT lay (tT b RU t τ) := by
  have hpos := (split_positive_c hS hT hi hU RU RT).1
  have hneg := (split_positive_c hS hT hi hU RU RT).2
  have hcT : c ∈ T := hT.2.2.1
  have hcb : c ≠ b := hT.2.2.2.1.symm
  have hxT : ∀ v : ↥(clInteriorBranches RT), v.1.toNode ∈ clRealizationNodes G T ∧ v.1.toNode ≠ b.toNode := by
    intro v
    obtain ⟨hvb, hvT⟩ := Finset.mem_erase.mp v.2
    exact ⟨(branch_mem_clRealizationNodes v.1).mpr hvT, fun h => hvb (Mole.branch_toNode_injective h)⟩
  have hu : clLocalClock RU t τ a = t 0 := clLocalClock_upper RU t τ
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun v hv => ?_, ⟨fun v => ?_, fun hb => ?_, fun hb => ?_⟩⟩
    · have h := h1 ⟨v, mem_interior_of_S hS hT hi hU hv⟩
      have hc := clLocalClock_internal RU t τ ⟨v, mem_interior_of_S hS hT hi hU hv⟩
      rw [hu, hc]
      exact h
    · have := h1 ⟨v.1, mem_interior_of_T hS hT hi hU v.2⟩
      obtain ⟨hr, hn⟩ := hxT v
      refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
      have h4 := this.2.2.2
      rw [← pclockT hS hT hi hU RU RT t τ hr hn] at h4
      exact h4
    · have h := h2 (hpos ▸ hb)
      rw [← clockT hS hT hi hU RU RT t τ hcT] at h
      exact h
    · have h := h3 (hneg ▸ hb)
      rw [← clockT hS hT hi hU RU RT t τ hcT] at h
      exact h
  · rintro ⟨hs, h1, h2, h3⟩
    refine ⟨fun v => ?_, fun hb => ?_, fun hb => ?_⟩
    · have hv : v.1 ∈ (S ∪ T).erase a := v.2
      rw [split_interior hS hT hi hU] at hv
      rcases Finset.mem_union.mp hv with hv | hv
      · have h := hs v.1 hv
        rw [hu, clLocalClock_internal RU t τ v] at h
        exact h
      · have := h1 ⟨v.1, hv⟩
        obtain ⟨hr, hn⟩ := hxT ⟨v.1, hv⟩
        refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
        have h4 := this.2.2.2
        rw [pclockT hS hT hi hU RU RT t τ hr hn] at h4
        exact h4
    · have h := h2 (hpos ▸ hb)
      rw [clockT hS hT hi hU RU RT t τ hcT] at h
      exact h
    · have h := h3 (hneg ▸ hb)
      rw [clockT hS hT hi hU RU RT t τ hcT] at h
      exact h

end Clock

end WaveTurbulence.VineEstS4
