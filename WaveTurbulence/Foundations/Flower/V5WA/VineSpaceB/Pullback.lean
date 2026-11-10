/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.BondSplit
public import WaveTurbulence.Foundations.VineEst.VineSpaceB.BondStatements
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.NormalizedAffine
public import WaveTurbulence.Foundations.Vine.DegenVine.MixAlgebra

/-! # V5-SPACE-EXT: the engine pullback of the bond weight, with mass `cψ ^ (3 * |U|)`

Each dart factor is a C2-A spatial measure of one node momentum, realized in the normalized engine lattice by
`enginePullback_nodeMap`; products of realizations are realizations with the product mass (`CharMix.mul`). For a
top-supported weight each bond has at most one non-constant dart factor (the one at its layer-`p` end), and a
block has at most `4 |U|` darts, so at most `2 |U| ≤ 3 |U|` factors carry mass `cψ`, the others mass `1`. -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist RegRed Reg.Skeleton VineEstS2 VineSpaceK DegenVine Cut2A MeasureTheory

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem enginePullback_mul (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (m1 m2 : (GNode G.tree → Fin d → ℤ) → ℂ) (c1 c2 : ℝ)
    (h1 : EnginePullback R L base m1 c1) (h2 : EnginePullback R L base m2 c2) :
    EnginePullback R L base (fun z => m1 z * m2 z) (c1 * c2) := by
  intro n hM9 B hL
  obtain ⟨N1, hN1, e1⟩ := h1 n hM9 B hL
  obtain ⟨N2, hN2, e2⟩ := h2 n hM9 B hL
  refine ⟨CharMix.mul N1 N2, ?_, ?_⟩
  · rw [CharMix.mass_mul]
    exact mul_le_mul hN1 hN2 N2.mass_nonneg (N1.mass_nonneg.trans hN1)
  · intro β hβ x
    rw [CharMix.val_mul, ← e1 β hβ x, ← e2 β hβ x]

theorem enginePullback_mono (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m : (GNode G.tree → Fin d → ℤ) → ℂ} {c c' : ℝ} (h : EnginePullback R L base m c) (hc : c ≤ c') :
    EnginePullback R L base m c' := by
  intro n hM9 B hL
  obtain ⟨N, hN, e⟩ := h n hM9 B hL
  exact ⟨N, hN.trans hc, e⟩

theorem enginePullback_congr (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m m' : (GNode G.tree → Fin d → ℤ) → ℂ} {c : ℝ} (h : EnginePullback R L base m c) (he : m = m') :
    EnginePullback R L base m' c := he ▸ h

theorem enginePullback_finsetProd (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → (GNode G.tree → Fin d → ℤ) → ℂ) (c : ι → ℝ)
    (h : ∀ i ∈ s, EnginePullback R L base (f i) (c i)) :
    EnginePullback R L base (fun z => ∏ i ∈ s, f i z) (∏ i ∈ s, c i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact enginePullback_one R L base
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact enginePullback_mul R L base _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- A spatial measure of one node momentum is realized with its mass. -/
theorem enginePullback_nodeValue (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {α : Type} [MeasurableSpace α] (M : SpatialMeasure (Mom d) α) (n0 : GNode G.tree) :
    EnginePullback R L base (fun z => M.value (cosetDecoration G L base z n0)) M.mass := by
  classical
  refine enginePullback_congr R L base (enginePullback_nodeMap R L base M 0
    (fun v => if v = n0 then ContinuousLinearMap.id ℝ (Mom d) else 0)) ?_
  funext z
  congr 1
  rw [zero_add, Finset.sum_eq_single n0 (fun v _ hv => by simp [hv]) (fun h => absurd (Finset.mem_univ n0) h)]
  simp [cosetDecoration]

/-- The non-constant darts of a top-supported weight. -/
def topDarts (G : Garden w) (lay : GBranch G.tree → ℕ) (U : Finset (GBranch G.tree)) (p : ℕ) :
    Finset (GardenDart G) :=
  (regionDarts G U).filter fun y => lay (G.molecule.atom (G.molecule.mate y)) < p ∧ lay (G.molecule.atom y) = p

theorem card_regionDarts_le (hU : G.molecule.IsBlock U a b) : (regionDarts G U).card ≤ 4 * U.card := by
  classical
  have hsub : regionDarts G U ⊆ U.biUnion (fun v => dartsIn G.molecule U v) := by
    intro y hy
    have hy' := mem_regionDarts.mp hy
    exact Finset.mem_biUnion.mpr ⟨_, hy'.1, (mem_dartsIn G.molecule).mpr ⟨rfl, hy'⟩⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun v hv => ?_
  rw [card_dartsIn]
  by_cases hva : v = a
  · subst hva
    rw [degIn_eq_out_add_in, hU.2.2.2.2.1, hU.2.2.2.2.2.1]
    norm_num
  · by_cases hvb : v = b
    · subst hvb
      rw [degIn_eq_out_add_in, hU.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.1]
      norm_num
    · rw [hU.2.2.2.2.2.2.2.2.1 v hv hva hvb]

theorem card_topDarts_le (hU : G.molecule.IsBlock U a b) (lay : GBranch G.tree → ℕ) (p : ℕ) :
    (topDarts G lay U p).card ≤ 2 * U.card := by
  classical
  set N := topDarts G lay U p with hN
  have hmate : ∀ y ∈ N, G.molecule.mate y ∈ regionDarts G U \ N := by
    intro y hy
    obtain ⟨hyR, hyT⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_sdiff.mpr ⟨mem_regionDarts.mpr ((inGroup_mate_iff y).mpr (mem_regionDarts.mp hyR)), ?_⟩
    intro hm
    obtain ⟨_, hmT⟩ := Finset.mem_filter.mp hm
    rw [G.molecule.mate_mate] at hmT
    omega
  have himg : N.image G.molecule.mate ⊆ regionDarts G U \ N := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact hmate y hy
  have hcard : (N.image G.molecule.mate).card = N.card :=
    Finset.card_image_of_injective _ (Mole.mate_injective G.molecule)
  have hNsub : N ⊆ regionDarts G U := Finset.filter_subset _ _
  have h1 := Finset.card_le_card himg
  rw [hcard] at h1
  have h2 := card_regionDarts_le hU
  have h3 := Finset.card_sdiff_add_card_eq_card hNsub
  omega

end WaveTurbulence.VineSpaceB
