/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCDict
public import WaveTurbulence.Foundations.Molecule.VineGroupGaps
public import WaveTurbulence.Foundations.Molecule.VineJointFlows
/-! # VINE-COUNT part 5: contract flows/energies versus dart sums; decorations as fibre points.

For an actual block `S` with joints `a, b`, the contract's `flow`/`energy` (sums over the internal bonds with
incidence signs) agree with the dart sums `groupFlow` / `Γ_v`. A decoration `κ` of `M` gives a point of
`FlowFiber M S a b (Mom d) r` with `r = gapAt L w κ x₁ x₂` (the gap of the removed vine). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- Sum over the internal bonds of incidence-weighted symmetric functions equals the signed dart sum. -/
theorem sum_bond_incidence {E : Type*} [AddCommGroup E] [Module ℝ E] (M : Molecule V D) (S : Finset V) (v : V)
    (f : D → E) (hf : ∀ x, f (M.mate x) = f x) :
    ∑ e : Bond M S, (incidence M v e.1 : ℝ) • f e.1 =
      ∑ x ∈ (M.dartsAt v).filter (M.InGroup S), M.dartSign x • f x := by
  have hB : internalBondSet M S = Finset.univ.filter (fun x => M.out x = true ∧ M.InGroup S x) := by
    unfold internalBondSet Molecule.bonds
    ext x; simp [Finset.mem_filter]
  have h1 : ∑ e : Bond M S, (incidence M v e.1 : ℝ) • f e.1 =
      ∑ x ∈ Finset.univ.filter (fun x => M.out x = true ∧ M.InGroup S x), (incidence M v x : ℝ) • f x := by
    rw [← hB]
    exact Finset.sum_coe_sort (internalBondSet M S) (fun e => (incidence M v e : ℝ) • f e)
  rw [h1, Finset.sum_filter]
  have h2 : ∑ x ∈ (M.dartsAt v).filter (M.InGroup S), M.dartSign x • f x =
      ∑ x : D, if (M.atom x = v ∧ M.InGroup S x) then M.dartSign x • f x else 0 := by
    rw [Finset.sum_filter]
    have : (M.dartsAt v) = Finset.univ.filter (fun x => M.atom x = v) := rfl
    rw [this, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : M.atom x = v <;> by_cases h' : M.InGroup S x <;> simp [h, h']
  rw [h2]
  -- split the right side into out and in parts
  have h3 : ∀ x : D, (if (M.atom x = v ∧ M.InGroup S x) then M.dartSign x • f x else 0) =
      (if (M.atom x = v ∧ M.InGroup S x ∧ M.out x = true) then f x else 0) -
      (if (M.atom x = v ∧ M.InGroup S x ∧ M.out x = false) then f x else 0) := by
    intro x
    unfold Molecule.dartSign
    cases ho : M.out x <;> by_cases h : M.atom x = v <;> by_cases h' : M.InGroup S x <;> simp [h, h', ho]
  have h4 : ∀ x : D, (if (M.out x = true ∧ M.InGroup S x) then (incidence M v x : ℝ) • f x else 0) =
      (if (M.atom x = v ∧ M.InGroup S x ∧ M.out x = true) then f x else 0) -
      (if (M.atom (M.mate x) = v ∧ M.InGroup S x ∧ M.out x = true) then f x else 0) := by
    intro x
    unfold incidence
    by_cases h1 : M.atom x = v <;> by_cases h2 : M.atom (M.mate x) = v <;> by_cases h3 : M.InGroup S x <;>
      by_cases h4 : M.out x = true <;> simp [h1, h2, h3, h4]
  simp_rw [h3, h4]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  -- the in-part equals the mate-reindexed out-part
  let e : D ≃ D := Function.Involutive.toPerm M.mate M.mate_mate
  rw [← Equiv.sum_comp e (fun x => if (M.atom x = v ∧ M.InGroup S x ∧ M.out x = false) then f x else 0)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have he : e x = M.mate x := rfl
  rw [he, hf x]
  have hg : M.InGroup S (M.mate x) ↔ M.InGroup S x := ⟨fun h => ⟨by simpa [M.mate_mate] using h.2, h.1⟩, fun h => ⟨h.2, by rw [M.mate_mate]; exact h.1⟩⟩
  have ho : M.out (M.mate x) = false ↔ M.out x = true := by
    rw [M.out_mate]; cases M.out x <;> simp
  by_cases h1 : M.atom (M.mate x) = v <;> by_cases h2 : M.InGroup S x <;> by_cases h3 : M.out x = true <;>
    simp [h1, h2, h3, hg, ho]

theorem flow_eq_groupFlow (M : Molecule V D) (S : Finset V) (k : D → Mom d) (hk : ∀ x, k (M.mate x) = k x) (v : V) :
    flow M S (fun e : Bond M S => k e.1) v = Vine.groupFlow M S k v := by
  unfold flow Vine.groupFlow
  rw [← sum_bond_incidence M S v k hk]
  refine Finset.sum_congr rfl fun e _ => ?_
  exact (Int.cast_smul_eq_zsmul ℝ _ _).symm

section Block
variable {M : Molecule V D} {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
include hB

theorem group_eq_all_of_interior (hM : ∀ v ∈ M.atoms, M.deg v ≤ 4) {v : V} (hv : v ∈ S) (hva : v ≠ a) (hvb : v ≠ b) :
    (M.dartsAt v).filter (M.InGroup S) = M.dartsAt v ∧ M.deg v = 4 := by
  obtain ⟨hS, -, -, -, -, -, -, -, hint, -⟩ := hB
  have h4 : M.degIn S v = 4 := hint v hv hva hvb
  have hd : M.deg v ≤ 4 := hM v (hS hv)
  have hle : M.degIn S v ≤ M.deg v := degIn_le_deg M S v
  have hdeg : M.deg v = 4 := le_antisymm hd (h4 ▸ hle)
  refine ⟨Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) ?_, hdeg⟩
  have : ((M.dartsAt v).filter (M.InGroup S)).card = 4 := h4
  unfold Molecule.deg at hdeg
  omega

theorem energy_interior_eq (hM : ∀ v ∈ M.atoms, M.deg v ≤ 4) {v : V} (hv : v ∈ S) (hva : v ≠ a) (hvb : v ≠ b)
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) :
    energy M S (fun e : Bond M S => Molecule.kvec L w κ e.1) v = - M.Gamma L w κ v := by
  have hk : ∀ x, ‖Molecule.kvec L w κ (M.mate x)‖ ^ 2 = ‖Molecule.kvec L w κ x‖ ^ 2 := by
    intro x; simp [Molecule.kvec, hκ x]
  have h := sum_bond_incidence M S v (fun x => ‖Molecule.kvec L w κ x‖ ^ 2) hk
  obtain ⟨hg, -⟩ := group_eq_all_of_interior hB hM hv hva hvb
  rw [hg] at h
  unfold energy Molecule.Gamma
  simp only [smul_eq_mul] at h
  rw [← h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

theorem flow_interior_eq_zero (hM : ∀ v ∈ M.atoms, M.deg v ≤ 4) {v : V} (hv : v ∈ S) (hva : v ≠ a) (hvb : v ≠ b)
    (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) :
    flow M S (fun e : Bond M S => Molecule.kvec L w κ e.1) v = 0 := by
  have hk : ∀ x, Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
    intro x; simp [Molecule.kvec, hdec.1 x]
  rw [flow_eq_groupFlow M S _ hk]
  obtain ⟨hg, hdeg⟩ := group_eq_all_of_interior hB hM hv hva hvb
  unfold Vine.groupFlow
  rw [hg, hdec.2 v (hB.1 hv)]
  exact hc v (hB.1 hv) hdeg

end Block

section Joint
variable {M : Molecule V D} (K : VineCut M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower)
include hB

theorem x₁_ne_x₂ : K.x₁ ≠ K.x₂ := fun h => by
  have h1 := x₁_out K
  have h2 := x₂_out K
  rw [h] at h1; rw [h1] at h2; exact Bool.false_ne_true h2

theorem y₁_ne_y₂ : K.y₁ ≠ K.y₂ := fun h => by
  have h1 := y₁_out K
  have h2 := y₂_out K
  rw [h] at h1; rw [h1] at h2; exact Bool.false_ne_true h2

theorem group_at_a : (M.dartsAt K.C.upper).filter (M.InGroup K.C.atoms) = {K.x₁, K.x₂} := by
  ext x
  simp only [Finset.mem_filter, mem_dartsAt, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hg⟩
    cases ho : M.out x
    · exact Or.inl (grp_at_a_in K hB hx hg ho)
    · exact Or.inr (grp_at_a_out K hB hx hg ho)
  · rintro (rfl | rfl)
    · exact ⟨x₁_atom K, x₁_inGroup K⟩
    · exact ⟨x₂_atom K, x₂_inGroup K⟩

theorem group_at_b : (M.dartsAt K.C.lower).filter (M.InGroup K.C.atoms) = {K.y₁, K.y₂} := by
  ext x
  simp only [Finset.mem_filter, mem_dartsAt, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hg⟩
    cases ho : M.out x
    · exact Or.inl (grp_at_b_in K hB hx hg ho)
    · exact Or.inr (grp_at_b_out K hB hx hg ho)
  · rintro (rfl | rfl)
    · exact ⟨y₁_atom K, y₁_inGroup K⟩
    · exact ⟨y₂_atom K, y₂_inGroup K⟩

theorem groupFlow_a {E : Type*} [AddCommGroup E] [Module ℝ E] (k : D → E) :
    Vine.groupFlow M K.C.atoms k K.C.upper = k K.x₂ - k K.x₁ := by
  unfold Vine.groupFlow
  rw [group_at_a K hB, Finset.sum_pair (x₁_ne_x₂ K hB)]
  simp [Molecule.dartSign, x₁_out K, x₂_out K]
  abel

theorem groupFlow_b {E : Type*} [AddCommGroup E] [Module ℝ E] (k : D → E) :
    Vine.groupFlow M K.C.atoms k K.C.lower = k K.y₂ - k K.y₁ := by
  unfold Vine.groupFlow
  rw [group_at_b K hB, Finset.sum_pair (y₁_ne_y₂ K hB)]
  simp [Molecule.dartSign, y₁_out K, y₂_out K]
  abel

variable (hMol : M.IsMolecule) (hM : ∀ v ∈ M.atoms, M.deg v ≤ 4)
include hMol hM

/-- The gap of the removed vine is the difference of the two internal labels at the lower joint. -/
theorem gap_b_eq (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) :
    Molecule.kvec L w κ K.y₂ - Molecule.kvec L w κ K.y₁ = Molecule.gapAt L w κ K.x₁ K.x₂ := by
  have hk : ∀ x, Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
    intro x; simp [Molecule.kvec, hdec.1 x]
  have hcc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x = 0 :=
    fun v hv hd => (hdec.2 v hv).trans (hc v hv hd)
  have h := Vine.block_jointFlow_neg M hMol hB (Molecule.kvec L w κ) hk hcc
  rw [groupFlow_a K hB, groupFlow_b K hB] at h
  unfold Molecule.gapAt
  have := congrArg Neg.neg h
  rw [neg_neg] at this
  rw [← this]; abel

theorem flow_a_eq (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ) :
    flow M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1) K.C.upper =
      -Molecule.gapAt L w κ K.x₁ K.x₂ := by
  have hk : ∀ x, Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
    intro x; simp [Molecule.kvec, hdec.1 x]
  rw [flow_eq_groupFlow M _ _ hk, groupFlow_a K hB]
  unfold Molecule.gapAt
  abel

theorem flow_b_eq (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) :
    flow M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1) K.C.lower =
      Molecule.gapAt L w κ K.x₁ K.x₂ := by
  have hk : ∀ x, Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
    intro x; simp [Molecule.kvec, hdec.1 x]
  rw [flow_eq_groupFlow M _ _ hk, groupFlow_b K hB]
  exact gap_b_eq K hB hMol hM L w c κ hdec hc

/-- A decoration is a point of the flow fibre of the removed vine over its gap. -/
noncomputable def kfibElt (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) :
    FlowFiber M K.C.atoms K.C.upper K.C.lower (Mom d) (Molecule.gapAt L w κ K.x₁ K.x₂) :=
  ⟨fun e => Molecule.kvec L w κ e.1, flow_a_eq K hB hMol hM L w c κ hdec,
   flow_b_eq K hB hMol hM L w c κ hdec hc,
   fun v hv hva hvb => flow_interior_eq_zero hB hM hv hva hvb L w c κ hdec hc⟩

theorem kfibElt_val (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (e : Bond M K.C.atoms) :
    (kfibElt K hB hMol hM L w c κ hdec hc).1 e = Molecule.kvec L w κ e.1 := rfl

end Joint

end WaveTurbulence.VineCount
