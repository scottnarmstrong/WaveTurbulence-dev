/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCFlow`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 5: contract flows/energies versus dart sums; decorations as fibre points.

For an actual block `S` with joints `a, b`, the contract's `flow`/`energy` (sums over the internal bonds with
incidence signs) agree with the dart sums `groupFlow` / `Γ_v`. A decoration `κ` of `M` gives a point of
`FlowFiber M S a b (Mom d) r` with `r = gapAt L w κ x₁ x₂` (the gap of the removed vine). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Block
variable {M : Molecule V D} {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
include hB

end Block

section Joint
variable {M : Molecule V D} (K : VineCut g M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower)
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

end WaveTurbulence.GammaLow.FinalCount.Step1
