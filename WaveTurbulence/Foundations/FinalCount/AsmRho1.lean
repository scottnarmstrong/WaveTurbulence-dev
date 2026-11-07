/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RestrictLad
public import WaveTurbulence.Foundations.FinalCount.CutLad2
public import WaveTurbulence.Foundations.FinalCount.BetaCut
public import WaveTurbulence.Foundations.WaveB.Ladders
public import WaveTurbulence.Foundations.FinalCount.G3Iso
/-! **FINALCOUNT-ASSEMBLY, M1 (part 1): the change of `ρ = q + m` under an operation** (TARGET L2226, "each of Operations 1-4 changes
the value of `ρ` by at most `C₀`").

`LadderTransfer M M' A`: on the atom set `A`, the molecules `M` and `M'` have the same bond multiplicities and directions, and the atoms of `M'`
outside `A` have degree `≤ 2` (so lie in no ladder).  Then the ladders of `M'` are exactly the ladders of `M` inside `A`, and
`ρ(M) ≤ ρ(M') + ladderLoss M A`, where `ladderLoss M A` counts the maximal ladders of `M` leaving `A` and the free atoms of `M` outside `A`.
Instances: a cut (`A = atoms ∖ {v}`), and any closed removal (`restrictP`).  `ladderLoss M A ≤ |atoms ∖ A|`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount

universe u1 u2 u3
variable {V : Type u1} [DecidableEq V] {D : Type u2} [Fintype D] [DecidableEq D] {D' : Type u3} [Fintype D'] [DecidableEq D']

/-- `ρ`-loss of passing from `M` to a molecule that is unchanged on `A`: the maximal ladders of `M` not inside `A`, plus the free atoms outside `A`. -/
noncomputable def ladderLoss (M : Molecule V D) (A : Finset V) : ℕ :=
  (M.maximalLadders.filter fun S => ¬ S ⊆ A).card +
    (M.atoms.filter fun v => v ∉ A ∧ ∀ S ∈ M.maximalLadders, v ∉ S).card

structure LadderTransfer (M : Molecule V D) (M' : Molecule V D') (A : Finset V) : Prop where
  subM : ∀ a ∈ A, a ∈ M.atoms
  subM' : ∀ a ∈ A, a ∈ M'.atoms
  bonds : ∀ a ∈ A, ∀ b ∈ A, M'.bondsBetween a b = M.bondsBetween a b
  dir : ∀ a ∈ A, ∀ b ∈ A, M'.Directed a b ↔ M.Directed a b
  low : ∀ x ∈ M'.atoms, x ∉ A → M'.deg x ≤ 2

namespace LadderTransfer
variable {M : Molecule V D} {M' : Molecule V D'} {A : Finset V} (T : LadderTransfer M M' A)
include T

theorem isLadder_iff {m : ℕ} {u w : Fin (m + 1) → V} (hu : ∀ j, u j ∈ A) (hw : ∀ j, w j ∈ A) :
    M'.IsLadder u w ↔ M.IsLadder u w := by
  unfold Molecule.IsLadder
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ (and_congr ?_ ?_)))
  · exact forall_congr' fun j => ⟨fun _ => ⟨T.subM _ (hu j), T.subM _ (hw j)⟩,
      fun _ => ⟨T.subM' _ (hu j), T.subM' _ (hw j)⟩⟩
  · exact forall_congr' fun j => by rw [T.bonds _ (hu j) _ (hw j)]
  · exact forall_congr' fun j => by
      rw [T.bonds _ (hu _) _ (hu _), T.bonds _ (hw _) _ (hw _), T.dir _ (hu _) _ (hu _), T.dir _ (hw _) _ (hw _)]

theorem ladderSet_sub {S : Finset V} (h : M'.IsLadderSet S) : S ⊆ A ∧ M.IsLadderSet S := by
  obtain ⟨m, u, w, hL, rfl⟩ := h
  have h3 : ∀ a ∈ Molecule.ladderAtoms u w, a ∈ A := by
    intro a ha
    by_contra hna
    have h1 := ladder_atom_deg_ge_three M' hL ha
    have h2 := T.low a (ladderAtoms_subset_atoms M' hL ha) hna
    omega
  have hu : ∀ j, u j ∈ A := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inl rfl⟩)
  have hw : ∀ j, w j ∈ A := fun j => h3 _ ((mem_ladderAtoms u w _).2 ⟨j, Or.inr rfl⟩)
  exact ⟨h3, ⟨m, u, w, (T.isLadder_iff hu hw).1 hL, rfl⟩⟩

theorem ladderSet_of_sub {S : Finset V} (h : M.IsLadderSet S) (hS : S ⊆ A) : M'.IsLadderSet S := by
  obtain ⟨m, u, w, hL, rfl⟩ := h
  have hu : ∀ j, u j ∈ A := fun j => hS ((mem_ladderAtoms u w _).2 ⟨j, Or.inl rfl⟩)
  have hw : ∀ j, w j ∈ A := fun j => hS ((mem_ladderAtoms u w _).2 ⟨j, Or.inr rfl⟩)
  exact ⟨m, u, w, (T.isLadder_iff hu hw).2 hL, rfl⟩

theorem maximal_of_sub {S : Finset V} (hS : S ∈ M.maximalLadders) (hA : S ⊆ A) : S ∈ M'.maximalLadders := by
  rw [mem_maximalLadders_iff] at hS ⊢
  exact ⟨T.ladderSet_of_sub hS.1 hA, fun S' hS' hsub => hS.2 S' (T.ladderSet_sub hS').2 hsub⟩

theorem free_of_mem {v : V} (hvA : v ∈ A) (hv : ∀ S ∈ M.maximalLadders, v ∉ S) :
    v ∈ M'.atoms ∧ ∀ S ∈ M'.maximalLadders, v ∉ S := by
  refine ⟨T.subM' v hvA, fun S hS hvS => ?_⟩
  obtain ⟨S₁, hS₁, hsub⟩ := exists_maximal_ladder_ge M (T.ladderSet_sub ((mem_maximalLadders_iff _).1 hS).1).2
  exact hv S₁ hS₁ (hsub hvS)

/-- **`ρ(M) ≤ ρ(M') + ladderLoss M A`.** -/
theorem rho_le : M.rho ≤ M'.rho + ladderLoss M A := by
  unfold Molecule.rho Molecule.numLadders Molecule.numFree ladderLoss
  set X := M.maximalLadders.filter (· ⊆ A) with hX
  set Y := M.atoms.filter (fun v => v ∈ A ∧ ∀ S ∈ M.maximalLadders, v ∉ S) with hY
  have hX' : X.card ≤ M'.maximalLadders.card := by
    refine Finset.card_le_card fun S hS => ?_
    rw [hX, Finset.mem_filter] at hS
    exact T.maximal_of_sub hS.1 hS.2
  have hY' : Y.card ≤ (M'.atoms.filter fun v => ∀ S ∈ M'.maximalLadders, v ∉ S).card := by
    refine Finset.card_le_card fun v hv => ?_
    rw [hY, Finset.mem_filter] at hv
    rw [Finset.mem_filter]
    exact T.free_of_mem hv.2.1 hv.2.2
  have e1 : M.maximalLadders.card = X.card + (M.maximalLadders.filter fun S => ¬ S ⊆ A).card := by
    rw [hX]; exact (Finset.card_filter_add_card_filter_not (s := M.maximalLadders) (p := fun S => S ⊆ A)).symm
  have e2 : (M.atoms.filter fun v => ∀ S ∈ M.maximalLadders, v ∉ S).card =
      Y.card + (M.atoms.filter fun v => v ∉ A ∧ ∀ S ∈ M.maximalLadders, v ∉ S).card := by
    rw [hY, ← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_union]
      by_cases hv : v ∈ A <;> simp [hv]
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact h2.2.1 h1.2.1
  omega

end LadderTransfer

/-- The loss is at most the number of atoms outside `A` (maximal ladders are disjoint). -/
theorem ladderLoss_le_card (M : Molecule V D) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) (A : Finset V) :
    ladderLoss M A ≤ (M.atoms \ A).card := by
  unfold ladderLoss
  set 𝓛 := M.maximalLadders.filter fun S => ¬ S ⊆ A
  set F := M.atoms.filter fun v => v ∉ A ∧ ∀ S ∈ M.maximalLadders, v ∉ S
  have hdis := LadderDisjoint.maximalLadders_pairwiseDisjoint_of_degree_le_four M hM
  -- choose a representative outside A for each ladder
  have hrep : ∀ S ∈ 𝓛, ∃ a ∈ S, a ∈ M.atoms \ A := by
    intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨a, ha, haA⟩ := Finset.not_subset.1 hS.2
    exact ⟨a, ha, Finset.mem_sdiff.2 ⟨isLadderSet_subset M ((mem_maximalLadders_iff M).1 hS.1).1 ha, haA⟩⟩
  have h1 : 𝓛.card ≤ ((M.atoms \ A).filter fun v => ∃ S ∈ M.maximalLadders, v ∈ S).card := by
    rcases 𝓛.eq_empty_or_nonempty with h0 | ⟨S0, hS0⟩
    · rw [h0]; simp
    · haveI : Nonempty V := ⟨(hrep S0 hS0).choose⟩
      choose! r hr using hrep
      have hinj : Set.InjOn r (𝓛 : Set (Finset V)) := by
        intro S hS S' hS' e
        by_contra hne
        have := hdis (Finset.mem_filter.1 hS).1 (Finset.mem_filter.1 hS').1 hne
        exact Finset.disjoint_left.1 this (hr S hS).1 (e ▸ (hr S' hS').1)
      have himg : 𝓛.image r ⊆ (M.atoms \ A).filter fun v => ∃ S ∈ M.maximalLadders, v ∈ S := by
        intro v hv
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hv
        exact Finset.mem_filter.2 ⟨(hr S hS).2, S, (Finset.mem_filter.1 hS).1, (hr S hS).1⟩
      exact ((Finset.card_image_of_injOn hinj).symm.le).trans (Finset.card_le_card himg)
  have hFsub : F ⊆ (M.atoms \ A).filter fun v => ¬ ∃ S ∈ M.maximalLadders, v ∈ S := by
    intro v hv
    rw [Finset.mem_filter] at hv
    exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hv.1, hv.2.1⟩, fun ⟨S, hS, hvS⟩ => hv.2.2 S hS hvS⟩
  calc 𝓛.card + F.card ≤ ((M.atoms \ A).filter fun v => ∃ S ∈ M.maximalLadders, v ∈ S).card +
        ((M.atoms \ A).filter fun v => ¬ ∃ S ∈ M.maximalLadders, v ∈ S).card :=
        Nat.add_le_add h1 (Finset.card_le_card hFsub)
    _ = (M.atoms \ A).card := Finset.card_filter_add_card_filter_not _

/-! ## Instances -/

section instances
variable (M : Molecule V D)

/-- **A cut at `v`**: `A = atoms ∖ {v}`. -/
theorem cutTransfer {v v₂ : V} {x₁ x₂ : D} (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4) :
    LadderTransfer M (M.cut v v₂ x₁ x₂) (M.atoms.erase v) where
  subM a ha := Finset.mem_of_mem_erase ha
  subM' a ha := by
    have := Finset.mem_of_mem_erase ha
    exact Finset.mem_insert_of_mem this
  bonds a ha b hb := by
    have ha' := Finset.mem_erase.1 ha
    have hb' := Finset.mem_erase.1 hb
    exact cut_bondsBetween_eq M ha'.1 (fun e => hcd.2.1 (by rw [← e]; exact ha'.2)) hb'.1
      (fun e => hcd.2.1 (by rw [← e]; exact hb'.2))
  dir a ha b hb := by
    have ha' := Finset.mem_erase.1 ha
    have hb' := Finset.mem_erase.1 hb
    exact cut_directed_iff M ha'.1 (fun e => hcd.2.1 (by rw [← e]; exact ha'.2)) hb'.1
      (fun e => hcd.2.1 (by rw [← e]; exact hb'.2))
  low x hx hxA := by
    by_cases h1 : x = v
    · subst h1; rw [cut_deg_v M hcd]
    · have h2 : x = v₂ := by
        by_contra h2
        apply hxA
        refine Finset.mem_erase.2 ⟨h1, ?_⟩
        exact (Finset.mem_insert.1 hx).resolve_left h2
      subst h2
      have := cut_deg_v₂ M hcd
      omega

/-- **ρ under a cut**: `ρ(M) ≤ ρ(cut) + 1`. -/
theorem rho_le_cut {v v₂ : V} {x₁ x₂ : D} (hcd : M.IsCutData v v₂ x₁ x₂) (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) :
    M.rho ≤ (M.cut v v₂ x₁ x₂).rho + 1 := by
  have h := (cutTransfer M hcd (hM v hcd.1)).rho_le
  have h2 := ladderLoss_le_card M hM (M.atoms.erase v)
  have h3 : (M.atoms \ M.atoms.erase v).card ≤ 1 := by
    have : M.atoms \ M.atoms.erase v ⊆ {v} := by
      intro a ha
      rw [Finset.mem_sdiff, Finset.mem_erase] at ha
      simpa using fun h => ha.2 ⟨h, ha.1⟩
    exact (Finset.card_le_card this).trans (by simp)
  omega

/-- **A closed removal**: `A = {a ∈ atoms | P a}`; the removed atoms (not `P`) are gone, `restrictP` keeps the rest unchanged. -/
theorem restrictTransfer (P : V → Prop) [DecidablePred P] (h : PClosed M P) :
    LadderTransfer M (restrictP M P h) (M.atoms.filter P) where
  subM a ha := (Finset.mem_filter.1 ha).1
  subM' a ha := by
    have := Finset.mem_filter.1 ha
    show a ∈ M.atoms.filter P
    exact ha
  bonds a ha b hb := restrictP_bondsBetween M P h (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  dir a ha b hb := restrictP_directed M P h (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  low x hx hxA := absurd hx hxA

end instances

end WaveTurbulence.FinalCountAsm
