/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2
import Mathlib.Tactic

/-! # The relaxed count `𝔄` under a relabelling of darts, and its monotonicity in the LG parameter

Two molecules on the same atoms whose darts correspond (same atoms, mates and directions) have the same ladders, the
same large gaps and the same cell gaps, so `𝔄` does not change. Erasing twice is erasing the union.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

section Equiv
variable (M : Molecule V D) (N : Molecule V E) (f : D ≃ E) (hA : M.atoms = N.atoms)
  (ha : ∀ x, N.atom (f x) = M.atom x) (hm : ∀ x, N.mate (f x) = f (M.mate x)) (ho : ∀ x, N.out (f x) = M.out x)
include hA ha hm ho

omit hA [DecidableEq D] [DecidableEq E] in
theorem bondsBetween_eq_of_dart_equiv (u v : V) : M.bondsBetween u v = N.bondsBetween u v := by
  classical
  have hend (x : D) : N.ends (f x) = M.ends x := by unfold Molecule.ends; rw [ha, hm, ha]
  unfold Molecule.bondsBetween
  apply card_bij (fun x _ => f x)
  · intro x hx
    simp only [mem_filter, Molecule.bonds, mem_univ, true_and] at hx ⊢
    exact ⟨(ho x).trans hx.1, (hend x).trans hx.2⟩
  · intro x _ y _ he; exact f.injective he
  · intro y hy
    obtain ⟨x, rfl⟩ := f.surjective y
    refine ⟨x, ?_, rfl⟩
    simp only [mem_filter, Molecule.bonds, mem_univ, true_and] at hy ⊢
    exact ⟨(ho x).symm.trans hy.1, (hend x).symm.trans hy.2⟩

omit hA [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E] in
theorem directed_iff_of_dart_equiv (u v : V) : M.Directed u v ↔ N.Directed u v := by
  constructor
  · rintro ⟨x, hx, hxa, hxb⟩
    exact ⟨f x, (ho x).trans hx, (ha x).trans hxa, by rw [hm, ha]; exact hxb⟩
  · rintro ⟨y, hy, hya, hyb⟩
    obtain ⟨x, rfl⟩ := f.surjective y
    exact ⟨x, (ho x).symm.trans hy, (ha x).symm.trans hya, by rw [hm, ha] at hyb; exact hyb⟩

omit [DecidableEq D] [DecidableEq E] in
theorem sourceLadder_iff_of_dart_equiv {m : ℕ} (u v : Fin (m + 1) → V) :
    Degen.SourceLadder M u v ↔ Degen.SourceLadder N u v := by
  simp only [Degen.SourceLadder, hA, bondsBetween_eq_of_dart_equiv M N f ha hm ho,
    directed_iff_of_dart_equiv M N f ha hm ho]

omit [DecidableEq D] [DecidableEq E] in
/-- **The admissibility `lgAdm` is carried along a dart relabelling.** -/
theorem lgAdm_relabel {d : ℕ} {L γ η : ℝ} {P : Finset V → ℝ} {κ : D → (Fin d → ℤ)} (h : lgAdm M L γ η P κ) :
    lgAdm N L γ η P (MoleProp.relabelDartLabels f κ) := by
  have hkv (x : D) : Molecule.kvec L 0 (MoleProp.relabelDartLabels f κ) (f x) = Molecule.kvec L 0 κ x := by
    simp only [Molecule.kvec, MoleProp.relabelDartLabels, Equiv.coe_fn_mk, f.symm_apply_apply]
  refine ⟨fun y₁ y₂ h12 hdir => ?_, fun u v hL r hr => ?_⟩
  · obtain ⟨x₁, rfl⟩ := f.surjective y₁
    obtain ⟨x₂, rfl⟩ := f.surjective y₂
    rw [hkv, hkv]
    exact h.1 x₁ x₂ (by rw [← ha, ← ha]; exact h12) (by rw [← ho, ← ho]; exact hdir)
  · have hL' := (sourceLadder_iff_of_dart_equiv M N f hA ha hm ho u v).mpr hL
    obtain ⟨y₁, y₂, he1, he2, ha1, ha2, rfl⟩ := hr
    obtain ⟨x₁, rfl⟩ := f.surjective y₁
    obtain ⟨x₂, rfl⟩ := f.surjective y₂
    have hend (x : D) : N.ends (f x) = M.ends x := by unfold Molecule.ends; rw [ha, hm, ha]
    refine h.2 u v hL' _ ⟨x₁, x₂, (hend x₁).symm.trans he1, (hend x₂).symm.trans he2, (ha x₁).symm.trans ha1,
      (ha x₂).symm.trans ha2, ?_⟩
    simp only [Molecule.gapAt, hkv]

/-- **`𝔄` is invariant under a dart relabelling.** -/
theorem afree_le_of_dart_equiv {d : ℕ} (L γ δ η C1 : ℝ) (P : Finset V → ℝ) :
    AFree M d L γ δ η C1 P ≤ AFree N d L γ δ η C1 P :=
  MoleProp.countAFree_le_of_dart_equiv M N f hA ha hm ho L γ δ C1 0 _ _
    (fun _ h => lgAdm_relabel M N f hA ha hm ho h) P

theorem ladderCells_eq_of_dart_equiv' : MoleProp.ladderCells M = MoleProp.ladderCells N :=
  MoleProp.ladderCells_eq_of_dart_equiv M N f hA ha hm ho

theorem afreeSup_le_of_dart_equiv {d : ℕ} (L γ δ η C1 : ℝ) :
    AFreeSup M d L γ δ η C1 ≤ AFreeSup N d L γ δ η C1 := by
  unfold AFreeSup
  rw [ladderCells_eq_of_dart_equiv' M N f hA ha hm ho]
  exact iSup₂_mono fun P _ => afree_le_of_dart_equiv M N f hA ha hm ho L γ δ η C1 P

end Equiv

/-- **Erasing twice is erasing the union** (for `𝔄`). -/
theorem afree_erase_erase_le (M : Molecule V D) (Y Z : Finset V) {d : ℕ} (L γ δ η C1 : ℝ) (P : Finset V → ℝ) :
    AFree (Degen.eraseAtoms (Degen.eraseAtoms M Y) Z) d L γ δ η C1 P ≤
      AFree (Degen.eraseAtoms M (Y ∪ Z)) d L γ δ η C1 P := by
  refine afree_le_of_dart_equiv _ _ (MoleProp.eraseDartUnionEquiv M Y Z) ?_ (fun _ => rfl)
    (fun _ => Subtype.ext rfl) (fun _ => rfl) L γ δ η C1 P
  ext a
  change (a ∈ (M.atoms \ Y) \ Z) ↔ a ∈ M.atoms \ (Y ∪ Z)
  simp only [mem_sdiff, mem_union, not_or]
  tauto

omit [DecidableEq D] in
/-- Large gaps with parameter `η` are large gaps with any smaller parameter. -/
theorem lgAdm_mono (M : Molecule V D) {d : ℕ} {L γ η η' : ℝ} (hL : 1 ≤ L) (hη : η' ≤ η) {P : Finset V → ℝ}
    {κ : D → (Fin d → ℤ)} (h : lgAdm M L γ η P κ) : lgAdm M L γ η' P κ :=
  ⟨fun x y h1 h2 => (Real.rpow_le_rpow_of_exponent_le hL (by linarith)).trans (h.1 x y h1 h2), h.2⟩

/-- **`𝔄` increases when the LG parameter decreases.** -/
theorem afree_mono_eta (M : Molecule V D) {d : ℕ} {L γ δ η η' C1 : ℝ} (hL : 1 ≤ L) (hη : η' ≤ η)
    (P : Finset V → ℝ) : AFree M d L γ δ η C1 P ≤ AFree M d L γ δ η' C1 P := by
  unfold AFree MoleProp.countAFree
  exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono (MoleProp.countEFree_mono _ L γ δ 0
    fun κ h => lgAdm_mono M hL hη h)) bot_le

theorem afree_le_afreeSup (M : Molecule V D) {d : ℕ} {L γ δ η C1 : ℝ} (P : Finset V → ℝ)
    (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) : AFree M d L γ δ η C1 P ≤ AFreeSup M d L γ δ η C1 :=
  le_iSup₂_of_le (f := fun P (_ : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) => AFree M d L γ δ η C1 P) P hP le_rfl

end WaveTurbulence.MoleProp4
