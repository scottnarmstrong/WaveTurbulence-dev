/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmCountBase
/-! **FINALCOUNT-ASSEMBLY, A2: monotonicity and subadditivity of `countE`/`countA` in the admissible class.** -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem encard_le_countE (M : Molecule V D) (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) (β : V → ℝ) (k0 : D → Mom d)
    (hk0 : ∀ x, k0 (M.mate x) = k0 x) :
    {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}.encard ≤ M.countE L γ δ w Adm := by
  unfold Molecule.countE
  exact le_iSup_of_le c (le_iSup_of_le hc (le_iSup_of_le β (le_iSup_of_le k0 (le_iSup_of_le hk0 le_rfl))))

theorem countE_mono_adm (M : Molecule V D) (L γ δ : ℝ) (w : Mom d) {Adm Adm' : (D → (Fin d → ℤ)) → Prop}
    (h : ∀ κ, Adm κ → Adm' κ) : M.countE L γ δ w Adm ≤ M.countE L γ δ w Adm' := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  refine le_trans (Set.encard_le_encard ?_) (encard_le_countE M L γ δ w Adm' c hc β k0 hk0)
  rintro κ ⟨a, b, e⟩; exact ⟨a, b, h κ e⟩

theorem countE_union_le {ι : Type*} (M : Molecule V D) (L γ δ : ℝ) (w : Mom d) (S : Finset ι)
    {Adm : (D → (Fin d → ℤ)) → Prop} (Adm' : ι → (D → (Fin d → ℤ)) → Prop)
    (h : ∀ κ, Adm κ → ∃ j ∈ S, Adm' j κ) :
    M.countE L γ δ w Adm ≤ ∑ j ∈ S, M.countE L γ δ w (Adm' j) := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  have hsub : {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ} ⊆
      ⋃ j ∈ S, {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm' j κ} := by
    rintro κ ⟨a, b, e⟩
    obtain ⟨j, hj, hj'⟩ := h κ e
    exact Set.mem_biUnion hj ⟨a, b, hj'⟩
  refine le_trans (Set.encard_le_encard hsub) (le_trans (Finset.set_encard_biUnion_le S _) ?_)
  refine Finset.sum_le_sum fun j _ => ?_
  exact encard_le_countE M L γ δ w (Adm' j) c hc β k0 hk0

theorem countA_mono_adm (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d) {Adm Adm' : (D → (Fin d → ℤ)) → Prop}
    (h : ∀ κ, Adm κ → Adm' κ) (P : Finset V → ℝ) : M.countA L γ δ C₁ w Adm P ≤ M.countA L γ δ C₁ w Adm' P := by
  unfold Molecule.countA
  have := ENat.toENNReal_le.2 (countE_mono_adm M L γ δ w h)
  gcongr

theorem countA_union_le {ι : Type*} (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d) (S : Finset ι)
    {Adm : (D → (Fin d → ℤ)) → Prop} (Adm' : ι → (D → (Fin d → ℤ)) → Prop)
    (h : ∀ κ, Adm κ → ∃ j ∈ S, Adm' j κ) (P : Finset V → ℝ) :
    M.countA L γ δ C₁ w Adm P ≤ ∑ j ∈ S, M.countA L γ δ C₁ w (Adm' j) P := by
  unfold Molecule.countA
  rw [← Finset.sum_mul]
  have := ENat.toENNReal_le.2 (countE_union_le M L γ δ w S Adm' h)
  have e : ((∑ j ∈ S, M.countE L γ δ w (Adm' j) : ℕ∞) : ℝ≥0∞) = ∑ j ∈ S, ((M.countE L γ δ w (Adm' j) : ℕ∞) : ℝ≥0∞) :=
    map_sum ENat.toENNRealRingHom _ _
  rw [e] at this; gcongr

end WaveTurbulence.FinalCountAsm
