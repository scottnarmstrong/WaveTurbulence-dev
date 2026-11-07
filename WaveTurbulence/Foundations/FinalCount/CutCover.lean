/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Molecules
/-! Generic covering lemma for `Molecule.countE` (FINALCOUNT-HALF M1). -/
@[expose] public section
set_option autoImplicit false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

set_option linter.unusedSectionVars false
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The decoration set of one parameter triple. -/
def decSet (M : Molecule V D) (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) : Set (D → (Fin d → ℤ)) :=
  {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}

/-- Each parameter-class set is bounded by `countE`. -/
theorem decSet_encard_le_countE (M : Molecule V D) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    (β : V → ℝ) (k0 : D → Mom d) (hk : ∀ x, k0 (M.mate x) = k0 x) :
    (decSet M L γ δ w Adm c β k0).encard ≤ M.countE L γ δ w Adm := by
  unfold Molecule.countE
  refine le_iSup_of_le c (le_iSup_of_le hc (le_iSup_of_le β (le_iSup_of_le k0 (le_iSup_of_le hk ?_))))
  exact le_rfl

/-- A parameter triple admissible for `M` (`c_v = 0` at degree 4, `k0` constant on bonds). -/
def ParamOK (M : Molecule V D) (c : V → Mom d) (k0 : D → Mom d) : Prop :=
  (∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) ∧ ∀ x, k0 (M.mate x) = k0 x

/-- **Covering lemma.** If for every admissible parameter triple of `M` the decoration set is covered by the
decoration sets of at most `N` admissible parameter triples of `M'`, then `𝔈(M) ≤ N · 𝔈(M')`. -/
theorem countE_le_mul_of_cover {V' : Type*} [DecidableEq V'] (M : Molecule V D) (M' : Molecule V' D)
    (L γ δ : ℝ) (w : Mom d) (Adm Adm' : (D → (Fin d → ℤ)) → Prop) (N : ℕ)
    (h : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ (ι : Type) (I : Finset ι) (f : ι → (V' → Mom d) × (V' → ℝ) × (D → Mom d)), I.card ≤ N ∧
        (∀ i ∈ I, ParamOK M' (f i).1 (f i).2.2) ∧
        decSet M L γ δ w Adm c β k0 ⊆
          ⋃ i ∈ I, decSet M' L γ δ w Adm' (f i).1 (f i).2.1 (f i).2.2) :
    M.countE L γ δ w Adm ≤ (N : ℕ∞) * M'.countE L γ δ w Adm' := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk => ?_
  obtain ⟨ι, I, f, hn, hf, hsub⟩ := h c β k0 ⟨hc, hk⟩
  calc _ ≤ (⋃ i ∈ I, decSet M' L γ δ w Adm' (f i).1 (f i).2.1 (f i).2.2).encard :=
        Set.encard_le_encard hsub
    _ ≤ ∑ i ∈ I, (decSet M' L γ δ w Adm' (f i).1 (f i).2.1 (f i).2.2).encard :=
        set_encard_biUnion_le I _
    _ ≤ ∑ _i ∈ I, M'.countE L γ δ w Adm' :=
        Finset.sum_le_sum fun i hi => decSet_encard_le_countE M' L γ δ w Adm' _ (hf i hi).1 _ _ (hf i hi).2
    _ = (I.card : ℕ∞) * M'.countE L γ δ w Adm' := by simp
    _ ≤ (N : ℕ∞) * M'.countE L γ δ w Adm' := by gcongr

end WaveTurbulence.FinalCount
