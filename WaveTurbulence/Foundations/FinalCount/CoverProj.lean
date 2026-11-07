/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutCover
/-! Covering lemma with a projection (FINALCOUNT-G2, infrastructure): the decorations of `M` are covered by at most
`N` sets, each injecting under a restriction map into a decoration set of the smaller molecule `M'`. Used for the
removal steps (a removed component is determined by finitely many bond vectors). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **Covering with projection.** If for every admissible parameter triple of `M` the decoration set is covered by at
most `N` sets `G i`, and the projection `ρ` is injective on each `G i` with image inside the decoration set of an
admissible parameter triple of `M'`, then `𝔈(M) ≤ N · 𝔈(M')`. -/
theorem countE_le_mul_of_cover_proj {V' D' : Type*} [DecidableEq V'] [Fintype D'] [DecidableEq D']
    (M : Molecule V D) (M' : Molecule V' D') (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (D' → (Fin d → ℤ)) → Prop)
    (ρ : (D → (Fin d → ℤ)) → (D' → (Fin d → ℤ))) (N : ℕ)
    (h : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ (ι : Type) (I : Finset ι) (G : ι → Set (D → (Fin d → ℤ))) (f : ι → (V' → Mom d) × (V' → ℝ) × (D' → Mom d)),
        I.card ≤ N ∧ (∀ i ∈ I, ParamOK M' (f i).1 (f i).2.2) ∧
        decSet M L γ δ w Adm c β k0 ⊆ ⋃ i ∈ I, G i ∧
        ∀ i ∈ I, Set.InjOn ρ (G i ∩ decSet M L γ δ w Adm c β k0) ∧
          ρ '' (G i ∩ decSet M L γ δ w Adm c β k0) ⊆ decSet M' L γ δ w Adm' (f i).1 (f i).2.1 (f i).2.2) :
    M.countE L γ δ w Adm ≤ (N : ℕ∞) * M'.countE L γ δ w Adm' := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk => ?_
  obtain ⟨ι, I, G, f, hn, hf, hcov, hinj⟩ := h c β k0 ⟨hc, hk⟩
  set S := decSet M L γ δ w Adm c β k0 with hS
  have hSsub : S ⊆ ⋃ i ∈ I, (G i ∩ S) := by
    intro κ hκ
    obtain ⟨i, hi, hG⟩ := Set.mem_iUnion₂.mp (hcov hκ)
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hG, hκ⟩
  calc S.encard ≤ (⋃ i ∈ I, (G i ∩ S)).encard := Set.encard_le_encard hSsub
    _ ≤ ∑ i ∈ I, (G i ∩ S).encard := set_encard_biUnion_le I _
    _ ≤ ∑ _i ∈ I, M'.countE L γ δ w Adm' := by
        refine Finset.sum_le_sum fun i hi => ?_
        calc (G i ∩ S).encard = (ρ '' (G i ∩ S)).encard := (Set.InjOn.encard_image (hinj i hi).1).symm
          _ ≤ (decSet M' L γ δ w Adm' (f i).1 (f i).2.1 (f i).2.2).encard :=
              Set.encard_le_encard (hinj i hi).2
          _ ≤ _ := decSet_encard_le_countE M' L γ δ w Adm' _ (hf i hi).1 _ _ (hf i hi).2
    _ = (I.card : ℕ∞) * M'.countE L γ δ w Adm' := by simp
    _ ≤ (N : ℕ∞) * M'.countE L γ δ w Adm' := by gcongr

end WaveTurbulence.FinalCount
