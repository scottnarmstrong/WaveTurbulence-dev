/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.LatticeCfg
/-! FLOWER-P7: counting lemmas for the sums over component data pairs. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

theorem vec_le_of_kindOK {M : ℕ} {kind : TreeKind} {v : Fin (2 * 3) → ℕ} (h : VecKindOK M kind v)
    (c : Fin (2 * 3)) : v c ≤ M := by
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective c
  cases kind with
  | tr =>
    have h1 := h j
    have h2 : v (idx j i) ≤ ∑ i' : Fin 3, v (idx j i') :=
      Finset.single_le_sum (f := fun i' => v (idx j i')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    show v (idx j i) ≤ M
    omega
  | L0 => exact (h j).2 i

theorem glueVec_inl {a b w : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin w) (vA : Fin a → ℕ) (vB : Fin b → ℕ) (i : Fin a) :
    glueVec σ vA vB (σ (.inl i)) = vA i := by simp [glueVec]

theorem glueVec_inr {a b w : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin w) (vA : Fin a → ℕ) (vB : Fin b → ℕ) (i : Fin b) :
    glueVec σ vA vB (σ (.inr i)) = vB i := by simp [glueVec]

theorem entries_of_glueKindOK {a b : ℕ} {M : ℕ} {kind : TreeKind} (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3))
    (vA : Fin a → ℕ) (vB : Fin b → ℕ) (h : VecKindOK M kind (glueVec σ vA vB)) :
    (∀ i, vA i ≤ M) ∧ ∀ i, vB i ≤ M :=
  ⟨fun i => by simpa [glueVec_inl] using vec_le_of_kindOK h (σ (.inl i)),
   fun i => by simpa [glueVec_inr] using vec_le_of_kindOK h (σ (.inr i))⟩

theorem sum_pairs_le {a b : ℕ} (DA : Finset (ℕ × (Fin a → ℕ))) (DB : Finset (ℕ × (Fin b → ℕ)))
    (J : ℕ × (Fin a → ℕ) → ℕ × (Fin b → ℕ) → Prop) {instJ : ∀ x y, Decidable (J x y)} (N0 M : ℕ)
    (hJ : ∀ x y, J x y → x.1 + y.1 = N0 ∧ (∀ i, x.2 i ≤ M) ∧ (∀ i, y.2 i ≤ M))
    (f : ℕ × (Fin a → ℕ) → ℕ × (Fin b → ℕ) → ℝ) (T : ℝ) (hT : 0 ≤ T) (hf : ∀ x y, J x y → f x y ≤ T) :
    ∑ x ∈ DA, ∑ y ∈ DB, (@ite ℝ (J x y) (instJ x y) (f x y) 0) ≤ (((N0 + 1) * ((M + 1) ^ a * (M + 1) ^ b) : ℕ) : ℝ) * T := by
  classical
  have hite : ∀ x y, @ite ℝ (J x y) (instJ x y) (f x y) 0 = if J x y then f x y else 0 := fun x y => by
    by_cases h : J x y <;> simp [h]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hite x y))]
  rw [← Finset.sum_product' (f := fun x y => if J x y then f x y else 0), ← Finset.sum_filter]
  have hsub : (DA ×ˢ DB).filter (fun z => J z.1 z.2) ⊆
      ((Finset.range (N0 + 1)) ×ˢ (vecBox a M ×ˢ vecBox b M)).image
        (fun q => ((q.1, q.2.1), (N0 - q.1, q.2.2))) := by
    intro z hz
    obtain ⟨-, hJz⟩ := Finset.mem_filter.1 hz
    obtain ⟨h1, h2, h3⟩ := hJ _ _ hJz
    refine Finset.mem_image.2 ⟨(z.1.1, z.1.2, z.2.2), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨by omega, mem_vecBox h2, mem_vecBox h3⟩
    · ext <;> simp <;> omega
  calc ∑ z ∈ (DA ×ˢ DB).filter (fun z => J z.1 z.2), f z.1 z.2
      ≤ ((DA ×ˢ DB).filter (fun z => J z.1 z.2)).card • T :=
        Finset.sum_le_card_nsmul _ _ _ fun z hz => hf _ _ (Finset.mem_filter.1 hz).2
    _ ≤ (((N0 + 1) * ((M + 1) ^ a * (M + 1) ^ b) : ℕ) : ℝ) * T := by
        rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ hT
        have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
        rw [Finset.card_product, Finset.card_product, Finset.card_range, card_vecBox, card_vecBox] at hc
        exact_mod_cast hc

end WaveTurbulence.FlowerP7
