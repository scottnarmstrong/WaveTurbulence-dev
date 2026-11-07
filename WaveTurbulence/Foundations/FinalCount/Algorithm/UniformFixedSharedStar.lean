/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformFixedThirdFine
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameGap
import Mathlib.Tactic

/-! # Two independent internal pairs after fixing the shared star label -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_fixed_shared_star_count_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
    ∀ v1 ∈ r.removedAtoms, ∀ v2 ∈ r.removedAtoms,
    ∀ (e : Fin 5 ↪ Fin P.edges.length), Function.Surjective e →
    ∀ (t1 : AppbTripleFrame r v1) (t2 : AppbTripleFrame r v2),
      (∀ j,t1.index j = e (![1,2,0] j)) → (∀ j,t2.index j = e (![3,4,0] j)) →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∀ (z : Fin d → ℤ) (Q : Finset (Fin P.edges.length → (Fin d → ℤ))),
      Q ⊆ r.localChoices p hLp γ δ w Adm → (∀ q ∈ Q,q (e 0) = z) →
      (Q.card : ℝ) ≤ L^(2*((d : ℝ)-γ)-3*η/2) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_triple_fixed_third_fine_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M P r v1 hv1 v2 hv2 e he t1 t2 ht1 ht2 p w Adm hLG z Q hQ hz
  have h10 := ht1 (0 : Fin 3)
  have h11 := ht1 (1 : Fin 3)
  have h12 := ht1 (2 : Fin 3)
  have h20 := ht2 (0 : Fin 3)
  have h21 := ht2 (1 : Fin 3)
  have h22 := ht2 (2 : Fin 3)
  change t1.index 0 = e 1 at h10
  change t1.index 1 = e 2 at h11
  change t1.index 2 = e 0 at h12
  change t2.index 0 = e 3 at h20
  change t2.index 1 = e 4 at h21
  change t2.index 2 = e 0 at h22
  let f1 := fun q : Fin P.edges.length → (Fin d → ℤ) => (q (t1.index 0),q (t1.index 1))
  let f2 := fun q : Fin P.edges.length → (Fin d → ℤ) => (q (t2.index 0),q (t2.index 1))
  have hi : Set.InjOn (fun q => (f1 q,f2 q)) (Q : Set _) := by
    intro q hq q' hq' hp
    have ha := congrArg Prod.fst hp
    have hb := congrArg Prod.snd hp
    funext i
    obtain ⟨j,rfl⟩ := he i
    fin_cases j
    · exact (hz q hq).trans (hz q' hq').symm
    · have hh := congrArg Prod.fst ha
      change q (t1.index 0) = q' (t1.index 0) at hh
      rw [h10] at hh
      have hn : (1 : Fin 5) = ⟨1,by decide⟩ := by decide
      rw [hn] at hh
      exact hh
    · have hh := congrArg Prod.snd ha
      change q (t1.index 1) = q' (t1.index 1) at hh
      rw [h11] at hh
      have hn : (2 : Fin 5) = ⟨2,by decide⟩ := by decide
      rw [hn] at hh
      exact hh
    · have hh := congrArg Prod.fst hb
      change q (t2.index 0) = q' (t2.index 0) at hh
      rw [h20] at hh
      have hn : (3 : Fin 5) = ⟨3,by decide⟩ := by decide
      rw [hn] at hh
      exact hh
    · have hh := congrArg Prod.snd hb
      change q (t2.index 1) = q' (t2.index 1) at hh
      rw [h21] at hh
      have hn : (4 : Fin 5) = ⟨4,by decide⟩ := by decide
      rw [hn] at hh
      exact hh
  have hsub : Q.image (fun q => (f1 q,f2 q)) ⊆ (Q.image f1) ×ˢ (Q.image f2) := by
    intro a ha
    obtain ⟨q,hq,rfl⟩ := mem_image.mp ha
    exact mem_product.mpr ⟨mem_image_of_mem _ hq,mem_image_of_mem _ hq⟩
  have hc : Q.card ≤ (Q.image f1).card*(Q.image f2).card := by
    rw [← Finset.card_image_of_injOn hi]
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_product _ _)
  have hb1 := hL₀ V D L hL hLp M P r v1 hv1 t1 p w Adm z Q hQ (by simpa only [h12] using hz) (by
    intro hsign κ hκ
    exact appb_tripleFrame_pair_gap r t1 hv1 L w κ _ hκ.1.1 (hLG κ hκ.2.2) 0 1 (by decide) hsign)
  have hb2 := hL₀ V D L hL hLp M P r v2 hv2 t2 p w Adm z Q hQ (by simpa only [h22] using hz) (by
    intro hsign κ hκ
    exact appb_tripleFrame_pair_gap r t2 hv2 L w κ _ hκ.1.1 (hLG κ hκ.2.2) 0 1 (by decide) hsign)
  have hcast : (Q.card : ℝ) ≤ ((Q.image f1).card : ℝ)*((Q.image f2).card : ℝ) := by exact_mod_cast hc
  refine (hcast.trans (mul_le_mul hb1 hb2 (by positivity) (Real.rpow_nonneg hLp.le _))).trans_eq ?_
  rw [← Real.rpow_add hLp]
  congr 1
  ring

end WaveTurbulence.Mole.AppbAlgorithm
