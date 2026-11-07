/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOverlapEncoding
public import WaveTurbulence.Foundations.FinalCount.AppBOrderedSignedTriple
public import WaveTurbulence.Foundations.FinalCount.AppBStarPhysical
import Mathlib.Tactic

/-! # Overlapping triple counting with arbitrary admissible source signs -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset

theorem appb_signed_star_physical_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, 0 < L → ∀ w : Mom d,
    ∀ (signs : Bool → Fin 3 → ℤˣ),
      (∀ b,¬∀ j,signs b j = 1) → (∀ b,¬∀ j,signs b j = -1) →
    ∀ (K : Bool → Mom d) (β : Bool → ℝ) (centers : Fin 5 → Mom d),
    ∀ s : Finset (Fin 5 → (Fin d → ℤ)),
      (∀ q ∈ s, (∀ j,‖w+latticePoint L (q j)-centers j‖ ≤ 1) ∧
        ∀ b, (∑ j : Fin 3,(signs b j : ℤ) • (w+latticePoint L (q (appbOverlapRaw false b j)))) = K b ∧
          |(∑ j : Fin 3,(((signs b j : ℤ) : ℝ))*‖w+latticePoint L (q (appbOverlapRaw false b j))‖^2)-β b| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_star_physical_count_bound d hd γ hγ δ hδ m
  refine ⟨L₀,?_⟩
  intro L hL hLp w signs hplus hminus K β centers s hs
  obtain ⟨o⟩ := appb_overlap_order_exists (signs false) (signs true) (hplus false) (hminus false) (hplus true) (hminus true)
  let encode := fun q : Fin 5 → (Fin d → ℤ) => fun j => q (o.index j)
  have heinj : Function.Injective encode := by
    intro q q' he
    funext i
    obtain ⟨j,rfl⟩ := Finite.surjective_of_injective o.index.injective i
    exact congrFun he j
  let σ1 := signs o.swap (o.first 0)
  let σ2 := signs (!o.swap) (o.second 0)
  have hs1 : signs o.swap (o.first 0) = signs o.swap (o.first 2) := by
    cases ho : o.swap <;> simpa [ho] using o.first_same
  have ho1 : signs o.swap (o.first 0) ≠ signs o.swap (o.first 1) := by
    cases ho : o.swap <;> simpa [ho] using o.first_opposite
  have hs2 : signs (!o.swap) (o.second 0) = signs (!o.swap) (o.second 2) := by
    cases ho : o.swap <;> simpa [ho] using o.second_same
  have ho2 : signs (!o.swap) (o.second 0) ≠ signs (!o.swap) (o.second 1) := by
    cases ho : o.swap <;> simpa [ho] using o.second_opposite
  have hb := hL₀ L hL hLp o.profile w
    (((σ1⁻¹ : ℤˣ) : ℤ) • K o.swap) (((σ2⁻¹ : ℤˣ) : ℤ) • K (!o.swap))
    (fun j => centers (o.index j)) (((σ1⁻¹ : ℤˣ) : ℤ)*β o.swap) (((σ2⁻¹ : ℤˣ) : ℤ)*β (!o.swap))
    (s.image encode) (by
      intro q hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
      let Q := fun j : Fin 5 => w+latticePoint L (u j)
      have hm1 := appb_ordered_signed_triple_momentum (signs o.swap) o.first hs1 ho1
        (fun j => Q (appbOverlapRaw false o.swap j)) (K o.swap) ((hs u hu).2 o.swap).1
      have hm2 := appb_ordered_signed_triple_momentum (signs (!o.swap)) o.second hs2 ho2
        (fun j => Q (appbOverlapRaw false (!o.swap) j)) (K (!o.swap)) ((hs u hu).2 (!o.swap)).1
      have he1 := appb_ordered_signed_triple_energy (signs o.swap) o.first hs1 ho1
        (fun j => ‖Q (appbOverlapRaw false o.swap j)‖^2) (β o.swap) _ ((hs u hu).2 o.swap).2
      have he2 := appb_ordered_signed_triple_energy (signs (!o.swap)) o.second hs2 ho2
        (fun j => ‖Q (appbOverlapRaw false (!o.swap) j)‖^2) (β (!o.swap)) _ ((hs u hu).2 (!o.swap)).2
      have hfirst (j : Fin 3) := appb_overlap_first_index (signs false) (signs true) o j
      have hsecond := appb_overlap_second_encoding (signs false) (signs true) o u
      refine ⟨fun j => (hs u hu).1 (o.index j),?_,?_,?_,?_⟩
      · simp only [hfirst] at hm1
        exact hm1
      · change (w+latticePoint L (appbStarSecond o.profile (encode u)).1)-
          (w+latticePoint L (appbStarSecond o.profile (encode u)).2.1)+
          (w+latticePoint L (appbStarSecond o.profile (encode u)).2.2) = _
        rw [hsecond]
        exact hm2
      · simp only [hfirst] at he1
        exact he1
      · change |‖w+latticePoint L (appbStarSecond o.profile (encode u)).1‖^2-
          ‖w+latticePoint L (appbStarSecond o.profile (encode u)).2.1‖^2+
          ‖w+latticePoint L (appbStarSecond o.profile (encode u)).2.2‖^2-_| ≤ _
        rw [hsecond]
        exact he2)
  rw [card_image_of_injective _ heinj] at hb
  exact hb

end WaveTurbulence.Mole
