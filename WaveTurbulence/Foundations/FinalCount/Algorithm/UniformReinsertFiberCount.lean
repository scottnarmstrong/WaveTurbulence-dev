/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleFixedThird

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformTripleFixedThird
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # Counting actual reinsertion fibers by the remaining internal pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

/-- Conditional reconstruction helper: the caller supplies the proved
injectivity of the concrete figure's three-label projection. The pair
count itself is derived from actual source equations and the internal-gap
test, rather than assumed as an input. -/
theorem uniform_reinsert_card_le_of_frame_injective (d : ℕ) (hd : 2 ≤ d) (δ γ : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
    ∀ v ∈ r.removedAtoms, ∀ t : AppbTripleFrame r v,
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      Set.InjOn (t.project (K := Fin d → ℤ)) (r.localChoices p hLp γ δ w Adm : Set _) →
      (appbIncidenceSign M v (r.edge (t.index 0)).val ≠ appbIncidenceSign M v (r.edge (t.index 1)).val →
        ∀ κ,κ ∈ p.decorations L γ δ w Adm →
        L^(-γ+2*min γ (1-γ)/3) ≤ ‖Molecule.kvec L w κ (r.edge (t.index 0)).val-
          Molecule.kvec L w κ (r.edge (t.index 1)).val‖) →
      ∀ S : Finset (D → (Fin d → ℤ)), (∀ κ ∈ S,κ ∈ p.decorations L γ δ w Adm) →
      (S.card : ℝ) ≤ L^((d : ℝ)-γ-31*min γ (1-γ)/48)*
        ((S.image (fun κ => r.reinsertedLabels κ (t.index 2))).card : ℝ) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_triple_fixed_third_good_bound d hd δ γ hδ hγ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M P r v hv t p w Adm hframe hgap S hS
  let post := fun κ : D → (Fin d → ℤ) => r.reinsertedLabels κ (t.index 2)
  let T := fun ζ => S.filter fun κ => post κ = ζ
  have hfiber (ζ : (Degen.RetainedDart M r.removedAtoms ⊕ Bool) → (Fin d → ℤ)) :
      ((T ζ).card : ℝ) ≤ L^((d : ℝ)-γ-31*min γ (1-γ)/48) := by
    let Q := (T ζ).image r.localLabels
    have hQ : Q ⊆ r.localChoices p hLp γ δ w Adm := by
      intro q hq
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hq
      exact (r.mem_localChoices p hLp γ δ w Adm _).mpr ⟨κ,hS κ (mem_filter.mp hκ).1,rfl⟩
    have hfixed : ∀ q ∈ Q,q (t.index 2) = ζ (Sum.inr true) := by
      intro q hq
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hq
      exact congrFun (mem_filter.mp hκ).2 (Sum.inr true)
    have hb := hL₀ V D L hL hLp M P r v hv t p w Adm (ζ (Sum.inr true)) Q hQ hfixed hgap
    have hinj : Set.InjOn (fun κ : D → (Fin d → ℤ) =>
        (r.localLabels κ (t.index 0),r.localLabels κ (t.index 1))) (T ζ : Set _) := by
      intro κ hκ κ' hκ' he
      have hp := (mem_filter.mp hκ).2.trans (mem_filter.mp hκ').2.symm
      have hdec := hS κ (mem_filter.mp hκ).1
      have hdec' := hS κ' (mem_filter.mp hκ').1
      have hloc : r.localLabels κ = r.localLabels κ' := by
        apply hframe
          ((r.mem_localChoices p hLp γ δ w Adm _).mpr ⟨κ,hdec,rfl⟩)
          ((r.mem_localChoices p hLp γ δ w Adm _).mpr ⟨κ',hdec',rfl⟩)
        funext j
        fin_cases j
        · exact congrArg Prod.fst he
        · exact congrArg Prod.snd he
        · exact congrFun hp (Sum.inr true)
      apply r.labels_injective hdec.1.1 hdec'.1.1 hloc
      funext x
      exact congrFun hp (Sum.inl x)
    have hc : (Q.image (fun q => (q (t.index 0),q (t.index 1)))).card = (T ζ).card := by
      dsimp only [Q]
      rw [Finset.image_image]
      exact card_image_of_injOn hinj
    rw [hc] at hb
    exact hb
  have hcard := card_eq_sum_card_image post S
  calc
    (S.card : ℝ) = ∑ ζ ∈ S.image post,((T ζ).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _ζ ∈ S.image post,L^((d : ℝ)-γ-31*min γ (1-γ)/48) := sum_le_sum (fun ζ hζ => hfiber ζ)
    _ = _ := by rw [sum_const,nsmul_eq_mul]; ring

end WaveTurbulence.Mole.AppbAlgorithm
