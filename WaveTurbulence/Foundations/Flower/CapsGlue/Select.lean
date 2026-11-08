/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Stem
/-! # A3a CAPS-GLUE: stem sets, depth selections and `selOK` of a glue -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {m w d : ℕ} {a : Fin m → ℕ}

theorem stemSetCap_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (c : Fin m) (i : Fin (a c)) :
    stemSetCap (glueL σ LA) J (σ ⟨c, i⟩) =
      (stemSetCap (LA c) (resJ σ J c) i).map (embBr σ (fun c => (LA c).garden.tree) c) := by
  ext b
  obtain ⟨⟨c', y⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective b
  simp only [stemSetCap, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, embBr_apply]
  constructor
  · rintro ⟨h1, h2, h3⟩
    simp only [glueBranchN_val] at h1
    obtain ⟨hc, hy⟩ := (sigma_val_eq_iff σ i y.1.1).1 h1
    subst hc
    have hy' : y.1.1 = i := hy
    refine ⟨y, ⟨hy', ?_, ?_⟩, rfl⟩
    · rw [glueBranchN_toNode] at h2
      exact (onCapStem_glueN σ LA J c' y.toNode).1 h2
    · exact fun hp => h3 ((isCapFlowerParent_glueN σ LA J c' y).2 hp)
  · rintro ⟨y, ⟨h1, h2, h3⟩, he⟩
    have he' := (glueBranchN σ fun c => (LA c).garden.tree).injective he
    simp only [Sigma.mk.injEq] at he'
    obtain ⟨rfl, he2⟩ := he'
    have := eq_of_heq he2
    subst this
    refine ⟨by simp [h1], ?_, ?_⟩
    · rw [glueBranchN_toNode]
      exact (onCapStem_glueN σ LA J c y.toNode).2 h2
    · exact fun hp => h3 ((isCapFlowerParent_glueN σ LA J c y).1 hp)

theorem stemAt_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (c : Fin m) (i : Fin (a c)) (k : ℕ) :
    stemAt (glueL σ LA) J (σ ⟨c, i⟩) k =
      (stemAt (LA c) (resJ σ J c) i k).map (embBr σ (fun c => (LA c).garden.tree) c) := by
  have hS : (stemSetCap (glueL σ LA) J (σ ⟨c, i⟩)).filter (fun b => b.1.2.length = k) =
      ((stemSetCap (LA c) (resJ σ J c) i).filter (fun b => b.1.2.length = k)).map
        (embBr σ (fun c => (LA c).garden.tree) c) := by
    rw [stemSetCap_glueN, Finset.filter_map]
    congr 1
  unfold stemAt
  by_cases h : ((stemSetCap (LA c) (resJ σ J c) i).filter fun b => b.1.2.length = k).card = 1
  · have hG : ((stemSetCap (glueL σ LA) J (σ ⟨c, i⟩)).filter fun b => b.1.2.length = k).card = 1 := by
      rw [hS, Finset.card_map]; exact h
    rw [dif_pos hG, dif_pos h, Option.map_some]
    congr 1
    have e1 := Classical.choose_spec (Finset.card_eq_one.mp hG)
    have e2 := Classical.choose_spec (Finset.card_eq_one.mp h)
    have e1' := hS.symm.trans e1
    rw [e2, Finset.map_singleton] at e1'
    exact (Finset.singleton_inj.mp e1').symm
  · have hG : ¬ ((stemSetCap (glueL σ LA) J (σ ⟨c, i⟩)).filter fun b => b.1.2.length = k).card = 1 := by
      rw [hS, Finset.card_map]; exact h
    rw [dif_neg hG, dif_neg h]
    rfl

theorem selCap_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (c : Fin m) (i : Fin (a c)) :
    selCap (glueL σ LA) J kSel (σ ⟨c, i⟩) =
      (selCap (LA c) (resJ σ J c) (resF σ kSel c) i).map (embBr σ (fun c => (LA c).garden.tree) c) := by
  unfold selCap resF
  rcases kSel (σ ⟨c, i⟩) with _ | k
  · rfl
  · exact stemAt_glueN σ LA J c i k

theorem selOK_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) :
    selOK (glueL σ LA) J kSel = ∏ c, selOK (LA c) (resJ σ J c) (resF σ kSel c) := by
  have key : ∀ c i, ((resF σ kSel c i).isSome → (selCap (LA c) (resJ σ J c) (resF σ kSel c) i).isSome) ↔
      ((kSel (σ ⟨c, i⟩)).isSome → (selCap (glueL σ LA) J kSel (σ ⟨c, i⟩)).isSome) := by
    intro c i
    rw [selCap_glueN, Option.isSome_map]
    rfl
  by_cases h : ∀ j, (kSel j).isSome → (selCap (glueL σ LA) J kSel j).isSome
  · unfold selOK
    rw [if_pos h]
    symm
    refine Finset.prod_eq_one fun c _ => ?_
    rw [if_pos]
    exact fun i => (key c i).2 (h _)
  · unfold selOK
    rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj1, hj2⟩ := h
    obtain ⟨⟨c, i⟩, rfl⟩ := σ.surjective j
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    rw [if_neg]
    intro hall
    exact hj2 ((key c i).1 (hall i) hj1)

end WaveTurbulence.Flower.CapsGlue
