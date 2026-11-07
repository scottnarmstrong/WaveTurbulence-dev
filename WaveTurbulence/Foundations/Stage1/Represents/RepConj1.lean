/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4KConj
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the leafwise kernel of a conjugate garden (finding F-CONJ)

`kernelLeaves` of the conjugate garden `LH` of `LG` with the transported leaf profile `transferProf h H` is the
complex conjugate of `kernelLeaves` of `LG` with profile `H`.  Conjugation reverses the signs, so the input leaves
of `LH` are the partners of the input leaves of `LG`; the profile of the input leaf `ℓ'` of `LH` is the profile of
the input leaf `pair (leafEquiv⁻¹ ℓ')` of `LG` (the same proof as `PL234.Conj.kernelK_conj`).
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset ComplexConjugate
open scoped Classical

namespace WaveTurbulence.Represents

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL234.Conj

variable {w : ℕ} {LG LH : LayeredGarden w} {e : Fin w ≃ Fin w}

theorem pair_symm_mem_input (h : IsConjugateBy LG LH e) {ℓ' : GLeaf LH.garden.tree}
    (hℓ' : ℓ' ∈ inputLeaves LH.garden) :
    LG.garden.pair ((leafEquiv h).symm ℓ') ∈ inputLeaves LG.garden := by
  obtain ⟨ℓ, rfl⟩ := (leafEquiv h).surjective ℓ'
  simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ' ⊢
  obtain ⟨hs, hm⟩ := hℓ'
  rw [mark_leaf] at hm
  rw [leaf_toNode, sign_node] at hs
  have hne : LG.garden.pair ℓ ≠ ℓ := fun he => ((LG.garden.pair_eq_iff ℓ).1 he) hm
  rw [Equiv.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · show nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = 1
    rw [LG.garden.pair_sign ℓ hne]
    exact hs
  · by_contra hm'
    have := (LG.garden.pair_eq_iff (LG.garden.pair ℓ)).2 hm'
    rw [LG.garden.pair_pair] at this
    exact hne this.symm

theorem leafEquiv_pair_mem_input (h : IsConjugateBy LG LH e) {ℓ : GLeaf LG.garden.tree}
    (hℓ : ℓ ∈ inputLeaves LG.garden) :
    leafEquiv h (LG.garden.pair ℓ) ∈ inputLeaves LH.garden := by
  simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
  obtain ⟨hs, hm⟩ := hℓ
  have hne : LG.garden.pair ℓ ≠ ℓ := fun he => ((LG.garden.pair_eq_iff ℓ).1 he) hm
  refine ⟨?_, ?_⟩
  · rw [leaf_toNode, sign_node]
    show -nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = 1
    rw [LG.garden.pair_sign ℓ hne, neg_neg]
    exact hs
  · rw [mark_leaf]
    by_contra hm'
    have := (LG.garden.pair_eq_iff (LG.garden.pair ℓ)).2 hm'
    rw [LG.garden.pair_pair] at this
    exact hne this.symm

/-- Reindexing of products over the input leaves of the conjugate garden. -/
theorem prod_inputs_conj (h : IsConjugateBy LG LH e) {β : Type*} [CommMonoid β]
    (G : GLeaf LH.garden.tree → β) :
    ∏ ℓ' ∈ inputLeaves LH.garden, G ℓ' =
      ∏ ℓ ∈ inputLeaves LG.garden, G (leafEquiv h (LG.garden.pair ℓ)) := by
  symm
  refine Finset.prod_nbij' (fun ℓ => leafEquiv h (LG.garden.pair ℓ))
    (fun ℓ' => LG.garden.pair ((leafEquiv h).symm ℓ')) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · exact fun ℓ hℓ => leafEquiv_pair_mem_input h hℓ
  · exact fun ℓ' hℓ' => pair_symm_mem_input h hℓ'
  · intro ℓ _
    simp only [Equiv.symm_apply_apply, LG.garden.pair_pair]
  · intro ℓ' _
    simp only [LG.garden.pair_pair, Equiv.apply_symm_apply]

/-- Transport of a leaf-indexed datum: the datum of the address of a leaf `ℓ'` of `LH` is the datum of the
address of the partner of the corresponding leaf of `LG`. -/
noncomputable def transferProf {α : Type*} (h : IsConjugateBy LG LH e) (T : (Fin w × Path) → α) :
    (Fin w × Path) → α :=
  fun a => if hx : ∃ ℓ' : GLeaf LH.garden.tree, ℓ'.1 = a then
    T (LG.garden.pair ((leafEquiv h).symm hx.choose)).1 else T a

theorem transferProf_leaf {α : Type*} (h : IsConjugateBy LG LH e) (T : (Fin w × Path) → α)
    (ℓ' : GLeaf LH.garden.tree) :
    transferProf h T ℓ'.1 = T (LG.garden.pair ((leafEquiv h).symm ℓ')).1 := by
  have hx : ∃ ℓ'' : GLeaf LH.garden.tree, ℓ''.1 = ℓ'.1 := ⟨ℓ', rfl⟩
  unfold transferProf
  simp only [hx, ↓reduceDIte]
  have : hx.choose = ℓ' := Subtype.ext hx.choose_spec
  rw [this]

variable {d : ℕ}

theorem summand_leaves_eq (h : IsConjugateBy LG LH e) (L γ δ : ℝ) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ)
    (up' : GBranch LH.garden.tree → ℝ) (hup : ∀ b, up' (branchEquiv h b) = up b) (s : ℝ) (k₀ : Mom d)
    (nroot nroot' : Fin w → (Fin d → ℤ)) (hroot : ∀ j, nroot' (e j) = nroot j) (nfl : Fin d → ℤ)
    (κ : GenDecoration LG.garden d nroot nfl) :
    (epsDec LH.garden (decEquiv h nroot nroot' hroot nfl κ).1 : ℂ) *
        phaseIntegral L γ δ LH.garden (kDomain LH up' s) s
          (cosetDecoration LH.garden L k₀ (decEquiv h nroot nroot' hroot nfl κ).1) *
        ∏ ℓ ∈ inputLeaves LH.garden, (transferProf h H ℓ.1
          (cosetDecoration LH.garden L k₀ (decEquiv h nroot nroot' hroot nfl κ).1 ℓ.toNode) : ℂ) =
      conj ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) := by
  have hd : (decEquiv h nroot nroot' hroot nfl κ).1 = fun a => κ.1 ((nodeEquiv h).symm a) := rfl
  have hc : cosetDecoration LH.garden L k₀ (decEquiv h nroot nroot' hroot nfl κ).1 =
      fun a => cosetDecoration LG.garden L k₀ κ.1 ((nodeEquiv h).symm a) := rfl
  have hκ : ∀ ℓ : GLeaf LG.garden.tree, cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode =
      cosetDecoration LG.garden L k₀ κ.1 (LG.garden.pair ℓ).toNode := fun ℓ => by
    unfold cosetDecoration
    rw [κ.2.1.2 ℓ]
  rw [hc, hd, epsDec_eq h κ.1, phaseIntegral_eq h L γ δ (cosetDecoration LG.garden L k₀ κ.1) up up' hup s,
    prod_inputs_conj h, map_mul, map_mul, Complex.conj_ofReal, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  rw [Complex.conj_ofReal, transferProf_leaf, Equiv.symm_apply_apply, LG.garden.pair_pair, leaf_toNode]
  simp only [Equiv.symm_apply_apply]
  rw [← hκ ℓ]

/-- **The leafwise kernel of a conjugate garden is the conjugate kernel** (transported profiles). -/
theorem kernelLeaves_conj (h : IsConjugateBy LG LH e) (L γ δ : ℝ) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ)
    (up' : GBranch LH.garden.tree → ℝ) (hup : ∀ b, up' (branchEquiv h b) = up b) (s : ℝ) (k₀ : Mom d)
    (nroot nroot' : Fin w → (Fin d → ℤ)) (hroot : ∀ j, nroot' (e j) = nroot j) (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LH (transferProf h H) up' s k₀ nroot' nfl =
      conj (kernelLeaves L γ δ LG H up s k₀ nroot nfl) := by
  unfold kernelLeaves
  rw [map_mul, map_mul, map_pow, Complex.conj_ofReal, order_eq h, zeta_eq h, Complex.conj_tsum,
    ← (decEquiv h nroot nroot' hroot nfl).tsum_eq]
  congr 1
  exact tsum_congr fun κ => summand_leaves_eq h L γ δ H up up' hup s k₀ nroot nroot' hroot nfl κ

/-- Couples: swapping the two trees swaps `(t, s)`. -/
theorem coupleLeaves_conj {LG LH : LayeredGarden 2} (h : IsConjugateCouple LG LH) (L γ δ : ℝ)
    (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) :
    coupleLeaves L γ δ LH (transferProf h H) s t k = conj (coupleLeaves L γ δ LG H t s k) := by
  unfold coupleLeaves
  refine kernelLeaves_conj h L γ δ H _ _ (fun b => ?_) 0 k _ _ (fun _ => rfl) 0
  rcases b with ⟨⟨i, p⟩, hp⟩
  show (if Equiv.swap (0 : Fin 2) 1 i = 0 then s else t) = if i = 0 then t else s
  fin_cases i <;> simp

/-- The cost of the transported profile bound is unchanged. -/
theorem leafSizeProduct_conj (h : IsConjugateBy LG LH e) (B : (Fin w × Path) → NNReal) :
    leafSizeProduct LH (transferProf h B) = leafSizeProduct LG B := by
  unfold leafSizeProduct
  rw [prod_inputs_conj h]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  rw [transferProf_leaf, Equiv.symm_apply_apply, LG.garden.pair_pair]

theorem leafwiseControlled_conj (h : IsConjugateBy LG LH e) {H : LeafProfiles w d}
    {B : (Fin w × Path) → NNReal} (hc : LeafwiseControlled LG H B) :
    LeafwiseControlled LH (transferProf h H) (transferProf h B) := by
  intro ℓ' hℓ'
  rw [transferProf_leaf, transferProf_leaf]
  exact hc _ (pair_symm_mem_input h hℓ')

end WaveTurbulence.Represents
