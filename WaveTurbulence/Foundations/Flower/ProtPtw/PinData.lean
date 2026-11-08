/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.TreeFacts

/-! # D6a PROT-PTW: the pin data of a protected tree

`pin = true`: the terminal branch `T` is designated at `s`; its link `j₀` is exceptional and carries the dagger.
`pin = false`: nothing is designated and the dagger is `1`. Packaged as: the exceptional set `Ep` of the pin, the
dagger weights `dag`, and the facts the kernel bounds need. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links

variable {d : ℕ} {LG : LayeredGarden 1} {X : RegChain}

theorem pin_data (hX : X.DecodesTree LG.garden) (pin : Bool) (hpin : pin = true → X.lonePath ≠ []) (s t₀ L : ℝ)
    (k : Mom d) (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind)
    (hind1 : pin = false → ∀ κ, ind κ = 1) :
    ∃ (Ep : Finset (Fin (X.treeLinks (LG.garden.sig 0)).length))
      (dag : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ),
      Ep.card ≤ (if pin then 1 else 0) ∧
      (∀ i ∉ Ep, ∀ e, (if pin then ProtCfg.term else ProtCfg.none).fix X s s t₀ (treeLinkBranch hX i e) = none) ∧
      (∀ b : GBranch LG.garden.tree, (pin = true → b.1.2 ≠ X.lonePath.dropLast) →
        (if pin then ProtCfg.term else ProtCfg.none).fix X s s t₀ b = none) ∧
      (∀ i q, ‖dag i q‖ ≤ 1) ∧ (∀ i ∉ Ep, ∀ q, dag i q = 1) ∧
      (∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
        (ind (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ)
          (fun j => (p (j, 0), p (j, 1)))).1) : ℂ) = ∏ i, dag i (p (i, 0), p (i, 1))) := by
  cases pin with
  | false =>
    refine ⟨∅, fun _ _ => 1, by simp, fun i _ e => ?_, fun b _ => ?_, fun _ _ => by simp, fun _ _ _ => rfl,
      fun p => ?_⟩
    · exact fix_none_eq s t₀ _
    · exact fix_none_eq s t₀ _
    · rw [hind1 rfl, Finset.prod_const_one, Complex.ofReal_one]
  | true =>
    obtain ⟨bT, hT⟩ := exists_termBranch hX (hpin rfl)
    set v := (treeLinkEquiv hX).symm bT
    have hbT : treeLinkBranch hX v.1 v.2 = bT := (treeLinkEquiv hX).apply_symm_apply bT
    have hT' : (treeLinkBranch hX v.1 v.2).1.2 = X.lonePath.dropLast := by rw [hbT]; exact hT
    refine ⟨{v.1}, fun i q => if i = v.1 then daggerWeight hX L k ind v.1 q else 1, by simp, fun i hi e => ?_,
      fun b hb => ?_, fun i q => ?_, fun i hi q => ?_, fun p => ?_⟩
    · simp only [ite_true]
      rw [fix_term_eq s t₀ bT hT, ite_eq_right]
      intro h
      apply hi
      rw [← hbT] at h
      exact Finset.mem_singleton.mpr ((treeLinkBranch_eq_iff hX i v.1 e v.2).1 h).1
    · simp only [ite_true]
      rw [fix_term_eq s t₀ bT hT, ite_eq_right]
      rintro rfl
      exact hb rfl hT
    · dsimp only
      by_cases h : i = v.1
      · rw [ite_eq_left h]; exact daggerWeight_norm_le hX L k ind hind v.1 q
      · rw [ite_eq_right h, norm_one]
    · dsimp only
      rw [ite_eq_right (fun h => hi (Finset.mem_singleton.mpr h))]
    · dsimp only
      rw [ind_coset_eq_dagger hX (hpin rfl) L k ind hind v.1 v.2 hT' p, Finset.prod_ite_eq' Finset.univ v.1,
        ite_eq_left (Finset.mem_univ _)]

end WaveTurbulence.Flower.ProtPtw
