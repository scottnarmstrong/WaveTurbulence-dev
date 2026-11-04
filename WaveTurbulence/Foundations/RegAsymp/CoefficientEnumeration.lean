/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.MCSum

/-! # Transport the actual J3 coefficient representation to prescribed variables

The change of variables is a permutation, hence preserves every source
coefficient bound without dimension-dependent losses.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR

/-- An MCRep may be expressed on any specified finite enumeration of its
active addresses. The source equality and all SRep bounds are retained. -/
theorem mcRep_on_enumeration {V κ : Type} [DecidableEq V] [Fintype κ]
    {θ a b A N : ℝ} {S : Set V} {F : (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : MCRep θ a b A N S F) (g : κ → V) (hg : Function.Injective g)
    (hrg : Set.range g = S) :
    ∃ C : (κ → ℝ) → ℝ × ℝ → ℂ, SRep θ a b A N C ∧
      ∀ α t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
        F α t s = ∫ lam, C (α ∘ g) lam*e2 lam t s := by
  rcases hF with ⟨ι,hι,f,C,hf,hrf,hN,hC,hmain,hper,hrep⟩
  let := hι
  let e : ι ≃ κ := (Equiv.ofInjective f hf).trans
    ((Set.equivOfEq (hrf.trans hrg.symm)).trans (Equiv.ofInjective g hg).symm)
  have he (i : ι) : g (e i) = f i := by
    have hh := (Equiv.ofInjective g hg).apply_symm_apply
      ((Set.equivOfEq (hrf.trans hrg.symm)) ((Equiv.ofInjective f hf) i))
    exact congrArg Subtype.val hh
  refine ⟨fun β lam => C (fun i => β (e i)) lam,
    (show SRep θ a b A N C from ⟨hN,hC,hmain,hper⟩).reindex e,?_⟩
  intro α t s ht hs
  rw [hrep α t s ht hs]
  apply integral_congr_ae
  exact ae_of_all _ (fun lam => by simp only [Function.comp_apply,he]; rfl)

end WaveTurbulence.RegAsymp
