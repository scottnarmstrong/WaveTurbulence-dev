/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceComponentProfile
public import WaveTurbulence.Foundations.RegAsymp.FiniteVariableIntegral

/-! # One actual couple NT coefficient family with its classified leading integrals -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory TTree Links ClassJR MainCoef WithLp

/-- The SAME selected J3 coefficients expand the original couple phase
and have the exact signed JB leading integrals. The family is fixed
before all physical scales, decorations, root momenta and order cutoffs. -/
theorem couple_profiles_with_classified_leading {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) :
    ∃ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (C Z)) ∧
      (∀ α t s, t ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
        BtJR Q (0,[]) (1,[]) α t s =
          ∑ Z : (chosenSet Q.links).powerset,
            (∏ z ∈ Z.val, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹)*
              ∫ lam, ApproxNT.resProfile (markedLinkIndices Q Z.val)
                (fun Ω => C Z (ofLp Ω) lam) (fun j => α (chosenNode Q j))*e2 lam t s) ∧
      ∀ Z : (chosenSet Q.links).powerset,
        ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1,
          (∫ β, ∫ lam, C Z β lam*e2 lam t s) =
            if Q.dominant = true ∧ IsSpecialSet Q.links Z.val then
              (-1:ℂ)^Z.val.card*(Q.JB 0 t s:ℂ) else 0 := by
  classical
  obtain ⟨G,hG,hBt,hlim⟩ := couple_time_expansion_classified hη hη2 hA Q hwf
  have hRep (Z : (chosenSet Q.links).powerset) :=
    sourceCoefficient_on_unmarkedLinks (hG Z.val (Finset.mem_powerset.mp Z.property))
  choose C hC hrep using hRep
  refine ⟨C,hC,?_,?_⟩
  · intro α t s ht hs
    rw [hBt α t s ht hs]
    calc
      _ = ∑ Z : (chosenSet Q.links).powerset,
          (∏ z ∈ Z.val, PhiZ Cancel.zetaA z (α z))*G Z.val α t s :=
        (Finset.sum_coe_sort _ _).symm
      _ = _ := Finset.sum_congr rfl (fun Z _ =>
        sourceComponent_resProfile_of_representation (Finset.mem_powerset.mp Z.property)
          (G Z.val) (C Z) (hrep Z) α t s ht hs)
  · intro Z t ht s hs
    have hm := hlim Z.val (Finset.mem_powerset.mp Z.property) t ht s hs (0 : Cancel.Addr → ℝ)
    let f := fun j : {j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} => chosenNode Q j
    have hf : Function.Injective f := (chosenNode_injective Q).comp Subtype.val_injective
    have hr : Set.range f = ↑(chosenSet Q.links \ Z.val) := range_unmarked_chosenNode Q Z.val
    have hfun : (fun α => G Z.val α t s) = fun α => ∫ lam, C Z (α ∘ f) lam*e2 lam t s := by
      funext α
      exact hrep Z α t s ht hs
    rw [hfun] at hm
    rw [mint_comp_eq_integral (chosenSet Q.links \ Z.val) f hf hr
      (fun β => ∫ lam, C Z β lam*e2 lam t s) 0] at hm
    exact hm

end WaveTurbulence.RA1Leafwise
