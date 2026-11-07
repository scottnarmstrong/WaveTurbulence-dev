/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.MixCounted
public import WaveTurbulence.Foundations.SumintPar.SourceRestrictionRecombination

/-! # From the uniform kernel bound to the multiplied restriction norm (DEGEN-VINE)

The analogue of `SumintPar.XNorm00Restr_source_of_kernel_bound` for the multiplied expression `exprMix`:
the same hypothesis (a bound uniform in the input modulation `ν`), the same conclusion with the factor
`mass` of the mixture.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVinePar
open WaveTurbulence.DegenVine
open WaveTurbulence.SumintPar MeasureTheory Set
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

theorem XNorm00Restr_mix_of_kernel_bound (hd : 1 ≤ d) (M : CharMix D.S d)
    (hI : 0 < D.S.I) {A L γ δ η : ℝ} {N : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hη : η ≤ 1/3) (hD : D.Admissible A L γ η N) {h θ : ℝ}
    (hh : h ∈ Ioc (0:ℝ) 1) (hθ : θ ∈ Icc (0:ℝ) 1)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hkernel : ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (c : ℝ),
      XNorm00 θ (fun z (v : sourceOutputSet D L γ η) => kernelExtension D hI c h
        (weightedCutoffInput D L γ δ η p ν (v.1 0-v.1 1)) z) ≤ B) :
    XNorm00Restr θ (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
      (fun t v => exprMix M hI L γ δ η t v) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M)*
        (ENNReal.ofReal M.mass *
        (ENNReal.ofReal (2^θ)*ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^θ)*
          (ENNReal.ofReal (4^θ)*
            (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*h⁻¹*h⁻¹)*B)))) := by
  classical
  let : Fintype (sourceOutputSet D L γ η) := (finite_sourceOutputSet D hL γ η).fintype
  obtain ⟨p,hp⟩ := exists_mixCounted_agreement (δ := δ) hd M hI N hh.1 hA hL hη hD
  let F := fun t (v : sourceOutputSet D L γ η) => mixCounted M hI N h L γ δ η hD p v.1 t
  have hrestrict : XNorm00Restr θ (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
      (fun t v => exprMix M hI L γ δ η t v) ≤ XNorm00 θ F := by
    apply XNorm00Restr_le_family_extension θ _ _ _ (fun _ h => h) _ F
    intro t ht v hv
    exact hp v (fun j => (hv.1 j).2) t (sourceOutputTimeSet_subset_cube D hD ht)
  apply hrestrict.trans
  apply XNorm00_mixCounted_le hd M hI N h hA hL hη hD p
    (fun v : sourceOutputSet D L γ η => v.1) (fun v j => (v.2.1 j).2) θ
  intro q ν
  exact XNorm00_weightedSourceExtension_le D hI N hh hθ L γ δ η q ν
    (fun v : sourceOutputSet D L γ η => v.1 0-v.1 1) B hB (fun j => hkernel q ν ((j:ℝ)*h))

end WaveTurbulence.DegenVinePar
