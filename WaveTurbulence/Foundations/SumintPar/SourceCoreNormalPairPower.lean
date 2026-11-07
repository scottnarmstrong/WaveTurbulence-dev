/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreNormalMass
public import WaveTurbulence.Foundations.SumintPar.SourceNormalBlockBound
public import WaveTurbulence.Foundations.SumintPar.SourceOrdinaryPairBound

/-!
# Actual normal and ordinary pair coarse-core power bounds

These apply the proved original source mass estimates to the actual
coarse integrals. Constants are chosen before delta and the step count.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- TARGET sumint Step 3: actual untouched normal cores keep the four-input source power bound. -/
theorem exists_source_normal_core_power_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (τstar : ℝ) (hτstar : 0 < τstar)
    (β : ℝ) (hβ : 0 < β) (hβγ : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/16 →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (N : ℕ), τstar = (N:ℝ)*δ →
      ∀ A η : ℝ, D.Admissible A L γ η N → γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c : ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}),
      (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c (L^(-β)) (.inl i.1) z) ≤
      ENNReal.ofReal (C*δ^(-2:ℝ)*L^(4*((d:ℝ)-γ)-(if normalIncoherent D i then β/20 else 0))) := by
  obtain ⟨C,hC,hbound⟩ := exists_source_normal_block_bound d hd γ hγ τstar hτstar β hβ hβγ hhigh
  refine ⟨C,hC,?_⟩
  intro δ hδ hδsmall
  obtain ⟨R,hR,hbound⟩ := hbound δ hδ hδsmall
  refine ⟨R,hR,?_⟩
  intro L hL D N hτ A η hD hγη p ν r hr hrupper t c i
  have hLp : 0 < L := by linarith only [hR,hL]
  exact (lintegral_sourceCore_normal_le D hLp γ δ η p ν r t c (L^(-β)) i).trans
    (hbound L hL D N hτ A η hD hγη p ν r hr hrupper t c i)

/-- TARGET sumint Step 3: actual untouched ordinary pair cores keep their native two-input power bound. -/
theorem exists_source_pair_core_power_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηsmall : η ≤ 1/3)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β)
    (hβγ : β/2 < 2*γ) (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ)
        (a : Σ i : Fin D.S.I, Fin (D.S.m i)),
      ¬ (caseAPair D a ∨ caseCPair D a) →
      (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c (L^(-β)) (.inr (.inl a)) z) ≤
      ENNReal.ofReal (C*δ⁻¹*L^(2*((d:ℝ)-γ)-(if pairIncoherent D a then β/2 else 0))) := by
  obtain ⟨C,hC,hbound⟩ := exists_source_ordinary_pair_bound d hd γ hγ η hη hηsmall τstar hτstar β hβ hβγ hβη
  refine ⟨C,hC,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p ν r t c a ha
  have hLp : 0 < L := by linarith only [hR,hL]
  exact (lintegral_sourceCore_pair_le D hLp γ δ η p ν r t c (L^(-β)) (fun _ => 0) a ha).trans
    (hbound L hL D A hD p ν r t c (fun _ => 0) a (fun h => ha (Or.inl h)) (fun h => ha (Or.inr h)))

end WaveTurbulence.SumintPar
