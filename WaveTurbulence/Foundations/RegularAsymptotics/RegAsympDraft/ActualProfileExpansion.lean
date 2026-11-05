/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceProfileExpansion

/-! # Exact resonant-profile expansion of the actual source phase integral -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory TTree Links ClassJR MainCoef Set

/-- One family of source coefficients, chosen before the decoration and
root momentum, expands every actual layer-zero couple phase integral.
No analytic remainder or leading-term identity is assumed. -/
theorem actual_couple_profile_expansion {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) :
    ∃ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (C Z)) ∧
      ∀ (d : ℕ) (L γ δ : ℝ) (LG : LayeredGarden 2),
        (∀ a, LG.layer a = 0) → Q.Decodes LG.garden →
      ∀ k : GNode LG.garden.tree → Mom d, IsDecoration LG.garden k →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ s₁ s₂ : ℝ,
      phaseIntegral L γ δ LG.garden (kDomain LG (fun b => if b.1.1=0 then t else s) s₁) s₂ k =
        ∑ Z : (chosenSet Q.links).powerset,
          (∏ z ∈ Z.val, ((Cancel.zetaA z : ℂ)*Real.pi*Complex.I)⁻¹)*
            ∫ lam, ApproxNT.resProfile (markedLinkIndices Q Z.val)
              (fun Ω => C Z (WithLp.ofLp Ω) lam)
              (fun j => alphaOmega L γ δ LG.garden k (chosenNode Q j))*e2 lam t s := by
  classical
  obtain ⟨G,hG,hF,-⟩ := couple_time_expansion_classified hη hη2 hA Q hwf
  have hrep (Z : (chosenSet Q.links).powerset) :=
    sourceComponent_resProfile_representation (Finset.mem_powerset.mp Z.property)
      (hG Z.val (Finset.mem_powerset.mp Z.property))
  choose C hC hrepC using hrep
  refine ⟨C,hC,?_⟩
  intro d L γ δ LG h0 hQ k hk t ht s hs s₁ s₂
  rw [actual_phaseIntegral_eq_BtJR L γ δ LG h0 hQ hk ht hs s₁ s₂]
  calc
    _ = ∑ Z : (chosenSet Q.links).powerset,
        (∏ z ∈ Z.val, PhiZ Cancel.zetaA z (alphaOmega L γ δ LG.garden k z))*
          G Z.val (alphaOmega L γ δ LG.garden k) t s := by
      rw [hF (alphaOmega L γ δ LG.garden k) t s ht hs]
      exact (Finset.sum_coe_sort _ (fun Z =>
        (∏ z ∈ Z, PhiZ Cancel.zetaA z (alphaOmega L γ δ LG.garden k z))*
          G Z (alphaOmega L γ δ LG.garden k) t s)).symm
    _ = _ := Finset.sum_congr rfl (fun Z _ => hrepC Z _ t s ht hs)

end WaveTurbulence.RegAsymp
