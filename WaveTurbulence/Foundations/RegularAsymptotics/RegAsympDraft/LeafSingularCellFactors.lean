/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafMaskedSingularMass
public import WaveTurbulence.Foundations.RegAsymp.CountableCellSingularRepresentation

/-! # Actual ordinary-cell factors for the global source Fourier representation -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Incoh Finset

variable {d n m : ℕ}

/-- The literal product of ordinary physical cell factors. -/
def leafSingularCellFn
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (i : LeafSingularCellIndex S) (τ : (Fin n → Mom d) × (Fin n → Mom d))
    (x y : Fin n → Mom d) : ℂ :=
  ∏ j, cellFn (NTSP.intVec (i.2.2.val j).1) (NTSP.intVec (i.2.2.val j).2)
    (τ.1 j) (τ.2 j) (x j) (y j)

/-- The same literal cell factors after all singular integrations. -/
def leafSingularCellOp (J : Finset (Fin n))
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (i : LeafSingularCellIndex S) (τ : (Fin n → Mom d) × (Fin n → Mom d)) : ℂ :=
  ∏ j, cellOp J j (NTSP.intVec (i.2.2.val j).1) (NTSP.intVec (i.2.2.val j).2) (τ.1 j) (τ.2 j)

theorem norm_leafSingularCellFn_le_one
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (i : LeafSingularCellIndex S) (τ : (Fin n → Mom d) × (Fin n → Mom d))
    (x y : Fin n → Mom d) : ‖leafSingularCellFn S i τ x y‖ ≤ 1 := by
  rw [leafSingularCellFn,norm_prod]
  exact prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_cellFn_le _ _ _ _ _ _)

theorem stronglyMeasurable_leafSingularCellFn
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (i : LeafSingularCellIndex S) (x y : Fin n → Mom d) :
    StronglyMeasurable (fun τ => leafSingularCellFn S i τ x y) := by
  unfold leafSingularCellFn
  apply Finset.stronglyMeasurable_fun_prod
  intro j _
  have hm : Measurable (fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
      (((τ.1 j),(τ.2 j)),((x j),(y j)))) :=
    (((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)).prodMk measurable_const
  have hc : StronglyMeasurable (fun z : (Mom d × Mom d) × (Mom d × Mom d) =>
      cellFn (NTSP.intVec (i.2.2.val j).1) (NTSP.intVec (i.2.2.val j).2) z.1.1 z.1.2 z.2.1 z.2.2) :=
    (continuous_cellFn_all _ _).stronglyMeasurable
  exact hc.comp_measurable (g := fun τ : (Fin n → Mom d) × (Fin n → Mom d) =>
    (((τ.1 j),(τ.2 j)),((x j),(y j)))) hm

/-- The full countable Fourier-cell kernel with the literal root mask. -/
def leafSingularCellKernel {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d) (x y : Fin Q.links.length → Mom d) : ℂ :=
  ∑' i : LeafSingularCellIndex S, ∫ uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)),
    leafMaskedSingularCoefficient hQ hG F S k i uv * leafSingularCellFn S i uv.2 x y

/-- The literal globally summable cell kernel has the actual generic
singular representation; no singular convergence premise is introduced. -/
theorem singInt_leafSingularCellKernel_eq {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    {F : Mom d → ℂ} {B C : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^Q.links.length) (J : Finset (Fin Q.links.length)) (k : Mom d) :
    singInt J (leafSingularCellKernel hQ hG F S k) =
      ∑' i : LeafSingularCellIndex S, ∫ uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
          ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)),
        leafMaskedSingularCoefficient hQ hG F S k i uv * leafSingularCellOp J S i uv.2 := by
  have := isFiniteMeasureOnCompacts_pairs (n := Q.links.length) (d := d)
  exact singInt_countableCellMixture
    (I := LeafSingularCellIndex S)
    (U := (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) volume hd J
    (fun i j => NTSP.intVec (i.2.2.val j).1) (fun i j => NTSP.intVec (i.2.2.val j).2)
    (fun _ uv => uv.2.1) (fun _ uv => uv.2.2)
    (fun _ => measurable_snd.fst) (fun _ => measurable_snd.snd)
    (leafMaskedSingularCoefficient hQ hG F S k)
    (stronglyMeasurable_leafMaskedSingularCoefficient hQ hG (by omega) hB hF S k)
    (integrable_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S k)
    (summable_integral_norm_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S hS k)

end WaveTurbulence.RegAsymp
