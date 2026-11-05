/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerFamilyKernelSum
/-! Convergence after summing every independent lower component, as required for the explicit error series. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_lowerFamily_prod_KG {d w p Natt : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (n : (B : P.parts) → Fin B.1.card → (Fin d → ℤ)) :
    (∑ low : LowerFamily sig top P p Natt, ∏ B : P.parts, KG L γ δ F (low B).low p (n B)) =
      ∏ B : P.parts, lowerKernelSum L γ δ F
        (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt (n B) := by
  have hp := tsum_independent_prod (fun (B : P.parts) (D : LowerGraftData
      (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt) => KG L γ δ F D.low p (n B))
  simpa only [tsum_fintype, lowerKernelSum] using hp

theorem summable_lowerKernelSum_graft_series {d w p Natt : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (hP : TopPartitionIrreducible top P)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    Summable (fun κ : ForestDecoration top d n =>
      (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) *
      ∏ B : P.parts, lowerKernelSum L γ δ F
        (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt
        (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)) := by
  let f := fun (low : LowerFamily sig top P p Natt) (κ : ForestDecoration top d n) =>
    (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) *
      ∏ B : P.parts, KG L γ δ F (low B).low p
        (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)
  have hs : Summable (fun κ => ∑ low : LowerFamily sig top P p Natt, f low κ) :=
    summable_sum (fun low _ =>
      (graftLowerFamily sig top P hP low).summable_KG_graft_series L γ δ F t hpt htp n hF)
  apply hs.congr
  intro κ
  dsimp only [f]
  rw [← mul_sum]
  exact congrArg (fun z : ℂ => (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) * z)
    (sum_lowerFamily_prod_KG L γ δ F sig top P (fun B k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode))

end WaveTurbulence.Induct
