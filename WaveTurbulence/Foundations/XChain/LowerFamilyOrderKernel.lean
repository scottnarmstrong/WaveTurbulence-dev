/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerOrderKernelSum
public import WaveTurbulence.Foundations.XChain.GardenGraftOrder
/-! The full graft kernel sum can be grouped by actual attached orders with arbitrary total-order weights. -/
public section
namespace WaveTurbulence.Induct
open Finset SysAPI

theorem sum_KG_graftLowerFamily_by_order {d w p Natt : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (hP : TopPartitionIrreducible top P)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) (W : ℕ → ℂ) :
    (∑ low : LowerFamily sig top P p Natt,
      W (graftLowerFamily sig top P hP low).graft.garden.order *
        KG L γ δ F (graftLowerFamily sig top P hP low).graft t n) =
      (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))) *
      ∑' κ : ForestDecoration top d n,
        (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) *
          ∑ orders : P.parts → Fin (Natt + 1),
            W ((∑ j, (top j).order) + ∑ B, (orders B).1) *
              ∏ B : P.parts, lowerOrderKernelSum L γ δ F
                (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt (orders B)
                (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) := by
  classical
  let A : ℂ := ∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))
  let c := fun κ : ForestDecoration top d n => ∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j
  let u := fun low : LowerFamily sig top P p Natt => (graftLowerFamily sig top P hP low).graft.garden.order
  let f := fun (low : LowerFamily sig top P p Natt) (κ : ForestDecoration top d n) =>
    c κ * (W (u low) * ∏ B : P.parts, KG L γ δ F (low B).low p
      (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode))
  have ho (low : LowerFamily sig top P p Natt) :
      u low = (∑ j, (top j).order) + ∑ B : P.parts, (low B).low.garden.order :=
    gardenGraft_order sig top P (fun B => (low B).low.garden)
      (fun B => (low B).plain) (fun B k => congrFun (low B).sign k)
  have hs (low : LowerFamily sig top P p Natt) : Summable (f low) := by
    have h := ((graftLowerFamily sig top P hP low).summable_KG_graft_series L γ δ F t hpt htp n hF).mul_left (W (u low))
    exact h.congr (fun κ => by
      change W (u low) * (c κ * ∏ B : P.parts, KG L γ δ F (low B).low p
        (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)) = f low κ
      dsimp [f]
      ring)
  have he : (∑ low : LowerFamily sig top P p Natt, W (u low) *
      KG L γ δ F (graftLowerFamily sig top P hP low).graft t n) = A * ∑ low, ∑' κ, f low κ := by
    rw [mul_sum]
    apply sum_congr rfl
    intro low _
    rw [(graftLowerFamily sig top P hP low).KG_graft L γ δ F t hpt htp n hF]
    change W (u low) * (A * ∑' κ : ForestDecoration top d n,
      c κ * ∏ B : P.parts, KG L γ δ F (low B).low p
        (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)) = A * ∑' κ, f low κ
    rw [← mul_assoc, mul_comm (W (u low)) A, mul_assoc, ← tsum_mul_left]
    apply congrArg (fun z : ℂ => A * z)
    apply tsum_congr
    intro κ
    dsimp [f]
    ring
  refine he.trans (congrArg (fun z : ℂ => A * z) ?_)
  rw [← Summable.tsum_finsetSum (fun low _ => hs low)]
  apply tsum_congr
  intro κ
  change (∑ low : LowerFamily sig top P p Natt, c κ * (W (u low) *
    ∏ B : P.parts, KG L γ δ F (low B).low p
      (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode))) = _
  rw [← mul_sum]
  apply congrArg (fun z : ℂ => c κ * z)
  simp_rw [ho]
  exact sum_lowerFamily_by_orders L γ δ F sig top P κ
    (fun orders => W ((∑ j, (top j).order) + ∑ B, (orders B).1))

end WaveTurbulence.Induct
