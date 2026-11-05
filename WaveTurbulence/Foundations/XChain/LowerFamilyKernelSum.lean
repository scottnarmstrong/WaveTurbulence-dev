/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftExpansionFinite
public import WaveTurbulence.Foundations.XChain.CanonicalGraftSeriesSummability
public import WaveTurbulence.Foundations.XChain.LowerKernelSum
/-! Finite independent lower-garden sums factor into the exact input-kernel sum for each leaf block. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI

abbrev LowerFamily {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (p Natt : ℕ) :=
  (B : P.parts) → LowerGraftData
    (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt

noncomputable def graftLowerFamily {w p Natt : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (hP : TopPartitionIrreducible top P)
    (low : LowerFamily sig top P p Natt) : CanonicalGraftData sig p where
  top := top
  partition := P
  low B := (low B).low
  plain B := (low B).plain
  sign B k := congrFun (low B).sign k
  irreducible := hP
  component B := (low B).component

theorem sum_KG_graftLowerFamily {d w p Natt : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (hP : TopPartitionIrreducible top P)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    (∑ low : LowerFamily sig top P p Natt, KG L γ δ F (graftLowerFamily sig top P hP low).graft t n) =
      (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))) *
      ∑' κ : ForestDecoration top d n, (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) *
        ∏ B : P.parts, lowerKernelSum L γ δ F
          (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt
          (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) := by
  let A : ℂ := ∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))
  let c := fun κ : ForestDecoration top d n => ∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j
  let f := fun (low : LowerFamily sig top P p Natt) (κ : ForestDecoration top d n) =>
    c κ * ∏ B : P.parts, KG L γ δ F (low B).low p
      (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)
  have hs (low : LowerFamily sig top P p Natt) : Summable (f low) :=
    (graftLowerFamily sig top P hP low).summable_KG_graft_series L γ δ F t hpt htp n hF
  have he : (∑ low : LowerFamily sig top P p Natt,
      KG L γ δ F (graftLowerFamily sig top P hP low).graft t n) = A * ∑ low, ∑' κ, f low κ := by
    rw [mul_sum]
    exact sum_congr rfl (fun low _ => (graftLowerFamily sig top P hP low).KG_graft L γ δ F t hpt htp n hF)
  refine he.trans (congrArg (fun z : ℂ => A * z) ?_)
  rw [← Summable.tsum_finsetSum (fun low _ => hs low)]
  apply tsum_congr
  intro κ
  change (∑ low : LowerFamily sig top P p Natt, c κ * ∏ B : P.parts,
    KG L γ δ F (low B).low p (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)) = _
  rw [← mul_sum]
  apply congrArg (fun z : ℂ => c κ * z)
  have hp := tsum_independent_prod (fun (B : P.parts) (D : LowerGraftData
      (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt) =>
    KG L γ δ F D.low p (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode))
  simpa only [tsum_fintype, lowerKernelSum] using hp

end WaveTurbulence.Induct
