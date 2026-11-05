/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCoefficientSubsets
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeadingSpatialIdentification

/-! # The entire classified leading tree sum has the exact original special weights -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ApproxNT Finset Reg MainCoef

/-- The complete classified leading sum is exactly the original special-set sum,
with the spatial factor2^n and the corrected F61 sign, both signs and all orders. -/
theorem tree_classified_leading_sum_eq {d : ℕ} {G : Garden 1} {X : RegChain}
    (hd : 3 ≤ d) (hX : X.DecodesTree G) {F : Mom d → ℝ} {B C : ℝ} (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length) (t s : ℝ) (k : Mom d) :
    (∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt (G.sig 0) (rootT (G.sig 0)))).powerset,
      (∏ z ∈ Z.val, ((ClassJR.nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
        (if X.dominant=true ∧ IsSpecialSet (X.linksAt (G.sig 0) (rootT (G.sig 0))) Z.val then
          (-1:ℂ)^Z.val.card*(X.JBtree 0 t s:ℂ) else 0)*
        treeLeadingSpatialProfile hX (treeMarkedIndices (treeChosenAddress X (G.sig 0)) Z.val)
          (fun _ k => (F k:ℂ)) S k) =
      if X.dominant=true then (2:ℂ)^(X.treeLinks (G.sig 0)).length*
        ∑ Z ∈ specialSets (X.treeLinks (G.sig 0)),
          specialWeight ![G.sig 0] Z*(X.JBtree 0 t s:ℂ)*
            (X.Nstar F Z (G.sig 0) ((0:Fin 1),[]) k:ℂ) else 0 := by
  classical
  by_cases hdom : X.dominant=true
  · rw [ite_eq_left hdom,← (treeCoefficientSubsetEquiv X (G.sig 0)).sum_comp]
    have hterm (Z : (WaveTurbulence.chosenSet (X.treeLinks (G.sig 0))).powerset) :
        (∏ z ∈ (treeCoefficientSubsetEquiv X (G.sig 0) Z).val,
          ((ClassJR.nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
          (if X.dominant=true ∧ IsSpecialSet (X.linksAt (G.sig 0) (rootT (G.sig 0)))
              (treeCoefficientSubsetEquiv X (G.sig 0) Z).val then
            (-1:ℂ)^(treeCoefficientSubsetEquiv X (G.sig 0) Z).val.card*(X.JBtree 0 t s:ℂ) else 0)*
          treeLeadingSpatialProfile hX (treeMarkedIndices (treeChosenAddress X (G.sig 0))
            (treeCoefficientSubsetEquiv X (G.sig 0) Z).val) (fun _ k => (F k:ℂ)) S k =
        (2:ℂ)^(X.treeLinks (G.sig 0)).length*
          (if IsSpecialSet (X.treeLinks (G.sig 0)) Z.val then
            specialWeight ![G.sig 0] Z.val*(X.JBtree 0 t s:ℂ)*
              (X.Nstar F Z.val (G.sig 0) ((0:Fin 1),[]) k:ℂ) else 0) := by
      change (∏ z ∈ Z.val.image (treeCoefficientAddress (G.sig 0)), _)*
        (if X.dominant=true ∧ IsSpecialSet (X.linksAt (G.sig 0) (rootT (G.sig 0)))
          (Z.val.image (treeCoefficientAddress (G.sig 0))) then
            (-1:ℂ)^(Z.val.image (treeCoefficientAddress (G.sig 0))).card*(X.JBtree 0 t s:ℂ) else 0)*
        treeLeadingSpatialProfile hX (treeMarkedIndices (treeChosenAddress X (G.sig 0))
          (Z.val.image (treeCoefficientAddress (G.sig 0)))) (fun _ k => (F k:ℂ)) S k = _
      simp only [tree_isSpecialSet_coefficient_image,treeMarkedIndices_coefficient_image]
      simp only [hdom,true_and]
      by_cases hsp : IsSpecialSet (X.treeLinks (G.sig 0)) Z.val
      · rw [ite_eq_left hsp,ite_eq_left hsp,
          treeLeadingSpatialProfile_eq_Nstar hd hX hdom hB hF Z.val hsp S hcover hS k]
        calc
          _ = (2:ℂ)^(X.treeLinks (G.sig 0)).length*
            (((∏ z ∈ Z.val.image (treeCoefficientAddress (G.sig 0)),
              ((ClassJR.nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
              (-1:ℂ)^(Z.val.image (treeCoefficientAddress (G.sig 0))).card)*
                (X.JBtree 0 t s:ℂ)*(X.Nstar F Z.val (G.sig 0) ((0:Fin 1),[]) k:ℂ)) := by ring
          _ = _ := by rw [tree_coefficient_signed_weight_eq]
      · simp only [hsp,ite_false,mul_zero,zero_mul]
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    congr 1
    simpa only [specialSets,Finset.sum_filter] using
      (Finset.sum_coe_sort (WaveTurbulence.chosenSet (X.treeLinks (G.sig 0))).powerset
        (fun Z : Finset (Fin 1 × TTree.Path) => if IsSpecialSet (X.treeLinks (G.sig 0)) Z then
          specialWeight ![G.sig 0] Z*(X.JBtree 0 t s:ℂ)*
            (X.Nstar F Z (G.sig 0) ((0:Fin 1),[]) k:ℂ) else 0))
  · simp [hdom]

end WaveTurbulence.RegAsymp
