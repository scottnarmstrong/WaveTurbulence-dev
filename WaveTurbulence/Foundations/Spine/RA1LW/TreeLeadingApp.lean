/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFam
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeLeadingSum
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeLeadingNormalizedProfile
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceGardenSign
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalLeadingFactor

/-! # The actual classified leading tree profiles equal the literal original app -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT WithLp MainCoef

/-- An actual decoded tree has precisely the garden phase in the original tree app. -/
theorem tree_decoded_garden_zeta {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    G.zeta=zetaOfTrees ![G.sig 0] ![X.plug (G.sig 0) .leaf] := by
  have hs : G.sig=![G.sig 0] := by funext j; fin_cases j; rfl
  have ht : G.tree=![X.plug (G.sig 0) .leaf] := by funext j; fin_cases j; exact hX.1
  rw [garden_zeta_eq_zetaOfTrees,ht,hs]
  simp only [Matrix.cons_val_zero]

/-- Conditional same-family assembly: the classified original coefficient integrals
and proved source singular identity give literal app, at both signs and every order. -/
theorem tree_leading_eq_app_of_classified {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {L δ γ : ℝ} (hL : 0 < L) (hδ : δ ≠ 0)
    (C : (Z : (ClassJR.chosenSet ((toJRc X).linksAt (G.sig 0) (rootT (G.sig 0)))).powerset) →
      ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ treeMarkedIndices (treeChosenAddress X (G.sig 0)) Z.val} → ℝ) →
        ℝ × ℝ → ℂ)
    {θ a b Agev N : ℝ} (hθ : 0 ≤ θ) (hC : ∀ Z, SRep θ a b Agev N (C Z))
    (hclass : ∀ Z, ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      (∫ β, ∫ lam, C Z β lam*e2 lam t s) =
        if X.dominant=true ∧ IsSpecialSet (X.linksAt (G.sig 0) (rootT (G.sig 0))) Z.val then
          (-1:ℂ)^Z.val.card*(X.JBtree 0 t s:ℂ) else 0)
    {H : LGSpine.LeafProfiles 1 d} {B Ccover : ℝ} (hB : 0 ≤ B)
    (hF : ∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) (k : Mom d) :
    G.zeta*∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt (G.sig 0) (rootT (G.sig 0)))).powerset,
      (∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
        (((δ/(2*L^((d:ℝ)-γ)))^(2*(X.treeLinks (G.sig 0)).length):ℝ):ℂ)*
          (∫ u, rootAmplitudeSum (treeRootLeafAmplitude (treeInputFam G H) S) k u *
            pairedInverseProfile (fun lam => treeNormalizedScalar hX
              (fun lam β γ' z => approxApp L (2*δ) γ
                (treeMarkedIndices (treeChosenAddress X (G.sig 0)) Z.val)
                (fun Ω => C Z (ofLp Ω) lam) (halfCellAmplitude z β γ')) S lam u) ![t,s]
                  ∂treeLeafCellMeasure S) = LGSpine.LeafApp.tree δ 0 H X (G.sig 0) t s k := by
  classical
  let n := (X.treeLinks (G.sig 0)).length
  have hsize : X.size=2*n := by
    have hh := chain_linksAt_length X (G.sig 0) ((0:Fin 1),[])
    change n*2=X.size at hh
    omega
  have hhalf : X.size/2=n := by omega
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)
  let scale : ℂ := ((L^(2*(d:ℝ)-2*γ)*(2*δ)⁻¹:ℝ):ℂ)^n
  have hnrm : q*scale=(((δ/8)^n:ℝ):ℂ) := by
    simpa only [q,scale,Complex.ofReal_mul,Complex.ofReal_pow] using
      congrArg Complex.ofReal (physical_leading_normalization n d hL hδ)
  simp_rw [tree_leading_profile_mixture_eq hX L (2*δ) γ _ (tree_integrable_symbol_of_SRep hθ (hC _)),
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,hclass _ t s hs hst ht]
  calc
    _ = (q*scale)*G.zeta*∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt (G.sig 0) (rootT (G.sig 0)))).powerset,
        (∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
          (if X.dominant=true ∧ IsSpecialSet (X.linksAt (G.sig 0) (rootT (G.sig 0))) Z.val then
            (-1:ℂ)^Z.val.card*(X.JBtree 0 t s:ℂ) else 0)*
          treeLeadingSpatialProfile hX (treeMarkedIndices (treeChosenAddress X (G.sig 0)) Z.val)
            (treeInputFam G H) S k := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Z _
      dsimp only [q,scale,n]
      ring
    _ = _ := by
      rw [tree_classified_leading_sum_eq hd hX hB hF S hcover hS t s k,hnrm,
        LGSpine.LeafApp.tree,← tree_decoded_garden_zeta hX]
      by_cases hdom : X.dominant=true
      · simp only [hdom,ite_true]
        rw [hhalf,hsize]
        rw [← physical_leading_app_prefactor n δ]
        ring
      · simp [hdom]

end WaveTurbulence.RA1Leafwise
