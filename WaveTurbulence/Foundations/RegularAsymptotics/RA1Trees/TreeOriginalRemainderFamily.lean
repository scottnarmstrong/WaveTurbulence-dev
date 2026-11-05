/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeKernelProfileMixtures
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeadingApp
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePhysicalMixtureSplit
public import WaveTurbulence.Foundations.IncohInst.SourceOrders

/-! # The original KTstar minus literal app is the actual finite physical error family -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT WithLp MainCoef

/-- One original coefficient family, chosen before physical data, gives the EXACT
original kernel minus literal app as the original moving-root physical NT/Wick errors. -/
theorem exists_tree_original_remainder_family {η Agev : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ Agev)
    (X : RegChain) (hwf : X.wf=true) (ζ : ℤˣ) :
    ∃ C : (Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset) →
        ({j : Fin (X.treeLinks ζ).length // j ∉ treeMarkedIndices (treeChosenAddress X ζ) Z.val} → ℝ) →
          ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) Agev (CTη η^(2*X.size+1)) (C Z)) ∧
      ∀ (d : ℕ), 3 ≤ d → ∀ (L γ δ : ℝ), 1 ≤ L → δ ≠ 0 →
      ∀ (LG : LayeredGarden 1) (hζ : LG.garden.sig 0=ζ),
      (∀ a, LG.layer a=0) → ∀ hX : X.DecodesTree LG.garden,
      ∀ B : ℝ, 0 ≤ B → ∀ F : Mom d → ℝ,
      Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B →
      ∀ S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
        Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ),
      (∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
        ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c) →
      ∀ Ccover : ℝ, (∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length) →
      ∀ t s : ℝ, 0 ≤ s → s<t → t≤1 → ∀ k : Mom d,
      KTstar L γ δ (fun _ => F) LG t s k - X.app δ 0 F (LG.garden.sig 0) t s k =
        LG.garden.zeta*∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
          (∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
            ∫ u, rootAmplitudeSum (treeRootLeafAmplitude (fun _ k => (F k:ℂ)) S) k u *
              pairedInverseProfile (fun lam => treeNormalizedScalar hX
                (treePhysicalErrorScalar L δ γ
                  (by cases hζ; exact treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val)
                  (by cases hζ; exact C Z)) S lam u) ![t,s] ∂treeLeafCellMeasure S := by
  classical
  obtain ⟨C,hC,hclass,hkernel⟩ := KTstar_classified_leaf_profile_mixtures hη hη2 hA X hwf ζ
  refine ⟨C,hC,?_⟩
  intro d hd L γ δ hL hδ LG hζ h0 hX B hB F hF S hcover Ccover hS t s hs hst ht k
  cases hζ
  have hθ : 0 ≤ 1-η/8 := by linarith
  have hker := hkernel d (40*d) (40*d) L γ δ LG rfl h0 hX B hB hL
    (by omega) (by omega) F (fun _ => hF) S hcover Ccover hS t s hs hst ht k
  have hinputs : treeInputFunctions LG (fun _ => F) = (fun _ k => (F k:ℂ)) := rfl
  rw [hinputs] at hker
  have hlead := tree_leading_eq_app_of_classified (γ := γ) hd hX (zero_lt_one.trans_le hL) hδ C hθ hC
    hclass hB hF S hcover hS hs hst ht k
  rw [tree_order_eq_twice_links hX] at hker
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*(X.treeLinks (LG.garden.sig 0)).length):ℝ):ℂ)
  have hq : (coupling d L γ δ:ℂ)^(2*(X.treeLinks (LG.garden.sig 0)).length)=q := by
    simp only [q,coupling,Complex.ofReal_pow]
  rw [hq] at hker
  rw [hker,← hlead]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro Z _
  have he := tree_physical_profile_mixture_sub_leading hd hX hL δ γ
    (treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val) (hC Z).reg
    (tree_integrable_symbol_of_SRep hθ (hC Z)) (fun _ k => (F k:ℂ))
    (by omega) (by omega) hB (fun _ => hF) S hS ![t,s] k
  change q*_ - q*_ = _ at he
  calc
    _ = LG.garden.zeta*(∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)*
      (q*(∫ u, rootAmplitudeSum (treeRootLeafAmplitude (fun _ k => (F k:ℂ)) S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX (fun lam β γ' z =>
          treeProfileArrayScalar L (2*δ*L^(2*γ)) treeWickArrayWeight z β γ'
            (treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val) (C Z) lam) S lam u) ![t,s]
          ∂treeLeafCellMeasure S) - q*(∫ u, rootAmplitudeSum
          (treeRootLeafAmplitude (fun _ k => (F k:ℂ)) S) k u * pairedInverseProfile
          (fun lam => treeNormalizedScalar hX (fun lam β γ' z => approxApp L (2*δ) γ
            (treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val)
            (fun Ω => C Z (ofLp Ω) lam) (halfCellAmplitude z β γ')) S lam u) ![t,s]
              ∂treeLeafCellMeasure S)) := by
      dsimp only [q]
      ring
    _ = _ := by rw [he]; ring

end WaveTurbulence.RegAsymp
