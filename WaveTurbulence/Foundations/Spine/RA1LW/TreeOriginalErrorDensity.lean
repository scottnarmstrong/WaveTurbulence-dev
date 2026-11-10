/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFam
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeOriginalRemainderFamily
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFinitePhysicalErrors

/-! # The literal original tree remainder is one actual original-frequency density -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT MainCoef

/-- The entire original KTstar-app is an actual moving-root inverse-profile mixture,
with the same source SRep family and every original sign and cutoff retained. -/
theorem exists_tree_original_error_density {d : ℕ} (hd : 3 ≤ d) {η Agev : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ Agev)
    {X : RegChain} (hwf : X.wf=true) (LG : LayeredGarden 1) (hX : X.DecodesTree LG.garden)
    (h0 : ∀ a, LG.layer a=0) {L : ℝ} (hL : 1 ≤ L) (δ γ : ℝ) (hδ : δ ≠ 0)
    {H : LGSpine.LeafProfiles 1 d} {B Ccover : ℝ} (hB : 0 ≤ B)
    (hF : ∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length) :
    ∃ C : (Z : (ClassJR.chosenSet ((toJRc X).linksAt (LG.garden.sig 0) (rootT (LG.garden.sig 0)))).powerset) →
      ({j : Fin (X.treeLinks (LG.garden.sig 0)).length //
        j ∉ treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) Agev (CTη η^(2*X.size+1)) (C Z)) ∧
      ∀ t s : ℝ, 0 ≤ s → s<t → t≤1 → ∀ k : Mom d,
      LGSpine.treeLeaves L γ δ LG H t s k - LGSpine.LeafApp.tree δ 0 H X (LG.garden.sig 0) t s k =
        treeRootLeafMixture (treeInputFam LG.garden H) S (fun ts u => pairedInverseProfile
          (fun lam => ∑ Z : (ClassJR.chosenSet ((toJRc X).linksAt (LG.garden.sig 0) (rootT (LG.garden.sig 0)))).powerset,
            (LG.garden.zeta*(∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹))*
              treeNormalizedScalar hX (treePhysicalErrorScalar L δ γ
                (treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val) (C Z)) S lam u) ts) ![t,s] k := by
  classical
  obtain ⟨C,hC,hrem⟩ := exists_tree_original_remainder_family hη hη2 hA X hwf (LG.garden.sig 0)
  refine ⟨C,hC,?_⟩
  intro t s hs hst ht k
  have he := hrem d hd L γ δ hL hδ LG rfl h0 hX B hB H hF S hcover Ccover hS t s hs hst ht k
  rw [he]
  unfold treeRootLeafMixture
  have hsum := tree_finite_physical_errors_eq_profile hd hX hL δ γ
    (fun Z : (ClassJR.chosenSet ((toJRc X).linksAt (LG.garden.sig 0) (rootT (LG.garden.sig 0)))).powerset =>
      treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val) C (fun Z => (hC Z).reg)
      (fun Z => tree_integrable_symbol_of_SRep (by linarith : 0 ≤ 1-η/8) (hC Z))
      (fun Z => LG.garden.zeta*(∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹))
      (treeInputFam LG.garden H) (by omega) (by omega) hB (fun _ => hF _) S hS ![t,s] k
  rw [← hsum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end WaveTurbulence.RA1Leafwise
