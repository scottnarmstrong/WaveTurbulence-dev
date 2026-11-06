/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourcePlacedFactors
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressFreeze

/-! # Products of independent actual source couple blocks -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Function

/-- Two disjoint actual child-couple blocks factor in their original
operator order. Both PV limits are derived from the respective original
input norms. The two leaf inputs may differ. -/
theorem addressAppAlong_two_source_blocks {d w : ℕ} (hd : 3 ≤ d)
    (Q₁ Q₂ : RegCpl) {K M : ℕ} {H₁ H₂ : Fin w × TTree.Path → Mom d → ℝ} {B₁ B₂ : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hF₁ : ∀ z, Fourier.spatialNorm K M (addrFam H₁ z) ≤ ENNReal.ofReal B₁)
    (hF₂ : ∀ z, Fourier.spatialNorm K M (addrFam H₂ z) ≤ ENNReal.ofReal B₂)
    (Z : Finset (Fin w × TTree.Path)) (a₁ b₁ a₂ b₂ : Fin w × TTree.Path)
    (hab₁ : Indep a₁ b₁) (hab₂ : Indep a₂ b₂) (k₁ k₂ : Mom d)
    (hdisj : List.Disjoint ((Q₁.linksAt a₁ b₁).map Prod.fst) ((Q₂.linksAt a₂ b₂).map Prod.fst))
    (θ : Fin w × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z (((Q₁.linksAt a₁ b₁).map Prod.fst)++((Q₂.linksAt a₂ b₂).map Prod.fst))
      (fun θ => cplLeafProduct (addrFam H₁) θ Q₁ a₁ b₁ k₁*cplLeafProduct (addrFam H₂) θ Q₂ a₂ b₂ k₂) θ =
    addressAppAlong Z ((Q₁.linksAt a₁ b₁).map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H₁) θ Q₁ a₁ b₁ k₁) θ *
    addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H₂) θ Q₂ a₂ b₂ k₂) θ := by
  have hinner : addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H₁) θ Q₁ a₁ b₁ k₁*cplLeafProduct (addrFam H₂) θ Q₂ a₂ b₂ k₂) =
      (fun θ => cplLeafProduct (addrFam H₁) θ Q₁ a₁ b₁ k₁ *
        addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
          (fun θ => cplLeafProduct (addrFam H₂) θ Q₂ a₂ b₂ k₂) θ) := by
    funext θ
    apply addressAppAlong_mul_placed_source hd Q₂ hK hM hB₂ hF₂ Z a₂ b₂ hab₂ k₂
    intro z hz θ x y
    exact addressAppAlong_cplLeafProduct_update_of_not_mem Z [] H₁ Q₁ a₁ b₁ k₁ hab₁ z
      (fun hz₁ => List.disjoint_left.mp hdisj hz₁ hz) θ (x,y)
  rw [addressAppAlong_append,hinner]
  have hswap : (fun θ => cplLeafProduct (addrFam H₁) θ Q₁ a₁ b₁ k₁ *
        addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
          (fun θ => cplLeafProduct (addrFam H₂) θ Q₂ a₂ b₂ k₂) θ) =
      (fun θ => addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
          (fun θ => cplLeafProduct (addrFam H₂) θ Q₂ a₂ b₂ k₂) θ *
        cplLeafProduct (addrFam H₁) θ Q₁ a₁ b₁ k₁) := by
    funext θ
    exact mul_comm _ _
  rw [hswap]
  have hout := addressAppAlong_mul_placed_source hd Q₁ hK hM hB₁ hF₁ Z a₁ b₁ hab₁ k₁
    (fun θ => addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H₂) θ Q₂ a₂ b₂ k₂) θ)
    (fun z hz θ x y => addressAppAlong_cplLeafProduct_update_of_not_mem Z _ H₂ Q₂
      a₂ b₂ k₂ hab₂ z (List.disjoint_left.mp hdisj hz) θ (x,y)) θ
  exact hout.trans (mul_comm _ _)

end WaveTurbulence.RA1Leafwise
