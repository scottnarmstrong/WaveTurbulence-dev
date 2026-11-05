/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceBlockProducts

/-! # Scalar factors through two actual source child blocks -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Function

/-- Two disjoint actual child-couple blocks factor in their original
operator order. Both PV limits are derived from the respective original
input norms. The two leaf inputs may differ. -/
theorem addressAppAlong_scalar_two_source_blocks {d w : ℕ} (hd : 3 ≤ d)
    (Q₁ Q₂ : RegCpl) {K M : ℕ} {F₁ F₂ : Mom d → ℂ} {B₁ B₂ : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hF₁ : Fourier.spatialNorm K M F₁ ≤ ENNReal.ofReal B₁)
    (hF₂ : Fourier.spatialNorm K M F₂ ≤ ENNReal.ofReal B₂)
    (Z : Finset (Fin w × TTree.Path)) (a₁ b₁ a₂ b₂ : Fin w × TTree.Path)
    (hab₁ : Indep a₁ b₁) (hab₂ : Indep a₂ b₂) (k₁ k₂ : Mom d)
    (hdisj : List.Disjoint ((Q₁.linksAt a₁ b₁).map Prod.fst) ((Q₂.linksAt a₂ b₂).map Prod.fst))
    (c : ℂ) (θ : Fin w × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z (((Q₁.linksAt a₁ b₁).map Prod.fst)++((Q₂.linksAt a₂ b₂).map Prod.fst))
      (fun θ => (c*cplLeafProduct F₁ θ Q₁ a₁ b₁ k₁)*cplLeafProduct F₂ θ Q₂ a₂ b₂ k₂) θ =
    c*addressAppAlong Z ((Q₁.linksAt a₁ b₁).map Prod.fst)
      (fun θ => cplLeafProduct F₁ θ Q₁ a₁ b₁ k₁) θ *
    addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
      (fun θ => cplLeafProduct F₂ θ Q₂ a₂ b₂ k₂) θ := by
  have hinner : addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
      (fun θ => (c*cplLeafProduct F₁ θ Q₁ a₁ b₁ k₁)*cplLeafProduct F₂ θ Q₂ a₂ b₂ k₂) =
      (fun θ => (c*cplLeafProduct F₁ θ Q₁ a₁ b₁ k₁) *
        addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
          (fun θ => cplLeafProduct F₂ θ Q₂ a₂ b₂ k₂) θ) := by
    funext θ
    apply addressAppAlong_mul_placed_source hd Q₂ hK hM hB₂ hF₂ Z a₂ b₂ hab₂ k₂
    intro z hz θ x y
    have hh := addressAppAlong_cplLeafProduct_update_of_not_mem Z [] F₁ Q₁ a₁ b₁ k₁ hab₁ z
      (fun hz₁ => List.disjoint_left.mp hdisj hz₁ hz) θ (x,y)
    exact congrArg (fun v => c*v) hh
  rw [addressAppAlong_append,hinner]
  have hswap : (fun θ => (c*cplLeafProduct F₁ θ Q₁ a₁ b₁ k₁) *
        addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
          (fun θ => cplLeafProduct F₂ θ Q₂ a₂ b₂ k₂) θ) =
      (fun θ => (c*addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
          (fun θ => cplLeafProduct F₂ θ Q₂ a₂ b₂ k₂) θ) *
        cplLeafProduct F₁ θ Q₁ a₁ b₁ k₁) := by
    funext θ
    ring
  rw [hswap]
  have hout := addressAppAlong_mul_placed_source hd Q₁ hK hM hB₁ hF₁ Z a₁ b₁ hab₁ k₁
    (fun θ => c*addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
      (fun θ => cplLeafProduct F₂ θ Q₂ a₂ b₂ k₂) θ)
    (fun z hz θ x y => congrArg (fun v => c*v)
      (addressAppAlong_cplLeafProduct_update_of_not_mem Z _ F₂ Q₂
        a₂ b₂ k₂ hab₂ z (List.disjoint_left.mp hdisj hz) θ (x,y))) θ
  exact hout.trans (by ring)

end WaveTurbulence.RegAsymp
