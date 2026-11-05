/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceBlockProducts

/-! # Three independent source child blocks in the original integration order -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Function

/-- Three disjoint actual source blocks factor without changing their
singular integration order. This is the child-block calculation used at
a type1 source node; all PV convergence follows from the input norm. -/
theorem addressAppAlong_three_source_blocks {d w : ℕ} (hd : 3 ≤ d)
    (Q₁ Q₂ Q₃ : RegCpl) {K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (Z : Finset (Fin w × TTree.Path)) (a₁ b₁ a₂ b₂ a₃ b₃ : Fin w × TTree.Path)
    (hab₁ : Indep a₁ b₁) (hab₂ : Indep a₂ b₂) (hab₃ : Indep a₃ b₃) (k₁ k₂ k₃ : Mom d)
    (h₁₂ : List.Disjoint ((Q₁.linksAt a₁ b₁).map Prod.fst) ((Q₂.linksAt a₂ b₂).map Prod.fst))
    (h₁₃ : List.Disjoint ((Q₁.linksAt a₁ b₁).map Prod.fst) ((Q₃.linksAt a₃ b₃).map Prod.fst))
    (h₂₃ : List.Disjoint ((Q₂.linksAt a₂ b₂).map Prod.fst) ((Q₃.linksAt a₃ b₃).map Prod.fst))
    (θ : Fin w × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z (((Q₁.linksAt a₁ b₁).map Prod.fst)++
      ((Q₂.linksAt a₂ b₂).map Prod.fst)++((Q₃.linksAt a₃ b₃).map Prod.fst))
      (fun θ => cplLeafProduct F θ Q₁ a₁ b₁ k₁*cplLeafProduct F θ Q₂ a₂ b₂ k₂*
        cplLeafProduct F θ Q₃ a₃ b₃ k₃) θ =
    addressAppAlong Z ((Q₁.linksAt a₁ b₁).map Prod.fst)
      (fun θ => cplLeafProduct F θ Q₁ a₁ b₁ k₁) θ *
    addressAppAlong Z ((Q₂.linksAt a₂ b₂).map Prod.fst)
      (fun θ => cplLeafProduct F θ Q₂ a₂ b₂ k₂) θ *
    addressAppAlong Z ((Q₃.linksAt a₃ b₃).map Prod.fst)
      (fun θ => cplLeafProduct F θ Q₃ a₃ b₃ k₃) θ := by
  let L₁ := (Q₁.linksAt a₁ b₁).map Prod.fst
  let L₂ := (Q₂.linksAt a₂ b₂).map Prod.fst
  let L₃ := (Q₃.linksAt a₃ b₃).map Prod.fst
  let H₁ := fun θ => cplLeafProduct F θ Q₁ a₁ b₁ k₁
  let H₂ := fun θ => cplLeafProduct F θ Q₂ a₂ b₂ k₂
  let H₃ := fun θ => cplLeafProduct F θ Q₃ a₃ b₃ k₃
  let R₂ := addressAppAlong Z L₂ H₂
  let R₃ := addressAppAlong Z L₃ H₃
  have hc₁ (L : List (Fin w × TTree.Path)) (z) (hz : z ∉ L₁) (θ) (x y : Mom d) :
      addressAppAlong Z L H₁ (update θ z (x,y)) = addressAppAlong Z L H₁ θ :=
    addressAppAlong_cplLeafProduct_update_of_not_mem Z L F Q₁ a₁ b₁ k₁ hab₁ z hz θ (x,y)
  have hc₂ (L : List (Fin w × TTree.Path)) (z) (hz : z ∉ L₂) (θ) (x y : Mom d) :
      addressAppAlong Z L H₂ (update θ z (x,y)) = addressAppAlong Z L H₂ θ :=
    addressAppAlong_cplLeafProduct_update_of_not_mem Z L F Q₂ a₂ b₂ k₂ hab₂ z hz θ (x,y)
  have hc₃ (L : List (Fin w × TTree.Path)) (z) (hz : z ∉ L₃) (θ) (x y : Mom d) :
      addressAppAlong Z L H₃ (update θ z (x,y)) = addressAppAlong Z L H₃ θ :=
    addressAppAlong_cplLeafProduct_update_of_not_mem Z L F Q₃ a₃ b₃ k₃ hab₃ z hz θ (x,y)
  have hi₃ : addressAppAlong Z L₃ (fun θ => H₁ θ*H₂ θ*H₃ θ) =
      (fun θ => H₁ θ*H₂ θ*R₃ θ) := by
    funext θ
    apply addressAppAlong_mul_placed_source hd Q₃ hK hM hB hF Z a₃ b₃ hab₃ k₃
    intro z hz θ x y
    have he₁ := hc₁ [] z (fun h => List.disjoint_left.mp h₁₃ h hz) θ x y
    have he₂ := hc₂ [] z (fun h => List.disjoint_left.mp h₂₃ h hz) θ x y
    change H₁ (update θ z (x,y))*H₂ (update θ z (x,y)) = H₁ θ*H₂ θ
    rw [show H₁ (update θ z (x,y)) = H₁ θ from he₁,
      show H₂ (update θ z (x,y)) = H₂ θ from he₂]
  have hi₂ : addressAppAlong Z L₂ (fun θ => H₁ θ*H₂ θ*R₃ θ) =
      (fun θ => (H₁ θ*R₃ θ)*R₂ θ) := by
    have hs : (fun θ => H₁ θ*H₂ θ*R₃ θ) = (fun θ => (H₁ θ*R₃ θ)*H₂ θ) := by
      funext θ
      ring
    rw [hs]
    funext θ
    apply addressAppAlong_mul_placed_source hd Q₂ hK hM hB hF Z a₂ b₂ hab₂ k₂
    intro z hz θ x y
    have he₁ := hc₁ [] z (fun h => List.disjoint_left.mp h₁₂ h hz) θ x y
    have he₃ := hc₃ L₃ z (List.disjoint_left.mp h₂₃ hz) θ x y
    change H₁ (update θ z (x,y))*R₃ (update θ z (x,y)) = H₁ θ*R₃ θ
    rw [show H₁ (update θ z (x,y)) = H₁ θ from he₁,
      show R₃ (update θ z (x,y)) = R₃ θ from he₃]
  change addressAppAlong Z (L₁++L₂++L₃) (fun θ => H₁ θ*H₂ θ*H₃ θ) θ =
    addressAppAlong Z L₁ H₁ θ*R₂ θ*R₃ θ
  rw [addressAppAlong_append,addressAppAlong_append,hi₃,hi₂]
  have hs : (fun θ => H₁ θ*R₃ θ*R₂ θ) = (fun θ => (R₂ θ*R₃ θ)*H₁ θ) := by
    funext θ
    ring
  rw [hs]
  have hh := addressAppAlong_mul_placed_source hd Q₁ hK hM hB hF Z a₁ b₁ hab₁ k₁
    (fun θ => R₂ θ*R₃ θ) (fun z hz θ x y => by
      change R₂ (update θ z (x,y))*R₃ (update θ z (x,y)) = R₂ θ*R₃ θ
      rw [show R₂ (update θ z (x,y)) = R₂ θ from
        hc₂ L₂ z (List.disjoint_left.mp h₁₂ hz) θ x y,
        show R₃ (update θ z (x,y)) = R₃ θ from
        hc₃ L₃ z (List.disjoint_left.mp h₁₃ hz) θ x y]) θ
  exact hh.trans (by ring)

end WaveTurbulence.RegAsymp
