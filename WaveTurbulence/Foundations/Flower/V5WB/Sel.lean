/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Defs

/-! # V5W-B-WORLD: the weighted row selector and the normalization of the pinned row product

* `gAt g`: the weight `g : Mom d₀ → ℂ` as a dimension-indexed family (`1` off `d₀`), the form `RowSel.g` takes.
* `selW p g cψ`: the weighted `RowSel` (ruling F2) of one vine region: top layer `p`, weight `g`, constant `cψ`.
* `rowNorm`: the normalization of the incoherent rows of a region, `∏ cψ ^ (2·order + 2)` over the incoherent
  regional couples and `∏ cψ ^ (2·order + 1)` over the incoherent interior trees.
* `clLocalStarProductFW_eq`: V5W-0's pinned selected product (unnormalized top-weighted incoherent rows) is
  `rowNorm` times main's `clLocalStarProduct` at `selW` (normalized rows, `KQsel`/`KTsel`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence WaveTurbulence.VineEst WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1W

/-- The weight `g` on `Mom d₀` as a dimension-indexed family (`1` in every other dimension). -/
def gAt {d₀ : ℕ} (g : Mom d₀ → ℂ) : (d : ℕ) → Mom d → ℂ :=
  fun d => if h : d = d₀ then (by subst h; exact g) else fun _ => 1

@[simp] theorem gAt_self {d₀ : ℕ} (g : Mom d₀ → ℂ) : gAt g d₀ = g := by
  simp [gAt]

theorem norm_gAt_le {d₀ : ℕ} {g : Mom d₀ → ℂ} {cψ : ℝ} (h1 : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ) (d : ℕ) (x : Mom d) :
    ‖gAt g d x‖ ≤ cψ := by
  unfold gAt
  split_ifs with h
  · subst h
    exact hg x
  · simpa using h1

theorem gAt_im {d₀ : ℕ} {g : Mom d₀ → ℂ} (hr : ∀ x, (g x).im = 0) (d : ℕ) (x : Mom d) : (gAt g d x).im = 0 := by
  unfold gAt
  split_ifs with h
  · subst h
    exact hr x
  · simp

/-- **The weighted row selector of one vine region** (top layer `p`, real weight `g` bounded by `cψ ≥ 1`). -/
def selW {d₀ : ℕ} (p : ℕ) (g : Mom d₀ → ℂ) (cψ : ℝ) (h1 : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ)
    (hr : ∀ x, (g x).im = 0) : RowSel () where
  weighted := true
  p := p
  cψ := cψ
  g := gAt g
  one_le_cψ := h1
  norm_g_le := norm_gAt_le h1 hg
  g_real := gAt_im hr

/-- An incoherent couple row at `selW` is the normalized top-weighted kernel. -/
theorem KQsel_selW {d₀ : ℕ} (p : ℕ) (g : Mom d₀ → ℂ) (cψ : ℝ) (h1 : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ)
    (hr : ∀ x, (g x).im = 0) {incoh : ℕ} (h : incoh ≠ 0) (q q' : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d₀ → ℝ)
    (LG : LayeredGarden 2) (t s : ℝ) (k : Mom d₀) :
    KQsel (S := selW p g cψ h1 hg hr) incoh q q' L γ δ F LG t s k =
      (((cψ ^ (2 * LG.garden.order + 2))⁻¹ : ℝ) : ℂ) *
        coupleLeavesTop L γ δ p g q q' LG (LGSpine.layerProfiles LG F) t s k := by
  unfold KQsel
  rw [if_neg h]
  change (((cψ ^ (2 * LG.garden.order + 2))⁻¹ : ℝ) : ℂ) *
      coupleLeavesTop L γ δ p (gAt g d₀) q q' LG (LGSpine.layerProfiles LG F) t s k = _
  rw [gAt_self]

/-- An incoherent tree row at `selW` is the normalized top-weighted kernel. -/
theorem KTsel_selW {d₀ : ℕ} (p : ℕ) (g : Mom d₀ → ℂ) (cψ : ℝ) (h1 : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ)
    (hr : ∀ x, (g x).im = 0) {incoh : ℕ} (h : incoh ≠ 0) (q : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d₀ → ℝ)
    (LG : LayeredGarden 1) (t s : ℝ) (k : Mom d₀) :
    KTsel (S := selW p g cψ h1 hg hr) incoh q L γ δ F LG t s k =
      (((cψ ^ (2 * LG.garden.order + 1))⁻¹ : ℝ) : ℂ) *
        treeLeavesTop L γ δ p g q LG (LGSpine.layerProfiles LG F) t s k := by
  unfold KTsel
  rw [if_neg h]
  change (((cψ ^ (2 * LG.garden.order + 1))⁻¹ : ℝ) : ℂ) *
      treeLeavesTop L γ δ p (gAt g d₀) q LG (LGSpine.layerProfiles LG F) t s k = _
  rw [gAt_self]

section Norm
variable {w d : ℕ} {G : Garden w}

/-- The normalization of the couple row of a source pair (`1` if coherent). -/
def coupleNorm (cψ : ℝ) (D : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (pr : SourcePair G) : ℝ :=
  if coupleIncoh D hG layer hLayer pr = 0 then 1
  else cψ ^ (2 * (nativeCoupleLayered D hG layer hLayer pr).garden.order + 2)

/-- The normalization of the tree row of a branch (`1` if coherent). -/
def treeNorm (cψ : ℝ) (D : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (v : GBranch G.tree) : ℝ :=
  if treeIncoh D hG layer hLayer v = 0 then 1
  else cψ ^ (2 * (nativeChainLayered D hG layer hLayer v).garden.order + 1)

/-- The normalization of the incoherent rows of a region. -/
def rowNorm (cψ : ℝ) (D : ReconstructionData G) (hG : G.IsPlain) {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) : ℝ :=
  (∏ pr ∈ clRegionalPairs hG U, coupleNorm cψ D hG layer hLayer pr) *
    ∏ v ∈ clInteriorBranches R, treeNorm cψ D hG layer hLayer v

end Norm

/-- **The pinned selected product is the normalization times main's selected product at `selW`.** -/
theorem clLocalStarProductFW_eq {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {d₀ : ℕ} (p : ℕ) (g : Mom d₀ → ℂ) (cψ : ℝ) (h1 : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ) (hr : ∀ x, (g x).im = 0)
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d₀ → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d₀)
    (κ : GNode G.tree → (Fin d₀ → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProductFW p g D hG R L γ δ F layer hLayer base κ t τ =
      (rowNorm cψ D hG R layer hLayer : ℂ) *
        clLocalStarProduct (rowSel := selW p g cψ h1 hg hr) D hG R L γ δ F layer hLayer base κ t τ := by
  have hc : (cψ : ℂ) ≠ 0 := by exact_mod_cast (show cψ ≠ 0 by linarith)
  unfold clLocalStarProductFW clLocalStarProduct rowNorm
  simp only []
  push_cast
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun pr _ => ?_) (Finset.prod_congr rfl fun v _ => ?_)
  · unfold coupleNorm selCoupleRow
    by_cases h : coupleIncoh D hG layer hLayer pr = 0
    · simp only [h, ↓reduceIte, Complex.ofReal_one, one_mul]
      exact (KQsel_of_incoh_eq_zero (S := selW p g cψ h1 hg hr) rfl _ _ _ _ _ _ _ _ _ _).symm
    · simp only [h, ↓reduceIte]
      rw [KQsel_selW p g cψ h1 hg hr h]
      push_cast
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul]
      rfl
  · unfold treeNorm selTreeRow
    by_cases h : treeIncoh D hG layer hLayer v = 0
    · simp only [h, ↓reduceIte, Complex.ofReal_one, one_mul]
      exact (KTsel_of_incoh_eq_zero (S := selW p g cψ h1 hg hr) rfl _ _ _ _ _ _ _ _ _).symm
    · simp only [h, ↓reduceIte]
      rw [KTsel_selW p g cψ h1 hg hr h]
      push_cast
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul]
      rfl

end WaveTurbulence.Flower.V5WB
