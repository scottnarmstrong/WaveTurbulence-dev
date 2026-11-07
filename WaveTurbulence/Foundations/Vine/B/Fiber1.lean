/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Unit
public import WaveTurbulence.Foundations.Vine.B.PiProd
import Mathlib.Tactic

/-!
# VINE-B♯: the product integrand `Ψ(z, κ)` on `(τ', (τ_j))` and its integrability

`psiInt z κ p` is the integrand of the glued integral (`integrand_glue`): `ε̃(z) 1_{openSb}(τ') sbInt · Π_j unitInt`.
It is jointly measurable and dominated by `Bz(z) · Π_j lb_j(κ_j)` times the indicator of the unit box.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

theorem abs_splicedEpsilon_le (G : Garden w) (hinges : Finset (GBranch G.tree)) (z : GNode G.tree → (Fin d → ℤ)) :
    |splicedEpsilon G hinges z| ≤ 1 := by
  unfold splicedEpsilon
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun v _ => abs_epsCoef_le_one' _ _ _

theorem norm_routedPhase {G : Garden w} {J' : Type} (frq : ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J') (tt : Fin w → ℝ) (τ : GBranch G.tree → ℝ) :
    ‖routedPhase frq route tt τ‖ = 1 := by
  unfold routedPhase
  rw [norm_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  generalize route s i = r
  rcases r with y | j
  · exact Complex.norm_exp_ofReal_mul_I _
  · exact norm_one

theorem norm_recExp (L γ δ : ℝ) (ζ : ℤˣ) (t : ℝ) (m : Fin 4 → Mom d) : ‖recExp L γ δ ζ t m‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The amplitude bound of a decoration of `G_sb`. -/
noncomputable def ampBound (hSb : Gsb.IsPlain) (L : ℝ) (base : Mom d) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0) : ℝ :=
  ∏ s', ‖amp s' (base + latticePoint L (z.1 (slotNode hSb s')))‖

theorem ampBound_nonneg (hSb : Gsb.IsPlain) (L : ℝ) (base : Mom d) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0) : 0 ≤ ampBound hSb L base amp z :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

/-- The box of the `G_sb` times. -/
def boxSb (layerSb : GBranch Gsb.tree → ℕ) : Set (GBranch Gsb.tree → ℝ) :=
  Set.pi Set.univ fun c => Set.Icc (layerSb c : ℝ) (layerSb c + 1)

theorem volume_boxSb (layerSb : GBranch Gsb.tree → ℕ) : (volume : Measure (GBranch Gsb.tree → ℝ)) (boxSb layerSb) = 1 := by
  unfold boxSb
  rw [volume_pi_pi]
  simp

theorem openSb_subset_box (layerSb : GBranch Gsb.tree → ℕ) (tt : Fin w → ℝ) :
    openSb Gsb layerSb tt ⊆ boxSb layerSb := fun τ h c _ => ⟨(h.1 c).1.le, (h.1 c).2.le⟩

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- The product integrand of the glued integral. -/
noncomputable def psiInt (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j)))) : ℂ :=
  (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
    (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
      (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
        ∏ j, Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z τ' j (κs j) (p.2 j)) p.1

end SpliceShape

end WaveTurbulence.VineB
