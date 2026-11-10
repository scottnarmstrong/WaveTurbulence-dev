/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Dagger
public import WaveTurbulence.Foundations.Flower.FiltGate.StarDecay

/-! # D6a PROT-PTW: the link weights of a protected tree

The D6 multiplier (star weights, the filter layer `F ∪ Sel` with the annular factor `chiD(|Ω|/M₂)` on the selected
branch, the upper layer, the dagger) on link arrays: the star-measure value times the link weights
`ψ_i(q) = φ_i(⟨q⟩) · dag_i(q)` (`φ_i` = D5b-1's `treeLinkFilt`, `dag` the dagger on the pinned link). Bounds:
`‖ψ_i‖ ≤ K = filtMomentConst⁴`; on the selected link `ψ_j` vanishes for `|⟨q⟩| < M₂/4`, so its antiderivative weight is
`≤ 2K/(π δ L^{2γ} M₂)`; non-exceptional links keep D5a's pair masses. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links
open WaveTurbulence.Flower.FiltSrc WaveTurbulence.Flower.FiltProd WaveTurbulence.Flower.FiltGate

/-- The annular profile vanishes near zero. -/
theorem chiD_eq_zero_of_lt {x : ℝ} (hx : |x| < 1 / 2) : FlShell.chiD x = 0 := by
  unfold FlShell.chiD
  have hloc : chi0 =ᶠ[nhds x] fun _ => 1 := by
    have ho : IsOpen {y : ℝ | |y| < 1 / 2} := isOpen_lt continuous_abs continuous_const
    filter_upwards [ho.mem_nhds hx] with y hy
    unfold chi0
    have hy' : |y| < 1 / 2 := hy
    exact Real.smoothTransition.one_of_one_le (by linarith)
  rw [hloc.deriv_eq, deriv_const, mul_zero]

variable {d : ℕ} {LG : LayeredGarden 1} {X : RegChain}

/-- The link weights of the D6 multiplier. -/
def treePsi (hX : X.DecodesTree LG.garden) (L : ℝ) (F Fu : Finset (GBranch LG.garden.tree))
    (ann : GBranch LG.garden.tree → Bool) (M Mu : GBranch LG.garden.tree → ℝ)
    (dag : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) :
    Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ :=
  fun i q => treeLinkFilt hX F Fu ann M Mu i (linkBilinear L q) * dag i q

theorem norm_treePsi_le (hX : X.DecodesTree LG.garden) {L : ℝ} (hL : 0 ≤ L) (F Fu : Finset (GBranch LG.garden.tree))
    (ann : GBranch LG.garden.tree → Bool) (M Mu : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, L ≤ M b)
    (hMu : ∀ b ∈ Fu, L ≤ Mu b) (dag : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ)
    (hdag : ∀ i q, ‖dag i q‖ ≤ 1) (i : Fin (X.treeLinks (LG.garden.sig 0)).length) (q : LPair d) :
    ‖treePsi hX L F Fu ann M Mu dag i q‖ ≤ filtMomentConst ^ 4 := by
  unfold treePsi
  rw [norm_mul]
  calc _ ≤ filtMomentConst ^ 4 * 1 := mul_le_mul
        (PresentedMult.norm_le (presentedMult_treeLinkFilt hX hL F Fu ann M Mu hM hMu i) hL
          filtMomentConst_pow_pos.le _)
        (hdag i q) (norm_nonneg _) filtMomentConst_pow_pos.le
    _ = _ := mul_one _

/-- The selected (annular) factor vanishes the link weight where `|⟨q⟩| < M₂/4`. -/
theorem treePsi_eq_zero_of_small (hX : X.DecodesTree LG.garden) (L : ℝ) (F Fu : Finset (GBranch LG.garden.tree))
    (ann : GBranch LG.garden.tree → Bool) (M Mu : GBranch LG.garden.tree → ℝ)
    (dag : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ)
    (j : Fin (X.treeLinks (LG.garden.sig 0)).length) (ev : Fin 2) (hvF : treeLinkBranch hX j ev ∈ F)
    (hann : ann (treeLinkBranch hX j ev) = true) {M₂ : ℝ} (hM₂ : 0 < M₂) (hMv : M (treeLinkBranch hX j ev) = M₂)
    (q : LPair d) (hq : |linkBilinear L q| < M₂ / 4) : treePsi hX L F Fu ann M Mu dag j q = 0 := by
  unfold treePsi treeLinkFilt linkFiltWeight linkFiltMult
  have hmem : treeLinkBranch hX j ev ∈ F ∩ treeLinkBlock hX j :=
    Finset.mem_inter.mpr ⟨hvF, Finset.mem_image.mpr ⟨ev, Finset.mem_univ _, rfl⟩⟩
  rw [Finset.prod_eq_zero hmem, zero_mul, zero_mul]
  rw [hann, hMv]
  simp only [filtProf, ite_true, Complex.ofReal_eq_zero]
  apply chiD_eq_zero_of_lt
  rw [abs_div, abs_abs, abs_of_pos hM₂, div_lt_iff₀ hM₂, abs_mul]
  norm_num
  linarith

end WaveTurbulence.Flower.ProtPtw
