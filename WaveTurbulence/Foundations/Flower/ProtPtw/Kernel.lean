/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Bound

/-! # D6a PROT-PTW: the pinned paired-tree kernel, pointwise (o82 Prop 14.2 with `a = 0`)

`kernelProt` of a paired tree with designated branches `fix`: if every link of `E^c` has both branches free, the kernel
is bounded at every clock pair and output by `c^{2n} · (star mass) · (cell mass) · ∏_{E} c_i(5L)^{2d} · ∏_{E^c} M_i`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links

variable {d : ℕ} {LG : LayeredGarden 1} {X : RegChain}

theorem extendFix_eq_fill {w : ℕ} (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) :
    G.extendFix fix τ = fill (fun b => fix b = none) (fun b => (fix b).getD 0) τ := by
  funext b
  unfold fill
  by_cases h : fix b = none
  · rw [dite_eq_left h]
    exact extendFix_free G fix τ ⟨b, h⟩
  · rw [dite_eq_right h]
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
    rw [extendFix_some G fix τ hv]
    simp only [hv, Option.getD_some]

/-- The cell mass of the leaf profiles (main's localization constants). -/
def cellMass (d n m M : ℕ) (C B : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (C ^ n) * (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
    ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))

/-- **The pointwise bound of the designated paired-tree kernel** (no selected time). -/
theorem enorm_kernelProt_tree_le (hX : X.DecodesTree LG.garden) {α : Type*} [MeasurableSpace α]
    {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (H : LeafProfiles 1 d) (mult : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k : Mom d)
    (F : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) {Bψ : ℝ} (hBψ : 0 ≤ Bψ)
    (hψ : ∀ i q, ‖ψ i q‖ ≤ Bψ)
    (hW : ∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      mult (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
        F.value (pairedLattice L p) * arrayWeight ψ p)
    (hs : Summable (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
      ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k (fun i j => latticePoint L (p (i, j)))‖))
    {K M : ℕ} {B : ℝ} (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (treeInputFunctionsL LG H a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (Links.TPlus LG.garden)) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c x, (treeCarrier hX).inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 => x p.1 p.2) ≠ 0 →
        z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ (X.treeLinks (LG.garden.sig 0)).length)
    (E : Finset (Fin (X.treeLinks (LG.garden.sig 0)).length)) (cE : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ)
    (hcE : ∀ i ∈ E, 0 ≤ cE i ∧ ∀ q, ‖ψ i q‖ ≤ cE i)
    (Mi : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ≥0∞)
    (hMi : ∀ i ∉ E, ∀ A : LayerLink d, A.leftLayer = (treeLayerLinks (d := d) LG hX i).leftLayer →
      A.rightLayer = (treeLayerLinks (d := d) LG hX i).rightLayer →
      ∫⁻ s in linkBox A, ‖genLinkTimeFactor L γ δ A (ψ i) s‖ₑ ≤ Mi i)
    (hfree : ∀ i ∉ E, ∀ e, fix (treeLinkBranch hX i e) = none) :
    ‖kernelProt L γ δ LG H mult up s fix k (fun _ => 0) 0‖ₑ ≤
      ENNReal.ofReal (coupling d L γ δ ^ (2 * (X.treeLinks (LG.garden.sig 0)).length)) *
        (ENNReal.ofReal F.mass * cellMass d (X.treeLinks (LG.garden.sig 0)).length
          (Fintype.card (Links.TPlus LG.garden)) M C B *
          ∏ i, (if i ∈ E then ENNReal.ofReal (cE i * (5 * L) ^ (2 * d)) else Mi i)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [kernelProt_tree_eq_integral hX hLp γ δ H mult up s fix k F ψ hBψ hψ hW hs, enorm_mul]
  have hc : ‖(coupling d L γ δ : ℂ) ^ (2 * (X.treeLinks (LG.garden.sig 0)).length)‖ₑ =
      ENNReal.ofReal (coupling d L γ δ ^ (2 * (X.treeLinks (LG.garden.sig 0)).length)) := by
    rw [← Complex.ofReal_pow, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact (even_two_mul _).pow_nonneg _
  rw [hc]
  apply mul_le_mul' le_rfl
  apply (enorm_integral_le_lintegral_enorm _).trans
  let keep := fun b : GBranch LG.garden.tree => fix b = none
  let y := fun b : GBranch LG.garden.tree => (fix b).getD 0
  have hpt (τ : {b // fix b = none} → ℝ) :
      ‖(protDom LG up s fix).indicator (treeIntegrand hX L γ δ H k F ψ) (LG.garden.extendFix fix τ)‖ₑ ≤
        (unitBox fun b : {b // keep b} => (LG.layer b.1.toNode : ℝ)).indicator 1 τ *
          arrayEnvelope (treeCarrier hX) F (gardenCircle LG.garden) L γ δ (treeLayerLinks LG hX) ψ
            (treeInputFunctionsL LG H) S k (supG L γ δ E cE ψ) ((treeClockEquiv hX).symm (fill keep y τ)) := by
    by_cases hτ : LG.garden.extendFix fix τ ∈ protDom LG up s fix
    · have hb : τ ∈ (unitBox fun b : {b // keep b} => (LG.layer b.1.toNode : ℝ)) :=
        protDom_subset_freeBox LG up s fix τ hτ
      rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hb, Pi.one_apply, one_mul, ← extendFix_eq_fill]
      exact enorm_arrayIntegrand_le (treeCarrier hX) F (gardenCircle LG.garden) hL γ δ (treeLayerLinks LG hX) ψ hBψ
        hψ (treeInputFunctionsL LG H) hK hM hB hf S k hcover hS (supG L γ δ E cE ψ)
        (supG_ge hL γ δ E cE ψ hcE) _
    · rw [Set.indicator_of_notMem hτ, enorm_zero]
      exact bot_le
  refine (lintegral_mono hpt).trans ?_
  exact lintegral_keep_envelope_le hX hL γ δ H k F ψ hK hM hB hf S hS E cE Mi hMi keep y
    (fun i hi e => hfree i hi e)

end WaveTurbulence.Flower.ProtPtw
