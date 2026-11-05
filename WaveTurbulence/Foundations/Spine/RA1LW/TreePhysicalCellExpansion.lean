/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeKernelReindex
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeSourcePhaseBound
public import WaveTurbulence.Foundations.IncohInst.InputProductIdentity
public import WaveTurbulence.Foundations.IncohInst.CosetDecorationIdentity
public import WaveTurbulence.Foundations.RegAsymp.TreeLatticeCellExchange
public import WaveTurbulence.Foundations.Incoh.TreeAugmentedInputBounds

/-! # Exact global original KTstar cell expansion with the temporary root input -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh IncohInst Links

/-- The literal original squared-Wick and time coefficient, before a profile expansion. -/
def treeOriginalLatticeCoefficient {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1)
    {X : RegChain} (hX : X.DecodesTree LG.garden) (t s : ℝ) (k : Mom d)
    (p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ) : ℂ :=
  ((∏ j, linkWickFactor (p (j,0)) (p (j,1))):ℂ) *
    phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s
      (cosetDecoration LG.garden L k (treeDecOfParams hX (0:Fin d → ℤ)
        (fun j => (p (j,0),p (j,1)))).val)

/-- The original source coefficient is bounded uniformly over all lattice decorations. -/
theorem treeOriginalLatticeCoefficient_norm_le {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1)
    {X : RegChain} (hX : X.DecodesTree LG.garden) (h0 : ∀ a, LG.layer a = 0)
    (t s : ℝ) (k : Mom d)
    (p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ) :
    ‖treeOriginalLatticeCoefficient L γ δ LG hX t s k p‖ ≤ 1 := by
  rw [treeOriginalLatticeCoefficient,norm_mul,← Complex.ofReal_prod]
  have hw : ‖(((∏ j, linkWickFactor (p (j,0)) (p (j,1))):ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun j _ => abs_linkWickFactor_le _ _)
  exact (mul_le_mul hw (tree_norm_phaseIntegral_le_one L γ δ LG h0 _ _ _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- Source input rows recover the original physical kernel, with no analytic exchanges. -/
theorem treeLeaves_eq_original_lattice_source {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1)
    {X : RegChain} (hX : X.DecodesTree LG.garden) (H : LGSpine.LeafProfiles 1 d) (t s : ℝ) (k : Mom d) :
    LGSpine.treeLeaves L γ δ LG H t s k =
      (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta*
        ∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
          treeOriginalLatticeCoefficient L γ δ LG hX t s k p *
            (treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k
              (fun j i => latticePoint L (p (j,i))) := by
  rw [treeLeaves_treeLatticeEquiv L γ δ H LG hX]
  congr 1
  apply tsum_congr
  intro p
  rw [tree_sourceLeafWeight_eqL hX H k]
  unfold treeOriginalLatticeCoefficient
  rw [tree_decOfParams_eq_coset hX L k (fun j => (p (j,0),p (j,1)))]

/-- A root partition value times the literal KTstar is exactly the double original
cell/lattice series. Its rearrangement is justified by original source spatial norms. -/
theorem treeLeaves_mul_rootPartition_eq_tsum_cells {d K M : ℕ} (L γ δ : ℝ)
    (LG : LayeredGarden 1) {X : RegChain} (hX : X.DecodesTree LG.garden)
    (h0 : ∀ a, LG.layer a = 0) {B : ℝ} (hL : 1 ≤ L) (hK : d+1 ≤ K) (hM : 2*d ≤ M)
    (H : LGSpine.LeafProfiles 1 d)
    (hf : ∀ a, Fourier.spatialNorm K M (treeInputFunctionsL LG H a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    {Ccover : ℝ} (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (LG.garden.sig 0)).length)
    (q : Fin d → ℤ) (t s : ℝ) (k : Mom d) :
    LGSpine.treeLeaves L γ δ LG H t s k * treeRootPartition q k =
      (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta*
        ∑' u : SourceCellIndex S,
          ∑' p : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ,
            treeOriginalLatticeCoefficient L γ δ LG hX t s k p *
              (treeCarrier hX).withRootInput.sourceCellWeight
                (appendRootInput (treeInputFunctionsL LG H) (treeRootPartition q)) S k
                  (fun j i => latticePoint L (p (j,i))) u := by
  obtain ⟨Bq,hBq,hfq⟩ := exists_spatialNorm_bound_appendRootPartition
    (treeInputFunctionsL LG H) hf q
  have he := tree_lattice_eq_tsum_cells (treeCarrier hX).withRootInput
    (appendRootInput (treeInputFunctionsL LG H) (treeRootPartition q)) S k
    (fun c x => hcover c k x) hS hL hK hM hBq.le hfq
    (treeOriginalLatticeCoefficient L γ δ LG hX t s k)
    (treeOriginalLatticeCoefficient_norm_le L γ δ LG hX h0 t s k)
  rw [← he,treeLeaves_eq_original_lattice_source L γ δ LG hX H t s k]
  simp_rw [MomentumTreeData.sourceLeafWeight_withRootInput,← mul_assoc]
  rw [tsum_mul_right]
  ring

end WaveTurbulence.RA1Leafwise
