/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Tree

/-! # D6a PROT-PTW: the protected paired tree with fixed parameters (o82 Prop 14.2, (18.4))

Assembly of the pin data, the link weights, the kernel bounds (`enorm_kernelProt_tree_le`,
`enorm_kernelProt_tree_sel_le`) and the per-link accounting, for normalized leaves and fixed `γ, η, δ, L`; D5a's
one-link bounds (`hdec`) and main's cell cover (`hcov`) are the inputs. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links
open WaveTurbulence.Flower.FiltSrc WaveTurbulence.Flower.FiltProd WaveTurbulence.Flower.FiltGate

variable {d : ℕ}

/-- The cell cover property of main's localization. -/
def CellCover (d : ℕ) (Ccov : ℝ) : Prop :=
  ∀ (n m w : ℕ) (P : MomentumTreeData n m w) (k : Mom d) (c : Fin m → Fin d → ℤ),
    ∃ S : Finset ((Fin n × Fin 2) → Fin d → ℤ), (S.card : ℝ) ≤ Ccov ^ n ∧
      ∀ x : Fin n → Fin 2 → Mom d, P.inputCellWeight c k x ≠ 0 →
        ∀ z : (Fin n × Fin 2) → Fin d → ℤ, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S

/-- D5a's one-link bounds at fixed parameters. -/
def LinkDecay (d : ℕ) (C₀ C₂ γ η δ L Dr : ℝ) : Prop :=
  ∀ Q : LayerLink d, |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 ≤ Dr → ∀ (K : ℝ) (φ : ℝ → ℂ), PresentedMult L K φ →
    (filtLayerLinkMass L (δ * L ^ (2 * γ)) Q φ ≤ ENNReal.ofReal (K * (C₀ * kineticLinkScale d γ δ L))) ∧
    (Q.IsIncoherent → filtLayerLinkMass L (δ * L ^ (2 * γ)) Q φ ≤
      ENNReal.ofReal (K * (C₀ * C₂ * kineticLinkScale d γ δ L * L ^ (-(incoherenceExponent d γ - η)))))

/-- The D6 multiplier. -/
def protMult {LG : LayeredGarden 1} (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Sel : Finset (GBranch LG.garden.tree))
    (M₂ : ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) : (GNode LG.garden.tree → Mom d) → ℂ :=
  fun κ => starWeight S ω κ *
    filtWeight (F ∪ Sel) (fun b => decide (b ∈ Sel)) (fun b => if b ∈ Sel then M₂ else M b) κ *
    filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)

/-- The D6 multiplier with a general star factor `sw` (a cap couple transports its star weights to one). -/
def protMultG {LG : LayeredGarden 1} (sw : (GNode LG.garden.tree → Mom d) → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Sel : Finset (GBranch LG.garden.tree))
    (M₂ : ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) : (GNode LG.garden.tree → Mom d) → ℂ :=
  fun κ => sw κ *
    filtWeight (F ∪ Sel) (fun b => decide (b ∈ Sel)) (fun b => if b ∈ Sel then M₂ else M b) κ *
    filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)

theorem protMult_eq_G {LG : LayeredGarden 1} (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Sel : Finset (GBranch LG.garden.tree))
    (M₂ : ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) :
    protMult S ω F M Sel M₂ Fu Mu ind = protMultG (starWeight S ω) F M Sel M₂ Fu Mu ind := rfl

/-- The multiplier identity with a presented star factor. -/
theorem tree_mult_eqG {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden) (L : ℝ) (k : Mom d)
    (sw : (GNode LG.garden.tree → Mom d) → ℂ) {α : Type*} [MeasurableSpace α]
    (Gs : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (hsw : ∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      sw (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
        Gs.value (pairedLattice L p))
    (F Fu : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (dag : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ)
    (hdag : ∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      (ind (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) : ℂ) =
        ∏ i, dag i (p (i, 0), p (i, 1)))
    (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) :
    (fun κ => sw κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
      Gs.value (pairedLattice L p) * arrayWeight (treePsi hX L F Fu ann M Mu dag) p := by
  dsimp only
  rw [mul_assoc (sw _), tree_filtWeight_eq_arrayFiltWeight hX L k F Fu ann M Mu p, hsw p, hdag p, mul_assoc]
  congr 1
  unfold arrayFiltWeight arrayWeight treePsi
  rw [Finset.prod_mul_distrib]

/-- The normal-link mass bound. -/
def normalMass (d : ℕ) (K C₀ C₂ γ η δ L : ℝ) (inc : Prop) [Decidable inc] : ℝ≥0∞ :=
  ENNReal.ofReal (K * (C₀ * kineticLinkScale d γ δ L) *
    (if inc then C₂ * L ^ (-(incoherenceExponent d γ - η)) else 1))

theorem normal_link_mass {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden) {L : ℝ} (hL0 : 0 ≤ L)
    (γ δ : ℝ) {C₀ C₂ η Dr : ℝ} (hdec : LinkDecay d C₀ C₂ γ η δ L Dr)
    (F Fu : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool) (M Mu : GBranch LG.garden.tree → ℝ)
    (hM : ∀ b ∈ F, L ≤ M b) (hMu : ∀ b ∈ Fu, L ≤ Mu b)
    (dag : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ)
    (i : Fin (X.treeLinks (LG.garden.sig 0)).length) (hdag : ∀ q, dag i q = 1)
    (hspan : |((treeLayerLinks (d := d) LG hX i).leftLayer : ℝ) - (treeLayerLinks (d := d) LG hX i).rightLayer| + 1 ≤ Dr)
    (A : LayerLink d) (h1 : A.leftLayer = (treeLayerLinks (d := d) LG hX i).leftLayer)
    (h2 : A.rightLayer = (treeLayerLinks (d := d) LG hX i).rightLayer) :
    ∫⁻ s in linkBox A, ‖genLinkTimeFactor L γ δ A (treePsi hX L F Fu ann M Mu dag i) s‖ₑ ≤
      normalMass d (filtMomentConst ^ 4) C₀ C₂ γ η δ L (treeLayerLinks (d := d) LG hX i).IsIncoherent := by
  have hψ : treePsi hX L F Fu ann M Mu dag i = fun q => treeLinkFilt hX F Fu ann M Mu i (linkBilinear L q) := by
    funext q; simp only [treePsi, hdag q, mul_one]
  rw [hψ, lintegral_filtLink_eq]
  have hspanA : |(A.leftLayer : ℝ) - A.rightLayer| + 1 ≤ Dr := by rw [h1, h2]; exact hspan
  obtain ⟨hb1, hb2⟩ := hdec A hspanA _ _ (presentedMult_treeLinkFilt hX hL0 F Fu ann M Mu hM hMu i)
  unfold normalMass
  by_cases hi : (treeLayerLinks (d := d) LG hX i).IsIncoherent
  · have hA : A.IsIncoherent := by unfold LayerLink.IsIncoherent at hi ⊢; rw [h1, h2]; exact hi
    rw [ite_eq_left hi]
    refine (hb2 hA).trans (le_of_eq ?_)
    congr 1; ring
  · rw [ite_eq_right hi, mul_one]
    exact hb1

end WaveTurbulence.Flower.ProtPtw
