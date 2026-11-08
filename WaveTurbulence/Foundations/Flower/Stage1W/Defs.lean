/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FlowerTop.ThreeInputs
public import WaveTurbulence.Foundations.VineEst.RowSel.Vocab

/-! # STAGE1W-GLUE: Defs (ported by source from the S-STAGE1W probe, see COPIED-SHA256SUMS). -/


@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-! ## 1. Weight vocabulary

`topPsi`, `rowParentLayer`, `rowTopWeight`, `kernelLeavesW`, `coupleLeavesTop`, `treeLeavesTop` are now on main
(416902c8, V5W-B: `VineEst/RowSel/Vocab.lean`, the same text in this namespace), imported above. -/

/-- `J`-th moment mass of a Fourier presentation on `Mom d` (root derivatives of `g (k + ·)` cost it). -/
def momentMassMom {d : ℕ} {α : Type*} [MeasurableSpace α] (J : ℕ) (M : Cut2A.SpatialMeasure (Mom d) α) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ

/-- `g` has a Fourier presentation whose `J`-th moment mass is at most `c`. -/
def GPresented {d : ℕ} (J : ℕ) (g : Mom d → ℂ) (c : ℝ) : Prop :=
  ∃ (α : Type) (_ : MeasurableSpace α) (M : Cut2A.SpatialMeasure (Mom d) α),
    momentMassMom J M ≤ ENNReal.ofReal c ∧ ∀ x, M.value x = g x

/-- The node product of a three-label weight over the nonroot nodes (FC23's `nodeLabelProduct`, verbatim). -/
def nodeLabelProduct {w : ℕ} {E M : Type*} [CommMonoid M] (ψ : Fin w → ℕ → ℕ → E → M)
    (LG : LayeredGarden w) (p : ℕ) (k : GNode LG.garden.tree → E) : M :=
  ∏ a : GNode LG.garden.tree,
    if a.1.2 ≠ [] then ψ a.1.1 (LG.layer a) (LG.parentLayer p a) (k a) else 1

/-! ## 2. The frontier weight and the weighted `Represents` (new, minimal) -/

/-- **The frontier weight** of a garden decoration: `g j` at every top node of tree `j` (a nonroot node of layer
`< p` whose parent has layer `p`), read at its coset momentum.  This is S2-ST's `psiWeight p (topPsi ∘ g) base φ`
with `φ ≡ 1`. -/
def fwWeight {P : WTParams} {R : ℕ} (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (base : Mom P.d)
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} :
    ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ :=
  fun LG κ => nodeLabelProduct (fun j => topPsi p (g j)) LG p (cosetDecoration LG.garden P.L base κ.1)

/-- `kernelLeavesSel` with a decoration weight `wt` inside the restricted decoration sum. -/
def kernelLeavesSelW {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (wt : GenDecoration LG.garden d nroot nfl → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      if sel κ then wt κ * kernelLeavesTerm L γ δ LG H up s k₀ κ else 0

/-- `LeafFamily.valueSel` with a decoration weight. -/
def valueSelW {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w)
    (sel : GenDecoration LG.garden P.d roots 0 → Prop) (wt : GenDecoration LG.garden P.d roots 0 → ℂ) : ℂ :=
  @Finset.sum (F.ι LG) ℂ _ (@Finset.univ _ (F.fin LG)) fun i =>
    ((F.sign LG i : ℝ) : ℂ) * kernelLeavesSelW P.L P.γ P.δ LG (F.H LG i) (fun b => tt b.1.1) 0 base roots 0 sel wt

/-- `LeafFamily.value` with a decoration weight (no restriction). -/
def valueW {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w)
    (wt : GenDecoration LG.garden P.d roots 0 → ℂ) : ℂ :=
  valueSelW F tt base roots LG (fun _ => True) wt

/-- `Stage1Piece.Represents` with a decoration weight in the class sum; the integral conjunct is main's
`RepresentsInt` unchanged (so main's `stage1_core_bound_int` consumes it). -/
def RepresentsFW {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R)) (wt : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ)
    (s : ℝ) (val : ℂ) : Prop :=
  val = ∑ LG ∈ members, valueSelW F tt base roots LG (sel LG) (wt LG) ∧ π.RepresentsInt n tt base roots s val

/-! ## 3. The gate -/

/-- **The frontier-weighted Stage-1 gate** (PLAN §2.3, S-STAGE1W): main's `Stage1ReductionAt` plus one weight
`g : Fin (2R) → Mom d → ℂ`, applied by `topPsi` at the top nodes of each tree, `g j` real-valued and Fourier-presented
with `32 d`-th moment mass `≤ cψ`; the class sum is weighted by `fwWeight p g base` and the piece size is
`cψ ^ (16 N) * s` (S2-ST's `Stage1ReductionAtSTBLDψTop` size). -/
def Stage1ReductionAtFW (C₀ : ℕ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
    (∀ j x, (g j x).im = 0) →
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∃ (S : Stage1Data P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop),
    Stage1Partition roots A members cls sel ∧
    (∀ π, RepresentsFW (S.piece π) N tt base roots (members (cls π)) (sel π) U.toLF
      (fwWeight p g base) (cψ ^ (16 * N) * s) (S.val π)) ∧
    (∀ π, (S.piece π).Sound p base roots) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1Counts C₀ P R N S Cl hCl cls

/-- The gate form, as main's `Stage1ReductionGate`. -/
def Stage1ReductionGateFW : Prop :=
  ∃ C₀ : ℕ → ℝ → ℕ, (∀ d γ, 2 ≤ C₀ d γ) ∧ WTPrefix (fun P => Stage1ReductionAtFW (C₀ P.d P.γ) P)


end WaveTurbulence.Flower.Stage1W
