/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
/-! Literal local ladder expression of TARGET ladderl1new, L1978–L1992.
Only internal bond labels and ladder atom times are summed/integrated; all boundary data are fixed. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset MeasureTheory

/-- Dimension-independent time data avoids imposing any momentum data on the source clocks. -/
def localLadderClocks {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ)
    (S : Finset (GBranch G.tree)) (outside : GBranch G.tree → ℝ) : Set (S → ℝ) :=
  {t | (∀ v : S, t v ∈ Icc (layer v.1 : ℝ) (layer v.1 + 1)) ∧
    ∀ v u, v.IsChildOf u → v ∈ S ∨ u ∈ S →
      (if hv : v ∈ S then t ⟨v, hv⟩ else outside v) <
        (if hu : u ∈ S then t ⟨u, hu⟩ else outside u)}

noncomputable def localLadderTimeIntegral {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (outside : GBranch G.tree → ℝ)
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  ∫ t : S → ℝ, (localLadderClocks G D.layer S outside).indicator
    (fun t => ∏ v : S, Complex.exp ((Real.pi *
      (((((G.sign v.1.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        omegaNode G (cosetDecoration G L base z) v.1 + D.frequency v.1) * t v) : ℝ) * Complex.I)) t

/-- Fixed boundary bonds: only bonds with both ends in S are free. -/
def localLadderDecorations {w d : ℕ} (G : Garden w) (S : Finset (GBranch G.tree))
    (roots : Fin w → (Fin d → ℤ)) (boundary : GardenDart G → (Fin d → ℤ)) :
    Set (GenDecoration G d roots 0) :=
  {z | ∀ x, ¬ G.molecule.InGroup S x → bondIndex G z.1 x = boundary x}

noncomputable def localLadderGapIndicator {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (L γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : ℝ := by
  classical
  exact ∏ v ∈ S, match D.gapSpecification v with
    | none => 1
    | some q => if Molecule.gapKind L γ η
        (base + latticePoint L (bondIndex G z q.first) -
          (base + latticePoint L (bondIndex G z q.second))) = q.kind then 1 else 0

/-- The literal local kernel in ladderl1new: the outside time and bond values are fixed,
all internal bonds carry the original source smooth unit-ball amplitudes. -/
noncomputable def sourceLocalLadderKernel {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (S : Finset (GBranch G.tree)) (outside : GBranch G.tree → ℝ)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (boundary : GardenDart G → (Fin d → ℤ)) : ℂ :=
  (coupling d L γ δ : ℂ) ^ (S.card - 1) *
    ∑' z : localLadderDecorations G S roots boundary,
      ((∏ v ∈ S, epsCoef (z.1.1 (v.child 0)) (z.1.1 (v.child 1)) (z.1.1 (v.child 2))) : ℂ) *
      (localLadderGapIndicator G D S L γ η base z.1.1 : ℂ) *
      (∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
        D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1.1 x))) *
      localLadderTimeIntegral G D S outside L γ δ base z.1.1

noncomputable def sourceLadderIncoherency {w : ℕ} (G : Garden w)
    (layer : GBranch G.tree → ℕ) {m : ℕ} (u v : Fin (m + 1) → GBranch G.tree) : ℕ :=
  ∑ j, if layer (u j) = layer (v j) then 0 else 1

end WaveTurbulence.LGSpine
