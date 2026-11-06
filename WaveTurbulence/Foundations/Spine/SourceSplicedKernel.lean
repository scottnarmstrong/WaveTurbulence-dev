/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSubproObjects
/-! Explicit normalized spliced kernels (TARGET redvine2–redvine3, L1957–L1976).
The carrier is the actual garden and its actual decorations. In particular the epsilon
factors are the original epsCoef factors; arbitrary replacement sign functions are not data.
Only branch pre-layering is used, as required after splicing. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset

/-- Integer momentum carried by an actual PC or LP bond of the garden molecule. -/
def bondIndex {w d : ℕ} (G : Garden w) (z : GNode G.tree → (Fin d → ℤ)) :
    GardenDart G → (Fin d → ℤ)
  | .inl (c, _) => z c.1.toNode
  | .inr l => z l.1.toNode

/-- Darts of the bonds incident to at least one hinge, the only momentum arguments of Kdagger. -/
abbrev HingeDarts {w : ℕ} (G : Garden w) (hinges : Finset (GBranch G.tree)) :=
  {x : GardenDart G // G.molecule.atom x ∈ hinges ∨ G.molecule.atom (G.molecule.mate x) ∈ hinges}

/-- One local SG/LG/ZG specification in the literal source indicator. -/
structure LocalGapSpecification {w : ℕ} (G : Garden w) (v : GBranch G.tree) where
  first : GardenDart G
  second : GardenDart G
  at_first : G.molecule.atom first = v
  at_second : G.molecule.atom second = v
  distinct : second ≠ G.molecule.mate first
  opposite : G.molecule.out first ≠ G.molecule.out second
  kind : Molecule.GapKind

/-- Explicit data occurring in the normalized source formula. Support and derivative bounds
are separate source typing predicates, rather than hidden choices of approximation functions. -/
structure SplicedKernelData {w : ℕ} (G : Garden w) (d : ℕ) where
  layer : GBranch G.tree → ℕ
  hinges : Finset (GBranch G.tree)
  center : GardenDart G → Mom d
  edgeAmplitude : GardenDart G → Mom d → ℂ
  hingeAmplitude : (HingeDarts G hinges → Mom d) → ℂ
  gapSpecification : (v : GBranch G.tree) → Option (LocalGapSpecification G v)
  frequency : GBranch G.tree → ℝ
  /-- F-TT (R33): the root times `t_j` of the exterior garden; every branch of tree `j` satisfies `τ_b < t_j`
  (TARGET `sumint`, domain clause (ii): all variables are less than `t`). -/
  rootTime : Fin w → ℝ

/-- TARGET L1969–L1971: unit branch-time intervals with the actual parent-child ordering, truncated at the root
times (F-TT, R33: `τ_b < t_j` for the branches of tree `j`; automatic for non-root-adjacent branches). -/
def splicedTimeDomain {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) :
    Set (GBranch G.tree → ℝ) :=
  {t | (∀ v, t v ∈ Icc (layer v : ℝ) (layer v + 1)) ∧
    (∀ v u, v.IsChildOf u → t v < t u) ∧ ∀ v, t v < rootTime v.1.1}

/-- Original source epsilon factors, omitting exactly the hinges (TARGET L1962–L1964). -/
noncomputable def splicedEpsilon {w d : ℕ} (G : Garden w) (hinges : Finset (GBranch G.tree))
    (z : GNode G.tree → (Fin d → ℤ)) : ℝ :=
  ∏ v ∈ (univ : Finset (GBranch G.tree)).filter (fun v => v ∉ hinges),
    epsCoef (z (v.child 0)) (z (v.child 1)) (z (v.child 2))

noncomputable def splicedGapIndicator {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ℝ := by
  classical
  exact ∏ v : GBranch G.tree, match D.gapSpecification v with
    | none => 1
    | some q => if Molecule.gapKind L γ η
        (base + latticePoint L (bondIndex G z q.first) -
          (base + latticePoint L (bondIndex G z q.second))) = q.kind then 1 else 0

/-- The time integral in redvine2, retaining the original signed garden resonances. The
molecular Gamma/offset version in redvine3 is obtained by the garden energy correspondence. -/
noncomputable def splicedTimeIntegral {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  ∫ t : GBranch G.tree → ℝ, (splicedTimeDomain G D.layer D.rootTime).indicator
    (fun t => phaseProd L γ δ G (cosetDecoration G L base z) t *
      ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I)) t

/-- The literal normalized spliced kernel, before its external redvine2 coefficient. -/
noncomputable def splicedKernel {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) : ℂ :=
  (coupling d L γ δ : ℂ) ^ G.order *
    ∑' z : GenDecoration G d roots 0,
      (splicedEpsilon G D.hinges z.1 : ℂ) * (splicedGapIndicator G D L γ η base z.1 : ℂ) *
        (∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))) *
        D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z.1 x.1)) *
        splicedTimeIntegral G D L γ δ base z.1

/-- The amplitude hypotheses in TARGET L1965–L1974. No derivative bound is imposed on Kdagger. -/
def SplicedAmplitudeBounds {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d) : Prop :=
  (∀ x, D.center (G.molecule.mate x) = D.center x) ∧
  (∀ x ∈ G.molecule.bonds, SNorm (30 * d) 0 (D.edgeAmplitude x) ≤ 1 ∧
    ∀ k, 1 < ‖k - D.center x‖ → D.edgeAmplitude x k = 0) ∧
  (∀ K, ‖D.hingeAmplitude K‖ ≤ 1) ∧
    ∀ K, (∃ x : HingeDarts G D.hinges, 1 < ‖K x - D.center x.1‖) → D.hingeAmplitude K = 0

end WaveTurbulence.LGSpine
