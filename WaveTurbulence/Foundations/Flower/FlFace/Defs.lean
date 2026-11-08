/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.FirstMax
public import WaveTurbulence.Frozen.Defs.KDomainFix
public import WaveTurbulence.Frozen.Defs.PhaseProdOff
public import WaveTurbulence.Frozen.Defs.GardenExtendFix
/-! # FL-FACE: faces of the `kDomainFix` time domain at selected nodes (supplement Lemma 9.1)

Fix a layered garden `LG`, the frozen `kDomainFix` arguments `up` and `fix`, and a finite set `S` of selected free
branching nodes, at most one per tree. On `kDomainFix LG up fix` the time `t_v` of a selected node `v` ranges over the
open interval from the **lower endpoint** `max(𝔏_v, t_c : c a branching child of v)` to the **upper endpoint**
`min(top_v, t_q : q the parent of v)`, where `top_v = min (up v) (𝔏_v + 1)` is the external top time (the frozen
domain imposes both `t_v < up v` and `t_v < 𝔏_v + 1`; `0 < t_v` follows from `𝔏_v < t_v`).

A **face** chooses, for every selected `v`, one endpoint `F v : FaceEnd`:
- an upper one, `top` (`t_v := top_v`) or `parent q` (`t_v := t_q`), with sign `+1`;
- a lower one, `floor` (`t_v := 𝔏_v`) or `child c` (`t_v := t_c`), with sign `-1`.

The face domain keeps every constraint of `kDomainFix` that does not involve a selected time (`restDomain`) and adds,
for each selected `v`, the **cell** of its endpoint (`faceCell`): an upper endpoint must be the first minimizer of the
upper endpoints and exceed every lower endpoint (the upper face is *not* split over the maximizing child); a lower
endpoint must be the first maximizer of the lower endpoints (cell by cell) and lie below every upper endpoint. Ties are
broken by `FaceEnd.rank` (parent before top, floor before the children, children by a fixed enumeration of the
branching nodes), which makes the partition exact.

The face integrand is the `kDomainFix`-indicator × `phaseProdOff` integrand with `fix` modified to `fixSel fix S`
(the selected times are no longer integrated) and the selected times substituted by their endpoints (`faceSubst`).
The substitution adds `ω_v` to the phase at that endpoint: for `parent q` and `child c` the phase at the substituted
node becomes `e^{i(ω_q + ω_v) t_q}` (resp. `e^{i(ω_c + ω_v) t_c}`), for `top`/`floor` it is the constant
`e^{iω_v top_v}` (resp. `e^{iω_v 𝔏_v}`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlFace
open Finset

variable {w : ℕ}

/-- The endpoint chosen at a selected node: two upper kinds (`top`, `parent`) and two lower kinds (`floor`,
`child`). The parent and child carry the branching node whose time is substituted. -/
inductive FaceEnd {w : ℕ} (T : Fin w → TTree) : Type where
  /-- the external top time `min (up v) (𝔏_v + 1)` -/
  | top : FaceEnd T
  /-- the parent time `t_q` -/
  | parent (q : GBranch T) : FaceEnd T
  /-- the layer floor `𝔏_v` -/
  | floor : FaceEnd T
  /-- the time `t_c` of a branching child `c` -/
  | child (c : GBranch T) : FaceEnd T

namespace FaceEnd

variable {T : Fin w → TTree}

/-- Upper endpoints (`top`, `parent`) enter with sign `+1`, lower ones (`floor`, `child`) with `-1`. -/
def isUpper : FaceEnd T → Bool
  | top => true
  | parent _ => true
  | floor => false
  | child _ => false

/-- The tie-breaking rank: among upper endpoints the parent comes before `top`; among lower endpoints `floor` comes
first, then the children in a fixed enumeration of the branching nodes. -/
def rank : FaceEnd T → ℕ
  | top => Fintype.card (GBranch T)
  | parent q => Fintype.equivFin (GBranch T) q
  | floor => 0
  | child c => Fintype.equivFin (GBranch T) c + 1

end FaceEnd

section Tree

variable {T : Fin w → TTree}

/-- The branching parents of `v` (at most one). -/
def parents (v : GBranch T) : Finset (GBranch T) := univ.filter fun q => v.IsChildOf q

/-- The branching children of `v` (at most three). -/
def children (v : GBranch T) : Finset (GBranch T) := univ.filter fun c => c.IsChildOf v

/-- The upper endpoints of `v`: `top` and the parent, if any. -/
def upSet (v : GBranch T) : Finset (FaceEnd T) := insert FaceEnd.top ((parents v).image FaceEnd.parent)

/-- The lower endpoints of `v`: `floor` and the branching children. -/
def lowSet (v : GBranch T) : Finset (FaceEnd T) := insert FaceEnd.floor ((children v).image FaceEnd.child)

/-- All endpoints of `v` (at most six). -/
def endChoices (v : GBranch T) : Finset (FaceEnd T) := upSet v ∪ lowSet v

/-- `fix` with the selected nodes designated: their times are no longer integrated (the face substitution then
overwrites the placeholder value). -/
def fixSel (fix : GBranch T → Option ℝ) (S : Finset (GBranch T)) : GBranch T → Option ℝ :=
  fun b => if b ∈ S then some 0 else fix b

/-- A face: an endpoint at every node (only the values on the selected set matter). -/
abbrev Face (T : Fin w → TTree) : Type := GBranch T → FaceEnd T

/-- The faces at the selected set `S`: an endpoint of `endChoices v` at each `v ∈ S` (and `top`, a dummy, off `S`). -/
def faces (S : Finset (GBranch T)) : Finset (Face T) :=
  Fintype.piFinset fun b => if b ∈ S then endChoices b else {FaceEnd.top}

/-- The sign of a face: `(-1)^{#lower endpoints}`. -/
def faceSign (S : Finset (GBranch T)) (F : GBranch T → FaceEnd T) : ℂ :=
  ∏ v ∈ S, if (F v).isUpper then 1 else -1

end Tree

section Layered

variable (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)

/-- The external top time of a free node: `min (up v) (𝔏_v + 1)`. -/
def topTime (v : GBranch LG.garden.tree) : ℝ := min (up v) ((LG.layer v.toNode : ℝ) + 1)

/-- The value of an endpoint of `v` at the branch times `t`. -/
def endVal (v : GBranch LG.garden.tree) (t : GBranch LG.garden.tree → ℝ) : FaceEnd LG.garden.tree → ℝ
  | .top => topTime LG up v
  | .parent q => t q
  | .floor => (LG.layer v.toNode : ℝ)
  | .child c => t c

/-- The cell of the endpoint `E` of `v` at the times `t` (exact partition, ties broken by `FaceEnd.rank`):
- upper `E`: `E` is the first minimizer of the upper endpoints and every lower endpoint is below it;
- lower `E`: `E` is the first maximizer of the lower endpoints and it is below every upper endpoint. -/
def faceCell (v : GBranch LG.garden.tree) (E : FaceEnd LG.garden.tree) (t : GBranch LG.garden.tree → ℝ) : Prop :=
  if E.isUpper then
    IsFirstMin (upSet v) (endVal LG up v t) FaceEnd.rank E ∧ ∀ D ∈ lowSet v, endVal LG up v t D < endVal LG up v t E
  else
    IsFirstMax (lowSet v) (endVal LG up v t) FaceEnd.rank E ∧ ∀ U ∈ upSet v, endVal LG up v t E < endVal LG up v t U

/-- The constraints of `kDomainFix LG up fix` that involve no selected time. -/
def restDomain (fix : GBranch LG.garden.tree → Option ℝ) (S : Finset (GBranch LG.garden.tree)) :
    Set (GBranch LG.garden.tree → ℝ) :=
  {t | ∀ b, b ∉ S →
    (fix b = none → (LG.layer b.toNode : ℝ) < t b ∧ t b < LG.layer b.toNode + 1 ∧ 0 < t b ∧ t b < up b) ∧
      ∀ b' : GBranch LG.garden.tree, b' ∉ S → b'.IsChildOf b → (fix b' = none ∨ fix b = none) → t b' < t b}

/-- The domain of the face `F`: the unselected constraints and, at each selected `v`, the cell of `F v`. -/
def faceDomain (fix : GBranch LG.garden.tree → Option ℝ) (S : Finset (GBranch LG.garden.tree))
    (F : GBranch LG.garden.tree → FaceEnd LG.garden.tree) : Set (GBranch LG.garden.tree → ℝ) :=
  {t | t ∈ restDomain LG up fix S ∧ ∀ v ∈ S, faceCell LG up v (F v) t}

/-- The face substitution: the time of a selected `v` becomes the value of its endpoint `F v`. -/
def faceSubst (S : Finset (GBranch LG.garden.tree)) (F : GBranch LG.garden.tree → FaceEnd LG.garden.tree)
    (t : GBranch LG.garden.tree → ℝ) : GBranch LG.garden.tree → ℝ :=
  fun b => if b ∈ S then endVal LG up b t (F b) else t b

end Layered

/-- The time frequency of the phase at `b` in `phaseProdOff`: `ω_b = π ζ_b δ L^{2γ} Ω_b`, so that the phase at `b`
is `exp(i ω_b t_b)`. -/
def nodeFreq (L γ δ : ℝ) {d : ℕ} (G : Garden w) (k : GNode G.tree → Mom d) (b : GBranch G.tree) : ℝ :=
  Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G k b

/-- A product of time phases with arbitrary real frequencies `θ`: `∏_b exp(i θ_b t_b)`. With `θ = offFreq …` it is
`phaseProdOff` (`phaseProdOff_eq_phaseVec`); a frequency shifted by an adjacent Fourier variable (the residual
reduction of supplement §8.1, `α_v = β_v + ξ_v`) is another instance. -/
def phaseVec {T : Fin w → TTree} (θ : GBranch T → ℝ) (t : GBranch T → ℝ) : ℂ :=
  ∏ b, Complex.exp (((θ b * t b : ℝ) : ℂ) * Complex.I)

/-- The frequencies of `phaseProdOff`: `ω_b` off `off`, `0` on `off`. -/
def offFreq (L γ δ : ℝ) {d : ℕ} (G : Garden w) (off : Finset (GBranch G.tree)) (k : GNode G.tree → Mom d)
    (b : GBranch G.tree) : ℝ :=
  if b ∈ off then 0 else nodeFreq L γ δ G k b

/-- The integral of the face `F` for the phase product `phaseVec θ`. -/
def faceIntegralFreq (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (θ : GBranch LG.garden.tree → ℝ)
    (S : Finset (GBranch LG.garden.tree)) (F : GBranch LG.garden.tree → FaceEnd LG.garden.tree) : ℂ :=
  ∫ τ : {b : GBranch LG.garden.tree // fixSel fix S b = none} → ℝ,
    (faceDomain LG up fix S F).indicator (phaseVec θ)
      (faceSubst LG up S F (LG.garden.extendFix (fixSel fix S) τ))

/-- The phase of the face `F`: `phaseProdOff` at the substituted times. It equals a constant (the phases of the
selected nodes sent to `top`/`floor`) times the phase product in which `ω_v` is added to the frequency of the parent or
child that `v` is sent to (`facePhase_eq`). -/
def facePhase (L γ δ : ℝ) {d : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (off : Finset (GBranch LG.garden.tree)) (k : GNode LG.garden.tree → Mom d) (S : Finset (GBranch LG.garden.tree))
    (F : GBranch LG.garden.tree → FaceEnd LG.garden.tree) (t : GBranch LG.garden.tree → ℝ) : ℂ :=
  phaseProdOff L γ δ LG.garden off k (faceSubst LG up S F t)

/-- The integral of the face `F`: the `kDomainFix`-indicator × `phaseProdOff` integrand with `fix` modified to
`fixSel fix S` and the selected times substituted by their endpoints (`faceSubst`), integrated over the remaining free
times. -/
def faceIntegral (L γ δ : ℝ) {d : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (k : GNode LG.garden.tree → Mom d) (S : Finset (GBranch LG.garden.tree))
    (F : GBranch LG.garden.tree → FaceEnd LG.garden.tree) : ℂ :=
  ∫ τ : {b : GBranch LG.garden.tree // fixSel fix S b = none} → ℝ,
    (faceDomain LG up fix S F).indicator (phaseProdOff L γ δ LG.garden off k)
      (faceSubst LG up S F (LG.garden.extendFix (fixSel fix S) τ))

end WaveTurbulence.Flower.FlFace
