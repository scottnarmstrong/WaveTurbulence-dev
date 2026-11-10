/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
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

end Layered

/-- A product of time phases with arbitrary real frequencies `θ`: `∏_b exp(i θ_b t_b)`. With `θ = offFreq …` it is
`phaseProdOff` (`phaseProdOff_eq_phaseVec`); a frequency shifted by an adjacent Fourier variable (the residual
reduction of supplement §8.1, `α_v = β_v + ξ_v`) is another instance. -/
def phaseVec {T : Fin w → TTree} (θ : GBranch T → ℝ) (t : GBranch T → ℝ) : ℂ :=
  ∏ b, Complex.exp (((θ b * t b : ℝ) : ℂ) * Complex.I)

end WaveTurbulence.Flower.FlFace
