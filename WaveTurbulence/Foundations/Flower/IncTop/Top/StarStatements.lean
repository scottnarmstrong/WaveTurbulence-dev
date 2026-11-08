/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1W.Defs

/-! Ported by source from C2-B-TOP `C2BTop.StarStatements` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # C2-B-TOP: four-momentum (star) node weights, statement layer

Generalization of research-internal's `TopIncoherentDecayGate` requested by wt-orch (FINDING-STEMROW,
C2-E-B): the node weight at a weighted node `a` is a Fourier-presented function `ω a` of the four
momenta of its star `(k_a, k_{a0}, k_{a1}, k_{a2})` (a leaf reads `k_a` in all four slots), not only of
`k_a`.  The weighted set `S` and the weights are arbitrary data chosen after the regular object; each
weight has a Fourier presentation on `(Mom d)^4` whose `30d`-th moment in the TOTAL frequency
`ξ₀ + ξ₁ + ξ₂ + ξ₃` (the dual of the simultaneous root shift `y_s ↦ y_s + k`) is at most `c a`.
Translation-invariant weights (functions of momentum differences, e.g. `χ₀(Ω_b/M)` written on the
decoration manifold) have zero total frequency and cost only their mass.

* `Star d = (Mom d)^4` (Euclidean), `starNode`, `starMomenta`, `starWeight S ω κ = ∏_{a ∈ S} ω a (star κ a)`.
* `starMoment J M`, `StarPresented J ω c`.
* `coupleLeavesStar` / `treeLeavesStar`: research-internal's `kernelLeavesW` with multiplier `starWeight`.
* `StarIncoherentDecayAt P` / `StarIncoherentDecayGate`: main's `LeafwiseIncoherentDecayAt` for the
  star-weighted kernels at the cost `∏_{a ∈ S} c a`.

Lower-layer blindness is a consumer-side (class-commonness) requirement; the analytic gate holds for
arbitrary weights, so it is not a hypothesis here. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open Finset
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W

/-- The four momenta of a star. -/
abbrev Star (d : ℕ) := PiLp 2 (fun _ : Fin 4 => Mom d)

/-- The `s`-th node of the star of `a`: `a` itself for `s = 0` and its child `s - 1` otherwise;
a leaf has no children and reads itself in every slot. -/
def starNode {w : ℕ} {T : Fin w → TTree} (a : GNode T) (s : Fin 4) : GNode T :=
  if h : a.1.2 ∈ (T a.1.1).branching then
    Fin.cases a (fun j : Fin 3 => GBranch.child (⟨a.1, h⟩ : GBranch T) j) s
  else a

/-- The star momenta `(κ a, κ a0, κ a1, κ a2)`. -/
def starMomenta {w d : ℕ} {T : Fin w → TTree} (κ : GNode T → Mom d) (a : GNode T) : Star d :=
  WithLp.toLp 2 (fun s => κ (starNode a s))

/-- The star node weight of a decoration: `∏_{a ∈ S} ω a (κ a, κ a0, κ a1, κ a2)`. -/
def starWeight {w d : ℕ} {T : Fin w → TTree} (S : Finset (GNode T)) (ω : GNode T → Star d → ℂ)
    (κ : GNode T → Mom d) : ℂ :=
  ∏ a ∈ S, ω a (starMomenta κ a)

/-- The total frequency `ξ₀ + ξ₁ + ξ₂ + ξ₃`, dual to the simultaneous root shift of the star. -/
def starRootFrequency {d : ℕ} (ξ : Star d) : Mom d := ∑ s, ξ s

/-- `J`-th moment of a star presentation in the total frequency. -/
def starMoment {d : ℕ} {α : Type*} [MeasurableSpace α] (J : ℕ)
    (M : Cut2A.SpatialMeasure (Star d) α) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal ((1 + ‖starRootFrequency (M.frequency a)‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ

/-- `ω` has a Fourier presentation on `(Mom d)^4` with `J`-th total-frequency moment at most `c`. -/
def StarPresented {d : ℕ} (J : ℕ) (ω : Star d → ℂ) (c : ℝ) : Prop :=
  ∃ (α : Type) (_ : MeasurableSpace α) (M : Cut2A.SpatialMeasure (Star d) α),
    starMoment J M ≤ ENNReal.ofReal c ∧ ∀ y, M.value y = ω y

/-- Star-weighted leafwise couple kernel. -/
def coupleLeavesStar (L γ δ : ℝ) {d : ℕ} (LG : LayeredGarden 2) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Star d → ℂ) (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0 (starWeight S ω)

/-- Star-weighted leafwise tree kernel. -/
def treeLeavesStar (L γ δ : ℝ) {d : ℕ} (LG : LayeredGarden 1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Star d → ℂ) (H : LeafProfiles 1 d) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 (starWeight S ω)

/-- **C2-B-TOP, star form**: main's `LeafwiseIncoherentDecayAt` for star-weighted kernels, at the cost
`∏_{a ∈ S} c a` (the weighted set, weights and constants are arbitrary data). -/
def StarIncoherentDecayAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ (LG : LayeredGarden 2),
      Q.Decodes LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
      1 ≤ LG.incoherency Q.links →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star P.d → ℂ)
        (c : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * P.d) (ω a) (c a)) →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => coupleLeavesStar P.L P.γ P.δ LG S ω H (ts 0) (ts 1) k) ≤
        (∏ a ∈ S, ENNReal.ofReal (c a)) * regBound P n (LG.incoherency Q.links) *
          ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ (LG : LayeredGarden 1),
      X.DecodesTree LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q →
      (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
      1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star P.d → ℂ)
        (c : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * P.d) (ω a) (c a)) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => treeLeavesStar P.L P.γ P.δ LG S ω H (ts 0) (ts 1) k) ≤
        (∏ a ∈ S, ENNReal.ofReal (c a)) *
          regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) *
          ENNReal.ofReal (leafSizeProduct LG B))

/-- The gate form (all thresholds before the record `P`). -/
def StarIncoherentDecayGate : Prop := WTPrefix StarIncoherentDecayAt

end WaveTurbulence.Flower.IncTop