/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapSlotGeo

/-! # B3s-HELPER8 / CAP: the general slot box of a nontrivial cap slot, and the STOP configuration

The general slot box `MkSlotsI.genSlotBox` of a cap pair (pinned clocks fixed at their pins, main's `slotBox` if a
clock is free), for a nontrivial cap slot `K`:

* `genBox_j0`: the chain clock `ts j0` of a point of the box is in `[p, p + 1]` (a pin is `s` or `t`; a free clock
  is in its closed layer window, B3s's `slotBox_j0`);
* `genBox_root`: if the configuration pins the root (`rootTerm`, or `penTerm` with `|X.lonePath| = 2`) and the chain
  clock is pinned (a root clock at `t`, or a core pin), then `ts j0 ≥ rootPinVal` — the clock range on which β's
  `capSlotPat_const` gives the constant value;
* **`CapPenFree`** (the STOP configuration): the configuration pins the root and the chain clock is FREE;
  `capPenFree_spec`: then the pattern of the chain's tree is `dParent`, `|X.lonePath| = 2` (the root of the chain is
  the parent of the capped flower parent, pinned at `s`), and the chain's skeleton leaf is not a skeleton root. The
  box then contains points with `p ≤ ts j0 < s`, where the relaxed kernel depends on `ts j0` (free branches below
  the pinned top keep `τ < ts j0`), outside D3's root-pinning box `t' ≤ ts 0` (`t' > s`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.LGSpine WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo
  WaveTurbulence.Flower.ProtWhole WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsB WaveTurbulence.Represents

namespace WaveTurbulence.Flower.MkSlotsO

namespace CapK

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

/-- The pin of the chain clock of the cap pair. -/
abbrev clkJ0 (pat : Fin w → FixPat) (t s : ℝ) : Option ℝ :=
  MkSlotsI.clkPin (fun _ => t) (fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s))
    (argSrc hS (.inl q) K.j0)

/-- The general slot box of the cap pair. -/
abbrev capGenBox (pat : Fin w → FixPat) (t s : ℝ) : Set (Fin 2 → ℝ) :=
  MkSlotsI.genSlotBox p (fun b => layer (D.coreBranch hS b).toNode) hS (fun _ => t)
    (fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s)) (.inl q)

theorem clkJ0_val (pat : Fin w → FixPat) (t s v : ℝ) (h : clkJ0 K layer hLayer pat t s = some v) :
    v = s ∨ v = t := by
  unfold clkJ0 at h
  generalize argSrc hS (.inl q) K.j0 = y at h
  rcases y with j | β
  · simp only [MkSlotsI.clkPin, Option.some.injEq] at h
    exact Or.inr h.symm
  · exact fixCap_val h

include hGeo in
/-- **The chain clock of a point of the general slot box is in `[p, p + 1]`.** -/
theorem genBox_j0 (pat : Fin w → FixPat) (t s : ℝ) (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
    (ts : Fin 2 → ℝ) (hts : ts ∈ capGenBox (q := q) (J := J) layer hLayer (p := p) pat t s) :
    ts K.j0 ∈ Icc (p : ℝ) (p + 1) := by
  obtain ⟨hpin, hfree⟩ := hts
  cases h : clkJ0 K layer hLayer pat t s with
  | none => exact K.slotBox_j0 layer hLayer hGeo ts (hfree ⟨K.j0, h⟩)
  | some v =>
    rw [hpin K.j0 v h]
    rcases clkJ0_val K layer hLayer pat t s v h with rfl | rfl
    · exact ⟨hps.le, by linarith⟩
    · exact ⟨by linarith, htp.le⟩

/-- `rootTerm` arises only at a chain whose root is a garden root. -/
theorem rootTerm_u (pat : Fin w → FixPat) (h : CapP.cfgPat K layer hLayer pat = .rootTerm) : K.u.2 = [] := by
  unfold CapP.cfgPat objCfg at h
  rcases hp : pat K.u.1 with _ | _ | _ | i <;> simp only [hp] at h
  · split_ifs at h
  · by_cases h1 : PortFlower (layeredReconstruction D hS layer hLayer) J K.X K.u
    · by_cases h2 : K.u.2 = [] ∧ 2 ≤ K.X.lonePath.length
      · exact h2.1
      · simp only [h1, h2, ↓reduceIte] at h
        cases h
    · simp only [h1, ↓reduceIte] at h
      split_ifs at h
  · split_ifs at h
  · split_ifs at h

/-- `penTerm` arises only for the `dParent` pattern. -/
theorem penTerm_pat (pat : Fin w → FixPat) (h : CapP.cfgPat K layer hLayer pat = .penTerm) :
    pat K.u.1 = FixPat.dParent := by
  unfold CapP.cfgPat objCfg at h
  rcases hp : pat K.u.1 with _ | _ | _ | i <;> simp only [hp] at h
  · split_ifs at h
  · split_ifs at h
  · rfl
  · split_ifs at h

/-- A chain whose root is a garden root has the root clock `t`. -/
theorem clkJ0_root (pat : Fin w → FixPat) (t s : ℝ) (hu : K.u.2 = []) : clkJ0 K layer hLayer pat t s = some t := by
  have hl : K.leaf.toNode.1.2 = [] := (MkMark.inflatedPosition_nil_iff S D.tree K.leaf.toNode).1 hu
  unfold clkJ0
  rw [K.arg, clkOfNode_root' _ hl]
  rfl

/-- **On a root-pinning configuration with a pinned chain clock, the chain clock is at least the root pin.** -/
theorem genBox_root (pat : Fin w → FixPat) (t s : ℝ) (hst : s < t)
    (hroot : (CapP.cfgPat K layer hLayer pat).pinsRoot K.X = true)
    (hpinned : clkJ0 K layer hLayer pat t s ≠ none) (ts : Fin 2 → ℝ)
    (hts : ts ∈ capGenBox (q := q) (J := J) layer hLayer (p := p) pat t s) :
    rootPinVal (CapP.cfgPat K layer hLayer pat) s t ≤ ts K.j0 := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hpinned
  rw [hts.1 K.j0 v hv]
  rcases CapP.objCfg_cases K layer hLayer pat with h | h | h | ⟨i, h⟩
  · rw [h] at hroot; simp [ProtCfg.pinsRoot] at hroot
  · rw [clkJ0_root K layer hLayer pat t s (rootTerm_u K layer hLayer pat h)] at hv
    cases hv
    rw [h]; unfold rootPinVal; simp
  · rw [h]; unfold rootPinVal; simp only [↓reduceIte]
    rcases clkJ0_val K layer hLayer pat t s v hv with rfl | rfl
    · exact le_rfl
    · exact hst.le
  · rw [h] at hroot; simp [ProtCfg.pinsRoot] at hroot

/-- **The STOP configuration**: the configuration pins the root and the chain clock is free. -/
def CapPenFree (pat : Fin w → FixPat) (t s : ℝ) : Prop :=
  (CapP.cfgPat K layer hLayer pat).pinsRoot K.X = true ∧ clkJ0 K layer hLayer pat t s = none

/-- **The STOP configuration, explicitly**: pattern `dParent` on the chain's tree, `|X.lonePath| = 2` (the root of
the chain is the parent of the capped flower parent), the chain's skeleton leaf is not a skeleton root. -/
theorem capPenFree_spec (pat : Fin w → FixPat) (t s : ℝ) (h : CapPenFree K layer hLayer pat t s) :
    CapP.cfgPat K layer hLayer pat = .penTerm ∧ pat K.u.1 = FixPat.dParent ∧ K.X.lonePath.length = 2 ∧
      K.u.2 ≠ [] := by
  obtain ⟨hroot, hfree⟩ := h
  have hu : K.u.2 ≠ [] := fun hu => by
    rw [clkJ0_root K layer hLayer pat t s hu] at hfree; cases hfree
  rcases CapP.objCfg_cases K layer hLayer pat with hc | hc | hc | ⟨i, hc⟩
  · rw [hc] at hroot; simp [ProtCfg.pinsRoot] at hroot
  · exact absurd (rootTerm_u K layer hLayer pat hc) hu
  · refine ⟨hc, penTerm_pat K layer hLayer pat hc, ?_, hu⟩
    rw [hc] at hroot
    have h2 := two_le_lonePath K.ne
    have h3 : K.X.lonePath.dropLast.dropLast = [] := by simpa [ProtCfg.pinsRoot] using hroot
    have h4 := congrArg List.length h3
    simp only [List.length_dropLast, List.length_nil] at h4
    omega
  · rw [hc] at hroot; simp [ProtCfg.pinsRoot] at hroot

end CapK

end WaveTurbulence.Flower.MkSlotsO
