/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.CapPSup

/-! # B3s-HELPER3 (B5): a nontrivial cap slot under a pattern

For a nontrivial cap slot (B3s's `CapSide`) of the reconstruction with the pattern pins `fixCap … pat`, the relaxed
(R187) slot kernel at the cap momentum is `c₀ · capCfgKer … (ts j0)` (`CapP.capSlot_kernel_pat`, `CapP.cfgKer_m1`),
with `cfg = objCfg … pat X u` (`term`, `rootTerm`, `penTerm` or `termChild i`, valid by D2b). Then, from D3's
`ProtBoundAt`:
* `cfg` does not pin the root (`pinsRoot = false`): the superposition on the whole slot box (`capSlotPat_sup`, the twin
  of B3s's `CapSide.capSlot_sup`);
* `cfg` pins the root (`rootTerm`: root at `t`; `penTerm` with `Xp = nil`: root at `s`): every pin is at most the root
  pin `rootPinVal cfg s t` (`pinsRoot_fix`), so the kernel is CONSTANT in `ts j0 ≥ rootPinVal` (`kernelProt_up_const`)
  and bounded by D3's bound (`capCfg_pointwise` at `t`): `capSlotPat_const`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.VineEstS3.FS WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsB

/-! ### The pins of a root-pinning configuration -/

/-- The root pin of a configuration that pins the root: `s` for `penTerm`, `t` otherwise. -/
def rootPinVal (cfg : ProtCfg) (s t : ℝ) : ℝ := if cfg = .penTerm then s else t

theorem rootPinVal_le (cfg : ProtCfg) {s t : ℝ} (hst : s ≤ t) : rootPinVal cfg s t ≤ t := by
  unfold rootPinVal
  split_ifs
  · exact hst
  · exact le_rfl

theorem lookup_some_mem {β : Type*} (a : Path) (l : List (Path × β)) (v : β) (h : l.lookup a = some v) :
    ∃ k, (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    obtain ⟨k, v'⟩ := hd
    rw [lookup_cons'] at h
    split_ifs at h with hk
    · refine ⟨k, ?_⟩
      rw [Option.some_inj] at h
      rw [h]
      exact List.mem_cons_self
    · obtain ⟨k', hk'⟩ := ih h
      exact ⟨k', List.mem_cons_of_mem _ hk'⟩

/-- **At a root-pinning configuration the root is pinned at `rootPinVal`, and every pin is at most `rootPinVal`.** -/
theorem pinsRoot_fix {cfg : ProtCfg} {X : RegChain} (hr : cfg.pinsRoot X = true) (s t up : ℝ) (hst : s ≤ t)
    {T : Fin 1 → TTree} :
    (∀ b : GBranch T, b.1.2 = [] → cfg.fix X s t up b = some (rootPinVal cfg s t)) ∧
      ∀ (b : GBranch T) (v : ℝ), cfg.fix X s t up b = some v → v ≤ rootPinVal cfg s t := by
  have h0 : ∀ b : GBranch T, b.1.1.val = 0 := fun b => Fin.val_eq_zero b.1.1
  have hfix : ∀ b : GBranch T, cfg.fix X s t up b = (cfg.pins X s t up).lookup b.1.2 := fun b => by
    unfold ProtCfg.fix
    simp only [h0 b, ↓reduceIte]
  cases cfg with
  | root =>
    refine ⟨fun b hb => ?_, fun b v hv => ?_⟩
    · rw [hfix, hb]
      simp [ProtCfg.pins, rootPinVal]
    · rw [hfix] at hv
      obtain ⟨k, hk⟩ := lookup_some_mem _ _ _ hv
      simp only [ProtCfg.pins, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hk
      rw [hk.2]
      simp [rootPinVal]
  | rootTerm =>
    refine ⟨fun b hb => ?_, fun b v hv => ?_⟩
    · rw [hfix, hb]
      simp [ProtCfg.pins, rootPinVal]
    · rw [hfix] at hv
      obtain ⟨k, hk⟩ := lookup_some_mem _ _ _ hv
      simp only [ProtCfg.pins, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hk
      simp only [rootPinVal, reduceCtorEq, ↓reduceIte]
      rcases hk with hk | hk
      · rw [hk.2]
      · rw [hk.2]; exact hst
  | penTerm =>
    have hXp : X.lonePath.dropLast.dropLast = [] := by
      simpa [ProtCfg.pinsRoot] using hr
    refine ⟨fun b hb => ?_, fun b v hv => ?_⟩
    · rw [hfix, hb]
      simp [ProtCfg.pins, rootPinVal, hXp]
    · rw [hfix] at hv
      obtain ⟨k, hk⟩ := lookup_some_mem _ _ _ hv
      simp only [ProtCfg.pins, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hk
      simp only [rootPinVal, ↓reduceIte]
      rcases hk with hk | hk
      · rw [hk.2]
      · rw [hk.2]
  | none => simp [ProtCfg.pinsRoot] at hr
  | term => simp [ProtCfg.pinsRoot] at hr
  | termChild i => simp [ProtCfg.pinsRoot] at hr
  | trace => simp [ProtCfg.pinsRoot] at hr

namespace CapP

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

theorem cfgPat_valid {pat : Fin w → FixPat} (hpat : CapPatValid (layeredReconstruction D hS layer hLayer) J pat p) :
    (cfgPat K layer hLayer pat).Valid K.X (K.Dq layer hLayer).T1 p := by
  rw [K.capT1_eq layer hLayer]
  exact objCfg_valid_objTree hpat (K.capStem layer hLayer)

/-- The root branch of the paired tree. -/
def rootT1 : GBranch (K.Dq layer hLayer).T1.garden.tree :=
  ⟨((0 : Fin 1), []), by
    show [] ∈ (K.X.plug K.ζ .leaf).branching
    exact prefix_lone_branching K.X K.ζ List.nil_prefix (lonePath_ne_nil K.ne).symm⟩

end CapP

end WaveTurbulence.Flower.MkSlotsB
