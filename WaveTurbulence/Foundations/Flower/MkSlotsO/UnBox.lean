/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.UnTgt
public import WaveTurbulence.Foundations.Flower.MkSlotsG.PinGeo

/-! # B3s-HELPER8 / UNPIN (part 4): the general slot box inside main's slot box (or its closure)

`MkSlotsI.genBoxAt` fixes every pinned clock coordinate at its pin and asks main's `slotBox` when a clock is free.
When both clocks are pinned the box is one point; a pin lies in the closed window of its clock layer (β's
`MkSlotsG.fixCap_val`: every pinned branch is in layer `p`, pins are `s` or `t`; root clocks are pinned at `t`):

* `mem_closure_timeBoxGt_of_le`: `ts₁ ≤ ts₀` in `timeBox q q'` (`q' ≤ q`) lies in the closure of `timeBoxGt q q'`;
* `clkPin_window`: a pinned clock value lies in `[clkLayer, clkLayer + 1]`;
* `core_path_ne_nil`: the core of a non-root skeleton branch is not a garden root;
* **`genBoxAt_cpl_sub`**: on a couple slot `genBoxAt ⊆ timeBox q₀ q₁` (= `slotBox`);
* **`genBoxAt_chain_sub`**: on a chain slot `genBoxAt ⊆ closure (timeBoxGt q₀ q₁)` (two pins `(v₀, v₁)` have
  `v₁ ≤ v₀`: a pin at `t` of the lower clock is a garden-root pin, so the slot is a root chain, upper clock `t`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory Filter Topology
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-- A point of `timeBox q q'` with `ts₁ ≤ ts₀` lies in the closure of `timeBoxGt q q'` (`q' ≤ q`). -/
theorem mem_closure_timeBoxGt_of_le {q q' : ℝ} (hqq : q' ≤ q) {ts : Fin 2 → ℝ} (hts : ts ∈ timeBox q q')
    (hle : ts 1 ≤ ts 0) : ts ∈ closure (timeBoxGt q q') := by
  set y : Fin 2 → ℝ := ![q + 1, q'] with hy
  have hyb : y ∈ timeBox q q' := ⟨⟨by simp [hy], by simp [hy]⟩, ⟨by simp [hy], by simp [hy]⟩⟩
  set f : ℝ → (Fin 2 → ℝ) := fun r => ts + r • (y - ts) with hf
  have hfc : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hf0 : f 0 = ts := by simp [hf]
  have ht : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 ts) := by
    rw [← hf0]
    exact hfc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hconv := Represents.convex_timeBox q q'
  have hmem : f r ∈ timeBox q q' := by
    have e : f r = (1 - r) • ts + r • y := by
      simp only [hf]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [e]
    exact hconv hts hyb (by linarith [hr.2]) hr.1.le (by ring)
  refine ⟨hmem, ?_⟩
  simp only [hf, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hy, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h0 := hts.1
  have h1 := hts.2
  simp only [Set.mem_Icc] at h0 h1
  nlinarith [hr.1, hr.2]

/-- The core of a non-root skeleton branch is not a garden root. -/
theorem core_path_ne_nil {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree)
    (hb : b.1.2 ≠ []) : (D.coreBranch hS b).1.2 ≠ [] := by
  have hc : (D.coreBranch hS b).toNode =
      chainContextNode D hS b (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1)).toNode :=
    (chainContextNode_lone D hS b).symm
  have hp : (D.coreBranch hS b).1.2 = (attachedNode D hS b.toNode).1.2 ++
      (chainLoneLeaf (D.tree b) (nodeSign S.sig b.1)).1.2 := congrArg (fun z : GNode (D.forest hS) => z.1.2) hc
  have ha := MkSlots.IntGeo.attachedNode_nonroot D hS b.toNode hb
  intro h0
  rw [h0] at hp
  have h1 : (attachedNode D hS b.toNode).1.2 = [] := (List.append_eq_nil_iff.mp hp.symm).1
  rw [ha] at h1
  have h2 : ((D.coreBranch hS (b.toNode.parent hb)).child (b.toNode.1.2.getLast hb)).1.2 =
      (D.coreBranch hS (b.toNode.parent hb)).1.2 ++ [b.toNode.1.2.getLast hb] := rfl
  rw [h2] at h1
  simp at h1

section Box

variable {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
  (t s : ℝ) (p : ℕ)

/-- The clock layers of the slot `sl`. -/
abbrev clkL (sl : ReplacementSlot a.prime.skeleton) (i : Fin 2) : ℕ :=
  clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
    (argSrc a.prime.prime.1 sl i)

/-- **A pinned clock value lies in the closed window of its clock layer.** -/
theorem clkPin_window (hG : CapGeo (MkSlots.recLG a) J p) (hpat : CapPatValid (MkSlots.recLG a) J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf (MkSlots.recLG a).garden.tree, IsCapFlower (MkSlots.recLG a) J ℓ ∧ ℓ.1.1 = j)
    (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t) (y : ClkSrc a.prime.skeleton) (v : ℝ)
    (hv : clkPin (fun _ => t) (MkSlots.fixCore a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s)) y =
      some v) :
    (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) y : ℝ) ≤ v ∧
      v ≤ clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) y + 1 := by
  rcases y with j | b
  · simp only [clkPin, Option.some.injEq] at hv
    subst hv
    exact ⟨ht.1.le, ht.2.le⟩
  · have h := MkSlotsG.fixCap_val hG hpat hroot hs ht.2 hv
    exact ⟨h.1.le, h.2.1⟩

/-- **On a couple slot the general box lies in `timeBox q₀ q₁`.** -/
theorem genBoxAt_cpl_sub (hG : CapGeo (MkSlots.recLG a) J p) (hpat : CapPatValid (MkSlots.recLG a) J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf (MkSlots.recLG a).garden.tree, IsCapFlower (MkSlots.recLG a) J ℓ ∧ ℓ.1.1 = j)
    (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t) (q : SourcePair a.prime.skeleton) :
    genBoxAt p a J pat t s (.inl q) ⊆ timeBox (clkL a p (.inl q) 0 : ℝ) (clkL a p (.inl q) 1) := by
  intro ts hts
  obtain ⟨hpin, hfree⟩ := hts
  by_cases hf : ∃ i : Fin 2, clkPin (fun _ => t)
      (MkSlots.fixCore a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s))
      (argSrc a.prime.prime.1 (.inl q) i) = none
  · exact hfree hf
  · simp only [not_exists] at hf
    have hw : ∀ i : Fin 2, (clkL a p (.inl q) i : ℝ) ≤ ts i ∧ ts i ≤ clkL a p (.inl q) i + 1 := by
      intro i
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hf i)
      rw [hpin i v hv]
      exact clkPin_window a J pat t s p hG hpat hroot ht hs _ v hv
    exact ⟨hw 0, hw 1⟩

/-- **On a chain slot the general box lies in the closure of `timeBoxGt q₀ q₁`.** -/
theorem genBoxAt_chain_sub (hG : CapGeo (MkSlots.recLG a) J p) (hpat : CapPatValid (MkSlots.recLG a) J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf (MkSlots.recLG a).garden.tree, IsCapFlower (MkSlots.recLG a) J ℓ ∧ ℓ.1.1 = j)
    (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t) (b : GBranch a.prime.skeleton.tree)
    (hqq : clkL a p (.inr b) 1 ≤ clkL a p (.inr b) 0) :
    genBoxAt p a J pat t s (.inr b) ⊆ closure (timeBoxGt (clkL a p (.inr b) 0 : ℝ) (clkL a p (.inr b) 1)) := by
  intro ts hts
  obtain ⟨hpin, hfree⟩ := hts
  by_cases hf : ∃ i : Fin 2, clkPin (fun _ => t)
      (MkSlots.fixCore a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s))
      (argSrc a.prime.prime.1 (.inr b) i) = none
  · exact subset_closure (hfree hf)
  · simp only [not_exists] at hf
    obtain ⟨v0, hv0⟩ := Option.ne_none_iff_exists'.mp (hf 0)
    obtain ⟨v1, hv1⟩ := Option.ne_none_iff_exists'.mp (hf 1)
    have hw0 := clkPin_window a J pat t s p hG hpat hroot ht hs _ v0 hv0
    have hw1 := clkPin_window a J pat t s p hG hpat hroot ht hs _ v1 hv1
    have e0 := hpin 0 v0 hv0
    have e1 := hpin 1 v1 hv1
    refine mem_closure_timeBoxGt_of_le (by exact_mod_cast hqq) ⟨by rw [e0]; exact hw0, by rw [e1]; exact hw1⟩ ?_
    rw [e0, e1]
    -- the lower pin is `s`, or `t` at a garden-root core (then the slot is a root chain, upper pin `t`)
    have hv1' : MkSlots.fixCore a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s) b = some v1 := by
      simpa [argSrc, clkPin] using hv1
    have hsv : ∀ v, clkPin (fun _ => t)
        (MkSlots.fixCore a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s)) (argSrc a.prime.prime.1
          (.inr b) 0) = some v → s ≤ v := by
      intro v hv
      rcases hy : argSrc a.prime.prime.1 (.inr b) 0 with j | b'
      · rw [hy] at hv
        simp only [clkPin, Option.some.injEq] at hv
        rw [← hv]; exact hs.2.le
      · rw [hy] at hv
        rcases MkSlotsG.fixCap_value hv with h | ⟨h, -, -⟩
        · rw [h]
        · rw [h]; exact hs.2.le
    rcases MkSlotsG.fixCap_value hv1' with h | ⟨h, h0, -⟩
    · rw [h]; exact hsv v0 hv0
    · -- the core of `b` is a garden root: `b` is a skeleton root, its upper clock is the root clock at `t`
      have hbr : b.1.2 = [] := by
        by_contra hne
        exact core_path_ne_nil a.prime.data a.prime.prime.1 b hne h0
      have hy : argSrc a.prime.prime.1 (.inr b) 0 = .inl b.1.1 := by
        show (if (0 : Fin 2) = 0 then clkOfNode a.prime.skeleton b.toNode else .inr b) = .inl b.1.1
        rw [ite_eq_left rfl]
        have hbr' : b.toNode.1.2 = [] := hbr
        unfold clkOfNode
        rw [nodeToSlot, dite_eq_left hbr']
        rfl
      rw [hy] at hv0
      simp only [clkPin, Option.some.injEq] at hv0
      rw [h, ← hv0]

end Box

end WaveTurbulence.Flower.MkSlotsO
