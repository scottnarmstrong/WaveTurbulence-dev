/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBRModes
public import WaveTurbulence.Foundations.Flower.MkSlotsB.ROne
public import WaveTurbulence.Foundations.Flower.MkSlots.SliceSb

/-! # B3s-HELPER3 B2 (7): the relaxed pinned VINE-B♯ specializes to MkSlotsW's (`_one`)

When every constraint that the relaxed domains drop holds strictly at the pins — pins strictly inside their layer
windows, strictly below the upper times, strictly monotone along skeleton ancestry (`StrictPinsS`) — the relaxed and
unpinned domains agree on the pinned slices: of the skeleton (`coreTimeDomainWR = coreTimeDomainW`,
`mem_coreTimeDomainWR_iff_of_strict`) and of `G_sb` (`splicedTimeDomainFix = splicedTimeDomain`,
`mem_splicedTimeDomainFix_iff_of_edges`, whose hypotheses also follow from `MkSlots.AdmissibleSb`). Hence
`skelValWFR = MkSlotsW.skelValWF`, `outerValMμD (splicedTimeDomainFix …) = outerValMμ …`, and
`hasSum_skelValWFR_outerValMμD` becomes `MkSlotsW.hasSum_skelValWF_outerValMμ` (with `hW` replaced by `StrictPinsS`,
`hbox` on `coreTimeDomainW` as in MkSlotsW): **`hasSum_skelValWFR_outerValMμD_one`**.

Why not "no adjacent pins": a `G_sb` parent–child pair need not be a skeleton parent–child pair — the `G_sb` children
of a hinge `u1^j` are the boundary nodes `u21^j`, `u22^j`, children of the (interior, unpinned) lower joint `u2^j` in
the skeleton. Pins at a hinge and at its boundary node `u21^j` are not adjacent in the skeleton, yet the unpinned
`splicedTimeDomain` imposes `τ'(u21) < τ'(u1)` on them, which the relaxed `splicedTimeDomainFix` drops; equal values
`fix u21 = fix u1` make the unpinned slice empty and the relaxed one not. So the strictness is needed along `G_sb`
edges, i.e. along skeleton ANCESTRY through the units (`br_isAncB_of_isChildOf`); `StrictPinsS.smono` provides it.
Skeleton-adjacency alone suffices for the skeleton side (`coreTimeDomainWR` only drops parent-clock constraints). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsB
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkSlots (fixMeasure outerValMμ outerValMμD outerValMμ_eq_D AdmissibleSb)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW unitKernelMGW)

variable {w d : ℕ}

/-! ## Strict pins -/

/-- Pins strictly inside their windows, strictly below the upper time of their tree, strictly monotone along
ancestry (branch layering). -/
structure StrictPinsS {tree : Fin w → TTree} (layer : GBranch tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch tree → Option ℝ) : Prop where
  val : ∀ b v, fix b = some v → (layer b : ℝ) < v ∧ v < layer b + 1 ∧ v < tt b.1.1
  smono : ∀ x y v v', fix x = some v → fix y = some v' → IsAncB y x → v < v'

theorem StrictPinsS.relax {tree : Fin w → TTree} {layer : GBranch tree → ℕ} {tt : Fin w → ℝ}
    {fix : GBranch tree → Option ℝ} (h : StrictPinsS layer tt fix) : RelaxPinsS layer tt fix :=
  ⟨fun b v hv => ⟨(h.val b v hv).1, (h.val b v hv).2.1.le, (h.val b v hv).2.2.le⟩,
    fun x y v v' hx hy ha => (h.smono x y v v' hx hy ha).le⟩

/-- Pins strictly inside their windows and below the upper times, no two of them comparable (e.g. at most one per
tree), are strict. -/
theorem StrictPinsS.of_incomparable {tree : Fin w → TTree} (layer : GBranch tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch tree → Option ℝ)
    (hval : ∀ b v, fix b = some v → (layer b : ℝ) < v ∧ v < layer b + 1 ∧ v < tt b.1.1)
    (hnc : ∀ x y : GBranch tree, IsAncB y x → fix x = none ∨ fix y = none) : StrictPinsS layer tt fix := by
  refine ⟨hval, fun x y v v' hx hy ha => ?_⟩
  rcases hnc x y ha with h | h
  · rw [h] at hx; exact absurd hx (by simp)
  · rw [h] at hy; exact absurd hy (by simp)

/-- **On the pinned slice, under strict pins, the relaxed core domain is the unpinned one.** -/
theorem mem_coreTimeDomainWR_iff_of_strict {tree : Fin w → TTree} (layer : GBranch tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch tree → Option ℝ) (hP : StrictPinsS layer tt fix) (τ : GBranch tree → ℝ) (hτ : OnSlice fix τ) :
    τ ∈ coreTimeDomainWR layer tt fix ↔ τ ∈ coreTimeDomainW layer tt := by
  refine mem_coreTimeDomainWR_iff layer tt fix τ (fun b hb => ?_) (fun b hb hcf => ?_)
  · obtain ⟨v, hv, hτv⟩ := slice_val hτ hb
    have := hP.val b v hv
    rw [hτv]
    exact ⟨this.1, this.2.1, lt_of_le_of_lt (Nat.cast_nonneg _) this.1⟩
  · obtain ⟨v, hv, hτv⟩ := slice_val hτ hb
    rw [hτv]
    rcases hs : nodeToSlot b.toNode with j | ⟨c, i⟩
    · have hpc : parentClockWith tt τ b.toNode = tt j := by unfold parentClockWith; rw [hs]
      have hlt := (hP.val b v hv).2.2
      rw [show b.1.1 = j from index_of_slot_root b.toNode j hs] at hlt
      rw [hpc]
      exact hlt
    · have hc : fix c ≠ none := by
        intro h; apply hcf; unfold clockFree; rw [hs]; exact h
      obtain ⟨v', hv', hτv'⟩ := slice_val hτ hc
      have hpc : parentClockWith tt τ b.toNode = τ c := by unfold parentClockWith; rw [hs]
      rw [hpc, hτv']
      exact hP.smono b c v v' hv hv'
        (IsAncB.of_isChildOf (isChildOf_of_toNode_eq (node_eq_child_of_slot b.toNode c i hs)))

/-- **On the pinned slice the relaxed spliced domain is the unpinned one** when every pin lies in its closed window
below its root time and every pinned parent–child pair is strictly ordered (vacuous without adjacent pins). -/
theorem mem_splicedTimeDomainFix_iff_of_edges (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ)
    (hval : ∀ v x, fix v = some x → x ∈ Set.Icc (layer v : ℝ) (layer v + 1) ∧ x < rt v.1.1)
    (hedge : ∀ v u x y, v.IsChildOf u → fix v = some x → fix u = some y → x < y)
    (τ : GBranch G.tree → ℝ) (hτ : OnSlice fix τ) :
    τ ∈ splicedTimeDomainFix G layer rt fix ↔ τ ∈ splicedTimeDomain G layer rt := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun v u hvu => ?_, fun v => ?_⟩
    · rcases hv : fix v with _ | x
      · exact (h1 v hv).1
      · rw [hτ v x hv]; exact (hval v x hv).1
    · rcases hv : fix v with _ | x
      · exact h2 v u hvu (Or.inl hv)
      · rcases hu : fix u with _ | y
        · exact h2 v u hvu (Or.inr hu)
        · rw [hτ v x hv, hτ u y hu]; exact hedge v u x y hvu hv hu
    · rcases hv : fix v with _ | x
      · exact (h1 v hv).2
      · rw [hτ v x hv]; exact (hval v x hv).2
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun v _ => ⟨h1 v, h3 v⟩, fun v u hvu _ => h2 v u hvu⟩

/-- `MkSlots.AdmissibleSb` (pins in their windows below the root times, no pinned parent–child pair) gives the
hypotheses of `mem_splicedTimeDomainFix_iff_of_edges`. -/
theorem AdmissibleSb.edges {G : Garden w} {layer : GBranch G.tree → ℕ} {rt : Fin w → ℝ}
    {fix : GBranch G.tree → Option ℝ} (hA : AdmissibleSb G layer rt fix) :
    ∀ v u x y, v.IsChildOf u → fix v = some x → fix u = some y → x < y := by
  intro v u x y hvu hv hu
  rcases hA.adj v u hvu with h | h
  · rw [h] at hv; exact absurd hv (by simp)
  · rw [h] at hu; exact absurd hu (by simp)

/-! ## Congruence on a.e. equal domains -/

section Congr

variable {S : Garden w} {J : Type} [Fintype J]

theorem skelValWD_congr_ae (blk : J → CLBlock S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d)
    {A₁ A₂ : Set (GBranch S.tree → ℝ)} (fixS : GBranch S.tree → Option ℝ)
    (hA : ∀ᵐ τ ∂(fixMeasure fixS), τ ∈ A₁ ↔ τ ∈ A₂) :
    skelValWD blk hS L γ δ base roots tt selSk Fs A₁ fixS = skelValWD blk hS L γ δ base roots tt selSk Fs A₂ fixS := by
  unfold skelValWD
  congr 1
  refine tsum_congr fun κ => ?_
  unfold skelTermWD
  split_ifs
  · rw [integral_congr_ae (indicator_ae_eq_of_ae_iff hA _)]
  · rfl

theorem outerValMμD_congr_ae (G : Garden w) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) {Dom₁ Dom₂ : Set (GBranch G.tree → ℝ)}
    (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℂ) (hS : G.IsPlain)
    (μ : Measure (GBranch G.tree → ℝ)) (hD : ∀ᵐ τ ∂μ, τ ∈ Dom₁ ↔ τ ∈ Dom₂)
    (amp : ReplacementSlot G → Mom d → ℂ) (frq : ReplacementSlot G → Fin 2 → ℤ)
    {J' : Type} [Fintype J'] [DecidableEq J'] (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J')
    (hclk : J' → Fin 3 → ClkSrc G) (hmom : J' → Fin 4 → GNode G.tree)
    (HkM : J' → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) :
    outerValMμD G L γ δ base roots tt Dom₁ hinges Zw hS μ amp frq route hclk hmom HkM =
      outerValMμD G L γ δ base roots tt Dom₂ hinges Zw hS μ amp frq route hclk hmom HkM := by
  unfold outerValMμD
  congr 1
  refine tsum_congr fun z => ?_
  rw [integral_congr_ae (indicator_ae_eq_of_ae_iff hD _)]

end Congr

/-! ## The `_one` specialization -/

variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

/-- **Under strict pins the relaxed skeleton value is MkSlotsW's.** -/
theorem skelValWFR_eq_skelValWF_of_strict (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d) (fixS : GBranch S.tree → Option ℝ)
    (hP : StrictPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS) :
    skelValWFR blk D hS L γ δ base roots tt layer selSk Fs fixS =
      MkSlotsW.skelValWF blk D hS L γ δ base roots tt layer selSk Fs fixS := by
  unfold skelValWFR
  rw [← skelValWD_coreTimeDomainW]
  refine skelValWD_congr_ae blk hS L γ δ base roots tt selSk Fs fixS ?_
  filter_upwards [ae_onSlice fixS] with τ hτ
  exact mem_coreTimeDomainWR_iff_of_strict _ tt fixS hP τ hτ

/-- **Under strict pins the relaxed outer form is MkSlotsW's** (`outerValMμ`, main's `splicedTimeDomain`). -/
theorem outerValMμD_splicedTimeDomainFix_eq_of_strict (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (tt : Fin w → ℝ) (fixS : GBranch S.tree → Option ℝ)
    (hP : StrictPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (hinges : Finset (GBranch Gsb.tree))
    (Zw : GenDecoration Gsb d roots 0 → ℂ) (hSb : Gsb.IsPlain)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    {J' : Type} [Fintype J'] [DecidableEq J'] (route : ReplacementSlot Gsb → Fin 2 → ClkSrc Gsb ⊕ J')
    (hclk : J' → Fin 3 → ClkSrc Gsb) (hmom : J' → Fin 4 → GNode Gsb.tree)
    (HkM : J' → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) :
    outerValMμD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)))
        hinges Zw hSb (fixMeasure (fun c => fixS (Φ.br c))) amp frq route hclk hmom HkM =
      outerValMμ Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) hinges Zw hSb
        (fixMeasure (fun c => fixS (Φ.br c))) amp frq route hclk hmom HkM := by
  rw [outerValMμ_eq_D]
  refine outerValMμD_congr_ae Gsb L γ δ base roots tt hinges Zw hSb _ ?_ amp frq route hclk hmom HkM
  filter_upwards [ae_onSlice (fun c => fixS (Φ.br c))] with τ hτ
  refine mem_splicedTimeDomainFix_iff_of_edges Gsb _ tt _ (fun c x hx => ?_) (fun v u x y hvu hv hu => ?_) τ hτ
  · have h := hP.val _ x hx
    rw [← br_index Φ c]
    exact ⟨⟨h.1.le, h.2.1.le⟩, h.2.2⟩
  · exact hP.smono _ _ x y hv hu (br_isAncB_of_isChildOf Φ hvu)

open scoped Classical in
/-- **`_one`: under strict pins the relaxed pinned VINE-B♯ is MkSlotsW's statement** — exactly the conclusion of
`MkSlotsW.hasSum_skelValWF_outerValMμ`, with its binders (in its order, `hbox` on `coreTimeDomainW`) except `hW`
replaced by `StrictPinsS` (which implies `hW`). -/
theorem hasSum_skelValWFR_outerValMμD_one {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}
    (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hP : StrictPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμ Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd)
        (fun z => (Zw z : ℂ)) hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base))
      (MkSlotsW.skelValWF blk D hS L γ δ base roots tt layer selSk Fs fixS) := by
  have h := hasSum_skelValWFR_outerValMμD Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp fixS hU hP.relax
    (fun τ hτ hR => hbox τ ((mem_coreTimeDomainWR_iff_of_strict _ tt fixS hP τ hτ.pin).1 hR))
  rw [skelValWFR_eq_skelValWF_of_strict D hS L γ δ base roots tt layer selSk Fs fixS hP] at h
  simp_rw [outerValMμD_splicedTimeDomainFix_eq_of_strict Φ D hS layer tt fixS hP] at h
  exact h

end WaveTurbulence.Flower.MkSlotsB
