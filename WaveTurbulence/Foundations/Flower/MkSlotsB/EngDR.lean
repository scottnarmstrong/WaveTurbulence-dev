/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.EngDVN
public import WaveTurbulence.Foundations.Flower.MkSlotsB.EngDShift
public import WaveTurbulence.Foundations.Flower.FinalMKFine.LBPin

/-! # B3s-HELPER3 B3 (5): the domain-generic engine on the relaxed pinned domain

* `hHkPropD_of_hHkProp`: main's unpinned hinge hypothesis `HHkProp` gives `HHkPropD` on the relaxed pinned domain
  `splicedTimeDomainFix π.Gsb π.layer tt π.fix`, when the pins lie in their windows and below the root times (`hpv`),
  are monotone along pinned parent–child pairs (`hpm`), and the hinge clocks at branches are free (`hclk0`): a pinned
  point `τ` of the relaxed domain is shifted into the unpinned domain without moving the free coordinates
  (`exists_shift_mem_splicedTimeDomain`), and the hinge HasSum reads `τ` only through the hinge clocks.
* `representsIntMK_of_vineModesFixR`: `representsIntMK_of_vineModesFixD` at `Dom := splicedTimeDomainFix …`, with
  EngVN's hinge hypothesis. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsB

/-- **`HHkPropD` on the relaxed pinned domain from main's `HHkProp`** (the shift method). -/
theorem hHkPropD_of_hHkProp {P : WTParams} {R : ℕ} {J : Type} (π : Stage1PieceMK P.d R) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) (H : HingeFam J P.d)
    (hpv : ∀ b v, π.fix b = some v → (π.layer b : ℝ) < v ∧ v ≤ π.layer b + 1 ∧ v ≤ tt b.1.1)
    (hpm : ∀ b b' v v', π.fix b = some v → π.fix b' = some v' → b'.IsChildOf b → v' ≤ v)
    (hclk0 : ∀ j i c, hclk j i = Sum.inr c → π.fix c = none)
    (hHk : HHkProp π.toStage1PieceD tt base roots selSk hclk hmom Hk H) :
    HHkPropD π tt base roots selSk (splicedTimeDomainFix π.Gsb π.layer tt π.fix) hclk hmom Hk H := by
  intro κ hsel τ hτ hpin j c hc
  obtain ⟨ε, -, hmem⟩ := exists_shift_mem_splicedTimeDomain π.Gsb π.layer tt π.fix hpv hpm τ hτ hpin
  have hclkeq : (fun i => clockOf π.Gsb tt (fun b => τ b - ε * shiftW π.fix b) (hclk j i)) =
      fun i => clockOf π.Gsb tt τ (hclk j i) := by
    funext i
    rcases h : hclk j i with y | b
    · rfl
    · show τ b - ε * shiftW π.fix b = τ b
      rw [shiftW_of_none π.fix (hclk0 j i b h), mul_zero, sub_zero]
  have key := hHk κ hsel _ hmem j c hc
  rw [hclkeq] at key
  exact key

open scoped Classical in
/-- **`RepresentsIntMK` of a pinned vine piece from the mode form, on the RELAXED pinned domain**
(`representsIntMK_of_vineModesFixD` at `Dom := splicedTimeDomainFix π.Gsb π.layer tt π.fix ∩ splicedLBDomain π.lb`, R187). Against EngVN's
`representsIntMK_of_vineModesFix`: no `hslice`; `hval` is `outerValMμD` on the relaxed domain; `hhinge` is EngVN's
(main's unpinned `HHkProp`); NEW pin hypotheses `hpv` (pins in their windows, below the root times), `hpm` (pinned
parent–child pairs monotone) and `hclk0` (hinge clocks at branches are free), from which `HHkPropD` is derived by the
shift method. -/
theorem representsIntMK_of_vineModesFixR {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    -- the pins: in their windows and below the root times; monotone along pinned parent–child pairs
    (hpv : ∀ b v, π.fix b = some v → (π.layer b : ℝ) < v ∧ v ≤ π.layer b + 1 ∧ v ≤ tt b.1.1)
    (hpm : ∀ b b' v v', π.fix b = some v → π.fix b' = some v' → b'.IsChildOf b → v' ≤ v)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (cP : ℝ) (hcP : 0 ≤ cP)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    -- the hinge clocks at branches are free atoms
    (hclk0 : ∀ j i c, hclk j i = Sum.inr c → π.fix c = none)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    {I : Type} [Fintype I] (sgn : I → ℂ) (hsgn : ∀ i, ‖sgn i‖ ≤ 1)
    (fam : I → SlotFam π.Gsb P.d) (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c θ : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcθ : 2 * c ≤ θ)
    (hμ : ∀ i s, ∑' l, maxBracketPow θ (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μs i s)
    -- numerics data
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (ξ : ∀ s, (fam i).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp π.toStage1PieceD tt base roots selSk hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ) (hs : ∑ i, ‖sgn i‖ * ((∏ t, lf i t) * ∏ j, lfj i j) ≤ s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' ξ : ∀ t, (fam i).Λ t, (((∏ t, (fam i).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt
          (splicedTimeDomainFix π.Gsb π.layer tt π.fix ∩ splicedLBDomain π.lb) π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix)
          (fun t => (fam i).a t (ξ t)) (fun t => (fam i).m t (ξ t)) route hclk hmom (HkM i)) :
    π.RepresentsIntMK n cP tt base roots s val := by
  refine representsIntMK_of_vineModesFixD hd1 hL1 hη0 π hS tt base roots selSk hgsp
    (splicedTimeDomainFix π.Gsb π.layer tt π.fix ∩ splicedLBDomain π.lb)
    ((FlowerP5.measurableSet_splicedTimeDomainFix π.Gsb π.layer tt π.fix).inter
      (FinalMKFine.measurableSet_splicedLBDomain π.lb))
    ((measure_mono Set.inter_subset_left).trans (fixMeasure_splicedTimeDomainFix_le π.Gsb π.layer tt π.fix))
    (fun _ => Iff.rfl) hfilt hind cP hcP route hroute
    hclk hmom src src_dart src_root sgn hsgn fam μs HkM hc hc1 hcθ hμ x K Ch hx hK hCh hC sz g lf hlf hμb M0 cl2 gj
    nj lfj hlfj hM (fun i ξ => ?_) n s hs hexp hg hb hh hJ val hval
  obtain ⟨H, Mh, h1, h2, h3⟩ := hhinge i ξ
  exact ⟨H, Mh, h1, h2, fun κ hsel τ hτ hpin => hHkPropD_of_hHkProp π tt base roots selSk hclk hmom _ H hpv hpm hclk0 h2
    κ hsel τ hτ.1 hpin, h3⟩

end WaveTurbulence.Flower.MkSlotsB
