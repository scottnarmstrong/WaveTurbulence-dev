/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.FixMeasure
public import WaveTurbulence.Foundations.Flower.Stage1WVine.GenVB2

/-! # B3s MK-SLOTS: pinned VINE-B♯ (1/4) — the pinned skeleton value and the pinned measure steps

## Plan (pinned copy-thread of `Stage1WVine/{GenVB1, GenVB2, GenVB3, GenModes, WInteg}`)

The generic VINE-B♯ chain integrates against Lebesgue measure on three families of times:
* the skeleton times `GBranch S.tree → ℝ` (`skelVal`, `skelTerm`, `modeG`) — pinned: `fixMeasure fixS`;
* the `G_sb` times `GBranch Gsb.tree → ℝ` (`outerValM`, `fibIntG`, first factor of `psiIntG`) — pinned:
  `fixMeasure fixSb` with `fixSb c = fixS (Φ.br c)` (the pins of the old names);
* the unit-interior times `CLInternalTime (regionOf (blk j))` (`unitKernelMG`, `unitIG`) — unchanged (`volume`):
  pins are never at unit-interior atoms.
Everything pointwise (all of `GenVB1`, `integrand_glueG`, `psiIntG`, `fibIntG`, `inner_psiIntG`, the unit bounds,
`unitKernelMG` and its bounds, `hasSum_modeGG`, `modeG_eq_psiG`, the decoration bounds `kBoundG`) is REUSED by import;
only the lemmas integrating over skeleton or `G_sb` times are re-proved, with three measure steps:
1. `measurePreserving_timeSplit_fix` (this file): `timeSplit` is a coordinate relabeling, so it maps `fixMeasure fixS`
   to `(fixMeasure fixSb).prod volume` — provided the unit interiors `inter blk j` are unpinned (`hU`);
2. `fixMeasure_boxSb_le`, `fixMeasure_boxQ_le` (this file): the boxes have measure `≤ 1` (a pinned factor is a Dirac
   mass `≤ 1`) — this replaces `volume_boxSb`/`volume_boxQ` in every bound;
3. `indicator_openSb_ae_fix` (this file): the closed and open spliced domains agree `fixMeasure fix`-a.e. provided no
   pinned value is an endpoint of its layer window (`hW`); the parent order and root bounds are strict in both domains,
   so nothing else is needed.
Files: `PVB1` (definitions `skelTermF`, `skelValF`, the three measure steps), `PVB2` (pinned Fubini and the per-mode
identity `skelValF (modalFnG) = outerValMμ`), `PVBModes` (the pinned mode expansion
`hasSum_skelValF_outerValMμ` and its unpinned specialization), `PVBInteg` (pinned integrability/summability of the outer
integrand). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlots
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-! ## The pinned skeleton expression -/

open scoped Classical in
/-- **The pinned skeleton expression**: main's `VineB.skelVal` with the core time integral against the pinned product
measure `fixMeasure fixS` (Lebesgue at free branches, Dirac at pinned values). -/
def skelValF (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (fixS : GBranch S.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
    ∑' κ : GenDecoration S d roots 0, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
      (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
          ∏ s, Fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) τ ∂(fixMeasure fixS) else 0

open scoped Classical in
/-- The summand of `skelValF` at a skeleton decoration. -/
def skelTermF (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (fixS : GBranch S.tree → Option ℝ)
    (κ : GenDecoration S d roots 0) : ℂ :=
  if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
      (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
          ∏ s, Fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) τ ∂(fixMeasure fixS) else 0

theorem skelValF_eq (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (fixS : GBranch S.tree → Option ℝ) :
    skelValF D hS L γ δ base roots tt layer selSk Fs fixS =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d roots 0, skelTermF D hS L γ δ base roots tt layer selSk Fs fixS κ := rfl

/-- **No pins**: `skelValF` is main's `skelVal`. -/
theorem skelValF_none (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) :
    skelValF D hS L γ δ base roots tt layer selSk Fs (fun _ => none) =
      skelVal D hS L γ δ base roots tt layer selSk Fs := by
  unfold skelValF skelVal
  rw [fixMeasure_none]

/-! ## Measure step 1: the pinned time split -/

/-- Unit interiors are unpinned as soon as every atom of every unit is unpinned. -/
theorem fixU_of_atoms (fixS : GBranch S.tree → Option ℝ) (h : ∀ j, ∀ a ∈ (blk j).atoms, fixS a = none) :
    ∀ j, ∀ a ∈ inter blk j, fixS a = none :=
  fun j a ha => h j a (mem_inter.mp ha).1

/-- **The pinned time split.** If no unit-interior branch is pinned, the time split `τ ↦ (τ', (τ_j))` maps the pinned
skeleton measure to the pinned `G_sb` measure (pins of the old names `Φ.br c`) times Lebesgue measure on the unit
interiors. -/
theorem measurePreserving_timeSplit_fix (Φ : SpliceShape blk Gsb) (hd : Disj blk) (fixS : GBranch S.tree → Option ℝ)
    (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none) :
    MeasurePreserving (Φ.timeSplit hd) (fixMeasure fixS)
      ((fixMeasure (fun c => fixS (Φ.br c))).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  have h₁ : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Φ.branchSplit hd).symm).symm
      (fixMeasure fixS) (fixMeasure (fixS ∘ (Φ.branchSplit hd).symm)) :=
    (measurePreserving_piCongrLeft_fix (Φ.branchSplit hd).symm fixS).symm
  have h₂ := measurePreserving_sumPiEquivProdPi_fix (fixS ∘ (Φ.branchSplit hd).symm)
  have hl : (fixS ∘ (Φ.branchSplit hd).symm) ∘ Sum.inl = fun c => fixS (Φ.br c) := rfl
  have hr : (fixS ∘ (Φ.branchSplit hd).symm) ∘ Sum.inr = fun _ => none := by
    funext x
    exact hU x.1 x.2.1 x.2.2
  rw [hl, hr, fixMeasure_none] at h₂
  have h₃ : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (GBranch Gsb.tree → ℝ))
      (MeasurableEquiv.piCurry (fun (j : J) (_ : ↥(inter blk j)) => ℝ)))
      ((fixMeasure (fun c => fixS (Φ.br c))).prod (volume : Measure ((Σ j, ↥(inter blk j)) → ℝ)))
      ((fixMeasure (fun c => fixS (Φ.br c))).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (MeasurePreserving.id _).prod (measurePreserving_piCurry_real (fun j : J => ↥(inter blk j)))
  exact h₃.comp (h₂.comp h₁)

/-! ## Measure step 2: the boxes have pinned measure at most one -/

theorem fixFactor_Icc_le_one (o : Option ℝ) (a : ℝ) : fixFactor o (Set.Icc a (a + 1)) ≤ 1 := by
  cases o with
  | none => simp [fixFactor]
  | some v =>
    show (Measure.dirac v) (Set.Icc a (a + 1)) ≤ 1
    exact prob_le_one

theorem fixMeasure_boxSb_le (layerSb : GBranch Gsb.tree → ℕ) (fix : GBranch Gsb.tree → Option ℝ) :
    fixMeasure fix (boxSb layerSb) ≤ 1 := by
  unfold boxSb fixMeasure
  rw [Measure.pi_pi]
  exact Finset.prod_le_one fun c _ => fixFactor_Icc_le_one (fix c) _

theorem fixMeasure_boxQ_le (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (layerSb : GBranch Gsb.tree → ℕ) (fix : GBranch Gsb.tree → Option ℝ) :
    ((fixMeasure fix).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j)))))
      (SpliceShape.boxQ (blk := blk) D hS layer layerSb) ≤ 1 := by
  unfold SpliceShape.boxQ
  rw [Measure.prod_prod, volume_pi_pi]
  simp only [volume_boxU, Finset.prod_const_one, mul_one]
  exact fixMeasure_boxSb_le layerSb fix

/-- A constant on a set of measure `≤ 1` is integrable. -/
theorem integrable_indicator_const_of_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (h1 : μ s ≤ 1) (c : ℝ) : Integrable (s.indicator fun _ => c) μ :=
  (integrable_indicator_iff hs).2 (integrableOn_const (h1.trans_lt ENNReal.one_lt_top).ne)

/-- The integral of a nonnegative constant on a set of measure `≤ 1` is at most the constant. -/
theorem integral_indicator_const_le_of_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (h1 : μ s ≤ 1) {c : ℝ} (hc : 0 ≤ c) : ∫ x, s.indicator (fun _ => c) x ∂μ ≤ c := by
  rw [integral_indicator_const _ hs, smul_eq_mul]
  have hr : μ.real s ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (h1.trans_eq ENNReal.ofReal_one.symm)
  calc μ.real s * c ≤ 1 * c := mul_le_mul_of_nonneg_right hr hc
    _ = c := one_mul c

/-! ## Measure step 3: closed and open spliced domains agree a.e. on the pinned slice -/

theorem fixFactor_singleton_null (o : Option ℝ) (x : ℝ) (h : o ≠ some x) : fixFactor o {x} = 0 := by
  cases o with
  | none => simp [fixFactor]
  | some v =>
    show (Measure.dirac v) {x} = 0
    rw [Measure.dirac_apply' _ (measurableSet_singleton x)]
    have hv : v ∉ ({x} : Set ℝ) := fun hv => h (by rw [Set.mem_singleton_iff.mp hv])
    exact Set.indicator_of_notMem hv _

/-- **The closed and open spliced domains differ by a null set of the pinned measure**, provided no pinned value is an
endpoint of its layer window. -/
theorem indicator_openSb_ae_fix (G : Garden w) (layer : GBranch G.tree → ℕ) (tt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ)
    (hW : ∀ c v, fix c = some v → v ≠ (layer c : ℝ) ∧ v ≠ (layer c : ℝ) + 1) {E : Type*} [Zero E]
    (f : (GBranch G.tree → ℝ) → E) :
    (splicedTimeDomain G layer tt).indicator f =ᵐ[fixMeasure fix] (openSb G layer tt).indicator f := by
  have hne : ∀ c (x : ℝ), (x = layer c ∨ x = layer c + 1) → fix c ≠ some x := by
    intro c x hx hc
    obtain ⟨h1, h2⟩ := hW c x hc
    rcases hx with hx | hx
    · exact h1 hx
    · exact h2 hx
  have hN : (fixMeasure fix)
      (⋃ c, (Function.eval c ⁻¹' {(layer c : ℝ)} ∪ Function.eval c ⁻¹' {(layer c : ℝ) + 1})) = 0 := by
    refine measure_iUnion_null fun c => measure_union_null ?_ ?_
    · exact Measure.pi_eval_preimage_null _ (fixFactor_singleton_null _ _ (hne c _ (Or.inl rfl)))
    · exact Measure.pi_eval_preimage_null _ (fixFactor_singleton_null _ _ (hne c _ (Or.inr rfl)))
  refine (measure_eq_zero_iff_ae_notMem.1 hN).mono fun τ hτ => ?_
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_preimage, Function.eval, Set.mem_singleton_iff,
    not_exists, not_or] at hτ
  by_cases h : τ ∈ splicedTimeDomain G layer tt
  · have ho : τ ∈ openSb G layer tt := ⟨fun c => ⟨lt_of_le_of_ne (h.1 c).1 (Ne.symm (hτ c).1),
      lt_of_le_of_ne (h.1 c).2 (hτ c).2⟩, h.2.1, h.2.2⟩
    rw [Set.indicator_of_mem h, Set.indicator_of_mem ho]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun ho => h (openSb_subset G layer tt ho))]

/-- Pinned values strictly inside their layer windows avoid the endpoints. -/
theorem fixW_of_mem_Ioo {G : Garden w} (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ)
    (h : ∀ c v, fix c = some v → (layer c : ℝ) < v ∧ v < layer c + 1) :
    ∀ c v, fix c = some v → v ≠ (layer c : ℝ) ∧ v ≠ (layer c : ℝ) + 1 :=
  fun c v hc => ⟨(h c v hc).1.ne', (h c v hc).2.ne⟩

end WaveTurbulence.Flower.MkSlots
