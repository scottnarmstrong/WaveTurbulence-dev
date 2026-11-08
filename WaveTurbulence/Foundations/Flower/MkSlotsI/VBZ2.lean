/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.VBZ1
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBRInteg

/-! # B3s MK-SLOTS (final assembly, WP1): the pinned VINE-B♯ with a complex skeleton weight — mode expansion

β's `MkSlotsB/PVBRModes` with the selection indicator replaced by the complex skeleton weight `Zs = Zw ∘ resDec`
(`‖Zw‖ ≤ 1`). The per-term mode expansion is β's `hasSum_skelTerm_modesGWD_fix` at the trivial selection, multiplied
by the (mode-independent) weight; the interchange of the mode and decoration sums uses the weighted glue bound
`norm_skelTerm_glueGWZ_le_fix` (VBZ1).

* `hasSum_skelTerm_modesGWZ_fix`, `hasSum_skelVal_modesGWZ_fix`, `hasSum_skelValWZ_outerValMμD` (generic domains);
* **`hasSum_skelValWZRL_outerValMμD`**: the relaxed pinned VINE-B♯ with lower bounds and a complex skeleton weight;
* the class-sum (T4) inputs for the per-mode outer values: **`summable_modes_outerValMWZ`** (ξ-summability),
  **`integrable_outerIntegrandMDGW_modesR`** (integrability, per mode and decoration) and
  **`summable_outer_decorationsGWD_modesR`** (decoration summability with a complex weight `‖Zw‖ ≤ 1`, per mode), the
  mode instances of β's `integrable_outerIntegrandMDGW_fixR` / `summable_outer_decorationsGWD_fixR`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsI
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkSlots (fixMeasure outerValMμD)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW modalFnGW unitKernelMGW tsum_kBoundG_leW)
open WaveTurbulence.Flower.MkUnitsL.UnitGW (kBoundGW kBoundG_nonnegW summable_kBoundGW)
open WaveTurbulence.Flower.MkSlotsB

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)
variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

/-! ## The mode expansion -/

/-- The mode expansion of one weighted glued skeleton term (β's `MkSlotsB.hasSum_skelTerm_modesGWD_fix` at the
trivial selection, times the weight). -/
theorem hasSum_skelTerm_modesGWZ_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (Zs : GenDecoration S d roots 0 → ℂ)
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (hbox : ∀ τ, PinnedAt fixS τ → τ ∈ A → ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelTermWZ blk hS L γ δ base roots tt Zs
        (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) A fixS
        (Φ.glueDec hS hd hL base z κs))
      (skelTermWZ blk hS L γ δ base roots tt Zs Fs A fixS (Φ.glueDec hS hd hL base z κs)) := by
  classical
  have h := hasSum_skelTerm_modesGWD_fix Φ RB hd hSb hL γ δ D layer tt (fun _ => True) fam Box hexp fixS hU hG
    hbox z κs
  simp only [skelTermWD_eq_integral, ↓reduceIte] at h
  have h2 := h.mul_left (Zs (Φ.glueDec hS hd hL base z κs))
  simp only [skelTermWZ_eq_integral]
  convert h2 using 1
  funext ξ
  ring

/-- The mode expansion of the weighted skeleton value (cf. β's `MkSlotsB.hasSum_skelVal_modesGWD_fix`). -/
theorem hasSum_skelVal_modesGWZ_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (hbox : ∀ τ, PinnedAt fixS τ → τ ∈ A → ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelValWZ blk hS L γ δ base roots tt Zs
        (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) A fixS)
      (skelValWZ blk hS L γ δ base roots tt Zs Fs A fixS) := by
  have hL : L ≠ 0 := hL0.ne'
  have hcnt : ∀ s, Countable (fam.Λ s) := fam.cnt
  have hwt : Summable (modeWt fam) :=
    (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
  have key := hasSum_tsum_interchange (modeWt fam) (modeWt_nonneg fam) hwt (Φ.decSplit hS hd hL base roots)
    (fun ξ p => kBoundGW Φ RB hSb (fun s' x => fam.a s' (ξ s') x) p)
    (fun ξ p => kBoundG_nonnegW Φ RB hSb _ p)
    (fun ξ => summable_kBoundGW Φ RB hSb (roots := roots) _ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1)
    ((((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair Gsb) : ℕ) * ∏ j, RB.lbC j)
    (fun ξ => tsum_kBoundG_leW Φ RB hSb _ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1 _
      (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).2)
    (fun ξ κ => skelTermWZ blk hS L γ δ base roots tt Zs
      (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) A fixS κ)
    (fun κ => skelTermWZ blk hS L γ δ base roots tt Zs Fs A fixS κ)
    (fun ξ κ => by
      have := norm_skelTerm_glueGWZ_le_fix Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) Zs Zw hZw hZ fixS hU hG ((Φ.decSplit hS hd hL base roots) κ).1
        ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rw [hκ] at this
      exact this)
    (fun κ => by
      have := hasSum_skelTerm_modesGWZ_fix Φ RB hd hSb hL γ δ D layer tt Zs fam Box hexp fixS hU hG hbox
        ((Φ.decSplit hS hd hL base roots) κ).1 ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rwa [hκ] at this)
  have h2 := key.mul_left ((coupling d L γ δ : ℂ) ^ S.order * S.zeta)
  rw [skelValWZ]
  convert h2 using 1
  funext ξ
  rw [skelValWZ]
  ring

/-- **The pinned mode form on general domains with a complex weight**: core domain `A`, `G_sb` domain `B` (`hG`),
outer domain `Dom` a.e. equal to `B` (`hDB`) (cf. β's `MkSlotsB.hasSum_skelValWD_outerValMμD`). -/
theorem hasSum_skelValWZ_outerValMμD (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (Dom : Set (GBranch Gsb.tree → ℝ))
    (hDB : ∀ᵐ τ' ∂(fixMeasure (fun c => fixS (Φ.br c))), τ' ∈ Dom ↔ τ' ∈ B)
    (hbox : ∀ τ, PinnedAt fixS τ → τ ∈ A → ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt Dom (Φ.hinges hd) Zw hSb
        (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZ blk hS L γ δ base roots tt Zs Fs A fixS) := by
  have key := hasSum_skelVal_modesGWZ_fix Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam Box hexp fixS hU hG hbox
  refine key.congr_fun fun ξ => ?_
  rw [skelVal_modal_eq_outerValMGWZ_fix Φ RB hd hSb hL0.ne' γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
    (fun s' => fam.m s' (ξ s')) Zs Zw hZw hZ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1 fixS hU hG Dom hDB]

/-! ## The relaxed pinned VINE-B♯ with a complex skeleton weight -/

/-- **The relaxed pinned VINE-B♯ with unit top weights, lower bounds and a complex skeleton weight** (WP1): β's
`MkSlotsB.hasSum_skelValWFRL_outerValMμD` with the selection indicator `if selSk κ then 1 else 0 = Zw (resDec κ)`
(`Zw` real) replaced by an arbitrary complex skeleton weight `Zs` with `Zs κ = Zw (Φ.resDec hS hd κ)`, `Zw` complex
of norm `≤ 1`. The skeleton value is `skelValWZRL` (core domain `coreTimeDomainWR … fixS ∩ lbDomR lbS`), the
conclusion is on main's relaxed spliced domain `splicedTimeDomainFix … (fixS ∘ Φ.br) ∩ lbDomR (lbS ∘ Φ.br)` with the
outer decoration weight `Zw`. -/
theorem hasSum_skelValWZRL_outerValMμD (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
          lbDomR (fun c => lbS (Φ.br c)))
        (Φ.hinges hd) Zw hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZRL blk D hS L γ δ base roots tt layer Zs Fs fixS lbS) :=
  hasSum_skelValWZ_outerValMμD Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam Box hexp fixS hU
    (GlueDomR.relaxedLB Φ hd D hS layer tt fixS lbS hU hlbU hP) _
    (ae_mem_splicedTimeDomainFix_lb_iff Gsb _ tt _ _) hbox

/-! ## The class-sum (T4) inputs for the per-mode outer values -/

/-- **ξ-summability of the weighted per-mode outer values** (the `hξ` input of the class sum): a consequence of
`hasSum_skelValWZRL_outerValMμD`. -/
theorem summable_modes_outerValMWZ (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs.fs (Φ.iota hS hSb s') ts x))
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    Summable (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValMμD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
          lbDomR (fun c => lbS (Φ.br c)))
        (Φ.hinges hd) Zw hSb (fixMeasure (fun c => fixS (Φ.br c)))
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base)) :=
  (hasSum_skelValWZRL_outerValMμD Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam Box hexp fixS lbS hU hlbU hP
    hbox).summable

/-- **Integrability of the per-mode relaxed outer integrand** (the `hint` input of the class sum), for every mode
`ξ` and decoration `z`, against the pinned measure (β's `MkSlotsB.integrable_outerIntegrandMDGW_fixR` at the
mode amplitudes, with the pins and lower bounds of `G_sb` pulled back from the skeleton). -/
theorem integrable_outerIntegrandMDGW_modesR (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (fam : SlotFam Gsb d) (ξ : ∀ s, fam.Λ s)
    (fixS lbS : GBranch S.tree → Option ℝ) (z : GenDecoration Gsb d roots 0) :
    Integrable (outerIntegrandMD Gsb L γ δ base roots tt
      (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
        lbDomR (fun c => lbS (Φ.br c))) hSb
      (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
      (unitKernelMGW blk D hS Fs L γ δ layer base) z)
      (fixMeasure (fun c => fixS (Φ.br c))) :=
  integrable_outerIntegrandMDGW_fixR Φ RB hd D hSb γ δ layer tt (fun s' => fam.a s' (ξ s'))
    (fun s' => fam.m s' (ξ s')) z (fun c => fixS (Φ.br c)) (fun c => lbS (Φ.br c))

/-- **Decoration summability of the per-mode relaxed outer value with a complex weight** (the `hsm` input of the
class sum), for every mode `ξ` and every complex decoration weight `‖Zw‖ ≤ 1` (β's
`MkSlotsB.summable_outer_decorationsGWD_fixR` at the mode amplitudes; the amplitude summability is
`tsum_ampBound_mode_le`). -/
theorem summable_outer_decorationsGWD_modesR (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (hL0 : 0 < L) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (fam : SlotFam Gsb d) (ξ : ∀ s, fam.Λ s)
    (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (fixS lbS : GBranch S.tree → Option ℝ) :
    Summable (fun z : GenDecoration Gsb d roots 0 =>
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * Zw z *
        ∫ τ, outerIntegrandMD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
            lbDomR (fun c => lbS (Φ.br c))) hSb
          (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
          (unitKernelMGW blk D hS Fs L γ δ layer base) z τ ∂(fixMeasure (fun c => fixS (Φ.br c)))) :=
  summable_outer_decorationsGWD_fixR Φ RB hd D hSb γ δ layer tt (fun s' => fam.a s' (ξ s'))
    (fun s' => fam.m s' (ξ s')) Zw hZw (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1
    (fun c => fixS (Φ.br c)) (fun c => lbS (Φ.br c))

/-- The per-mode outer value is the decoration sum of the integrals of β's `outerIntegrandMD` (rfl; the form in
which the class sum consumes it). -/
theorem outerValMμD_modes_eq (hd : Disj blk) (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (fam : SlotFam Gsb d)
    (ξ : ∀ s, fam.Λ s) (Zw : GenDecoration Gsb d roots 0 → ℂ) (Dom : Set (GBranch Gsb.tree → ℝ))
    (μ : Measure (GBranch Gsb.tree → ℝ)) :
    outerValMμD Gsb L γ δ base roots tt Dom (Φ.hinges hd) Zw hSb μ
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMGW blk D hS Fs L γ δ layer base) =
      (coupling d L γ δ : ℂ) ^ Gsb.order * Gsb.zeta *
        ∑' z : GenDecoration Gsb d roots 0, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * Zw z *
          ∫ τ, outerIntegrandMD Gsb L γ δ base roots tt Dom hSb
            (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
            (unitKernelMGW blk D hS Fs L γ δ layer base) z τ ∂μ := rfl

end WaveTurbulence.Flower.MkSlotsI
