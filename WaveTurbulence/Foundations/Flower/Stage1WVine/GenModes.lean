/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.GenVB3
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB8

/-! # STAGE1W-VINE (T3): the mode expansion of the outer slots for an arbitrary slot family

Copy-generalization of `Represents/RepVB2–RepVB8` (VINE-B♯ integration) from `slotFn` to an arbitrary slot family
`Fs`: if the outer slots of `Fs` have superpositions `Σ_l w_l a_l(k) e^{πi m_l·ts}` on boxes containing the slot
times of the core domain, then `skelVal(Fs) = Σ'_ξ w_ξ · outerValM(amp ξ, frq ξ, …, unitKernelMG Fs)`
(`hasSum_skelVal_outerValMG`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic WaveTurbulence.Flower.Stage1WVine.UnitG

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

theorem hasSum_modal_prodG (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (fam : SlotFam Gsb d) (tt : Fin w → ℝ)
    (τ : GBranch S.tree → ℝ) (k : GNode S.tree → Mom d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x *
      fsPhase (fam.m s' l) ts) (Fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      ∏ s, modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')) s
        (slotTs hS tt τ s) (k (slotNode hS s)))
      (∏ s, Fs s (slotTs hS tt τ s) (k (slotNode hS s))) := by
  have hmain := hasSum_outer_modes fam (fun s' => slotTs hS tt τ (Φ.iota hS hSb s'))
    (fun s' => k (slotNode hS (Φ.iota hS hSb s')))
    (fun s' => Fs (Φ.iota hS hSb s') (slotTs hS tt τ (Φ.iota hS hSb s')) (k (slotNode hS (Φ.iota hS hSb s'))))
    (fun s' => hexp s' _ (hbox s') _)
  set R : ℂ := ∏ j, ∏ s ∈ regSlots blk hS j, Fs s (slotTs hS tt τ s) (k (slotNode hS s)) with hR
  have h1 := hmain.mul_right R
  have e2 : ∏ s, Fs s (slotTs hS tt τ s) (k (slotNode hS s)) =
      (∏ s', Fs (Φ.iota hS hSb s') (slotTs hS tt τ (Φ.iota hS hSb s')) (k (slotNode hS (Φ.iota hS hSb s')))) * R := by
    rw [prod_slots hS hd (fun s => Fs s (slotTs hS tt τ s) (k (slotNode hS s))),
      Φ.prod_outer_iota hS hSb (fun s => Fs s (slotTs hS tt τ s) (k (slotNode hS s)))]
  rw [e2]
  refine h1.congr_fun fun ξ => ?_
  rw [prod_modalFnG Φ hd hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')) tt τ k]
  ring

theorem modeG_eq_psiG (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) (τ : GBranch S.tree → ℝ) :
    modeG (modalFnG Φ hS hSb Fs amp frq) D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ =
    psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs (Φ.timeSplit hd τ) := by
  have := integrand_glueG Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs (Φ.timeSplit hd τ).1
    (Φ.timeSplit hd τ).2
  rw [show Φ.glueTime hd (Φ.timeSplit hd τ).1 (Φ.timeSplit hd τ).2 = τ from by
    rw [← Φ.timeSplit_symm hd]; exact (Φ.timeSplit hd).symm_apply_apply τ] at this
  exact this

variable {hS : S.IsPlain} {Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ} {L : ℝ} {base : Mom d}

theorem integrable_modeGG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Integrable (fun τ => modeG (modalFnG Φ hS hSb Fs amp frq) D hS L γ δ base tt layer
      (Φ.glueDec hS hd hL base z κs) τ) := by
  have hi := integrable_psiIntG Φ RB hd D hSb γ δ layer tt amp frq z κs
  have hmp := Φ.measurePreserving_timeSplit hd
  have := (hmp.integrable_comp_emb (Φ.timeSplit hd).measurableEmbedding).2 hi
  refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
  exact (modeG_eq_psiG Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs τ).symm

theorem integral_norm_modeG_leG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ∫ τ, ‖modeG (modalFnG Φ hS hSb Fs amp frq) D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ‖ ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  have hmp : MeasurePreserving (Φ.timeSplit hd) volume volume := by
    rw [Measure.volume_eq_prod]; exact Φ.measurePreserving_timeSplit hd
  have e : ∫ τ, ‖modeG (modalFnG Φ hS hSb Fs amp frq) D hS L γ δ base tt layer (Φ.glueDec hS hd hL base z κs) τ‖ =
      ∫ p, ‖psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p‖ := by
    rw [← hmp.integral_comp' (fun p => ‖psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p‖)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [modeG_eq_psiG Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs τ]
  rw [e, Measure.volume_eq_prod]
  have hQ := SpliceShape.measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hv := SpliceShape.volume_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hgi : Integrable ((SpliceShape.boxQ (blk := blk) D hS layer
      (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
      (fun _ => ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)))
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [hv]; exact ENNReal.one_ne_top))
  refine (integral_mono (integrable_psiIntG Φ RB hd D hSb γ δ layer tt amp frq z κs).norm hgi
    fun p => norm_psiIntG_le Φ RB hd D hSb γ δ layer tt amp frq z κs p).trans_eq ?_
  rw [integral_indicator_const _ hQ, Measure.real, hv]
  simp

open scoped Classical in
theorem hasSum_modeGG (hd : Disj blk) (hSb : Gsb.IsPlain) (γ δ : ℝ) (D : ReconstructionData S)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (κ : GenDecoration S d roots 0) (τ : GBranch S.tree → ℝ) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      modeG (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
        D hS L γ δ base tt layer κ τ)
      (modeG Fs D hS L γ δ base tt layer κ τ) := by
  by_cases hτ : τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt
  · have hm := hasSum_modal_prodG Φ hd hS hSb Fs fam tt τ (fun x => base + latticePoint L (κ.1 x)) Box hexp (hbox τ hτ)
    have h2 := hm.mul_left ((epsDec S κ.1 : ℂ) * phaseProd L γ δ S (cosetDecoration S L base κ.1) τ)
    unfold modeG
    simp only [Set.indicator_of_mem hτ]
    convert h2 using 1
    · funext ξ; ring
    · ring
  · unfold modeG
    simp only [Set.indicator_of_notMem hτ, mul_zero]
    exact hasSum_zero

open scoped Classical in
theorem hasSum_skelTerm_modesG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelTerm D hS L γ δ base roots tt layer selSk
        (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
        (Φ.glueDec hS hd hL base z κs))
      (skelTerm D hS L γ δ base roots tt layer selSk Fs (Φ.glueDec hS hd hL base z κs)) := by
  by_cases hs : selSk (Φ.glueDec hS hd hL base z κs)
  · set κ := Φ.glueDec hS hd hL base z κs with hκ
    simp only [skelTerm_eq_integral, hs, ite_true]
    have : ∀ s, Countable (fam.Λ s) := fam.cnt
    set M : ℝ := ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) with hM
    have hM0 : 0 ≤ M := Finset.prod_nonneg fun j _ => RB.nonneg j _
    have hwt : Summable (modeWt fam) :=
      (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
    let G : (∀ s, fam.Λ s) → (GBranch S.tree → ℝ) → ℂ := fun ξ τ => ((modeWt fam ξ : ℝ) : ℂ) *
      modeG (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
        D hS L γ δ base tt layer κ τ
    have hint : ∀ ξ, Integrable (G ξ) := fun ξ =>
      (integrable_modeGG Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) z κs).const_mul _
    have hnorm : Summable fun ξ => ∫ τ, ‖G ξ τ‖ := by
      refine Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun τ => norm_nonneg _) (fun ξ => ?_) (hwt.mul_right M)
      have e1 : ∫ τ, ‖G ξ τ‖ = modeWt fam ξ * ∫ τ, ‖modeG
          (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')))
            D hS L γ δ base tt layer κ τ‖ := by
        simp only [G, norm_mul, Complex.norm_real, Real.norm_of_nonneg (modeWt_nonneg fam ξ)]
        rw [integral_const_mul]
      rw [e1]
      refine mul_le_mul_of_nonneg_left
        ((integral_norm_modeG_leG Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
          (fun s' => fam.m s' (ξ s')) z κs).trans ?_) (modeWt_nonneg fam ξ)
      have hab : ampBound hSb L base (fun s' x => fam.a s' (ξ s') x) z ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ => fam.a_one _ _ _
      calc _ ≤ 1 * M := mul_le_mul_of_nonneg_right hab hM0
        _ = M := one_mul _
    have key := hasSum_integral_of_summable_integral_norm hint hnorm
    have hpt : ∀ τ, ∑' ξ, G ξ τ = modeG Fs D hS L γ δ base tt layer κ τ :=
      fun τ => (hasSum_modeGG Φ hd hSb γ δ D layer tt fam Box hexp hbox κ τ).tsum_eq
    simp only [hpt] at key
    refine key.congr_fun fun ξ => ?_
    simp only [G]
    rw [integral_const_mul]
  · simp only [skelTerm_eq_integral, hs, ite_false, mul_zero]
    exact hasSum_zero

theorem tsum_kBoundG_le (RB : RegBound blk hS Fs L base) (hSb : Gsb.IsPlain) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (hsm : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) (N : ℝ)
    (hN : ∑' z : GenDecoration Gsb d roots 0, ampBound hSb L base amp z ≤ N) :
    ∑' p, kBoundG Φ RB hSb (roots := roots) amp p ≤ N * ∏ j, RB.lbC j := by
  have hkbs := summable_kBoundG Φ RB hSb (roots := roots) amp hsm
  have hfib := fun z => summable_fib_kBoundG Φ RB hSb (roots := roots) amp z
  have hΛ0 : 0 ≤ ∏ j, RB.lbC j := Finset.prod_nonneg fun j _ => lbC_nonneg RB j 0
  rw [hkbs.tsum_sigma' hfib]
  calc _ ≤ ∑' z : GenDecoration Gsb d roots 0, ampBound hSb L base amp z * ∏ j, RB.lbC j :=
        Summable.tsum_le_tsum (fun z => tsum_fib_kBoundG_le Φ RB hSb amp z) hkbs.sigma (hsm.mul_right _)
    _ = (∑' z, ampBound hSb L base amp z) * ∏ j, RB.lbC j := tsum_mul_right
    _ ≤ N * _ := mul_le_mul_of_nonneg_right hN hΛ0

open scoped Classical in
theorem hasSum_skelVal_modesG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL0 : 0 < L)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      skelVal D hS L γ δ base roots tt layer selSk
        (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))))
      (skelVal D hS L γ δ base roots tt layer selSk Fs) := by
  have hL : L ≠ 0 := hL0.ne'
  have hcnt : ∀ s, Countable (fam.Λ s) := fam.cnt
  have hwt : Summable (modeWt fam) :=
    (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
  have key := hasSum_tsum_interchange (modeWt fam) (modeWt_nonneg fam) hwt (Φ.decSplit hS hd hL base roots)
    (fun ξ p => kBoundG Φ RB hSb (fun s' x => fam.a s' (ξ s') x) p)
    (fun ξ p => kBoundG_nonneg Φ RB hSb _ p)
    (fun ξ => summable_kBoundG Φ RB hSb (roots := roots) _ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1)
    ((((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair Gsb) : ℕ) * ∏ j, RB.lbC j)
    (fun ξ => tsum_kBoundG_le Φ RB hSb _ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1 _
      (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).2)
    (fun ξ κ => skelTerm D hS L γ δ base roots tt layer selSk
      (modalFnG Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) κ)
    (fun κ => skelTerm D hS L γ δ base roots tt layer selSk Fs κ)
    (fun ξ κ => by
      have := norm_skelTerm_glueG_le Φ RB hd hSb hL γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) selSk Zw hZ ((Φ.decSplit hS hd hL base roots) κ).1
        ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rw [hκ] at this
      exact this)
    (fun κ => by
      have := hasSum_skelTerm_modesG Φ RB hd hSb hL γ δ D layer tt selSk fam Box hexp hbox
        ((Φ.decSplit hS hd hL base roots) κ).1 ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rwa [hκ] at this)
  have h2 := key.mul_left ((coupling d L γ δ : ℂ) ^ S.order * S.zeta)
  rw [skelVal_eq]
  convert h2 using 1
  funext ξ
  rw [skelVal_eq]
  ring

open scoped Classical in
/-- **The mode form of the skeleton expression with an arbitrary slot family** (cf.
`Represents.hasSum_skelVal_outerValM`). -/
theorem hasSum_skelVal_outerValMG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (Fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd) Zw hSb
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelMG blk D hS Fs L γ δ layer base))
      (skelVal D hS L γ δ base roots tt layer selSk Fs) := by
  have key := hasSum_skelVal_modesG Φ RB hd hSb hL0 γ δ D layer tt selSk Zw hZ fam Box hexp hbox
  refine key.congr_fun fun ξ => ?_
  rw [skelVal_modal_eq_outerValMG Φ RB hd hSb hL0.ne' γ δ D layer tt (fun s' x => fam.a s' (ξ s') x)
    (fun s' => fam.m s' (ξ s')) selSk Zw hZ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1]

end WaveTurbulence.Flower.Stage1WVine
