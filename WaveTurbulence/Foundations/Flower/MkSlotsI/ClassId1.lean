/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.VBC4
public import WaveTurbulence.Foundations.Flower.MkSlotsI.T4D
public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassForm

/-! # B3s-HELPER7 ClassId (part 1): generic tools for the class identity

* `skelValWZRL_const_mul`: the weighted relaxed pinned skeleton value is linear in the weight;
* **`weightedClassFactorizationμDLX`**: the pinned list-T4 on a general time domain (T4D2) with an extra outer sum
  over the centre assignments `X` (mode-dependent weights `Zw X`, families `amp X ξ`);
* `RegAgree`, `starProdGW_agree`, `unitKernelMGW_agree`, `RegBoundW.ofAgree`: the unit kernels and the regional
  bound only read the regional slots and the unit tops;
* `tsum_w_le_of_mass`, **`exists_hMC`**: the uniform chain-piece mass bound `hMC` of VBC from the moment masses of
  `SlotDataOK` (`maxBracketPow ≥ 1`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped ENNReal
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsI
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic
open WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineC
  WaveTurbulence.Flower.V5W
open WaveTurbulence.Flower.V5W2L (twistedLocalKernelFWL twistedRecenteredFWL unitRecenteredFWL)
open WaveTurbulence.Flower.MkSlots (fixMeasure outerValMμD)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW unitKernelMGW starProdGW clLocalSummandGW
  clLocalStarProductGW RegMeasW unitKernelFWL_classProd)
open WaveTurbulence.Flower.MkSlotsB (outerIntegrandMD)
open WaveTurbulence.VineA (PrescribedPrimeGarden)
open WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign WaveTurbulence.Flower.Stage1MKGate

variable {w d : ℕ}

/-! ## Linearity of the weighted skeleton value -/

section Lin
variable {S : Garden w} {J : Type} [Fintype J]

/-- **The weighted relaxed pinned skeleton value is linear in the weight.** -/
theorem skelValWZRL_const_mul (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ) (c : ℂ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Fs : SlotFamW S d) (fixS lbS : GBranch S.tree → Option ℝ) :
    skelValWZRL blk D hS L γ δ base roots tt layer (fun κ => c * Zs κ) Fs fixS lbS =
      c * skelValWZRL blk D hS L γ δ base roots tt layer Zs Fs fixS lbS := by
  unfold skelValWZRL skelValWZ skelTermWZ
  simp_rw [mul_assoc c]
  rw [tsum_mul_left]
  ring

end Lin

/-! ## The pinned list-T4 with an outer centre sum -/

-- [copied] world `Flower/MkSlotsI/T4D2.lean` lines 48–126 (`weightedClassFactorizationμDLZ`), with the type index
-- `I` dropped (one constant `sgn`) and an extra outer `tsum` over `X : Ξ₀` (families `ξ : Ξ X`), see COPIED-SHA256SUMS.
/-- **Pinned list-T4 on a general time domain, with an outer centre sum.** If every member of the τ-class has the
form `V = sgn · Σ'_X Σ'_ξ Wt X ξ · outerValMμD … (Zw X) … (amp X ξ) … (its own unit kernels)`, with the `X`-sums and the
`ξ`-sums summable and the integrability and decoration summability of the members' integrands, then the class sum is
`sgn · Σ'_X Σ'_ξ Wt X ξ · outerValMμD … (class kernels twistedRecenteredFWL)`. -/
theorem weightedClassFactorizationμDLX {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    {U₀ : J₀ → Finset (GBranch S.tree)} {a₀ b₀ : J₀ → GBranch S.tree} {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)}
    {n₀ : J₀ → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j)) (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j'))
    (hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool} (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = (unitsStart B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) (sgn : ℂ) {Ξ₀ : Type*} {Ξ : Ξ₀ → Type*} (Wt : ∀ X, Ξ X → ℂ)
    (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (Dom : Set (GBranch G.tree → ℝ)) (hinges : Finset (GBranch G.tree)) (Zw : Ξ₀ → GenDecoration G d roots 0 → ℂ)
    (hG : G.IsPlain) (μ : Measure (GBranch G.tree → ℝ))
    (amp : ∀ X, Ξ X → ReplacementSlot G → Mom d → ℂ) (frq : ∀ X, Ξ X → ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀) (hclk : J₀ → Fin 3 → ClkSrc G)
    (hmom : J₀ → Fin 4 → GNode G.tree) (F : J₀ → ℕ → Mom d → ℝ)
    (gU : J₀ → Mom d → ℂ) (SU : J₀ → List ℝ)
    (hV : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      V y.1.layered = sgn * ∑' X, ∑' ξ, Wt X ξ *
        outerValMμD G L γ δ base roots tt Dom hinges (Zw X) hG μ (amp X ξ) (frq X ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)))
    (hX : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun X => ∑' ξ, Wt X ξ *
        outerValMμD G L γ δ base roots tt Dom hinges (Zw X) hG μ (amp X ξ) (frq X ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    (hξ : ∀ X, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun ξ => Wt X ξ *
        outerValMμD G L γ δ base roots tt Dom hinges (Zw X) hG μ (amp X ξ) (frq X ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    (hint : ∀ X ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ z, Integrable (outerIntegrandMD G L γ δ base roots tt Dom hG (amp X ξ) (frq X ξ) route hclk hmom
        (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F j) base (modW lam)
          (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z) μ)
    (hsm : ∀ X ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * Zw X z *
          ∫ τ, outerIntegrandMD G L γ δ base roots tt Dom hG (amp X ξ) (frq X ξ) route hclk hmom
            (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F j) base (modW lam)
              (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ ∂μ)) :
    ∑ LG ∈ T, V LG = sgn * ∑' X, ∑' ξ, Wt X ξ *
      outerValMμD G L γ δ base roots tt Dom hinges (Zw X) hG μ (amp X ξ) (frq X ξ) route hclk hmom
        (fun j lam t k => twistedRecenteredFWL p (gU j) (SU j) S (a₀ j)
          (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
          L γ δ (F j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) := by
  rw [sum_layered_eq_sum_classU (Us := unitsSplit B₀) (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime
    (unitsRegion B₀ hdisj₀) T hT V, Finset.sum_congr rfl hV, ← Finset.mul_sum, ← Summable.tsum_finsetSum hX]
  congr 1
  refine tsum_congr fun X => ?_
  rw [← Summable.tsum_finsetSum (hξ X)]
  refine tsum_congr fun ξ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hfg : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ (j : J₀) (lam : ℤ) (t : Fin 3 → ℝ) (k : Fin 4 → Mom d),
        unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3) =
          recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
              ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
            twistedLocalKernelFWL p (gU j) (SU j)
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).1
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).2
              L γ δ (F j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
    intro y hy j lam t k
    obtain ⟨M, _, hR⟩ := (mem_classU hprime).mp hy
    unfold unitRecenteredFWL
    rw [hR.sign_upper j, unitKernelFWL_classProd hprime ((mem_classU hprime).mp hy) j]
    rfl
  rw [sum_classU_outerValMμD (Us := unitsSplit B₀) (p := p) (kind := kind)
    (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime (unitsRegion B₀ hdisj₀) G L γ δ base roots tt Dom hinges
    (Zw X) hG μ (amp X ξ) (frq X ξ) route hclk hmom _
    (fun j lam t k x => recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
        ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
      twistedLocalKernelFWL p (gU j) (SU j) x.1 x.2 L γ δ (F j) base (modW lam) (t 0) (t 1) (t 2)
        (k 0) (k 1) (k 2) (k 3))
    hfg (hint X ξ) (hsm X ξ)]
  congr 1
  funext j lam t k
  unfold twistedRecenteredFWL
  exact (Finset.mul_sum _ _ _).symm
-- [end copied]

/-! ## The unit kernels only read the regional slots and the unit tops -/

section Agree
variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] (blk : J → CLBlock S) (hS : S.IsPlain)

/-- Two slot families agree on the regional slots and at the tops of the units. -/
def RegAgree (Fs Fs' : SlotFamW S d) : Prop :=
  ∀ j, (∀ p ∈ clRegionalPairs hS (blk j).atoms, Fs.fs (.inl p) = Fs'.fs (.inl p)) ∧
    (∀ v ∈ (blk j).atoms.erase (blk j).upper, Fs.fs (.inr v) = Fs'.fs (.inr v)) ∧
    Fs.tw (blk j).upper = Fs'.tw (blk j).upper

variable {blk hS}

theorem starProdGW_agree {Fs Fs' : SlotFamW S d} (h : RegAgree blk hS Fs Fs') (L : ℝ) (base : Mom d) (j : J)
    (top : ℝ) (x : GNode S.tree → (Fin d → ℤ)) (u : GBranch S.tree → ℝ) :
    starProdGW hS Fs L base (blk j).atoms (blk j).upper top x u =
      starProdGW hS Fs' L base (blk j).atoms (blk j).upper top x u := by
  unfold starProdGW
  rw [(h j).2.2]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (Finset.prod_congr rfl fun p hp => ?_)
    (Finset.prod_congr rfl fun v hv => ?_)) rfl
  · rw [(h j).1 p hp]
  · rw [(h j).2.1 v hv]

/-- **The unit kernels only read the regional slots and the unit tops.** -/
theorem unitKernelMGW_agree {Fs Fs' : SlotFamW S d} (h : RegAgree blk hS Fs Fs') (D : ReconstructionData S)
    (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (base : Mom d) :
    unitKernelMGW blk D hS Fs L γ δ layer base = unitKernelMGW blk D hS Fs' L γ δ layer base := by
  unfold unitKernelMGW clLocalSummandGW clLocalStarProductGW
  simp only [starProdGW_agree h]

theorem regMeasW_agree {Fs Fs' : SlotFamW S d} (h : RegAgree blk hS Fs Fs') (L : ℝ) (base : Mom d) (j : J)
    (hm : RegMeasW hS Fs' L base (blk j).atoms (blk j).upper) : RegMeasW hS Fs L base (blk j).atoms (blk j).upper :=
  ⟨fun p hp n => by rw [(h j).1 p hp]; exact hm.1 p hp n,
    fun v hv n => by rw [(h j).2.1 v hv]; exact hm.2 v hv n⟩

/-- **The regional bound transfers along an agreement** (same `lb`, `lbC`). -/
def RegBoundW.ofAgree {Fs Fs' : SlotFamW S d} {L : ℝ} {base : Mom d} (RB : RegBoundW blk hS Fs' L base)
    (h : RegAgree blk hS Fs Fs') : RegBoundW blk hS Fs L base where
  lb := RB.lb
  lbC := RB.lbC
  nonneg := RB.nonneg
  norm_le := fun j x top u => by
    rw [starProdGW_agree h L base j top x u]
    exact RB.norm_le j x top u
  summable := RB.summable
  tsum_le := RB.tsum_le
  meas := fun j => regMeasW_agree h L base j (RB.meas j)

/-- A regional pair is not an outer slot of a splice shape. -/
theorem iota_ne_regPair {Gsb : Garden w} (Φ : SpliceShape blk Gsb) (hSb : Gsb.IsPlain) (j : J) {p : SourcePair S}
    (hp : p ∈ clRegionalPairs hS (blk j).atoms) (s' : ReplacementSlot Gsb) : Φ.iota hS hSb s' ≠ .inl p := by
  classical
  intro hs'
  have hmem := Φ.iota_mem_outer hS hSb s'
  rw [hs'] at hmem
  exact (Finset.mem_filter.mp hmem).2 j ((mem_regSlots_inl hS j p).mpr (Finset.mem_filter.mp hp).2)

/-- An interior chain slot of a unit is not an outer slot of a splice shape. -/
theorem iota_ne_regChain {Gsb : Garden w} (Φ : SpliceShape blk Gsb) (hSb : Gsb.IsPlain) (j : J) {v : GBranch S.tree}
    (hv : v ∈ (blk j).atoms.erase (blk j).upper) (s' : ReplacementSlot Gsb) : Φ.iota hS hSb s' ≠ .inr v := by
  classical
  intro hs'
  have hmem := Φ.iota_mem_outer hS hSb s'
  rw [hs'] at hmem
  exact (Finset.mem_filter.mp hmem).2 j ((mem_regSlots_inr hS j v).mpr
    (VineB.mem_inter.mpr ⟨(Finset.mem_erase.mp hv).2, (Finset.mem_erase.mp hv).1⟩))

end Agree

/-! ## The uniform chain-piece mass -/

/-- A moment mass bound with `maxBracketPow ≥ 1` bounds the total weight. -/
theorem tsum_w_le_of_mass (D : SlotDatum d) {θ : ℝ} (hθ : 0 ≤ θ) {M : ℝ}
    (hM : ∑' l, maxBracketPow θ (half (D.m l)) * ENNReal.ofReal (D.w l) ≤ ENNReal.ofReal M) :
    ∑' l, D.w l ≤ max M 0 := by
  have := D.cnt
  have h1 : ENNReal.ofReal (∑' l, D.w l) = ∑' l, ENNReal.ofReal (D.w l) :=
    ENNReal.ofReal_tsum_of_nonneg D.w_nn D.w_sum
  have h2 : ∑' l, ENNReal.ofReal (D.w l) ≤ ∑' l, maxBracketPow θ (half (D.m l)) * ENNReal.ofReal (D.w l) :=
    ENNReal.tsum_le_tsum fun l => le_mul_of_one_le_left bot_le (RepAnalytic.one_le_maxBracketPow hθ _)
  have h3 : ENNReal.ofReal (∑' l, D.w l) ≤ ENNReal.ofReal (max M 0) :=
    (h1.le.trans (h2.trans hM)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).mp h3

/-- **The uniform chain-piece mass bound** (`hMC` of VBC) from the moment masses of `SlotDataOK`: the slot masses are
centre-free, so one constant (a finite sum over the centred slots) bounds every `∑' l, (famCOfData sd c y).w l`. -/
theorem exists_hMC {Kg : ℕ → ℝ → ℝ} {P : WTParams} (hη0 : 0 ≤ P.η) {C : ℝ} {R : ℕ} {p : ℕ}
    {a : PrescribedPrimeGarden (2 * R)} {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat} {t s : ℝ}
    {kSel σ : Fin (2 * R) → Option ℕ} {Rs : Fin (2 * R) → ℝ} {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    {h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ} {b : ℝ} {Rf : Fin (2 * R) → Option ℝ}
    {dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)} {Mk : Set (Stage1.CLVine a.prime.skeleton)}
    {sd : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G → (Fin P.d → ℤ) → SlotDatum P.d}
    (hsd : SlotDataOK Kg P C p a J pat t s kSel σ Rs roots h b Rf dag Mk sd) :
    ∃ MC : ℝ, ∀ (c : CentredSlot (stSt a.prime.skeleton a.totalSigma Mk).G) (y : Fin P.d → ℤ),
      ∑' l, (famCOfData sd c y).w l ≤ MC := by
  classical
  set A : CentredSlot (stSt a.prime.skeleton a.totalSigma Mk).G → ℝ := fun c =>
    max (Kg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (iotaAt a Mk (.inr c.1))) 0 +
      max (Kg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) * genSlotMass P C b a J pat t s kSel Rs (iotaAt a Mk (.inr c.1))) 0
    with hA
  refine ⟨∑ c, A c, fun c y => ?_⟩
  have hA0 : ∀ c, 0 ≤ A c := fun c => add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hle : A c ≤ ∑ c, A c := Finset.single_le_sum (fun c _ => hA0 c) (Finset.mem_univ c)
  refine le_trans ?_ hle
  show ∑' l, (sd (.inr c.1) y).w l ≤ A c
  by_cases hsel : SelAdj (a.prime.data) a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
      (iotaAt a Mk (.inr c.1))
  · exact (tsum_w_le_of_mass _ (by norm_num) (hsd.massSel (.inr c.1) y hsel)).trans (le_add_of_nonneg_left
      (le_max_right _ _))
  · exact (tsum_w_le_of_mass _ hη0 (hsd.massEta (.inr c.1) y hsel)).trans (le_add_of_nonneg_right
      (le_max_right _ _))

end WaveTurbulence.Flower.MkSlotsI
