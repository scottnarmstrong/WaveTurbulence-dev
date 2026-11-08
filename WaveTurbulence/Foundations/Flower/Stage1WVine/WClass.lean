/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WHinge1

/-! # STAGE1W-VINE (T4 consumed): the weighted class sum in mode form

* `weightedClassFactorization_dep`: V5W-0's T4 `weightedClassFactorization` (one mode type `Ξ` for all type indices) in
  the form with mode types `Ξ i` depending on the type index (as main's `sum_tauClass_vineD_api_dep`): T4 is applied on the
  common mode type `Σ i, Ξ i` with the weights `sigWt` supported on the fiber of each `i` (the cross terms carry weight
  `0`; their integrability/summability is part of the hypotheses).
* `class_sum_modesW` (main's `class_sum_modes`, RepVD10, with the frontier weight): the sum of the weighted values over
  the unit class of the representative is the outer mode sum of the representative with the weighted class kernels
  `unitHkFW`, from the member identity `member_hVW` and the integrability data `member_integW`, `member_hsmW`.
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
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA
  WaveTurbulence.VineEstS2

/-! ## Mode families on the common mode type `Σ i, Ξ i` -/

section Sigma
variable {I : Type*} {Ξ : I → Type*}

open scoped Classical in
/-- The weights on `Σ i, Ξ i` supported on the fiber of `i`. -/
def sigWt (Wt : ∀ i, Ξ i → ℂ) (i : I) (x : Σ i', Ξ i') : ℂ := if x.1 = i then Wt x.1 x.2 else 0

theorem sigWt_mk (Wt : ∀ i, Ξ i → ℂ) (i : I) (ξ : Ξ i) : sigWt Wt i ⟨i, ξ⟩ = Wt i ξ := by
  unfold sigWt
  rw [if_pos rfl]

theorem sigWt_ne (Wt : ∀ i, Ξ i → ℂ) (i i' : I) (h : i' ≠ i) (ξ : Ξ i') : sigWt Wt i ⟨i', ξ⟩ = 0 := by
  unfold sigWt
  rw [if_neg h]

theorem sigWt_support (Wt : ∀ i, Ξ i → ℂ) (Φ : ∀ i', Ξ i' → ℂ) (i : I) :
    ∀ x ∉ Set.range (Sigma.mk i : Ξ i → Σ i', Ξ i'), sigWt Wt i x * Φ x.1 x.2 = 0 := by
  rintro ⟨i', ξ⟩ hx
  by_cases h : i' = i
  · subst h; exact absurd ⟨ξ, rfl⟩ hx
  · rw [sigWt_ne Wt i i' h ξ, zero_mul]

theorem tsum_sigWt_mul (Wt : ∀ i, Ξ i → ℂ) (Φ : ∀ i', Ξ i' → ℂ) (i : I) :
    ∑' x : (Σ i', Ξ i'), sigWt Wt i x * Φ x.1 x.2 = ∑' ξ : Ξ i, Wt i ξ * Φ i ξ := by
  have hinj : Function.Injective (Sigma.mk i : Ξ i → Σ i', Ξ i') := sigma_mk_injective
  rw [← hinj.tsum_eq (f := fun x : (Σ i', Ξ i') => sigWt Wt i x * Φ x.1 x.2)]
  · exact tsum_congr fun ξ => by rw [sigWt_mk]
  · intro x hx
    by_contra hn
    exact hx (sigWt_support Wt Φ i x hn)

theorem summable_sigWt_mul_iff (Wt : ∀ i, Ξ i → ℂ) (Φ : ∀ i', Ξ i' → ℂ) (i : I) :
    Summable (fun x : (Σ i', Ξ i') => sigWt Wt i x * Φ x.1 x.2) ↔ Summable (fun ξ : Ξ i => Wt i ξ * Φ i ξ) := by
  have hinj : Function.Injective (Sigma.mk i : Ξ i → Σ i', Ξ i') := sigma_mk_injective
  rw [← hinj.summable_iff (sigWt_support Wt Φ i)]
  exact summable_congr fun ξ => by simp only [Function.comp_apply, sigWt_mk]

end Sigma

/-- **T4 with index-dependent mode types**, from V5W-0's `weightedClassFactorization` on `Σ i, Ξ i`. -/
theorem weightedClassFactorization_dep {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) {J₀ : Type} [Fintype J₀]
    [DecidableEq J₀] {U₀ : J₀ → Finset (GBranch S.tree)} {a₀ b₀ : J₀ → GBranch S.tree}
    {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)} {n₀ : J₀ → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j))
    (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j')) (hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool}
    (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = (unitsStart B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) {I : Type*} [Fintype I] (sgn : I → ℂ) {Ξ : I → Type*} (Wt : ∀ i, Ξ i → ℂ) {d : ℕ}
    (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (lay : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℝ)
    (hG : G.IsPlain) (amp : ∀ i, Ξ i → ReplacementSlot G → Mom d → ℂ) (frq : ∀ i, Ξ i → ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀) (hclk : J₀ → Fin 3 → ClkSrc G)
    (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (gU : J₀ → Mom d → ℂ) (SU : J₀ → Option ℝ)
    (hV : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      V y.1.layered = ∑ i, sgn i * ∑' ξ : Ξ i, Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)))
    (hξ : ∀ i, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun ξ : Ξ i => Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    (hint : ∀ i i' (ξ : Ξ i'), ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer)
        (unitsRegion B₀ hdisj₀), ∀ z,
      Integrable (outerIntegrandM G L γ δ base roots tt lay hG (amp i' ξ) (frq i' ξ) route hclk hmom
        (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
          (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z))
    (hsm : ∀ i i' (ξ : Ξ i'), ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer)
        (unitsRegion B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
          ∫ τ, outerIntegrandM G L γ δ base roots tt lay hG (amp i' ξ) (frq i' ξ) route hclk hmom
            (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
              (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ)) :
    ∑ LG ∈ T, V LG = ∑ i, sgn i * ∑' ξ : Ξ i, Wt i ξ *
      outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => twistedRecenteredFW p (gU j) (SU j) S (a₀ j)
          (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
          L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) := by
  have key := weightedClassFactorization D hS layer hLayer B₀ hdisj₀ hprime T hT V sgn (Ξ := Σ i, Ξ i) (sigWt Wt)
    G L γ δ base roots tt lay hinges Zw hG (fun _ x => amp x.1 x.2) (fun _ x => frq x.1 x.2) route hclk hmom F gU SU
    (fun y hy => by
      rw [hV y hy]
      refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
      exact (tsum_sigWt_mul Wt (fun i' ξ => outerValM G L γ δ base roots tt lay hinges Zw hG (amp i' ξ) (frq i' ξ)
        route hclk hmom (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
          (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) i).symm)
    (fun i y hy => (summable_sigWt_mul_iff Wt (fun i' ξ => outerValM G L γ δ base roots tt lay hinges Zw hG
        (amp i' ξ) (frq i' ξ) route hclk hmom (fun j lam t k => unitRecenteredFW p (gU j) (SU j) y.1 (y.2 j) L γ δ
          (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) i).2 (hξ i y hy))
    (fun i x y hy z => hint i x.1 x.2 y hy z)
    (fun i x y hy => hsm i x.1 x.2 y hy)
  rw [key]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  exact tsum_sigWt_mul Wt (fun i' ξ => outerValM G L γ δ base roots tt lay hinges Zw hG (amp i' ξ) (frq i' ξ)
    route hclk hmom (fun j lam t k => twistedRecenteredFW p (gU j) (SU j) S (a₀ j)
      (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
      L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) i

variable {p : ℕ}

open scoped Classical in
/-- **The weighted class sum** (main's `class_sum_modes` with the frontier weight, through T4). -/
theorem class_sum_modesW {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (π : PcA R p (objKind (2 * R)) A)
    (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p (objKind (2 * R)) → ∀ x, stateLayer y.1 x ≤ p)
    (hcanM : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p (objKind (2 * R)) → IsCanonGC (p + 1) y.1.layered)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (hctrl : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p (objKind (2 * R)) → U.toLF.Controlled y.1.layered)
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (fam : U.ι → SlotFam a.fullProfile.piece.gap.garden P.d)
    (hexpR : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) P.L P.γ P.δ (U.h i) p g
        ((profileShape a).iota a.prime.prime.1 hG s') ts x))
    (T : Finset (LayeredGarden (2 * R)))
    (hT : (T : Set (LayeredGarden (2 * R))) = a.outputs (p := p) (kind := objKind (2 * R))) :
    ∑ LG ∈ T, valueSelW U.toLF tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG)
        (fwWeight p g base LG) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC a P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape a).route a.prime.prime.1 hG)
            ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            (fun j lam t k => unitHkFW P p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a) g
              (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j) base lam t k)) := by
  letI : Fintype U.ι := U.fin
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hall := fun y hy => member_hVW π a hπ P U hd1 hL1 tt htt base roots hlay hcanM hB g cψ hc hg hG fam hexpR y hy
    (hctrl y hy)
  have key := weightedClassFactorization_dep a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    (sourceAssembly a) (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) a.prime.prime T
    (sourceClass_hT a T hT)
    (fun LG => valueSelW U.toLF tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG) (fwWeight p g base LG))
    (fun i => ((U.sign i : ℝ) : ℂ)) (Ξ := fun i => ∀ s, (fam i).Λ s) (fun i ξ => ((modeWt (fam i) ξ : ℝ) : ℂ))
    a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt a.fullProfile.piece.layer a.fullProfile.piece.hinges
    (fun z => if selSkC a P.L P.γ P.η hL0.ne' base roots z then (1 : ℝ) else 0) hG
    (fun i ξ s x => (fam i).a s (ξ s) x) (fun i ξ s => (fam i).m s (ξ s))
    ((profileShape a).route a.prime.prime.1 hG)
    ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
    ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
    (fun i j => unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
    (fun j => g (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).upper.1.1) (fun _ => none)
    (fun y hy => (hall y hy).1)
    (fun i y hy => (hall y hy).2 i)
    (fun i i' ξ y hy z => member_integW a P U hd1 hL1 tt base roots hlay hcanM hB g cψ hc hg hG
      (fun s x => (fam i').a s (ξ s) x) (fun s => (fam i').m s (ξ s)) y hy i z)
    (fun i i' ξ y hy => member_hsmW a P U hd1 hL1 tt base roots hlay hcanM hB g cψ hc hg hG
      (fun s x => (fam i').a s (ξ s) x) (fun s => (fam i').m s (ξ s))
      (tsum_ampBound_mode_le (fam i') hG P.L hL0 base roots ξ).1
      (fun z => if selSkC a P.L P.γ P.η hL0.ne' base roots z then (1 : ℝ) else 0)
      (fun z => by split_ifs <;> simp) y hy i)
  unfold unitHkFW
  exact key

end WaveTurbulence.Flower.Stage1WVine
