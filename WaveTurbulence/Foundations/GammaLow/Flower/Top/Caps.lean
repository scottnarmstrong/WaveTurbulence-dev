/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Top.MkAsm
public import WaveTurbulence.Foundations.Flower.CapsStable.Top

/-! # FLOWER-LOW (packet L8), item B (5/6): the capped decomposition helpers, `0 < γ ≤ 1/2`

Main's `Flower.CapsComp.{DecompF, DecompG, Top}` and `Flower.CapsStable.Top` γ-carrying declarations copied by
source, `1 / 2 < P.γ` ↦ `P.γ ≤ 1 / 2`, names suffixed `Low`; the label twist stability `capsTwistStable` is main's
(γ-free). -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CapsComp
open scoped Classical
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkAsm
variable {w : ℕ}

/-- **`CapsDecompFLow` from the label twist stability.** -/
theorem capsDecompFAt_of_stableLow (hst : CapsTwistStable) (Pm : ℕ) (P : WTParams) : CapsDecompFAtLow Pm P := by
  intro hL _ p hp t _ s _ n n' ζ N hN kind pat dagger h b hb hh Rf σ hRf hdecay
  have hdecay' : ((∃ i, σ i ≠ none) ∨ ∃ i, (fun _ : Fin (2 * Pm) => (none : Option ℕ)) i ≠ none) →
      ∀ j, ∃ r, Rf j = some r ∧ (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧
        r ^ 10 ≤ ‖latticePoint P.L n‖ := by
    rintro (h1 | ⟨i, hi⟩)
    · exact hdecay h1
    · exact absurd rfl hi
  refine ⟨↥(strSet P p N kind pat ζ), inferInstance, fun x => x.1.m,
    fun x c => compData P p N kind pat ζ hp hN hst t s b hb (fun _ => none) (fun j hj => by simp at hj) Rf hRf σ
      (fun _ => P.L) (fun _ => le_rfl) h hh dagger n n' hdecay' x c, ?_, fun x => ?_, fun x => ?_,
    fun x c j => ?_, ?_⟩
  · rw [Fintype.card_coe]
    have := card_strSet_le P p N kind pat ζ (w := 2 * Pm)
    have e : 2 * (2 * Pm) = 4 * Pm := by ring
    rw [e] at this
    exact_mod_cast this
  · show ∑ c, 2 * x.1.R c = 4 * Pm
    rw [sum_two_R (valid_of_mem x.2) (capSgn ζ)]
    ring
  · exact sum_n_of_mem hp hN x.2
  · show capExt (fun _ => none) none _ = none
    rw [capExt_const]
  · rw [flowerWeighted_coreF_eq_capSum P p N kind pat dagger h Rf σ (capExt (fun _ => P.L) P.L) ζ t s n n']
    have e : ∀ LG : LayeredGarden (2 * Pm), selOK (capLayered LG p) (capJ (2 * Pm)) (fun _ => none) =
        selOK (capLayered LG p) (capJ (2 * Pm)) (capExt (fun _ => none) none) := fun LG => by rw [capExt_const]
    have e2 : ∀ LG : LayeredGarden (2 * Pm), selCap (capLayered LG p) (capJ (2 * Pm)) (fun _ => none) =
        selCap (capLayered LG p) (capJ (2 * Pm)) (capExt (fun _ => none) none) := fun LG => by rw [capExt_const]
    simp only [e, e2]
    have hS := sum_carrier_eq_prod (P := P) (p := p) (N := N) (kind := kind) (pat := pat) (ζ := ζ) hp hN
      (capExt (fun _ => none) none) (capExt Rf none) (capExt σ none) (capExt (fun _ => P.L) P.L) (capH h)
      (capDag dagger) (capRoots (fun _ => n) n') t s
      (hs_classX hL t s b hb _ _ _ _ h hh _ n n')
    unfold capVal capWt at hS
    refine hS.trans (Finset.sum_congr rfl fun x _ => Finset.prod_congr rfl fun c _ => ?_)
    exact (val_compData hp hN hst t s b hb (fun _ => none) _ Rf hRf σ (fun _ => P.L) _ h hh dagger n n'
      hdecay' x c).symm

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CapsComp
open scoped Classical
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkAsm
variable {w : ℕ}

/-- **`CapsDecompFLow`** (all parameters), from the label twist stability. -/
theorem capsDecompF_of_stableLow (hst : CapsTwistStable) : CapsDecompFLow :=
  fun Pm P => capsDecompFAt_of_stableLow hst Pm P

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CapsComp
open scoped Classical
open TTree Finset MeasureTheory WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkAsm GraftGen
variable {w : ℕ}

/-- **`CapsDecompGLow` from the label twist stability.** -/
theorem capsDecompGAt_of_stableLow (hst : CapsTwistStable) (Pm : ℕ) (P : WTParams) : CapsDecompGAtLow Pm P := by
  intro hL _ p hp t _ s _ n n' ζ N hN kind dagger h b hb hh Rf j₂ hj₂ hRf hsupp
  have hRf' : ∀ j r, (fun j => some (Rf j)) j = some r → P.L / 2 ≤ r := fun j r hr => by
    have : Rf j = r := Option.some.inj hr
    rw [← this]; exact hRf j
  have hdecay : ∀ kk : Fin (2 * Pm) → ℕ,
      ((∃ i, (fun _ : Fin (2 * Pm) => (none : Option ℕ)) i ≠ none) ∨ ∃ i, (fun j => some (kk j)) i ≠ none) →
      ∀ j, ∃ r, (fun j => some (Rf j)) j = some r ∧ (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧
        r ^ 10 ≤ ‖latticePoint P.L n‖ := fun _ _ j => ⟨Rf j, rfl, (hsupp j).1, (hsupp j).2⟩
  let D : (Fin (2 * Pm) → ℝ) → ∀ X : ↥(strSet P p N kind (fun _ => .plain) ζ) × ↥(depthSet (2 * Pm) N),
      Fin X.1.1.m → CompData P p t s b := fun Rs X c =>
    compData P p N kind (fun _ => .plain) ζ hp hN hst t s b hb (fun j => some (X.2.1 j)) (fun _ _ => rfl)
      (fun j => some (Rf j)) hRf' (fun _ => none) (fun j => max P.L (Rs j)) (fun j => le_max_left _ _) h hh dagger
      n n' (hdecay X.2.1) X.1 c
  refine ⟨↥(strSet P p N kind (fun _ => .plain) ζ) × ↥(depthSet (2 * Pm) N), inferInstance, fun X => X.1.1.m, D,
    ?_, fun Rs hRs X => ⟨?_, sum_n_of_mem hp hN X.1.2, fun _ => ?_⟩, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, card_depthSet]
    have h1 := card_strSet_le P p N kind (fun _ => FixPat.plain) ζ (w := 2 * Pm)
    have e : 2 * (2 * Pm) = 4 * Pm := by ring
    rw [e] at h1
    have h2 : ((N : ℝ) + 1) ^ (4 * Pm) = ((N : ℝ) + 1) ^ (2 * Pm) * ((N : ℝ) + 1) ^ (2 * Pm) := by
      rw [← pow_add]; ring_nf
    rw [h2, ← mul_assoc]
    push_cast
    gcongr
    exact_mod_cast h1
  · show ∑ c, 2 * X.1.1.R c = 4 * Pm
    rw [sum_two_R (valid_of_mem X.1.2) (capSgn ζ)]
    ring
  · have := prod_gain hp hN hst t s b hb X.2.1 (fun j => some (Rf j)) hRf' (fun j => max P.L (Rs j))
      (fun j => le_max_left _ _) h hh dagger n n' (hdecay X.2.1) X.1
    refine this.trans (Finset.prod_congr rfl fun j _ => ?_)
    rw [max_eq_right (le_of_mem_shellBox hL hRs j)]
  · rw [CapsFub.coreG_shell_exchange P hL p N kind dagger h b hb hh Rf hRf j₂ hj₂ ζ t s n n']
    refine setIntegral_congr_fun (CapsFub.measurableSet_shellBox _ _ _) fun R hR => ?_
    have hRL : ∀ j, P.L ≤ R j := le_of_mem_shellBox hL hR
    rw [flowerWeighted_eq_capSum]
    -- the depth sum at every carrier garden
    have hLG : ∀ LG ∈ carrierF P p N kind (fun _ => FixPat.plain) ζ,
        kernelKgen P.L P.γ P.δ (fun _ _ => 1) (capLayered LG p) (capFix LG (fun _ => .plain) t s)
          (capOff LG dagger) (capW LG dagger (fun k => Typed.frontierW LG p (fun j => some (Rf j)) k *
            CapsFub.shellIntegrand LG P.L k R * Typed.leafProd LG h k)) (fun _ => t) 0 (capRoots (fun _ => n) n') 0 =
        ∑ kk ∈ depthSet (2 * Pm) N, capVal P p (fun _ => .plain) (capKSel kk) (capExt (fun j => some (Rf j)) none)
          (fun _ => none) (capExt R P.L) (capH h) (capDag dagger) (capRoots (fun _ => n) n') t s (capLayered LG p) := by
      intro LG hLG
      have hc := (Set.Finite.mem_toFinset _).1 hLG
      have hF := oneFlower_of_isFlowerGarden hc.1.1
      have hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p :=
        fun ℓ hℓ => hc.1.2.1 _ ⟨ℓ, hℓ, GNode.isDesc_refl _⟩
      have hM : ∀ j, ∀ b ∈ Cases.stemSet LG j, b.1.2.length ≤ N := fun j b hb' => by
        have := stemSet_length_le_order LG j b hb'
        rwa [hc.2.2.1] at this
      rw [capW_shell_depth LG p hF hfl P.L N hM Rf R h dagger, capFix_eq_fixCap LG p hF,
        capOff_eq_offCap LG p hF]
      have hlin := Polar.kernelKgen_linear_step P.L P.γ P.δ (fun _ _ => 1) (capLayered LG p)
        (fixCap (capLayered LG p) (capJ (2 * Pm)) (capExt (fun _ => FixPat.plain) .plain) t s)
        (offCap (capLayered LG p) (capJ (2 * Pm)) (capDag dagger).isSome) (fun _ => t) 0 (capRoots (fun _ => n) n') 0
        (depthSet (2 * Pm) N) (fun _ => 1) 1
        (fun k => ∑ kk ∈ depthSet (2 * Pm) N, capWt (capLayered LG p) (capJ (2 * Pm)) p P.L (capKSel kk)
          (capExt (fun j => some (Rf j)) none) (fun _ => none) (capExt R P.L) (capH h) (capDag dagger) k)
        (fun kk => capWt (capLayered LG p) (capJ (2 * Pm)) p P.L (capKSel kk) (capExt (fun j => some (Rf j)) none)
          (fun _ => none) (capExt R P.L) (capH h) (capDag dagger))
        (fun κ => by simp only [one_mul])
        (fun kk _ => summable_capped hL hc _ _ _ _ _ _ h b hb hh _ t n n')
      simp only [Complex.ofReal_one, one_mul] at hlin
      exact hlin
    refine (Finset.sum_congr rfl hLG).trans ?_
    rw [Finset.sum_comm, ← Finset.sum_coe_sort (depthSet (2 * Pm) N)]
    -- each depth label decomposes as in Core-F
    have hdep : ∀ kk : ↥(depthSet (2 * Pm) N),
        ∑ LG ∈ carrierF P p N kind (fun _ => FixPat.plain) ζ, capVal P p (fun _ => .plain) (capKSel kk.1)
          (capExt (fun j => some (Rf j)) none) (fun _ => none) (capExt R P.L) (capH h) (capDag dagger)
          (capRoots (fun _ => n) n') t s (capLayered LG p) =
        ∑ x : ↥(strSet P p N kind (fun _ => .plain) ζ), ∏ c : Fin x.1.m, (D R (x, kk) c).val := by
      intro kk
      refine (sum_carrier_eq_prod hp hN _ _ _ _ _ _ _ t s (hs_classX hL t s b hb _ _ _ _ h hh _ n n')).trans
        (Finset.sum_congr rfl fun x _ => Finset.prod_congr rfl fun c _ => ?_)
      rw [val_compData, capExt_const, capExt_max_eq R hRL]
      rfl
    rw [Finset.sum_congr rfl fun kk _ => hdep kk, Fintype.sum_prod_type]
    exact Finset.sum_comm

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CapsComp
open scoped Classical
open TTree Finset MeasureTheory WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkAsm GraftGen
variable {w : ℕ}

/-- **`CapsDecompGLow`** (all parameters), from the label twist stability. -/
theorem capsDecompG_of_stableLow (hst : CapsTwistStable) : CapsDecompGLow :=
  fun Pm P => capsDecompGAt_of_stableLow hst Pm P

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CapsComp
open scoped Classical
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkAsm

/-- **The composite** (conditional on the label twist stability). -/
theorem flower_low_of_marked_of_stable (hst : CapsTwistStable) (B : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 24000)
    (hM : WTPrefixP (MarkedComponentBoundAtILow B)) (hCouple : CoupleClauseLowInput) : LayergardenFlowerLowGate :=
  flower_low_of_marked_of_caps (capsDecompF_of_stableLow hst) (capsDecompG_of_stableLow hst) B hB0 hB hM hCouple

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CapsStable
open scoped Classical
open WaveTurbulence.Flower.MkDefs

/-- **The flower gate from the marked component bound.** -/
theorem flower_low_of_marked_stable (B : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 24000)
    (hM : WTPrefixP (MarkedComponentBoundAtILow B)) (hCouple : CoupleClauseLowInput) : LayergardenFlowerLowGate :=
  flower_low_of_marked_of_stable capsTwistStable B hB0 hB hM hCouple

end

end WaveTurbulence.GammaLow.Flower
