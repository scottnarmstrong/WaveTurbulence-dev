/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntCore3
public import WaveTurbulence.Foundations.Flower.MkSlots.IntSlotFam
public import WaveTurbulence.Foundations.Flower.MkSlots.IntWeight
public import WaveTurbulence.Foundations.Flower.MkSlots.CapFin
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability

/-! # B3s MK-SLOTS (integration, member identity 1): auxiliary lemmas

* `kernelLeavesSelNWF_mul_ind`: a multiplier factor that is a constant times an indicator on coset decorations moves
  into the selection and in front;
* `capKernel_reconstruction`: the pinned capped kernel of a decoded garden at the selection `selAt` is the one of the
  reconstruction at the collapsed selection (`subst`);
* `norm_chainW_le`, `anchProfiles_summable` (the hypotheses of the pinned reduction);
* `isCapPair_iota`, `capTreeOf_iota`: cap pairs through a splice shape; `capSwap_congr`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlots.IntMember

/-- **A constant times an indicator in the multiplier.** -/
theorem kernelLeavesSelNWF_mul_ind {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel Q : GenDecoration LG.garden d nroot nfl → Prop) (m₀ r : (GNode LG.garden.tree → Mom d) → ℂ) (c : ℂ)
    (hr : ∀ κ : GenDecoration LG.garden d nroot nfl,
      r (cosetDecoration LG.garden L k₀ κ.1) = if Q κ then c else 0)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWF L γ δ LG H up s k₀ nroot nfl sel (fun k => m₀ k * r k) fix =
      c * kernelLeavesSelNWF L γ δ LG H up s k₀ nroot nfl (fun κ => sel κ ∧ Q κ) m₀ fix := by
  unfold kernelLeavesSelNWF
  rw [mul_left_comm c]
  congr 1
  refine (tsum_congr fun κ => ?_).trans tsum_mul_left
  simp only [hr κ]
  by_cases hs : sel κ <;> by_cases hq : Q κ <;> simp [hs, hq] <;> ring

/-- **The capped kernel of a decoded garden is the one of the reconstruction.** -/
theorem capKernel_reconstruction (P : WTParams) {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hprime : IsPrimeGarden S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hS layer hLayer = LG) (hd : D.Decodes hS LG.garden)
    (σ : NormalizedSplice.GroupPrescription S) (J : Finset (Fin w)) (p : ℕ) (t s : ℝ)
    (h : ℕ → Fin w → Fin w → Mom P.d → ℝ) (roots : Fin w → (Fin P.d → ℤ)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom P.d)) :
    kernelLeavesSelNWF P.L P.γ P.δ LG (anchProfiles J LG h P.L roots) (fun _ => t) 0 0 roots 0
        (fun κ => selAt P 0 ⟨S, hprime, D, hd⟩ σ κ)
        (fun k => ∏ z, capNodeW P.L P.γ P.δ p s LG J Rf dag z (k z)) (fixCap LG J (fun _ => FixPat.plain) t s) =
      kernelLeavesSelNWF P.L P.γ P.δ (layeredReconstruction D hS layer hLayer)
        (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots) (fun _ => t) 0 0 roots 0
        (fun κ => NormalizedSplice.selOf σ P.L P.γ P.η 0 (collapseGenDecoration D hS κ).1)
        (fun k => ∏ z, capNodeW P.L P.γ P.δ p s (layeredReconstruction D hS layer hLayer) J Rf dag z (k z))
        (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) := by
  subst hspec
  rfl

/-- The chain node weight is bounded by `1`. -/
theorem norm_chainW_le {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (L γ δ : ℝ) (p : ℕ) (s : ℝ)
    (J : Finset (Fin w)) (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (z : GNode (D.forest hS)) (x : Mom d) : ‖chainW D hS layer hLayer L γ δ p s J Rf dag z x‖ ≤ 1 := by
  have hf : ‖fwNode (layeredReconstruction D hS layer hLayer) p (fun j => frontierG (Rf j)) z x‖ ≤ 1 := by
    refine norm_fwNode_le (layeredReconstruction D hS layer hLayer) p _ 1 le_rfl (fun j y => ?_) z x
    unfold frontierG
    rw [Complex.norm_real, Real.norm_eq_abs]
    cases Rf j with
    | none => simp
    | some r =>
      simp only [Option.elim]
      rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
      exact XChain.ProductCut.chi0_le_one _
  unfold chainW
  rw [norm_mul]
  refine mul_le_one₀ hf (norm_nonneg _) ?_
  by_cases h1 : InCapNative D hS J z
  · rw [if_pos h1]
    exact norm_dagNodeW_le L γ δ s (layeredReconstruction D hS layer hLayer) J dag z x
  · rw [if_neg h1]
    by_cases h2 : IsCaseB D hS layer hLayer J z
    · rw [if_pos h2, norm_one]
    · rw [if_neg h2]
      exact norm_dagNodeW_le L γ δ s (layeredReconstruction D hS layer hLayer) J dag z x

/-- **The summability hypothesis of the pinned reduction** for the anchored profiles. -/
theorem anchProfiles_summable {w d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (p : ℕ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ) (hL : 1 ≤ L) (roots : Fin w → (Fin d → ℤ)) (b : ℝ) (hb : 0 ≤ b)
    (hd : 1 ≤ d) (hlay : ∀ a, LG.layer a ≤ p)
    (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal b)
    (ℓ : GLeaf LG.garden.tree) (k₀ : Mom d) :
    Summable fun n : Fin d → ℤ => |anchProfiles J LG h L roots ℓ.1 (k₀ + latticePoint L n)| := by
  have hL0 : L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL).ne'
  have hind : ∀ x : Mom d, Summable fun n : Fin d → ℤ =>
      |(fun y : Mom d => if y = x then (1 : ℝ) else 0) (k₀ + latticePoint L n)| := by
    intro x
    by_cases hx : ∃ n₀ : Fin d → ℤ, k₀ + latticePoint L n₀ = x
    · obtain ⟨n₀, hn₀⟩ := hx
      refine summable_of_ne_finset_zero (s := {n₀}) fun n hn => ?_
      have hne : n ≠ n₀ := fun h => hn (Finset.mem_singleton.mpr h)
      have : k₀ + latticePoint L n ≠ x := by
        rw [← hn₀]
        intro he
        exact hne (latticePoint_injective_of_ne_zero hL0 (add_left_cancel he))
      simp [this]
    · push_neg at hx
      have : (fun n : Fin d → ℤ => |(fun y : Mom d => if y = x then (1 : ℝ) else 0) (k₀ + latticePoint L n)|) =
          fun _ => 0 := funext fun n => by simp [hx n]
      rw [this]
      exact summable_zero
  unfold anchProfiles
  split_ifs with h1 h2
  · exact hind _
  · exact hind _
  · rw [typeProfiles_leaf]
    exact summable_abs_coset_of_SNormR (A := 40 * d) (B := 40 * d) hL (by omega) hb _
      (hB _ (hlay _) _ _) k₀

/-! ### Cap pairs through a splice shape -/

section Shape
variable {w d : ℕ} {S : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
  {G : Garden w} (Φ : SpliceShape blk G) (hS : S.IsPlain) (hG : G.IsPlain) (J : Finset (Fin w))

theorem leaf_fst (ℓ : GLeaf G.tree) : (Φ.leaf ℓ).1.1 = ℓ.1.1 := by
  have h := Φ.tree_eq ℓ.toNode
  rw [← Φ.leaf_node] at h
  exact h

/-- Cap pairs through a splice shape. -/
theorem isCapPair_iota (q : SourcePair G) :
    IsCapPair S hS J (pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG))) ↔ IsCapPair G hG J q := by
  unfold IsCapPair
  rw [Φ.iota_first hS hG q, Φ.iota_second hS hG q, leaf_fst, leaf_fst]

theorem capTreeOf_iota (q : SourcePair G) :
    capTreeOf S hS J (pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG))) = capTreeOf G hG J q := by
  unfold capTreeOf
  rw [Φ.iota_first hS hG q, Φ.iota_second hS hG q, leaf_fst, leaf_fst]

end Shape

/-- The cap swap only reads the non-cap slots of the old family. -/
theorem capSwap_congr {w d : ℕ} {S : Garden w} (hS : S.IsPlain) (J : Finset (Fin w))
    (Fs Fs' : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (Fcap : SourcePair S → (Fin 2 → ℝ) → Mom d → ℂ)
    (h : ∀ sl : ReplacementSlot S, (∀ q, sl = Sum.inl q → ¬ IsCapPair S hS J q) → Fs sl = Fs' sl) :
    capSwap hS J Fs Fcap = capSwap hS J Fs' Fcap := by
  funext sl
  rcases sl with q | b
  · show (if IsCapPair S hS J q then Fcap q else Fs (.inl q)) = (if IsCapPair S hS J q then Fcap q else Fs' (.inl q))
    by_cases hq : IsCapPair S hS J q
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq, h (.inl q) (fun q' he => by cases he; exact hq)]
  · exact h (.inr b) (fun q he => by cases he)

end WaveTurbulence.Flower.MkSlots.IntMember
