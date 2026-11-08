/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsE.ModeX

/-! # B3s-HELPER9 (MkSlotsE) 5: the mass of the centre-indexed mode sum

The centre-indexed modes are the pairs `⟨X, ξ⟩`, `X` an outer centre assignment, `ξ` a mode of the slot family
`famX fam₀ famC X`. A mode at `X` carries the restricted node-centre count `#ncsX (cl ξ) X` (`ModeX.repIntCMKS_modeX`).
Since the leaf-pair modes do not depend on `X` and `Σ_X #ncsX cl X ≤ nodeBallCard^m` (`NodeX.tsum_ncard_ncsX_le`),

`Σ_X Σ_ξ #ncsX · Π_s w ⟨m⟩^{θ_s} ≤ nodeBallCard^m · Π_s μ_s`

as soon as the per-slot masses at every centre are `≤ μ_s` UNIFORMLY in `X` (the chain modes at `X` are summed for
each `X` separately, the outer `X` sum is paid by the count):

* `tsum_sigma_split_le`: the abstract splitting (leaf part independent of `X`, chain part summed per `X`);
* `mode_pt_le`: the pointwise bound of one mode (the first step of δ's `MkSlotsS.modes_mass_sel_le`, copied);
* **`centre_modes_mass_le`**: δ's `modes_mass_sel_le` for the centre-indexed modes, with the count. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsS
open WaveTurbulence.Flower.MkSlotsI (CentredSlot chiX famX ChainPiece)
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsE

variable {w d : ℕ}

/-- **The abstract splitting**: a sigma sum whose fibre at `X` splits into an `X`-independent leaf part `a` (weight
`f a`, count `N X a`) and an `X`-dependent chain part `b` (weight `g X b`, summed per `X`). -/
theorem tsum_sigma_split_le {Xt : Type*} {Ξ : Xt → Type*} {ΛL : Type*} {ΛB : Xt → Type*}
    (e : ∀ X, Ξ X ≃ ΛL × ΛB X) (N : Xt → ΛL → ℝ≥0∞) (f : ΛL → ℝ≥0∞) (g : ∀ X, ΛB X → ℝ≥0∞)
    (F : ∀ X, Ξ X → ℝ≥0∞) (hF : ∀ X ξ, F X ξ = N X (e X ξ).1 * f (e X ξ).1 * g X (e X ξ).2)
    (Mg : ℝ≥0∞) (hg : ∀ X, ∑' b, g X b ≤ Mg) (Mn : ℝ≥0∞) (hN : ∀ a, ∑' X, N X a ≤ Mn) :
    ∑' p : (Σ X, Ξ X), F p.1 p.2 ≤ Mn * (∑' a, f a) * Mg := by
  rw [ENNReal.tsum_sigma' (fun p : (Σ X, Ξ X) => F p.1 p.2)]
  have hX : ∀ X, ∑' ξ : Ξ X, F X ξ ≤ ∑' a, N X a * f a * Mg := by
    intro X
    calc ∑' ξ : Ξ X, F X ξ = ∑' q : ΛL × ΛB X, N X q.1 * f q.1 * g X q.2 := by
          rw [← (e X).symm.tsum_eq]
          refine tsum_congr fun q => ?_
          rw [hF X, Equiv.apply_symm_apply]
      _ = ∑' a, ∑' b, N X a * f a * g X b :=
          ENNReal.tsum_prod (f := fun a b => N X a * f a * g X b)
      _ = ∑' a, N X a * f a * ∑' b, g X b := tsum_congr fun a => ENNReal.tsum_mul_left
      _ ≤ ∑' a, N X a * f a * Mg := ENNReal.tsum_le_tsum fun a => by gcongr; exact hg X
  calc ∑' X, ∑' ξ : Ξ X, F X ξ ≤ ∑' X, ∑' a, N X a * f a * Mg := ENNReal.tsum_le_tsum hX
    _ = ∑' a, ∑' X, N X a * f a * Mg := ENNReal.tsum_comm
    _ = ∑' a, (∑' X, N X a) * (f a * Mg) := tsum_congr fun a => by
        rw [← ENNReal.tsum_mul_right]; exact tsum_congr fun X => by ring
    _ ≤ ∑' a, Mn * (f a * Mg) := ENNReal.tsum_le_tsum fun a => by gcongr; exact hN a
    _ = Mn * (∑' a, f a) * Mg := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]; ring

/-- The pointwise bound of one mode (the first step of δ's `modes_mass_sel_le`, copied): the two clock losses and the
selection moments of every slot are paid by `Ks s · ⟨m_s/2⟩^{θ_s}`. -/
theorem mode_pt_le {G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) {Λ : ReplacementSlot G → Type}
    (W : ∀ s, Λ s → ℝ) (hW : ∀ s l, 0 ≤ W s l) (m : ∀ s, Λ s → Fin 2 → ℤ) {c : ℝ} (hc : 0 ≤ c)
    (e : ReplacementSlot G → Fin 2 → ℝ) (he : ∀ s i, 0 ≤ e s i) (θ : ReplacementSlot G → ℝ)
    (hθ : ∀ s, 2 * c + (e s 0 + e s 1) ≤ θ s) (Ks : ReplacementSlot G → ℝ)
    (hKs : ∀ s, (3 : ℝ) ^ (2 * c + (e s 0 + e s 1)) ≤ Ks s) (Kc : ℝ) (hKc : 0 ≤ Kc) (ξ : ∀ s, Λ s) :
    ENNReal.ofReal (‖(((∏ s, W s (ξ s) : ℝ)) : ℂ)‖ *
      (Kc * ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
      ∏ s, ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i) ≤
      ENNReal.ofReal Kc * ∏ s, (ENNReal.ofReal (Ks s) *
        (maxBracketPow (θ s) (half (m s (ξ s))) * ENNReal.ofReal (W s (ξ s)))) := by
  have hb := prod_modLam_le (fun s => m s (ξ s)) route hc
  have hp : 0 ≤ ∏ s, W s (ξ s) := Finset.prod_nonneg fun s _ => hW s _
  have hq : 0 ≤ ∏ s, ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i :=
    Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun i _ => by positivity
  rw [Complex.norm_real, Real.norm_of_nonneg hp]
  calc ENNReal.ofReal ((∏ s, W s (ξ s)) * (Kc * ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
        ∏ s, ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i)
      ≤ ENNReal.ofReal ((∏ s, W s (ξ s)) * (Kc * ∏ s, ∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) *
        ∏ s, ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i) := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hb hKc) hp) hq
    _ = ENNReal.ofReal (Kc * ∏ s, (W s (ξ s) * ((∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) *
          ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring_nf
    _ = ENNReal.ofReal Kc * ∏ s, ENNReal.ofReal (W s (ξ s) * ((∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) *
          ∏ i, (1 + |(m s (ξ s) i : ℝ)|) ^ e s i)) := by
        rw [ENNReal.ofReal_mul hKc, ENNReal.ofReal_prod_of_nonneg fun s _ => mul_nonneg (hW s _)
          (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (Finset.prod_nonneg fun i _ => by positivity))]
    _ ≤ _ := by
        gcongr with s
        rw [ENNReal.ofReal_mul (hW s _)]
        calc _ ≤ ENNReal.ofReal (W s (ξ s)) *
              (ENNReal.ofReal (Ks s) * maxBracketPow (θ s) (half (m s (ξ s)))) := by
              gcongr
              exact slot_moment_le _ (e s) hc (he s) (hθ s) (hKs s)
          _ = _ := by ring

section Centre

variable {S : Garden w} (hS : S.IsPlain) (fam₀ : SlotFam S d) (famC : CentredSlot S → (Fin d → ℤ) → ChainPiece d)

/-- The leaf modes (`X`-independent: on a leaf-pair slot `famX … X` is `fam₀ ⊕ ∅`). -/
abbrev LeafModes : Type := ∀ p : SourcePair S, (famX fam₀ famC 0).Λ (Sum.inl p)

/-- Splitting a mode at `X` into its leaf modes and its chain modes. -/
def splitX (X : CentredSlot S → (Fin d → ℤ)) :
    (∀ s, (famX fam₀ famC X).Λ s) ≃ LeafModes fam₀ famC × (∀ b : GBranch S.tree, (famX fam₀ famC X).Λ (Sum.inr b)) :=
  Equiv.sumPiEquivProdPi (fun s => (famX fam₀ famC X).Λ s)

/-- The leaf-pair centres of leaf modes. -/
def leafCtrL (a : LeafModes fam₀ famC) : GLeaf S.tree → Fin d → ℤ :=
  fun ℓ => (famX fam₀ famC 0).n (Sum.inl (pairOfLeaf S hS ℓ)) (a (pairOfLeaf S hS ℓ))

/-- **δ's `modes_mass_sel_le` for the centre-indexed modes, with the restricted node-centre count.** -/
theorem centre_modes_mass_le {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot S → Fin 2 → ClkSrc S ⊕ J) {c : ℝ} (hc : 0 ≤ c)
    (e : ReplacementSlot S → Fin 2 → ℝ) (he : ∀ s i, 0 ≤ e s i) (θ : ReplacementSlot S → ℝ)
    (hθ : ∀ s, 2 * c + (e s 0 + e s 1) ≤ θ s) (Ks : ReplacementSlot S → ℝ)
    (hKs : ∀ s, (3 : ℝ) ^ (2 * c + (e s 0 + e s 1)) ≤ Ks s) (μ : ReplacementSlot S → ℝ≥0∞)
    (hμ : ∀ (X : CentredSlot S → (Fin d → ℤ)) s, ∑' l, maxBracketPow (θ s) (half ((famX fam₀ famC X).m s l)) *
      ENNReal.ofReal ((famX fam₀ famC X).w s l) ≤ μ s)
    (Kc : ℝ) (hKc : 0 ≤ Kc) :
    ∑' p : (Σ X : CentredSlot S → (Fin d → ℤ), ∀ s, (famX fam₀ famC X).Λ s),
      (((ncsX (leafCtr hS (fun s => (famX fam₀ famC p.1).n s (p.2 s))) p.1).ncard : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (‖(((∏ s, (famX fam₀ famC p.1).w s (p.2 s) : ℝ)) : ℂ)‖ *
          (Kc * ∏ j, (1 + |((modLam (fun s => (famX fam₀ famC p.1).m s (p.2 s)) route j : ℤ) : ℝ)|) ^ c) *
          ∏ s, ∏ i, (1 + |((famX fam₀ famC p.1).m s (p.2 s) i : ℝ)|) ^ e s i) ≤
      ENNReal.ofReal Kc * ((nodeBallCard d ^ ∑ j, (S.tree j).order : ℕ) : ℝ≥0∞) *
        ∏ s, (ENNReal.ofReal (Ks s) * μ s) := by
  -- the per-slot weights
  set Fs : ∀ X : CentredSlot S → (Fin d → ℤ), ∀ s, (famX fam₀ famC X).Λ s → ℝ≥0∞ := fun X s l =>
    ENNReal.ofReal (Ks s) * (maxBracketPow (θ s) (half ((famX fam₀ famC X).m s l)) *
      ENNReal.ofReal ((famX fam₀ famC X).w s l)) with hFs
  have hW : ∀ X s l, 0 ≤ (famX fam₀ famC X).w s l := fun X => (famX fam₀ famC X).w_nn
  -- pointwise
  have h1 : ∀ p : (Σ X : CentredSlot S → (Fin d → ℤ), ∀ s, (famX fam₀ famC X).Λ s),
      (((ncsX (leafCtr hS (fun s => (famX fam₀ famC p.1).n s (p.2 s))) p.1).ncard : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (‖(((∏ s, (famX fam₀ famC p.1).w s (p.2 s) : ℝ)) : ℂ)‖ *
          (Kc * ∏ j, (1 + |((modLam (fun s => (famX fam₀ famC p.1).m s (p.2 s)) route j : ℤ) : ℝ)|) ^ c) *
          ∏ s, ∏ i, (1 + |((famX fam₀ famC p.1).m s (p.2 s) i : ℝ)|) ^ e s i) ≤
      ENNReal.ofReal Kc * ((((ncsX (leafCtr hS (fun s => (famX fam₀ famC p.1).n s (p.2 s))) p.1).ncard : ℕ) :
        ℝ≥0∞) * ∏ s, Fs p.1 s (p.2 s)) := by
    intro p
    have := mode_pt_le route (famX fam₀ famC p.1).w (hW p.1) (famX fam₀ famC p.1).m hc e he θ hθ Ks hKs Kc hKc p.2
    calc _ ≤ (((ncsX (leafCtr hS (fun s => (famX fam₀ famC p.1).n s (p.2 s))) p.1).ncard : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal Kc * ∏ s, Fs p.1 s (p.2 s)) := by gcongr
      _ = _ := by ring
  refine (ENNReal.tsum_le_tsum h1).trans ?_
  rw [ENNReal.tsum_mul_left, mul_assoc]
  gcongr
  -- the splitting
  have hsplit := tsum_sigma_split_le (Ξ := fun X => ∀ s, (famX fam₀ famC X).Λ s)
    (ΛB := fun X => ∀ b : GBranch S.tree, (famX fam₀ famC X).Λ (Sum.inr b))
    (fun X => splitX fam₀ famC X)
    (fun X a => (((ncsX (leafCtrL hS fam₀ famC a) X).ncard : ℕ) : ℝ≥0∞))
    (fun a => ∏ q, Fs 0 (Sum.inl q) (a q))
    (fun X b => ∏ b', Fs X (Sum.inr b') (b b'))
    (fun X ξ => (((ncsX (leafCtr hS (fun s => (famX fam₀ famC X).n s (ξ s))) X).ncard : ℕ) : ℝ≥0∞) *
      ∏ s, Fs X s (ξ s))
    (fun X ξ => by
      rw [Fintype.prod_sum_type, mul_assoc]
      rfl)
    (∏ b' : GBranch S.tree, (ENNReal.ofReal (Ks (Sum.inr b')) * μ (Sum.inr b')))
    (fun X => by
      rw [ennreal_tsum_pi_prod_fintype (fun b' l => Fs X (Sum.inr b') l)]
      refine Finset.prod_le_prod' fun b' _ => ?_
      simp only [hFs]
      rw [ENNReal.tsum_mul_left]
      gcongr
      exact hμ X (Sum.inr b'))
    ((nodeBallCard d ^ ∑ j, (S.tree j).order : ℕ) : ℝ≥0∞)
    (fun a => tsum_ncard_ncsX_le (leafCtrL hS fam₀ famC a))
  refine hsplit.trans ?_
  have hleaf : ∑' a : LeafModes fam₀ famC, ∏ q, Fs 0 (Sum.inl q) (a q) ≤
      ∏ q : SourcePair S, (ENNReal.ofReal (Ks (Sum.inl q)) * μ (Sum.inl q)) := by
    rw [ennreal_tsum_pi_prod_fintype (fun q l => Fs 0 (Sum.inl q) l)]
    refine Finset.prod_le_prod' fun q _ => ?_
    simp only [hFs]
    rw [ENNReal.tsum_mul_left]
    gcongr
    exact hμ 0 (Sum.inl q)
  rw [Fintype.prod_sum_type, mul_assoc]
  gcongr

end Centre

end WaveTurbulence.Flower.MkSlotsE
