/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.RegTarget

/-! # D6b: `ProtAnnBoundAt` by cases

* `ProtAnnCaseAt P case`: `ProtDefs.ProtAnnBoundAt`'s text with one more hypothesis `case pin Sel` (placed after
  `ProtAmbient p X LG`); `protAnnBoundAt_iff_case` shows that the case `True` is `ProtAnnBoundAt` itself.
* `ProtAnnPinSelAt P := ProtAnnCaseAt P (pin = true ∧ Sel.Nonempty)`: **the open case F-D6b-2** (a terminal pin and a
  selected annular vertex: no available `X^{1/4}` input for a pinned object with a `chiD` factor). It is the only
  hypothesis of the final gate besides D3's `ProtBoundGate`.
* `ProtAnnFreeSelAt P := ProtAnnCaseAt P (pin = false)`: the unpinned selected case.
* `protAnnCase_emptySel`: the case `Sel = ∅` (then `pin = true`) from D3's `ProtBoundAt` (`cfg = term`, `θ = η`).
* `protAnnBoundAt_of_cases`: the three cases give `ProtAnnBoundAt`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtWhole

open WaveTurbulence.Flower.ProtDefs

/-- `ProtAnnBoundAt` with one more hypothesis `case pin Sel` (after the ambient). -/
def ProtAnnCaseAt (P : WTParams) (case : ∀ {w : ℕ} (LG : LayeredGarden w), Bool → Finset (GBranch LG.garden.tree) → Prop) :
    Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n →
  ∀ (pin : Bool) (Sel : Finset (GBranch LG.garden.tree)), (pin = true → X.lonePath ≠ []) →
    (∀ b ∈ Sel, b.1.1.val = 0 ∧ b.1.2 <+: X.lonePath ∧ b.1.2 ≠ X.lonePath ∧
      (pin = true → b.1.2 ≠ X.lonePath.dropLast)) →
    1 ≤ (if pin then 1 else 0) + Sel.card → Sel.card ≤ 1 → ProtAmbient p X LG → case LG pin Sel →
  ∀ (M₂ : ℝ), P.L ≤ M₂ → ∀ (s : ℝ), (p : ℝ) < s → s < p + 1 → ∀ q' : ℕ, q' ≤ p →
    (w = 1 → ∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
    (pin = false → ∀ κ, ind κ = 1) →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (b₀ c₀ : Mom P.d),
    XNormRestr P.η (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ *
          filtWeight (F ∪ Sel) (fun b => decide (b ∈ Sel)) (fun b => if b ∈ Sel then M₂ else M b) κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) ((if pin then ProtCfg.term else ProtCfg.none).fix X s s (ts 0)) k
        (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) *
        ENNReal.ofReal (P.L ^ ((47 * P.d + 5) * ((if pin then 1 else 0) + Sel.card : ℕ)) *
          M₂ ^ (-((Sel.card : ℝ) / 18))) *
        regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B)

/-- **The open case F-D6b-2**: a terminal pin together with a selected annular vertex. -/
def ProtAnnPinSelAt (P : WTParams) : Prop := ProtAnnCaseAt P (fun _ pin Sel => pin = true ∧ Sel.Nonempty)

/-- The unpinned selected case. -/
def ProtAnnFreeSelAt (P : WTParams) : Prop := ProtAnnCaseAt P (fun _ pin _ => pin = false)

theorem protAnnBoundAt_iff_case (P : WTParams) : ProtAnnBoundAt P ↔ ProtAnnCaseAt P (fun _ _ _ => True) := by
  constructor
  · intro h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 _ M₂ a8 s a9 a10 q' a11 a11' S ω cω a12 F M a13 Fu Mu a14 ind
      a15 a16 H B a17 b₀ c₀
    exact h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 M₂ a8 s a9 a10 q' a11 a11' S ω cω a12 F M a13 Fu Mu a14 ind
      a15 a16 H B a17 b₀ c₀
  · intro h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 M₂ a8 s a9 a10 q' a11 a11' S ω cω a12 F M a13 Fu Mu a14 ind
      a15 a16 H B a17 b₀ c₀
    exact h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 trivial M₂ a8 s a9 a10 q' a11 a11' S ω cω a12 F M a13 Fu Mu a14
      ind a15 a16 H B a17 b₀ c₀

/-- **The case `Sel = ∅`** (then `pin = true`): D3's `ProtBoundAt` at `cfg = term`, `θ = η`, `L^{31d+6} ≤ L^{47d+5}`. -/
theorem protAnnCase_emptySel (P : WTParams) (hpin : ProtBoundAt P) (hL : 1 ≤ P.L) (hd : 1 ≤ P.d) :
    ProtAnnCaseAt P (fun _ _ Sel => Sel = ∅) := by
  intro p hp n hn w LG X hsh hsz pin Sel hpX _hSel hr _hcard hamb hS0 M₂ _hM₂ s hs1 hs2 q' hq' _hlay S ω cω hω F M hM
    Fu Mu hMu ind hind hind1 H B hHB b₀ c₀
  subst hS0
  have hpin1 : pin = true := by
    cases pin
    · simp at hr
    · rfl
  subst hpin1
  have hval : ProtCfg.term.Valid X LG p := hpX rfl
  set t : ℝ := (s + (p + 1)) / 2 with ht
  have hst : s < t := by rw [ht]; linarith
  have htp : t < p + 1 := by rw [ht]; linarith
  have key := hpin p hp n hn w LG X hsh hsz .term hval hamb P.η (31 * P.d + 6) (Or.inl ⟨rfl, rfl⟩) s t hs1 hst
    htp q' hq' S ω cω hω F M hM Fu Mu hMu ind hind (fun h => by rcases h with h | h | h <;> exact absurd h (by decide))
    H B hHB b₀ c₀
  have hbox : ProtCfg.term.box X t p q' = timeBoxGt p q' := by simp [ProtCfg.box, ProtCfg.pinsRoot]
  rw [hbox] at key
  have hfun : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ *
          filtWeight (F ∪ ∅) (fun b => decide (b ∈ (∅ : Finset (GBranch LG.garden.tree))))
            (fun b => if b ∈ (∅ : Finset (GBranch LG.garden.tree)) then M₂ else M b) κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) ((if true = true then ProtCfg.term else ProtCfg.none).fix X s s (ts 0)) k
        (fun _ => 0) 0) =
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) := by
    funext ts k
    simp only [Finset.union_empty, Finset.notMem_empty, decide_false, if_false, if_true]
    rfl
  rw [hfun]
  refine key.trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le) zero_le) zero_le
  simp only [Finset.card_empty, if_true, add_zero, Nat.cast_zero, zero_div, neg_zero, Real.rpow_zero, mul_one]
  rw [show (31 * (P.d : ℝ) + 6) = ((31 * P.d + 6 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  refine pow_le_pow_right₀ hL ?_
  omega

/-- **`ProtAnnBoundAt` from its cases.** -/
theorem protAnnBoundAt_of_cases (P : WTParams) (hpin : ProtBoundAt P) (hL : 1 ≤ P.L) (hd : 1 ≤ P.d)
    (hfree : ProtAnnFreeSelAt P) (hps : ProtAnnPinSelAt P) : ProtAnnBoundAt P := by
  rw [protAnnBoundAt_iff_case]
  intro p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 _
  by_cases hS : Sel = ∅
  · exact protAnnCase_emptySel P hpin hL hd p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 hS
  · cases pin with
    | false => exact hfree p hp n hn w LG X a1 a2 false Sel a3 a4 a5 a6 a7 rfl
    | true => exact hps p hp n hn w LG X a1 a2 true Sel a3 a4 a5 a6 a7 ⟨rfl, Finset.nonempty_iff_ne_empty.2 hS⟩

/-! ### Prefix form -/

theorem protAnnCaseAt_mono (case : ∀ {w : ℕ} (LG : LayeredGarden w), Bool → Finset (GBranch LG.garden.tree) → Prop) :
    LargeConstantMonotone (fun P => ProtAnnCaseAt P case) := by
  intro P c₁ c₂ hC _hC₂ hδ hL hCC _hCC₂ h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 a0 M₂ a8 s a9 a10 q' a11 a11'
    S ω cω a12 F M a13 Fu Mu a14 ind a15 a16 H B a17 b₀ c₀
  rw [N_largeConstants] at hn
  exact (h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 a0 M₂ a8 s a9 a10 q' a11 a11' S ω cω a12 F M a13 Fu Mu a14 ind
    a15 a16 H B a17 b₀ c₀).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (regBound_largeConstants_mono P (by linarith) hCC hδ.le (by linarith) n _) zero_le) zero_le)

end WaveTurbulence.Flower.ProtWhole
