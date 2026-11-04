/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCOne

/-!
# The type 2 recursion

DH21 (newexp2) (L929–L935): for a couple of type 2 with chains `c⁺, c⁻` and lone pair `Q_lp`,
`B̃_Q(t, s) = chainT c⁺ F⁺ t (t' ↦ chainT c⁻ F⁻ s (s' ↦ B̃_{Q_lp}(t', s')))` (`type2F`). Either chain
may be empty. `MCExp.chain'` is `MCExp.chain` allowing an empty chain; `MCExp.type2` applies it to the
`-` chain with the times swapped (`MCExp.swapTimes`), then to the `+` chain.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Type2

variable {V : Type} [DecidableEq V] {θ a b A : ℝ}

/-- The constant of a chain with a bottom coefficient (possibly empty chain). -/
@[expose] noncomputable def Nchain' (θ a b : ℝ) (c : LegalCode) (N : ℕ → ℝ) (Nb : ℝ) : ℝ :=
  max Nb (2 ^ (c.size + 1) * Nchain θ a b c N Nb)

/-- **A chain with a bottom coefficient** (possibly empty; DH21 Prop 5.1, Case 2). -/
theorem MCExp.chain' (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A)
    {σ : ℕ → V} {ε : ℕ → ℤ} (hε : ∀ j, ε j = 1 ∨ ε j = -1) {ζ : V → ℤ} {c : LegalCode}
    (hζ : ∀ j ∈ Set.Ico 0 c.size, ζ (σ j) = ε j) (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {S : ℕ → Finset V} {N : ℕ → ℝ} {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : ∀ j ∈ Set.Ico 0 c.size, MCExp θ a b A (N j) ζ (S j) (F j))
    {Sb : Finset V} {Nb : ℝ} {G : (V → ℝ) → ℝ → ℝ → ℂ} (hG : MCExp θ a b A Nb ζ Sb G)
    (hSS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, j ≠ k → Disjoint (S j) (S k))
    (hSb : ∀ j ∈ Set.Ico 0 c.size, Disjoint (S j) Sb)
    (hσS : ∀ j ∈ Set.Ico 0 c.size, ∀ k ∈ Set.Ico 0 c.size, σ k ∉ S j)
    (hσb : ∀ k ∈ Set.Ico 0 c.size, σ k ∉ Sb) :
    MCExp θ a b A (Nchain' θ a b c N Nb) ζ
      (unionS S 0 c.size ∪ Sb ∪ (Finset.Ico 0 c.size).image σ)
      (fun α t s => chainT σ ε c 0 F α t (fun t' => G α t' s)) := by
  have hA0 : 0 ≤ A := A1_nonneg.trans hA
  by_cases hc : c = .nil
  · subst hc
    have e : unionS S 0 LegalCode.nil.size ∪ Sb ∪ (Finset.Ico 0 LegalCode.nil.size).image σ =
        Sb := by
      simp [unionS, LegalCode.size]
    rw [e]
    exact (hG.mono (le_max_left _ _) hA0).congr fun α t s _ _ => by simp [chainT_nil]
  · exact (MCExp.chain hθ0 hθ1 ha hb hab1 hab hA hε hζ hc hinj hF hG hSS hSb hσS hσb).mono
      (le_max_right _ _) hA0

/-- **The type 2 recursion** (DH21 (newexp2)): the `+` chain in `t`, the `-` chain in `s`, and the
lone pair at the last times. -/
@[expose] noncomputable def type2F (σp : ℕ → V) (εp : ℕ → ℤ) (cp : LegalCode)
    (Fp : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (σm : ℕ → V) (εm : ℕ → ℤ) (cm : LegalCode)
    (Fm : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (Flp : (V → ℝ) → ℝ → ℝ → ℂ) : (V → ℝ) → ℝ → ℝ → ℂ :=
  fun α t s => chainT σp εp cp 0 Fp α t fun t' => chainT σm εm cm 0 Fm α s fun s' => Flp α t' s'

/-- The variables of the `-` chain with the lone pair. -/
@[expose] def varsMinus (σm : ℕ → V) (cm : LegalCode) (Sm : ℕ → Finset V) (Slp : Finset V) :
    Finset V :=
  unionS Sm 0 cm.size ∪ Slp ∪ (Finset.Ico 0 cm.size).image σm

/-- **DH21 Proposition 5.1, Case 2**: the type 2 recursion preserves the expansion (maincoef3). -/
theorem MCExp.type2 (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hab1 : a + b < 1) (hab : a + b ≤ θ) (hA : A1 ≤ A) {ζ : V → ℤ}
    {σp : ℕ → V} {εp : ℕ → ℤ} (hεp : ∀ j, εp j = 1 ∨ εp j = -1) {cp : LegalCode}
    (hζp : ∀ j ∈ Set.Ico 0 cp.size, ζ (σp j) = εp j) (hinjp : Set.InjOn σp (Set.Ico 0 cp.size))
    {Sp : ℕ → Finset V} {Np : ℕ → ℝ} {Fp : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (hFp : ∀ j ∈ Set.Ico 0 cp.size, MCExp θ a b A (Np j) ζ (Sp j) (Fp j))
    {σm : ℕ → V} {εm : ℕ → ℤ} (hεm : ∀ j, εm j = 1 ∨ εm j = -1) {cm : LegalCode}
    (hζm : ∀ j ∈ Set.Ico 0 cm.size, ζ (σm j) = εm j) (hinjm : Set.InjOn σm (Set.Ico 0 cm.size))
    {Sm : ℕ → Finset V} {Nm : ℕ → ℝ} {Fm : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (hFm : ∀ j ∈ Set.Ico 0 cm.size, MCExp θ a b A (Nm j) ζ (Sm j) (Fm j))
    {Slp : Finset V} {Nlp : ℝ} {Flp : (V → ℝ) → ℝ → ℝ → ℂ} (hlp : MCExp θ a b A Nlp ζ Slp Flp)
    (hSSm : ∀ j ∈ Set.Ico 0 cm.size, ∀ k ∈ Set.Ico 0 cm.size, j ≠ k → Disjoint (Sm j) (Sm k))
    (hSbm : ∀ j ∈ Set.Ico 0 cm.size, Disjoint (Sm j) Slp)
    (hσSm : ∀ j ∈ Set.Ico 0 cm.size, ∀ k ∈ Set.Ico 0 cm.size, σm k ∉ Sm j)
    (hσbm : ∀ k ∈ Set.Ico 0 cm.size, σm k ∉ Slp)
    (hSSp : ∀ j ∈ Set.Ico 0 cp.size, ∀ k ∈ Set.Ico 0 cp.size, j ≠ k → Disjoint (Sp j) (Sp k))
    (hSbp : ∀ j ∈ Set.Ico 0 cp.size, Disjoint (Sp j) (varsMinus σm cm Sm Slp))
    (hσSp : ∀ j ∈ Set.Ico 0 cp.size, ∀ k ∈ Set.Ico 0 cp.size, σp k ∉ Sp j)
    (hσbp : ∀ k ∈ Set.Ico 0 cp.size, σp k ∉ varsMinus σm cm Sm Slp) :
    MCExp θ a b A (Nchain' θ a b cp Np (Nchain' θ a b cm Nm Nlp)) ζ
      (unionS Sp 0 cp.size ∪ varsMinus σm cm Sm Slp ∪ (Finset.Ico 0 cp.size).image σp)
      (type2F σp εp cp Fp σm εm cm Fm Flp) := by
  -- the `-` chain, with the times swapped
  have hin := MCExp.chain' hθ0 hθ1 ha hb hab1 hab hA hεm hζm hinjm hFm (hlp.swapTimes true)
    hSSm hSbm hσSm hσbm
  have hin' := (hin.swapTimes true).congr (F' := fun α t' s =>
    chainT σm εm cm 0 Fm α s fun s' => Flp α t' s') fun α t s _ _ => by simp [swapT]
  -- the `+` chain
  exact MCExp.chain' hθ0 hθ1 ha hb hab1 hab hA hεp hζp hinjp hFp hin' hSSp hSbp hσSp hσbp

end Type2

end WaveTurbulence.ClassJR
