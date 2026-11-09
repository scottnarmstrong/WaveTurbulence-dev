/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2D
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Step2At
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2d
/-! **Ghost assembly, Phase 2 (E): helpers of the node lemma** (design: `CHAIN-DESIGN.md`).

`bank_empty` (no edge on the empty class), `S2Args.mono` (the uniform data pass to sub-classes), `PairOK.mono`,
`GhostPairsOK` failure gives a non-`PairOK` pair. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem bank_empty {L γ η : ℝ} {w : Mom d} (h : HSt V D₀) : bank L γ η w h ∅ = 0 := by
  obtain ⟨m, hm, he⟩ := exists_matching_eq (NCEdge L γ η w h ∅) (critSet L γ η h)
  unfold bank
  rw [← he, Finset.card_eq_zero]
  ext e
  simp only [notMem_empty, iff_false]
  intro he'
  obtain ⟨-, -, -, hE⟩ := hm.1 e he'
  exact hE.2.2.2.2.1 (fun k0 hk => absurd hk (Set.notMem_empty k0))

theorem S2Args.mono {L γ η : ℝ} {w : Mom d} {A B : (D₀ → (Fin d → ℤ)) → Prop} (hBA : ∀ k, B k → A k)
    {h : HSt V D₀} {T : TriData h.s.M} {Q : Fin 2 → ℝ} {kp : Fin 2 → ℕ} {hcl : PClosed T.kept (triKeep h.s T)}
    (a : S2Args L γ η w A h T Q kp hcl) : S2Args L γ η w B h T Q kp hcl := by
  have hI : ∀ {p : D₀ × D₀} {R : ℝ}, IotaUnif A L η w h p R → IotaUnif B L η w h p R := by
    rintro p R ⟨q, hq, hcar, sg, hsg, hb⟩
    exact ⟨q, hq, hcar, sg, hsg, fun k hk => hb k (hBA k hk)⟩
  refine ⟨a.hQ, a.hkp, fun k hk => a.hsg k (hBA k hk), fun k hk => a.hsim k (hBA k hk),
    fun k hk => a.hnz k (hBA k hk), fun he h50 => hI (a.hι₀ he h50), fun he h0 k hk => a.hι₀' he h0 k (hBA k hk),
    fun he h50 => ?_, fun he h0 k hk => a.hι₁' he h0 k (hBA k hk), a.h3⟩
  rcases a.hι₁ he h50 with hu | ⟨he0, sg, hsg', hb⟩
  · exact Or.inl (hI hu)
  · exact Or.inr ⟨he0, sg, hsg', fun k hk => hb k (hBA k hk)⟩

theorem PairOK.mono {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {T : TriData M} {L γ η : ℝ}
    {w : Mom d} {A B : (D → (Fin d → ℤ)) → Prop} (hBA : ∀ k, B k → A k) {j₁ j₂ : Fin 3} {Q₁ Q₂ : ℝ} {κ₁ κ₂ : ℕ}
    (hP : PairOK T L γ η w A j₁ j₂ Q₁ Q₂ κ₁ κ₂) : PairOK T L γ η w B j₁ j₂ Q₁ Q₂ κ₁ κ₂ := by
  rcases hP with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr fun κ' hκ' => h κ' (hBA κ' hκ')))

/-- **A failure of `GhostPairsOK` on a sub-class of a node class is an NC edge of the parent class.** -/
theorem edge_of_not_ghostPairsOK [Infinite V] {Rn : ℕ} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀}
    {A B : Set (D₀ → (Fin d → ℤ))} {n : T2 h} (hn : Node2 L γ η h n) (hI : Inv Rn h.s)
    (hBs : B ⊆ cls2 L γ η w h A n) (hG : ∀ k0 ∈ cls2 L γ η w h A n, HGap L w k0 h ∧ HInv L γ η w k0 h)
    (hne : B.Nonempty) (hok : ¬ GhostPairsOK L γ η w (fun k => k ∈ B) h (triOf hn)) :
    ∃ j₁ j₂ : Fin 3, NCEdge L γ η w h A ((triOf hn).t j₁) ((triOf hn).t j₂) ∧
      h.s.cls ((triOf hn).t j₁) ≠ .eps ∧ h.s.cls ((triOf hn).t j₂) ≠ .eps := by
  unfold GhostPairsOK at hok
  push Not at hok
  obtain ⟨j₁, j₂, hj, ⟨R₁, k₁, hc₁⟩, ⟨R₂, k₂, hc₂⟩, hnot⟩ := hok
  have hne' : (cls2 L γ η w h A n).Nonempty := hne.mono hBs
  rcases pairOK_or_edge hn hI hG hne' hj hc₁ hc₂ with hP | hE
  · exfalso
    apply hnot
    rw [ghostQ_eq hc₁, ghostQ_eq hc₂]
    have hk₁ : ghostK h (triOf hn) j₁ = k₁ := by simp [ghostK, hc₁]
    have hk₂ : ghostK h (triOf hn) j₂ = k₂ := by simp [ghostK, hc₂]
    rw [hk₁, hk₂]
    exact PairOK.mono (fun κ ⟨k0, hk0, e⟩ => ⟨k0, hBs hk0, e⟩) hP
  · refine ⟨j₁, j₂, hE, ?_, ?_⟩
    · rw [hc₁]; exact fun e => by cases e
    · rw [hc₂]; exact fun e => by cases e

end WaveTurbulence.GammaLow.FinalCount.Ghost
