/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2C
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Centre
public import WaveTurbulence.Foundations.FinalCount.G3BalS
/-! **Ghost assembly, Phase 2 (D): the creation cone of a split class** (design: `CHAIN-DESIGN.md`).

On a nonempty split class `σ` with `kOf σ ≥ 1`, L6E's `CreationCone` holds with `k = kOf σ`
(`creationCone_of_split`): a cone status of `f j` around a critical survivor neighbour `y` is `ConeAt j` with centre the
parameter of `y` (`coneAt_of_class`, via `coneAt_of_present`: `y` is a present degree-2 `α`-atom with one outgoing and
one incoming dart, `BalS`; its gap is nonzero by its record, `HInv.ok`, and `±` its record gap, `HGap.dg`); the relative
status is `ConeRel`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- A balanced non-`ε` atom of degree `2` has one outgoing and one incoming dart. -/
theorem darts_of_bal {s : St.{u} V D₀} (hB : BalS s) {a : V} (ha : a ∈ s.M.atoms) (hne : s.cls a ≠ .eps)
    (hd : s.M.deg a = 2) :
    ∃ x₁ x₂ : s.D, x₁ ≠ x₂ ∧ s.M.dartsAt a = {x₁, x₂} ∧ s.M.out x₁ = true ∧ s.M.out x₂ = false := by
  obtain ⟨ho, hi⟩ := hB.2 a ha hne hd
  obtain ⟨x₁, hx₁⟩ := card_eq_one.1 ho
  obtain ⟨x₂, hx₂⟩ := card_eq_one.1 hi
  have h1 : x₁ ∈ (s.M.dartsAt a).filter (fun x => s.M.out x = true) := by rw [hx₁]; exact mem_singleton_self _
  have h2 : x₂ ∈ (s.M.dartsAt a).filter (fun x => s.M.out x = false) := by rw [hx₂]; exact mem_singleton_self _
  rw [mem_filter] at h1 h2
  have hne' : x₁ ≠ x₂ := fun e => by rw [e, h2.2] at h1; cases h1.2
  refine ⟨x₁, x₂, hne', ?_, h1.2, h2.2⟩
  ext x
  constructor
  · intro hx
    cases ho' : s.M.out x
    · have : x ∈ (s.M.dartsAt a).filter (fun x => s.M.out x = false) := mem_filter.2 ⟨hx, ho'⟩
      rw [hx₂] at this; rw [mem_singleton.1 this]; simp
    · have : x ∈ (s.M.dartsAt a).filter (fun x => s.M.out x = true) := mem_filter.2 ⟨hx, ho'⟩
      rw [hx₁] at this; rw [mem_singleton.1 this]; simp
  · intro hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h1.1
    · exact h2.1

/-- **The cone of a class around a critical present atom is `ConeAt`.** -/
theorem coneAt_of_class {L γ δ η : ℝ} {w : Mom d} {h : HSt V D₀} (T : TriData h.s.M) (hd : 0 < d) (hB : BalS h.s)
    {B : Set (D₀ → (Fin d → ℤ))} (hRI : ∀ k0 ∈ B, HInv L γ η w k0 h ∧ HGap L w k0 h) {y : V}
    (hy : IsCritA L γ η h y) (j : Fin 3)
    (hcone : ∀ k0 ∈ B, InCone (L ^ (-6 * η)) (gcut h T L w k0 j) (gvec h L w k0 y)) :
    ConeAt T L γ δ η w (AdmS (fun k => k ∈ B) h.s) j := by
  obtain ⟨hym, hyd, R, hyc, -⟩ := hy
  have hne : h.s.cls y ≠ .eps := by rw [hyc]; exact fun e => by cases e
  obtain ⟨x₁, x₂, hx, hdarts, h1, h2⟩ := darts_of_bal hB hym hne hyd
  have hat : ∀ x ∈ ({x₁, x₂} : Finset h.s.D), h.s.M.atom x = y := by
    intro x hx'
    rw [← hdarts] at hx'
    simpa [Molecule.dartsAt] using hx'
  have hgv : ∀ k0 ∈ B, (Molecule.gapAt L w (k0 ∘ h.s.down) x₁ x₂ = gvec h L w k0 y ∨
      Molecule.gapAt L w (k0 ∘ h.s.down) x₁ x₂ = -gvec h L w k0 y) ∧ gvec h L w k0 y ≠ 0 := by
    intro k0 hk0
    obtain ⟨p, vis, hp, hg⟩ := (hRI k0 hk0).2.dg y hym hne x₂ x₁ (hat x₂ (by simp)) (hat x₁ (by simp)) h2 h1
    obtain ⟨-, p', vis', hp', -, -, -, hsg⟩ := ((hRI k0 hk0).1.ok y hym).1 R 0 hyc
    rw [hp] at hp'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hp')
    have hgv : gvec h L w k0 y = pgap L w k0 p := by unfold gvec; rw [hp]
    have hswap : Molecule.gapAt L w (k0 ∘ h.s.down) x₁ x₂ = -Molecule.gapAt L w (k0 ∘ h.s.down) x₂ x₁ := by
      unfold Molecule.gapAt; abel
    refine ⟨?_, by rw [hgv]; exact gapKind_SG_ne_zero hsg⟩
    rw [hswap, hgv]
    rcases hg with e | e
    · right; rw [e]
    · left; rw [e, neg_neg]
  refine coneAt_of_present T w _ j y hym x₁ x₂ hx hdarts h1 h2 hd ?_ ?_
  · rintro κ' ⟨k0, hk0, rfl⟩
    rcases (hgv k0 hk0).1 with e | e
    · rw [e]; exact (hgv k0 hk0).2
    · rw [e]; exact neg_ne_zero.2 (hgv k0 hk0).2
  · rintro κ' ⟨k0, hk0, rfl⟩
    exact inCone_pm_ctr (hgv k0 hk0).1 (hcone k0 hk0)

variable {L γ δ η : ℝ} {w : Mom d} (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
  (hcl : PClosed T.kept (triKeep h.s T))

/-- The cone status `s ≠ 0` of `f j` on a nonempty class: `f j` is critical, and there is a critical survivor `y`
around which all gaps of the class lie. -/
theorem stat_cone {B0 B : Set (D₀ → (Fin d → ℤ))} {σ : Sig} (hB : B ⊆ splitCls L γ η w h T Q kp hcl B0 σ)
    (hne : B.Nonempty) (j : Fin 2) (s : Fin 3) (hs : s ≠ 0)
    (hst : ∀ k0 ∈ B, statOK L γ η w h T Q kp hcl j s k0) :
    IsCritA L γ η (h.triPost T Q kp hcl) (T.f j.castSucc) ∧ ∃ y, IsCritA L γ η h y ∧
      ∀ k0 ∈ B, InCone (L ^ (-6 * η)) (gcut h T L w k0 j.castSucc) (gvec h L w k0 y) := by
  obtain ⟨k1, hk1⟩ := hne
  have hc : IsCritA L γ η (h.triPost T Q kp hcl) (T.f j.castSucc) := by
    have := hst k1 hk1
    unfold statOK at this
    by_contra hn
    simp only [hn, if_false] at this
    exact hs this
  obtain ⟨i, rfl⟩ : ∃ i : Fin 2, s = i.succ := by
    refine ⟨s.pred hs, (Fin.succ_pred s hs).symm⟩
  have hget : ∀ k0 ∈ B, ∃ y, nbrAt (h.triPost T Q kp hcl) (T.f j.castSucc) i = some y ∧
      y ∈ triSurv h T Q kp hcl ∧ IsCritA L γ η (h.triPost T Q kp hcl) y ∧
      InCone (L ^ (-6 * η)) (gcut h T L w k0 j.castSucc) (gvec h L w k0 y) := by
    intro k0 hk0
    have := hst k0 hk0
    unfold statOK at this
    simp only [hc, if_true] at this
    exact this.2 i rfl
  obtain ⟨y, hy1, hyX, hyc, -⟩ := hget k1 hk1
  refine ⟨hc, y, (triSurvMap h T Q kp hcl).critA hyX hyc, fun k0 hk0 => ?_⟩
  obtain ⟨y', hy1', -, -, hcone⟩ := hget k0 hk0
  rw [hy1] at hy1'
  rw [Option.some.inj hy1']
  exact hcone

/-- **The creation cone of a split class** (`k = kOf σ ≥ 1`). -/
theorem creationCone_of_split (hd : 0 < d) (hBal : BalS h.s) {B0 B : Set (D₀ → (Fin d → ℤ))} {σ : Sig}
    (hBs : B ⊆ splitCls L γ η w h T Q kp hcl B0 σ) (hne : B.Nonempty)
    (hRI : ∀ k0 ∈ B, HInv L γ η w k0 h ∧ HGap L w k0 h) (hk : 1 ≤ kOf σ) :
    CreationCone T L γ δ η w (AdmS (fun k => k ∈ B) h.s) (Q 0) (Q 1)
      (if h.s.cls (T.t 0) = .eps then kp 0 else 0) (if h.s.cls (T.t 1) = .eps then kp 1 else 0) (kOf σ) := by
  have hs0 : ∀ k0 ∈ B, statOK L γ η w h T Q kp hcl 0 σ.1 k0 := fun k0 hk0 => (hBs hk0).2.1
  have hs1 : ∀ k0 ∈ B, statOK L γ η w h T Q kp hcl 1 σ.2.1 k0 := fun k0 hk0 => (hBs hk0).2.2.1
  have hps : ∀ k0 ∈ B, pairSt L γ η w h T Q kp hcl σ.2.2 k0 := fun k0 hk0 => (hBs hk0).2.2.2
  have cone0 : σ.1 ≠ 0 → T.IsA0 ∧ (if h.s.cls (T.t 0) = .eps then kp 0 else 0) = 0 ∧ Crit L γ η (Q 0) ∧
      ConeAt T L γ δ η w (AdmS (fun k => k ∈ B) h.s) 0 := by
    intro h0
    obtain ⟨hc, y, hy, hcone⟩ := stat_cone h T Q kp hcl hBs hne 0 σ.1 h0 hs0
    obtain ⟨he, hA, hkp, hcr⟩ := critA_f0 h T Q kp hcl hc
    exact ⟨hA, by rw [if_pos he, hkp], hcr, coneAt_of_class T hd hBal hRI hy 0 hcone⟩
  have cone1 : σ.2.1 ≠ 0 → T.IsA1 ∧ (if h.s.cls (T.t 1) = .eps then kp 1 else 0) = 0 ∧ Crit L γ η (Q 1) ∧
      ConeAt T L γ δ η w (AdmS (fun k => k ∈ B) h.s) 1 := by
    intro h1
    obtain ⟨hc, y, hy, hcone⟩ := stat_cone h T Q kp hcl hBs hne 1 σ.2.1 h1 hs1
    obtain ⟨he, hA, hkp, hcr⟩ := critA_f1 h T Q kp hcl hc
    exact ⟨hA, by rw [if_pos he, hkp], hcr, coneAt_of_class T hd hBal hRI hy 1 hcone⟩
  by_cases h0 : σ.1 = 0 <;> by_cases h1 : σ.2.1 = 0
  · have hp : σ.2.2 = 1 := by
      unfold kOf at hk; simp only [h0, h1, ite_true, true_and] at hk
      by_contra hp; simp [hp] at hk
    have hkO : kOf σ = 1 := by unfold kOf; simp [h0, h1, hp]
    rw [hkO]
    obtain ⟨k1, hk1⟩ := hne
    have hboth : IsCritA L γ η (h.triPost T Q kp hcl) (T.f 0) ∧ IsCritA L γ η (h.triPost T Q kp hcl) (T.f 1) := by
      have := hps k1 hk1
      unfold pairSt at this
      by_contra hn
      simp only [hn, if_false, hp] at this
      exact absurd this (by decide)
    obtain ⟨he0, hA0, -, -⟩ := critA_f0 h T Q kp hcl hboth.1
    obtain ⟨he1, hA1, hkp1, hcr1⟩ := critA_f1 h T Q kp hcl hboth.2
    refine Or.inl ⟨rfl, Or.inr (Or.inr ⟨hA0, hA1, by rw [if_pos he1, hkp1], hcr1, ?_⟩)⟩
    rintro κ' ⟨k0, hk0, rfl⟩
    have := hps k0 hk0
    unfold pairSt at this
    simp only [hboth, and_self, if_true] at this
    exact this.2 hp
  · have hkO : kOf σ = 1 := by unfold kOf; simp [h0, h1]
    rw [hkO]
    obtain ⟨hA, hk', hcr, hc⟩ := cone1 h1
    exact Or.inl ⟨rfl, Or.inr (Or.inl ⟨hA, hk', hcr, hc⟩)⟩
  · have hkO : kOf σ = 1 := by unfold kOf; simp [h0, h1]
    rw [hkO]
    obtain ⟨hA, hk', hcr, hc⟩ := cone0 h0
    exact Or.inl ⟨rfl, Or.inl ⟨hA, hk', hcr, hc⟩⟩
  · have hkO : kOf σ = 2 := by unfold kOf; simp [h0, h1]
    rw [hkO]
    obtain ⟨hA0, hk0', hcr0, hc0⟩ := cone0 h0
    obtain ⟨hA1, hk1', hcr1, hc1⟩ := cone1 h1
    exact Or.inr ⟨rfl, hA0, hA1, hk0', hk1', hcr0, hcr1, hc0, hc1⟩

end WaveTurbulence.GammaLow.FinalCount.Ghost
