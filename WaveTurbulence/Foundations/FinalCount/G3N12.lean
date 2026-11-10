/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3HInv
/-! **FINALCOUNT-G3: (N1) and (N2) of ruling R18**, from the cutting history of a run.

* (N1) every `β`-atom of `𝕄_fin` is the product of a cut with nonzero gap (DH23 L1985, TARGET `remtame`);
* (N2) if `κ_{v₁} = κ_{v₂} = 0` and `g_β = ±g₁ ± g₂` (the three gaps sum to zero), then
  `|g_β| ≥ L^{-50η} min(R₁,R₂)` (DH23 L1895: "by the definition of `(ι_v, κ_v)`"). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- The gap of the cut that produced the atom `a`. -/
def AtomGap (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) (a : V) (g : Mom d) : Prop :=
  ∃ p vis, h.crec a = some (p, vis) ∧ g = pgap L w κ p

/-- **(N1)**: every `β`-atom has a recorded cut with nonzero gap. -/
theorem HInv.N1 {h : HSt V D₀} (hI : HInv L γ η w κ h) {b : V} (hb : b ∈ h.s.M.atoms) (hcb : h.s.cls b = .beta) :
    ∃ g, AtomGap L w κ h b g ∧ g ≠ 0 := by
  obtain ⟨p, vis, hr, hnz⟩ := (hI.ok b hb).2 hcb
  exact ⟨pgap L w κ p, ⟨p, vis, hr, rfl⟩, hnz⟩

theorem norm_pm {ga gc : Mom d} {sa sc : ℝ} (ha : sa = 1 ∨ sa = -1) (hc : sc = 1 ∨ sc = -1) :
    ∃ t : ℝ, (t = 1 ∨ t = -1) ∧ ‖sa • ga + sc • gc‖ = ‖gc + t • ga‖ := by
  have hsc : sc * sc = 1 := by rcases hc with rfl | rfl <;> norm_num
  refine ⟨sa * sc, ?_, ?_⟩
  · rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> simp
  · have e : sa • ga + sc • gc = sc • (gc + (sa * sc) • ga) := by
      rw [smul_add, smul_smul]
      have : sc * (sa * sc) = sa := by rw [mul_comm sa sc, ← mul_assoc, hsc, one_mul]
      rw [this, add_comm]
    rw [e, norm_smul]
    rcases hc with rfl | rfl <;> simp

/-- The later of two cuts sees the earlier one: if `ι = 0` there, the third gap is large. -/
theorem N2_aux {qa pc pb : D₀ × D₀} {vis : List (D₀ × D₀)} {Rc : ℝ} {sa sc : ℝ}
    (hsa : sa = 1 ∨ sa = -1) (hsc : sc = 1 ∨ sc = -1) (hq : qa ∈ vis)
    (hno : ¬ IotaHit L η w κ vis pc Rc)
    (hsum : pgap L w κ pb = sa • pgap L w κ qa + sc • pgap L w κ pc) (hnz : pgap L w κ pb ≠ 0) :
    L ^ (-50 * η) * Rc < ‖pgap L w κ pb‖ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht, hn⟩ := norm_pm (ga := pgap L w κ qa) (gc := pgap L w κ pc) hsa hsc
  rw [← hsum] at hn
  apply hno
  refine ⟨qa, hq, t, ht, ?_, ?_⟩
  · rw [← hn]; exact norm_pos_iff.2 hnz
  · rw [← hn]; exact hcon

/-- **(N2)** (DH23 L1895). -/
theorem HInv.N2 {h : HSt V D₀} (hI : HInv L γ η w κ h) (hL : 1 ≤ L) (hη : 0 ≤ η)
    {v₁ v₂ b : V} (h1 : v₁ ∈ h.s.M.atoms) (h2 : v₂ ∈ h.s.M.atoms) (hb : b ∈ h.s.M.atoms)
    {R₁ R₂ : ℝ} (c1 : h.s.cls v₁ = .alpha R₁ 0) (c2 : h.s.cls v₂ = .alpha R₂ 0) (cb : h.s.cls b = .beta)
    {g₁ g₂ gb : Mom d} (a1 : AtomGap L w κ h v₁ g₁) (a2 : AtomGap L w κ h v₂ g₂) (ab : AtomGap L w κ h b gb)
    (s₁ s₂ : ℝ) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) (hsum : gb = s₁ • g₁ + s₂ • g₂) :
    L ^ (-50 * η) * min R₁ R₂ ≤ ‖gb‖ := by
  obtain ⟨hl1, p1, vis1, hr1, hp1, -, hi1, -⟩ := (hI.ok v₁ h1).1 R₁ 0 c1
  obtain ⟨hl2, p2, vis2, hr2, hp2, -, hi2, -⟩ := (hI.ok v₂ h2).1 R₂ 0 c2
  obtain ⟨pb, visb, hrb, hnzb⟩ := (hI.ok b hb).2 cb
  obtain ⟨q1, w1, e1, rfl⟩ := a1
  obtain ⟨q2, w2, e2, rfl⟩ := a2
  obtain ⟨qb, wb, eb, rfl⟩ := ab
  rw [hr1] at e1; rw [hr2] at e2; rw [hrb] at eb
  simp only [Option.some.injEq, Prod.mk.injEq] at e1 e2 eb
  obtain ⟨rfl, rfl⟩ := e1; obtain ⟨rfl, rfl⟩ := e2; obtain ⟨rfl, rfl⟩ := eb
  have hLpos : 0 < L := by linarith
  have hρ1 : L ^ (-50 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hρ0 : 0 ≤ L ^ (-50 * η) := (Real.rpow_pos_of_pos hLpos _).le
  have hmin1 : min R₁ R₂ ≤ R₁ := min_le_left _ _
  have hmin2 : min R₁ R₂ ≤ R₂ := min_le_right _ _
  have no1 : ¬ IotaHit L η w κ vis1 p1 R₁ := fun hh => by have := hi1.2 hh; omega
  have no2 : ¬ IotaHit L η w κ vis2 p2 R₂ := fun hh => by have := hi2.2 hh; omega
  rcases hI.cmp v₁ h1 v₂ h2 p1 vis1 p2 vis2 hr1 hr2 with heq | hin2 | hin1
  · subst heq
    -- both gaps equal
    have hb0 : s₁ + s₂ ≠ 0 := by
      intro h0
      apply hnzb
      rw [hsum, ← add_smul, h0, zero_smul]
    have hs : s₁ = s₂ := by
      rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;>
        first | rfl | exact absurd (by norm_num) hb0
    have hnorm : ‖pgap L w κ pb‖ = 2 * ‖pgap L w κ p1‖ := by
      rw [hsum, ← hs, ← add_smul, norm_smul]
      rcases hs₁ with rfl | rfl <;> norm_num [Real.norm_eq_abs]
    rw [hnorm]
    have hmpos : 0 ≤ min R₁ R₂ := le_min hl1.pos.le hl2.pos.le
    calc L ^ (-50 * η) * min R₁ R₂ ≤ 1 * min R₁ R₂ := by gcongr
      _ ≤ R₁ := by rw [one_mul]; exact hmin1
      _ ≤ 2 * ‖pgap L w κ p1‖ := by linarith [hp1.1]
  · have := N2_aux hs₁ hs₂ hin2 no2 hsum hnzb
    calc L ^ (-50 * η) * min R₁ R₂ ≤ L ^ (-50 * η) * R₂ := by gcongr
      _ ≤ _ := this.le
  · have hsum' : pgap L w κ pb = s₂ • pgap L w κ p2 + s₁ • pgap L w κ p1 := by rw [hsum, add_comm]
    have := N2_aux hs₂ hs₁ hin1 no1 hsum' hnzb
    calc L ^ (-50 * η) * min R₁ R₂ ≤ L ^ (-50 * η) * R₁ := by gcongr
      _ ≤ _ := this.le

end WaveTurbulence.FinalCountG3
