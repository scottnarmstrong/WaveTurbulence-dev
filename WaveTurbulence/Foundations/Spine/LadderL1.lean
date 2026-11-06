/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.KernelCore
/-! # Time-L1 version of the ladder core bound (S3c COARSE-SPLICED)

The proof of `kernel_core` (S3b) bounds the integral over the unit time box of the modulus of the
finite lattice sum at fixed times; here that intermediate integral bound is stated and proved on
its own, so that several disjoint ladders can be multiplied after the time ordering is dropped. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.WeylSums WaveTurbulence.Sumint MeasureTheory Set Finset

variable {w d : ℕ} {G : Garden w}

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

open scoped Classical in
include C in
/-- **The time-L1 core bound for the local ladder sum.** -/
theorem kernel_core_L1 (hP : G.IsPlain) {L : ℝ} (hL0 : 0 < L) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (hd : 1 ≤ d)
    (γ η δ x T1 C0 : ℝ) (hδ : 0 < δ) (hC0 : 0 ≤ C0) (hρ : 0 ≤ L ^ (-γ + η))
    (hR : L * L ^ (-γ + η) ≤ L ^ (1 - γ + η))
    (hRung : ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), GoodTerm L (L ^ (1 - γ + η)) a b χ →
      RungOK γ x T1 δ L C0 a b χ)
    (hlay : ∀ a, δ * ((D.layer a : ℝ) + 1) ≤ T1)
    (boundary : GardenDart G → (Fin d → ℤ)) (NC : ℕ)
    (hNC : ∀ T : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary),
      (∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0) →
        (T.image (fun z => clsOf (u := u) (v := v) z.1)).card ≤ NC)
    (T0 : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary))
    (hT0 : ∀ z, z ∉ T0 → ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 = 0) :
    ∫ t in timeBox G D.layer (Molecule.ladderAtoms u v),
        ‖∑ z ∈ T0, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
          ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ ≤
      (NC : ℝ) * ((Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) : ℝ) ^ n *
        ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
          ∏ k : Fin n, rungBudget d γ x δ L C0
            ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
             (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k))))) := by
  set Bt : ℝ := (Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) : ℝ) ^ n *
    ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
      ∏ k : Fin n, rungBudget d γ x δ L C0
        ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
         (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k)))) with hBt
  have hBt0 : 0 ≤ Bt := by
    have hcff := cellFourierFactor_nonneg d
    have hbud : ∀ k : Fin n, 0 ≤ rungBudget d γ x δ L C0
        ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
         (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k))) := by
      intro k
      unfold rungBudget
      have hLx : 0 < L ^ (-x) := Real.rpow_pos_of_pos hL0 _
      have hE : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
      refine mul_nonneg hC0 (mul_nonneg hE ?_)
      split_ifs
      · exact hLx.le
      · exact zero_le_one
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hcff) _) (Finset.prod_nonneg fun k _ => hbud k))
  set T := T0.filter (fun z => ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0) with hTdef
  have hTmem : ∀ z, z ∈ T ↔ ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0 := fun z => by
    simp only [hTdef, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by_contra (fun hz => h (hT0 z hz)), h⟩
  have hTz : ∀ z, z ∉ T → ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 = 0 := fun z hz => by
    by_contra h; exact hz ((hTmem z).mpr h)
  have hTw : ∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0 := fun z hz => (hTmem z).mp hz
  have hsum : ∀ t : ↥(Molecule.ladderAtoms u v) → ℝ, ∑ z ∈ T0, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
      ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t = ∑ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
      ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t := fun t => by
    simp only [hTdef]
    refine (Finset.sum_filter_of_ne (fun z _ h => ?_)).symm
    intro h0
    exact h (by rw [h0, zero_mul])
  simp only [hsum]

  by_cases hTe : T.Nonempty
  swap
  · have : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTe
    rw [this]
    simp only [Finset.sum_empty, norm_zero]
    simp only [MeasureTheory.integral_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hBt0
  obtain ⟨z0, hz0⟩ := hTe
  have hcb := fun zs (hzs : zs ∈ T) => C.class_bound hP hL0 base roots hn D hD hd γ η δ x T1 C0 hδ hρ hR hRung
    hlay boundary T hTw hTz zs hzs
  choose! H hHc hHp hHi using hcb
  set cls : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary) → (GardenDart G → (Fin d → ℤ)) :=
    fun z => clsOf (u := u) (v := v) z.1 with hcls
  set 𝒞 := T.image cls with h𝒞
  set rep : (GardenDart G → (Fin d → ℤ)) → ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary) :=
    fun c => if h : ∃ zs ∈ T, cls zs = c then Classical.choose h else z0 with hrep
  have hrepc : ∀ c ∈ 𝒞, rep c ∈ T ∧ cls (rep c) = c := by
    intro c hc
    obtain ⟨zs, hzs, hzc⟩ := Finset.mem_image.mp hc
    have hex : ∃ zs ∈ T, cls zs = c := ⟨zs, hzs, hzc⟩
    simp only [hrep, dif_pos hex]
    exact Classical.choose_spec hex
  have hpt : ∀ t : ↥(Molecule.ladderAtoms u v) → ℝ, ‖∑ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
      ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ ≤ ∑ c ∈ 𝒞, H (rep c) (tauOf (u := u) (v := v) t) := by
    intro t
    have hfib := Finset.sum_fiberwise_of_maps_to (s := T) (t := 𝒞) (g := cls)
      (fun z hz => Finset.mem_image_of_mem cls hz)
      (fun z => ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 * ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t)
    rw [← hfib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c hc => ?_))
    obtain ⟨hrT, hrc⟩ := hrepc c hc
    have heq : T.filter (fun z => cls z = c) = T.filter (fun z => ∀ x, G.molecule.atom x ∉ intAtoms u v →
        bondIndex G z.1.1 x = bondIndex G (rep c).1.1 x) := by
      refine Finset.filter_congr (fun z _ => ?_)
      have h1 : cls z = c ↔ cls z = cls (rep c) := by rw [hrc]
      exact h1.trans (clsOf_eq_iff (u := u) (v := v) z.1 (rep c).1)
    rw [heq]
    exact hHp (rep c) hrT t
  have hre : ∀ G' : (Fin n → ℝ × ℝ) → ℝ,
      (∫ t in timeBox G D.layer (Molecule.ladderAtoms u v), G' (tauOf (u := u) (v := v) t)) =
        ∫ τ in Set.pi Set.univ (fun k : Fin n =>
          Icc (D.layer (v (LadderDarts.ir k)) : ℝ) (D.layer (v (LadderDarts.ir k)) + 1) ×ˢ
          Icc (D.layer (u (LadderDarts.ir k)) : ℝ) (D.layer (u (LadderDarts.ir k)) + 1)), G' τ := by
    intro G'
    have := integral_time_reindex (evIdx (u := u) (v := v)) (euIdx (u := u) (v := v)) C.idx_injective
      (fun a : ↥(Molecule.ladderAtoms u v) => Icc (D.layer a.1 : ℝ) (D.layer a.1 + 1)) (fun a => measurableSet_Icc) G'
    have hvol : (∏ r : {a : ↥(Molecule.ladderAtoms u v) // a ∉ Set.range (Sum.elim (evIdx (u := u) (v := v)) (euIdx (u := u) (v := v)))},
        (volume (Icc (D.layer r.1.1 : ℝ) (D.layer r.1.1 + 1))).toReal) = 1 := by
      refine Finset.prod_eq_one (fun r _ => ?_)
      simp [Real.volume_Icc]
    rw [hvol, one_mul] at this
    simp only [tauOf_eq]
    exact this
  have hI1 : IntegrableOn (fun t : ↥(Molecule.ladderAtoms u v) → ℝ => ‖∑ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
      ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖) (timeBox G D.layer (Molecule.ladderAtoms u v)) := by
    have hc : Continuous (fun t : ↥(Molecule.ladderAtoms u v) → ℝ => ∑ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
        ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t) :=
      continuous_finsetSum _ (fun z _ => continuous_const.mul (continuous_ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1))
    exact hc.norm.continuousOn.integrableOn_compact (isCompact_timeBox G D.layer (Molecule.ladderAtoms u v))
  have hcontH : ∀ c ∈ 𝒞, Continuous (fun t : ↥(Molecule.ladderAtoms u v) → ℝ => H (rep c) (tauOf (u := u) (v := v) t)) := by
    intro c hc
    have hcτ : Continuous (fun t : ↥(Molecule.ladderAtoms u v) → ℝ => tauOf (u := u) (v := v) t) := by
      simp only [tauOf_eq]
      exact continuous_pi (fun k => (continuous_apply _).prodMk (continuous_apply _))
    exact (hHc (rep c) (hrepc c hc).1).comp hcτ
  have hIH : ∀ c ∈ 𝒞, IntegrableOn (fun t : ↥(Molecule.ladderAtoms u v) → ℝ => H (rep c) (tauOf (u := u) (v := v) t))
      (timeBox G D.layer (Molecule.ladderAtoms u v)) := fun c hc =>
    (hcontH c hc).continuousOn.integrableOn_compact (isCompact_timeBox G D.layer (Molecule.ladderAtoms u v))
  calc ∫ t in timeBox G D.layer (Molecule.ladderAtoms u v), ‖∑ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
          ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖
      ≤ ∫ t in timeBox G D.layer (Molecule.ladderAtoms u v), ∑ c ∈ 𝒞, H (rep c) (tauOf (u := u) (v := v) t) :=
        integral_mono hI1 (integrable_finsetSum _ hIH) (fun t => hpt t)
    _ = ∑ c ∈ 𝒞, ∫ t in timeBox G D.layer (Molecule.ladderAtoms u v), H (rep c) (tauOf (u := u) (v := v) t) :=
        integral_finsetSum _ hIH
    _ = ∑ c ∈ 𝒞, ∫ τ in Set.pi Set.univ (fun k : Fin n =>
          Icc (D.layer (v (LadderDarts.ir k)) : ℝ) (D.layer (v (LadderDarts.ir k)) + 1) ×ˢ
          Icc (D.layer (u (LadderDarts.ir k)) : ℝ) (D.layer (u (LadderDarts.ir k)) + 1)), H (rep c) τ :=
        Finset.sum_congr rfl (fun c _ => hre _)
    _ ≤ ∑ _c ∈ 𝒞, Bt := Finset.sum_le_sum (fun c hc => hHi (rep c) (hrepc c hc).1)
    _ = (𝒞.card : ℝ) * Bt := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (NC : ℝ) * Bt := by
        refine mul_le_mul_of_nonneg_right ?_ hBt0
        exact_mod_cast hNC T hTw

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay
