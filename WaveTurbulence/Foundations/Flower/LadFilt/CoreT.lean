/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.LadderL1Fixed
public import WaveTurbulence.Foundations.Flower.LadFilt.ChainT

/-! # C3 LAD-FILT: the box-robust ladder kernel core (o83 Theorem K)

Copy-threads of main's `LadderDarts.Ctx.kernel_core_L1` (Spine/LadderL1) and `ladder_L1_fixed`
(Spine/LadderL1Fixed) on the unit time box translated by an arbitrary `τ : S → ℝ`: the bound is main's,
with `C₀` replaced by `2 C₀ + 16·81^d`, times the translation weight `∏_k (1 + κ|τ_{v_k}|)² (1 + κ|τ_{u_k}|)²`
over the interior rungs (`κ = δ L^{2γ}/2`). The window constant is `T₁` with `δ (layer + 2) ≤ T₁`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.LadFilt
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay WaveTurbulence.WeylSums
  WaveTurbulence.Sumint MeasureTheory Set Finset

variable {w d : ℕ}

/-- The product of unit time boxes translated by `τ`. -/
def timeBoxT (G : Garden w) (layer : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree)) (τ : S → ℝ) :
    Set (S → ℝ) :=
  Set.pi univ (fun a : S => Icc ((layer a.1 : ℝ) + τ a) ((layer a.1 : ℝ) + τ a + 1))

lemma isCompact_timeBoxT (G : Garden w) (layer : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree))
    (τ : S → ℝ) : IsCompact (timeBoxT G layer S τ) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

variable {G : Garden w}

section coreT
open WaveTurbulence.LadderDecay.LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDecay.LadderDarts.Ctx G.molecule u v)

/-- The translation weight of the interior rungs. -/
noncomputable def ladderWt (κ : ℝ) (τ : (Molecule.ladderAtoms u v) → ℝ) : ℝ :=
  ∏ k : Fin n, rungWt κ (τ (evIdx (u := u) (v := v) k)) (τ (euIdx (u := u) (v := v) k))

lemma one_le_ladderWt {κ : ℝ} (hκ : 0 ≤ κ) (τ : (Molecule.ladderAtoms u v) → ℝ) :
    1 ≤ ladderWt (u := u) (v := v) κ τ :=
  Finset.one_le_prod₀ (fun k _ => one_le_rungWt hκ _ _)

open scoped Classical in
include C in
/-- **The time-L1 core bound on a translated box** (main's `kernel_core_L1`). -/
theorem kernel_core_L1_T (hP : G.IsPlain) {L : ℝ} (hL1 : 1 ≤ L) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (hd : 1 ≤ d)
    (γ η δ x T1 C0 : ℝ) (hδ : 0 < δ) (hx0 : 0 ≤ x) (hC0 : 0 ≤ C0) (hρ : 0 ≤ L ^ (-γ + η))
    (hR : L * L ^ (-γ + η) ≤ L ^ (1 - γ + η))
    (hRung : ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), GoodTerm L (L ^ (1 - γ + η)) a b χ →
      RungOK γ x T1 δ L C0 a b χ)
    (hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x))
    (hlay : ∀ a, δ * ((D.layer a : ℝ) + 2) ≤ T1) (τ : (Molecule.ladderAtoms u v) → ℝ)
    (boundary : GardenDart G → (Fin d → ℤ)) (NC : ℕ)
    (hNC : ∀ T : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary),
      (∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0) →
        (T.image (fun z => clsOf (u := u) (v := v) z.1)).card ≤ NC)
    (T0 : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary))
    (hT0 : ∀ z, z ∉ T0 → ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 = 0) :
    ∫ t in timeBoxT G D.layer (Molecule.ladderAtoms u v) τ,
        ‖∑ z ∈ T0, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
          ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ ≤
      (NC : ℝ) * ((Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) : ℝ) ^ n *
        ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
          ∏ k : Fin n, (rungBudget d γ x δ L (2 * C0 + 16 * 81 ^ d)
              (D.layer (u (LadderDarts.ir k)) ≠ D.layer (v (LadderDarts.ir k))) *
            rungWt (δ * L ^ (2 * γ) / 2) (τ (evIdx (u := u) (v := v) k)) (τ (euIdx (u := u) (v := v) k))))) := by
  have hL0 : 0 < L := by linarith
  set Bt : ℝ := (Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) : ℝ) ^ n *
    ((7 ^ d * cellFourierFactor d) ^ Fintype.card (LadderDarts.Ctx.Code n) *
      ∏ k : Fin n, (rungBudget d γ x δ L (2 * C0 + 16 * 81 ^ d)
          (D.layer (u (LadderDarts.ir k)) ≠ D.layer (v (LadderDarts.ir k))) *
        rungWt (δ * L ^ (2 * γ) / 2) (τ (evIdx (u := u) (v := v) k)) (τ (euIdx (u := u) (v := v) k)))) with hBt
  have hBt0 : 0 ≤ Bt := by
    have hcff := cellFourierFactor_nonneg d
    have hbud : ∀ k : Fin n, 0 ≤ rungBudget d γ x δ L (2 * C0 + 16 * 81 ^ d)
          (D.layer (u (LadderDarts.ir k)) ≠ D.layer (v (LadderDarts.ir k))) *
        rungWt (δ * L ^ (2 * γ) / 2) (τ (evIdx (u := u) (v := v) k)) (τ (euIdx (u := u) (v := v) k)) := by
      intro k
      have hw : 0 ≤ rungWt (δ * L ^ (2 * γ) / 2) (τ (evIdx (u := u) (v := v) k))
          (τ (euIdx (u := u) (v := v) k)) := by unfold rungWt; positivity
      refine mul_nonneg ?_ hw
      unfold rungBudget
      have hLx : 0 < L ^ (-x) := Real.rpow_pos_of_pos hL0 _
      have hE : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
      refine mul_nonneg (by positivity) (mul_nonneg hE ?_)
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
  have hTw : ∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0 := fun z hz =>
    (hTmem z).mp hz
  have hsum : ∀ t : ↥(Molecule.ladderAtoms u v) → ℝ, ∑ z ∈ T0,
      ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
      ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t = ∑ z ∈ T,
      ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
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
  have hcb := fun zs (hzs : zs ∈ T) => class_bound_T C hP hL1 base roots hn D hD hd γ η δ x T1 C0 hδ hx0 hC0
    hρ hR hRung hB hlay (fun k => τ (evIdx (u := u) (v := v) k)) (fun k => τ (euIdx (u := u) (v := v) k))
    boundary T hTw hTz zs hzs
  choose! H hHc hHp hHi using hcb
  set cls : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary) →
      (GardenDart G → (Fin d → ℤ)) :=
    fun z => clsOf (u := u) (v := v) z.1 with hcls
  set 𝒞 := T.image cls with h𝒞
  set rep : (GardenDart G → (Fin d → ℤ)) →
      ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary) :=
    fun c => if h : ∃ zs ∈ T, cls zs = c then Classical.choose h else z0 with hrep
  have hrepc : ∀ c ∈ 𝒞, rep c ∈ T ∧ cls (rep c) = c := by
    intro c hc
    obtain ⟨zs, hzs, hzc⟩ := Finset.mem_image.mp hc
    have hex : ∃ zs ∈ T, cls zs = c := ⟨zs, hzs, hzc⟩
    simp only [hrep, dif_pos hex]
    exact Classical.choose_spec hex
  have hpt : ∀ t : ↥(Molecule.ladderAtoms u v) → ℝ,
      ‖∑ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
      ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ ≤
        ∑ c ∈ 𝒞, H (rep c) (tauOf (u := u) (v := v) t) := by
    intro t
    have hfib := Finset.sum_fiberwise_of_maps_to (s := T) (t := 𝒞) (g := cls)
      (fun z hz => Finset.mem_image_of_mem cls hz)
      (fun z => ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
        ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t)
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
      (∫ t in timeBoxT G D.layer (Molecule.ladderAtoms u v) τ, G' (tauOf (u := u) (v := v) t)) =
        ∫ σ in Set.pi Set.univ (fun k : Fin n =>
          Icc ((D.layer (v (LadderDarts.ir k)) : ℝ) + τ (evIdx (u := u) (v := v) k))
            ((D.layer (v (LadderDarts.ir k)) : ℝ) + τ (evIdx (u := u) (v := v) k) + 1) ×ˢ
          Icc ((D.layer (u (LadderDarts.ir k)) : ℝ) + τ (euIdx (u := u) (v := v) k))
            ((D.layer (u (LadderDarts.ir k)) : ℝ) + τ (euIdx (u := u) (v := v) k) + 1)), G' σ := by
    intro G'
    have := integral_time_reindex (evIdx (u := u) (v := v)) (euIdx (u := u) (v := v)) C.idx_injective
      (fun a : ↥(Molecule.ladderAtoms u v) => Icc ((D.layer a.1 : ℝ) + τ a) ((D.layer a.1 : ℝ) + τ a + 1))
      (fun a => measurableSet_Icc) G'
    have hvol : (∏ r : {a : ↥(Molecule.ladderAtoms u v) //
        a ∉ Set.range (Sum.elim (evIdx (u := u) (v := v)) (euIdx (u := u) (v := v)))},
        (volume (Icc ((D.layer r.1.1 : ℝ) + τ r.1) ((D.layer r.1.1 : ℝ) + τ r.1 + 1))).toReal) = 1 := by
      refine Finset.prod_eq_one (fun r _ => ?_)
      simp [Real.volume_Icc]
    rw [hvol, one_mul] at this
    simp only [tauOf_eq]
    exact this
  have hI1 : IntegrableOn (fun t : ↥(Molecule.ladderAtoms u v) → ℝ =>
      ‖∑ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
      ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖)
      (timeBoxT G D.layer (Molecule.ladderAtoms u v) τ) := by
    have hc : Continuous (fun t : ↥(Molecule.ladderAtoms u v) → ℝ =>
        ∑ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
        ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t) :=
      continuous_finsetSum _ (fun z _ => continuous_const.mul
        (continuous_ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1))
    exact hc.norm.continuousOn.integrableOn_compact (isCompact_timeBoxT G D.layer _ τ)
  have hcontH : ∀ c ∈ 𝒞, Continuous (fun t : ↥(Molecule.ladderAtoms u v) → ℝ =>
      H (rep c) (tauOf (u := u) (v := v) t)) := by
    intro c hc
    have hcτ : Continuous (fun t : ↥(Molecule.ladderAtoms u v) → ℝ => tauOf (u := u) (v := v) t) := by
      simp only [tauOf_eq]
      exact continuous_pi (fun k => (continuous_apply _).prodMk (continuous_apply _))
    exact (hHc (rep c) (hrepc c hc).1).comp hcτ
  have hIH : ∀ c ∈ 𝒞, IntegrableOn (fun t : ↥(Molecule.ladderAtoms u v) → ℝ =>
      H (rep c) (tauOf (u := u) (v := v) t)) (timeBoxT G D.layer (Molecule.ladderAtoms u v) τ) :=
    fun c hc => (hcontH c hc).continuousOn.integrableOn_compact (isCompact_timeBoxT G D.layer _ τ)
  calc ∫ t in timeBoxT G D.layer (Molecule.ladderAtoms u v) τ,
        ‖∑ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
          ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖
      ≤ ∫ t in timeBoxT G D.layer (Molecule.ladderAtoms u v) τ,
          ∑ c ∈ 𝒞, H (rep c) (tauOf (u := u) (v := v) t) :=
        integral_mono hI1 (integrable_finsetSum _ hIH) (fun t => hpt t)
    _ = ∑ c ∈ 𝒞, ∫ t in timeBoxT G D.layer (Molecule.ladderAtoms u v) τ,
          H (rep c) (tauOf (u := u) (v := v) t) :=
        integral_finsetSum _ hIH
    _ = ∑ c ∈ 𝒞, ∫ σ in Set.pi Set.univ (fun k : Fin n =>
          Icc ((D.layer (v (LadderDarts.ir k)) : ℝ) + τ (evIdx (u := u) (v := v) k))
            ((D.layer (v (LadderDarts.ir k)) : ℝ) + τ (evIdx (u := u) (v := v) k) + 1) ×ˢ
          Icc ((D.layer (u (LadderDarts.ir k)) : ℝ) + τ (euIdx (u := u) (v := v) k))
            ((D.layer (u (LadderDarts.ir k)) : ℝ) + τ (euIdx (u := u) (v := v) k) + 1)), H (rep c) σ :=
        Finset.sum_congr rfl (fun c _ => hre _)
    _ ≤ ∑ _c ∈ 𝒞, Bt := Finset.sum_le_sum (fun c hc => hHi (rep c) (hrepc c hc).1)
    _ = (𝒞.card : ℝ) * Bt := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (NC : ℝ) * Bt := by
        refine mul_le_mul_of_nonneg_right ?_ hBt0
        exact_mod_cast hNC T hTw

end coreT

end WaveTurbulence.Flower.LadFilt
