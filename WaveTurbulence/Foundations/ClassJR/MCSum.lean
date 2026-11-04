/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCPair
public import WaveTurbulence.Foundations.ClassJR.Reindex

/-!
# Sums of coefficient representations

The terms of DH21 (maincoef3) are regrouped by their set `Z`: a coefficient `B̃_{Q,Z}` is a finite
sum of terms with the same variables `S ∖ Z`. This file shows that `MCRep` is stable under
relabelling of the variables (`SRep.reindex`), under sums on the same variable set (`MCRep.add`,
`MCRep.finsum`), and under increasing the constant (`MCRep.mono`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Basic

variable {ι : Type*} [Fintype ι] {Γ : Type*}

theorem dnorm_add_le {f g : (ι → ℝ) → Γ → ℂ} (hf : ∀ γ, ContDiff ℝ ∞ fun β => f β γ)
    (hg : ∀ γ, ContDiff ℝ ∞ fun β => g β γ) (k : ℕ) (β : ι → ℝ) (γ : Γ) :
    dnorm k (fun β γ => f β γ + g β γ) β γ ≤ dnorm k f β γ + dnorm k g β γ := by
  unfold dnorm
  have e : lift1 (fun β γ => f β γ + g β γ) γ = lift1 f γ + lift1 g γ := rfl
  rw [e, iteratedFDeriv_add_apply ((contDiff_lift1 (hf γ)).contDiffAt.of_le
    (by exact_mod_cast le_top)) ((contDiff_lift1 (hg γ)).contDiffAt.of_le
    (by exact_mod_cast le_top))]
  exact enorm_add_le _ _

end Basic

section SRepOps

variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {θ a b A N N₁ N₂ : ℝ}

/-- **Relabelling the variables of a coefficient symbol.** -/
theorem SRep.reindex (e : ι ≃ ι') {C : (ι → ℝ) → ℝ × ℝ → ℂ} (h : SRep θ a b A N C) :
    SRep θ a b A N fun β lam => C (fun i => β (e i)) lam where
  nonneg := h.nonneg
  reg := h.reg.reindex e
  norm k := by
    simp_rw [dnorm_reindex]
    exact (lintegral_reindex e (F := fun α => ∫⁻ lam, wL θ lam * dnorm k C α lam)).trans_le
      (h.norm k)
  wnorm i := by
    have h' := h.wnorm (e.symm i)
    refine le_of_eq_of_le ?_ h'
    have := lintegral_reindex e (F := fun α => ∫⁻ lam, wL a lam * (1 + ‖α (e.symm i)‖ₑ) ^ b *
      ‖C α lam‖ₑ)
    simp only [Equiv.apply_symm_apply] at this
    exact this

/-- **Sums of coefficient symbols.** -/
theorem SRep.add {C₁ C₂ : (ι → ℝ) → ℝ × ℝ → ℂ} (h₁ : SRep θ a b A N₁ C₁)
    (h₂ : SRep θ a b A N₂ C₂) (hθ : 0 ≤ θ) (hA : 0 ≤ A) :
    SRep θ a b A (N₁ + N₂) fun β lam => C₁ β lam + C₂ β lam := by
  have hs : ∀ lam, ContDiff ℝ ∞ fun β => C₁ β lam + C₂ β lam := fun lam =>
    (h₁.reg.smooth lam).add (h₂.reg.smooth lam)
  have hm : StronglyMeasurable (Function.uncurry fun β lam => C₁ β lam + C₂ β lam) :=
    h₁.reg.meas.add h₂.reg.meas
  have hd₁ := measurable_dnorm h₁.reg.smooth h₁.reg.meas
  have hd₂ := measurable_dnorm h₂.reg.smooth h₂.reg.meas
  have hw : ∀ {c : ℝ}, Measurable fun lam : ℝ × ℝ => wL c lam := fun {c} => measurable_wL c
  -- the integrated bound with any weight
  have key : ∀ (w : (ι → ℝ) → ℝ × ℝ → ℝ≥0∞), Measurable (Function.uncurry w) → ∀ k,
      ∫⁻ β, ∫⁻ lam, w β lam * dnorm k (fun β lam => C₁ β lam + C₂ β lam) β lam ≤
        (∫⁻ β, ∫⁻ lam, w β lam * dnorm k C₁ β lam) +
          ∫⁻ β, ∫⁻ lam, w β lam * dnorm k C₂ β lam := by
    intro w hwm k
    have hf₁ : Measurable (Function.uncurry fun β lam => w β lam * dnorm k C₁ β lam) :=
      hwm.mul (hd₁ k)
    have hf₂ : Measurable (Function.uncurry fun β lam => w β lam * dnorm k C₂ β lam) :=
      hwm.mul (hd₂ k)
    calc ∫⁻ β, ∫⁻ lam, w β lam * dnorm k (fun β lam => C₁ β lam + C₂ β lam) β lam
        ≤ ∫⁻ β, ∫⁻ lam, (w β lam * dnorm k C₁ β lam + w β lam * dnorm k C₂ β lam) :=
          lintegral_mono fun β => lintegral_mono fun lam => by
            rw [← mul_add]
            exact mul_le_mul' le_rfl (dnorm_add_le h₁.reg.smooth h₂.reg.smooth k β lam)
      _ = ∫⁻ β, ((∫⁻ lam, w β lam * dnorm k C₁ β lam) + ∫⁻ lam, w β lam * dnorm k C₂ β lam) :=
          lintegral_congr fun β => lintegral_add_left hf₁.of_uncurry_left _
      _ = _ := lintegral_add_left
          (hf₁.lintegral_prod_right' : Measurable fun β => ∫⁻ lam, w β lam * dnorm k C₁ β lam) _
  refine ⟨add_nonneg h₁.nonneg h₂.nonneg, SymReg.of_lintegral hs hm fun k => ?_, fun k => ?_,
    fun i => ?_⟩
  · have h := key (fun _ _ => 1) measurable_const k
    simp only [one_mul] at h
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩) h
    · exact ne_top_of_le_ne_top (gev_ne_top _ _ _) (h₁.norm_unweighted hθ k)
    · exact ne_top_of_le_ne_top (gev_ne_top _ _ _) (h₂.norm_unweighted hθ k)
  · refine (key (fun _ lam => wL θ lam) (hw.comp measurable_snd) k).trans ?_
    rw [← gev_add h₁.nonneg h₂.nonneg hA]
    exact add_le_add (h₁.norm k) (h₂.norm k)
  · have hwi : Measurable (Function.uncurry fun (β : ι → ℝ) (lam : ℝ × ℝ) =>
        wL a lam * (1 + ‖β i‖ₑ) ^ b) := by
      change Measurable fun y : (ι → ℝ) × (ℝ × ℝ) => wL a y.2 * (1 + ‖y.1 i‖ₑ) ^ b
      have := measurable_wL a
      fun_prop
    have h := key (fun β lam => wL a lam * (1 + ‖β i‖ₑ) ^ b) hwi 0
    simp only [dnorm_zero] at h
    refine h.trans ?_
    rw [ENNReal.ofReal_add h₁.nonneg h₂.nonneg]
    exact add_le_add (h₁.wnorm i) (h₂.wnorm i)

end SRepOps

section MCRepOps

variable {V : Type} {θ a b A N N' N₁ N₂ : ℝ} {S : Set V}

theorem MCRep.mono {F : (V → ℝ) → ℝ → ℝ → ℂ} (h : MCRep θ a b A N S F) (hN : N ≤ N')
    (hA : 0 ≤ A) : MCRep θ a b A N' S F := by
  obtain ⟨ι, hι, f, C, hf, hr, hN0, hreg, hn, hw, he⟩ := h
  exact ⟨ι, hι, f, C, hf, hr, hN0.trans hN, hreg,
    fun k => (hn k).trans (gev_mono hN hA le_rfl (hN0.trans hN) k),
    fun i => (hw i).trans (ENNReal.ofReal_le_ofReal hN), he⟩

theorem MCRep.congr {F F' : (V → ℝ) → ℝ → ℝ → ℂ} (h : MCRep θ a b A N S F)
    (he : ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F' α t s = F α t s) :
    MCRep θ a b A N S F' := by
  obtain ⟨ι, hι, f, C, hf, hr, hN0, hreg, hn, hw, he'⟩ := h
  exact ⟨ι, hι, f, C, hf, hr, hN0, hreg, hn, hw, fun α t s ht hs =>
    (he α t s ht hs).trans (he' α t s ht hs)⟩

/-- The zero coefficient, on the variables of an injection. -/
theorem MCRep.zero_of_range {ι : Type} [Fintype ι] {f : ι → V} (hf : Function.Injective f)
    (hr : Set.range f = S) (hN : 0 ≤ N) : MCRep θ a b A N S fun _ _ _ => 0 := by
  refine ⟨ι, inferInstance, f, fun _ _ => 0, hf, hr, hN, symReg_zero, fun k => ?_, fun i => ?_,
    fun α t s _ _ => by simp⟩
  · simp only [dnorm_zero_fun, mul_zero, lintegral_zero]
    exact bot_le
  · simp only [enorm_zero, mul_zero, lintegral_zero]
    exact bot_le

/-- **Sums of coefficient representations on the same variables.** -/
theorem MCRep.add {F₁ F₂ : (V → ℝ) → ℝ → ℝ → ℂ} (h₁ : MCRep θ a b A N₁ S F₁)
    (h₂ : MCRep θ a b A N₂ S F₂) (hθ : 0 ≤ θ) (hA : 0 ≤ A) :
    MCRep θ a b A (N₁ + N₂) S fun α t s => F₁ α t s + F₂ α t s := by
  obtain ⟨ι₁, _, f₁, C₁, hf₁, hr₁, hS₁, he₁⟩ := h₁.exists_srep
  obtain ⟨ι₂, _, f₂, C₂, hf₂, hr₂, hS₂, he₂⟩ := h₂.exists_srep
  obtain ⟨e, hfe⟩ := exists_equiv_of_range_eq hf₁ hf₂ (hr₂.trans hr₁.symm)
  have hS := hS₁.add (hS₂.reindex e) hθ hA
  refine ⟨ι₁, inferInstance, f₁, _, hf₁, hr₁, hS.nonneg, hS.reg, hS.norm, hS.wnorm,
    fun α t s ht hs => ?_⟩
  have hφ : Continuous fun lam : ℝ × ℝ => e2 lam t s := by unfold e2; fun_prop
  have hc : ∀ (C : ℝ × ℝ → ℂ), Integrable C → Integrable fun lam => C lam * e2 lam t s :=
    fun C hC => hC.mul_bdd (c := 1) hφ.aestronglyMeasurable
      (Eventually.of_forall fun lam => (norm_e2 lam t s).le)
  have h2 : (fun i => (α ∘ f₁) (e i)) = α ∘ f₂ := by
    funext i; simp [hfe i]
  show F₁ α t s + F₂ α t s = _
  rw [he₁ α t s ht hs, he₂ α t s ht hs, ← integral_add (hc _ (hS₁.reg.integrable _))
    (hc _ (hS₂.reg.integrable _))]
  refine integral_congr_ae (Eventually.of_forall fun lam => ?_)
  simp only [h2]
  ring

/-- **Finite sums of coefficient representations on the same variables.** -/
theorem MCRep.finsum {κ : Type*} (K : Finset κ) {F : κ → (V → ℝ) → ℝ → ℝ → ℂ} {N : κ → ℝ}
    (h : ∀ k ∈ K, MCRep θ a b A (N k) S (F k)) (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    (hS : ∃ (ι : Type) (_ : Fintype ι) (f : ι → V), Function.Injective f ∧ Set.range f = S) :
    MCRep θ a b A (∑ k ∈ K, N k) S fun α t s => ∑ k ∈ K, F k α t s := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    obtain ⟨ι, _, f, hf, hr⟩ := hS
    simpa using MCRep.zero_of_range (θ := θ) (a := a) (b := b) (A := A) hf hr le_rfl
  | insert k K hk ih =>
    have hK := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hk' := h k (Finset.mem_insert_self k K)
    have hadd := hk'.add hK hθ hA
    rw [Finset.sum_insert hk]
    refine hadd.congr fun α t s _ _ => ?_
    rw [Finset.sum_insert hk]

end MCRepOps

end WaveTurbulence.ClassJR
