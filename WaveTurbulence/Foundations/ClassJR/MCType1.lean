/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCCase1
public import WaveTurbulence.Foundations.ClassJR.MCDefs

/-!
# DH21 Proposition 5.1, Case 1: the expansion step

DH21 L1100–L1112. If the three subcouple coefficients have the expansions (maincoef3)
`F_j = Σ_{Z_j ⊆ S_j} ∏_{z∈Z_j} Φ(ζ_z α_z) · G_{j,Z_j}` (`MCExp`), with pairwise disjoint variable sets
`S_j` not containing the root variable `v`, then the type 1 recursion (newexp1) `type1F v sw F` has
the expansion over `Z ⊆ {v} ∪ S₁ ∪ S₂ ∪ S₃` with `G_Z = type1F (G_{1,Z∩S₁}, G_{2,Z∩S₂}, G_{3,Z∩S₃})`
if `v ∉ Z` and `G_Z = 0` otherwise ("we may choose `Z = Z₁ ∪ Z₂ ∪ Z₃`", DH21 L1110).

* `MCRep.type1`: a single representation step (`SRep.case1`, `integral_C1_e2`).
* `type1F_expand`: the type 1 recursion is multilinear in the three coefficients.
* `MCExp.type1`: the expansion step.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Combinatorics

variable {V : Type} [DecidableEq V]

/-- `Σ_{Z ⊆ A ∪ B} F Z = Σ_{Z₁ ⊆ A} Σ_{Z₂ ⊆ B} F (Z₁ ∪ Z₂)` for disjoint `A`, `B`. -/
theorem sum_powerset_union_of_disjoint {M : Type*} [AddCommMonoid M] {B : Finset V} :
    ∀ {A : Finset V}, Disjoint A B → ∀ F : Finset V → M,
      ∑ Z ∈ (A ∪ B).powerset, F Z = ∑ Z₁ ∈ A.powerset, ∑ Z₂ ∈ B.powerset, F (Z₁ ∪ Z₂) := by
  intro A
  induction A using Finset.induction_on with
  | empty => intro _ F; simp
  | insert a A ha ih =>
    intro hd F
    have hdA : Disjoint A B := Finset.disjoint_of_subset_left (Finset.subset_insert a A) hd
    have haB : a ∉ B := Finset.disjoint_left.1 hd (Finset.mem_insert_self a A)
    have haAB : a ∉ A ∪ B := by simp [ha, haB]
    rw [Finset.insert_union, Finset.sum_powerset_insert haAB, Finset.sum_powerset_insert ha,
      ih hdA F, ih hdA fun Z => F (insert a Z)]
    congr 1
    exact Finset.sum_congr rfl fun Z₁ _ => Finset.sum_congr rfl fun Z₂ _ => by
      rw [Finset.insert_union]

theorem union3_inter_left {S₁ S₂ S₃ Z₁ Z₂ Z₃ : Finset V} (h12 : Disjoint S₁ S₂)
    (h13 : Disjoint S₁ S₃) (hZ₁ : Z₁ ⊆ S₁) (hZ₂ : Z₂ ⊆ S₂) (hZ₃ : Z₃ ⊆ S₃) :
    (Z₁ ∪ Z₂ ∪ Z₃) ∩ S₁ = Z₁ := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨(h | h) | h, hx⟩
    · exact h
    · exact absurd (hZ₂ h) (Finset.disjoint_left.1 h12 hx)
    · exact absurd (hZ₃ h) (Finset.disjoint_left.1 h13 hx)
  · intro h
    exact ⟨Or.inl (Or.inl h), hZ₁ h⟩

theorem union3_inter_mid {S₁ S₂ S₃ Z₁ Z₂ Z₃ : Finset V} (h12 : Disjoint S₁ S₂)
    (h23 : Disjoint S₂ S₃) (hZ₁ : Z₁ ⊆ S₁) (hZ₂ : Z₂ ⊆ S₂) (hZ₃ : Z₃ ⊆ S₃) :
    (Z₁ ∪ Z₂ ∪ Z₃) ∩ S₂ = Z₂ := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨(h | h) | h, hx⟩
    · exact absurd hx (Finset.disjoint_left.1 h12 (hZ₁ h))
    · exact h
    · exact absurd (hZ₃ h) (Finset.disjoint_left.1 h23 hx)
  · intro h
    exact ⟨Or.inl (Or.inr h), hZ₂ h⟩

theorem union3_inter_right {S₁ S₂ S₃ Z₁ Z₂ Z₃ : Finset V} (h13 : Disjoint S₁ S₃)
    (h23 : Disjoint S₂ S₃) (hZ₁ : Z₁ ⊆ S₁) (hZ₂ : Z₂ ⊆ S₂) (hZ₃ : Z₃ ⊆ S₃) :
    (Z₁ ∪ Z₂ ∪ Z₃) ∩ S₃ = Z₃ := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨(h | h) | h, hx⟩
    · exact absurd hx (Finset.disjoint_left.1 h13 (hZ₁ h))
    · exact absurd hx (Finset.disjoint_left.1 h23 (hZ₂ h))
    · exact h
  · intro h
    exact ⟨Or.inr h, hZ₃ h⟩

end Combinatorics

section RepBasics

variable {V : Type} {θ a b A N : ℝ}

/-- `MCRep` in terms of `SRep`. -/
theorem MCRep.exists_srep {S : Set V} {F : (V → ℝ) → ℝ → ℝ → ℂ} (h : MCRep θ a b A N S F) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → V) (C : (ι → ℝ) → ℝ × ℝ → ℂ),
      Function.Injective f ∧ Set.range f = S ∧ SRep θ a b A N C ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        F α t s = ∫ lam, C (α ∘ f) lam * e2 lam t s := by
  obtain ⟨ι, hι, f, C, hf, hr, hN, hreg, hn, hw, he⟩ := h
  exact ⟨ι, hι, f, C, hf, hr, ⟨hN, hreg, hn, hw⟩, he⟩

theorem MCRep.nonneg {S : Set V} {F : (V → ℝ) → ℝ → ℝ → ℂ} (h : MCRep θ a b A N S F) : 0 ≤ N := by
  obtain ⟨_, _, _, _, _, _, hN, _⟩ := h
  exact hN

theorem dnorm_zero_fun {ι Γ : Type*} [Fintype ι] (k : ℕ) (α : ι → ℝ) (γ : Γ) :
    dnorm k (fun (_ : ι → ℝ) (_ : Γ) => (0 : ℂ)) α γ = 0 := by
  simp only [dnorm]
  rw [show lift1 (fun (_ : ι → ℝ) (_ : Γ) => (0 : ℂ)) γ = 0 from rfl, iteratedFDeriv_zero]
  simp

theorem symReg_zero {ι Γ : Type*} [Fintype ι] [MeasureSpace Γ] :
    SymReg (fun (_ : ι → ℝ) (_ : Γ) => (0 : ℂ)) where
  smooth _ := contDiff_const
  meas := stronglyMeasurable_const
  dom k := by simp [supD, dnorm_zero_fun]

/-- **The zero coefficient.** -/
theorem MCRep.zero (hN : 0 ≤ N) (S : Finset V) :
    MCRep θ a b A N (S : Set V) (fun _ _ _ => 0) := by
  refine ⟨{x // x ∈ S}, inferInstance, Subtype.val, fun _ _ => 0, Subtype.val_injective, ?_, hN,
    symReg_zero, fun k => ?_, fun i => ?_, fun α t s _ _ => by simp⟩
  · ext x
    simp
  · simp only [dnorm_zero_fun, mul_zero, lintegral_zero]
    exact bot_le
  · simp only [enorm_zero, mul_zero, lintegral_zero]
    exact bot_le

/-- A coefficient representation is continuous on `[0,1]²`. -/
theorem MCRep.exists_continuous {S : Set V} {F : (V → ℝ) → ℝ → ℝ → ℂ} (h : MCRep θ a b A N S F)
    (α : V → ℝ) : ∃ R : ℝ → ℝ → ℂ, Continuous (fun p : ℝ × ℝ => R p.1 p.2) ∧
      ∀ t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F α t s = R t s := by
  obtain ⟨ι, _, f, C, -, -, -, hreg, -, -, he⟩ := h
  refine ⟨fun t s => ∫ lam, C (α ∘ f) lam * e2 lam t s, ?_, fun t s ht hs => he α t s ht hs⟩
  have hc : ∀ lam : ℝ × ℝ, Continuous fun p : ℝ × ℝ => e2 lam p.1 p.2 := fun lam => by
    unfold e2
    fun_prop
  refine continuous_of_dominated (bound := fun lam => ‖C (α ∘ f) lam‖) (fun p => ?_)
    (fun p => Eventually.of_forall fun lam => ?_) (hreg.integrable _).norm
    (Eventually.of_forall fun lam => continuous_const.mul (hc lam))
  · have hφ : Continuous fun lam : ℝ × ℝ => e2 lam p.1 p.2 := by
      unfold e2
      fun_prop
    exact (hreg.integrable _).1.mul hφ.aestronglyMeasurable
  · rw [norm_mul, norm_e2, mul_one]

end RepBasics

section TimeIntegrals

variable {V : Type}

/-- Double interval integrals of finite sums of continuous functions. -/
theorem integral2_finset_sum {κ : Type*} (I : Finset κ) (f : κ → ℝ → ℝ → ℂ)
    (hf : ∀ i, Continuous fun p : ℝ × ℝ => f i p.1 p.2) (t s : ℝ) :
    ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, ∑ i ∈ I, f i t₁ s₁ =
      ∑ i ∈ I, ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, f i t₁ s₁ := by
  have h1 : ∀ t₁, ∫ s₁ in (0 : ℝ)..s, ∑ i ∈ I, f i t₁ s₁ =
      ∑ i ∈ I, ∫ s₁ in (0 : ℝ)..s, f i t₁ s₁ := fun t₁ =>
    intervalIntegral.integral_finsetSum fun i _ =>
      ((hf i).comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s
  simp_rw [h1]
  refine intervalIntegral.integral_finsetSum fun i _ => ?_
  have : Continuous fun t₁ => ∫ s₁ in (0 : ℝ)..s, f i t₁ s₁ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hf i) 0 s
  exact this.intervalIntegrable 0 t

theorem continuous_swapT (b : Bool) {H : ℝ → ℝ → ℂ} (hH : Continuous fun p : ℝ × ℝ => H p.1 p.2)
    (α : V → ℝ) : Continuous fun p : ℝ × ℝ => swapT b (fun _ => H) α p.1 p.2 := by
  cases b
  · exact hH
  · exact hH.comp continuous_swap

/-- The type 1 recursion only sees its coefficients on `[0,1]²`. -/
theorem type1F_congr {F F' : Fin 3 → (V → ℝ) → ℝ → ℝ → ℂ} (α : V → ℝ)
    (hF : ∀ j t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F j α t s = F' j α t s)
    (v : V) (sw : Fin 3 → Bool) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    type1F v sw F α t s = type1F v sw F' α t s := by
  unfold type1F
  refine intervalIntegral.integral_congr fun t₁ ht₁ =>
    intervalIntegral.integral_congr fun s₁ hs₁ => ?_
  rw [uIcc_of_le ht.1] at ht₁
  rw [uIcc_of_le hs.1] at hs₁
  have ht₁' : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1, ht₁.2.trans ht.2⟩
  have hs₁' : s₁ ∈ Icc (0 : ℝ) 1 := ⟨hs₁.1, hs₁.2.trans hs.2⟩
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  cases h : sw j
  · simp only [swapT, Bool.false_eq_true, ↓reduceIte]
    exact hF j t₁ s₁ ht₁' hs₁'
  · simp only [swapT, ↓reduceIte]
    exact hF j s₁ t₁ hs₁' ht₁'

/-- **The type 1 recursion is multilinear** in its three coefficients. -/
theorem type1F_expand (α : V → ℝ) (v : V) (sw : Fin 3 → Bool) {κ : Type*} (Is : Fin 3 → Finset κ)
    (c : Fin 3 → κ → ℂ) (H : Fin 3 → κ → ℝ → ℝ → ℂ)
    (hH : ∀ j i, Continuous fun p : ℝ × ℝ => H j i p.1 p.2) (t s : ℝ) :
    type1F v sw (fun j _ t s => ∑ i ∈ Is j, c j i * H j i t s) α t s =
      ∑ i₁ ∈ Is 0, ∑ i₂ ∈ Is 1, ∑ i₃ ∈ Is 2, c 0 i₁ * c 1 i₂ * c 2 i₃ *
        type1F v sw ![fun _ => H 0 i₁, fun _ => H 1 i₂, fun _ => H 2 i₃] α t s := by
  have hsw : ∀ (b : Bool) (j : Fin 3) (t₁ s₁ : ℝ),
      swapT b (fun (_ : V → ℝ) t s => ∑ i ∈ Is j, c j i * H j i t s) α t₁ s₁ =
        ∑ i ∈ Is j, c j i * swapT b (fun _ => H j i) α t₁ s₁ := by
    intro b j t₁ s₁
    cases b <;> rfl
  have hce : Continuous fun p : ℝ × ℝ => cexp (π * I * (α v * (p.1 - p.2))) := by fun_prop
  -- the summands
  let P : κ → κ → κ → ℝ → ℝ → ℂ := fun i₁ i₂ i₃ t₁ s₁ =>
    cexp (π * I * (α v * (t₁ - s₁))) * (swapT (sw 0) (fun _ => H 0 i₁) α t₁ s₁ *
      swapT (sw 1) (fun _ => H 1 i₂) α t₁ s₁ * swapT (sw 2) (fun _ => H 2 i₃) α t₁ s₁)
  have hPc : ∀ i₁ i₂ i₃, Continuous fun p : ℝ × ℝ => P i₁ i₂ i₃ p.1 p.2 := fun i₁ i₂ i₃ =>
    hce.mul (((continuous_swapT _ (hH 0 i₁) α).mul (continuous_swapT _ (hH 1 i₂) α)).mul
      (continuous_swapT _ (hH 2 i₃) α))
  have hpt : ∀ t₁ s₁ : ℝ, cexp (π * I * (α v * (t₁ - s₁))) *
      ∏ j, swapT (sw j) (fun (_ : V → ℝ) t s => ∑ i ∈ Is j, c j i * H j i t s) α t₁ s₁ =
      ∑ i₁ ∈ Is 0, ∑ i₂ ∈ Is 1, ∑ i₃ ∈ Is 2, c 0 i₁ * c 1 i₂ * c 2 i₃ * P i₁ i₂ i₃ t₁ s₁ := by
    intro t₁ s₁
    rw [Fin.prod_univ_three, hsw, hsw, hsw, Finset.sum_mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₁ _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₂ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₃ _ => ?_
    simp only [P]
    ring
  have hT : ∀ i₁ i₂ i₃, type1F v sw ![fun _ => H 0 i₁, fun _ => H 1 i₂, fun _ => H 2 i₃] α t s =
      ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, P i₁ i₂ i₃ t₁ s₁ := fun i₁ i₂ i₃ => by
    unfold type1F
    simp only [Fin.prod_univ_three]
    rfl
  have hL : type1F v sw (fun j _ t s => ∑ i ∈ Is j, c j i * H j i t s) α t s =
      ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s,
        ∑ i₁ ∈ Is 0, ∑ i₂ ∈ Is 1, ∑ i₃ ∈ Is 2, c 0 i₁ * c 1 i₂ * c 2 i₃ * P i₁ i₂ i₃ t₁ s₁ := by
    unfold type1F
    simp_rw [hpt]
  rw [hL]
  have hc3 : ∀ i₁ i₂, Continuous fun p : ℝ × ℝ =>
      ∑ i₃ ∈ Is 2, c 0 i₁ * c 1 i₂ * c 2 i₃ * P i₁ i₂ i₃ p.1 p.2 := fun i₁ i₂ =>
    continuous_finsetSum _ fun i₃ _ => continuous_const.mul (hPc i₁ i₂ i₃)
  have hc2 : ∀ i₁, Continuous fun p : ℝ × ℝ =>
      ∑ i₂ ∈ Is 1, ∑ i₃ ∈ Is 2, c 0 i₁ * c 1 i₂ * c 2 i₃ * P i₁ i₂ i₃ p.1 p.2 := fun i₁ =>
    continuous_finsetSum _ fun i₂ _ => hc3 i₁ i₂
  rw [integral2_finset_sum _ _ hc2]
  refine Finset.sum_congr rfl fun i₁ _ => ?_
  rw [integral2_finset_sum _ _ (hc3 i₁)]
  refine Finset.sum_congr rfl fun i₂ _ => ?_
  rw [integral2_finset_sum _ _ fun i₃ => continuous_const.mul (hPc i₁ i₂ i₃)]
  refine Finset.sum_congr rfl fun i₃ _ => ?_
  rw [hT]
  simp_rw [intervalIntegral.integral_const_mul]

/-- A representation of a coefficient with swapped times. -/
theorem swapT_rep {F : (V → ℝ) → ℝ → ℝ → ℂ} {ι : Type*} {f : ι → V}
    {C : (ι → ℝ) → ℝ × ℝ → ℂ}
    (he : ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      F α t s = ∫ lam, C (α ∘ f) lam * e2 lam t s)
    (sw : Bool) (α : V → ℝ) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    swapT sw F α t s = ∫ lam, swapC sw C (α ∘ f) lam * e2 lam t s := by
  rw [integral_swapC_e2]
  cases sw
  · simp only [swapT, Bool.false_eq_true, ↓reduceIte]
    exact he α t s ht hs
  · simp only [swapT, ↓reduceIte]
    exact he α s t hs ht

end TimeIntegrals

section Type1Step

variable {V : Type} [DecidableEq V] {θ a b A : ℝ}

omit [DecidableEq V] in
/-- **DH21 Prop 5.1, Case 1, one representation step.** -/
theorem MCRep.type1 {N₁ N₂ N₃ : ℝ} {S₁ S₂ S₃ : Set V} {v : V}
    {F : Fin 3 → (V → ℝ) → ℝ → ℝ → ℂ} (h₁ : MCRep θ a b A N₁ S₁ (F 0))
    (h₂ : MCRep θ a b A N₂ S₂ (F 1)) (h₃ : MCRep θ a b A N₃ S₃ (F 2)) (h12 : Disjoint S₁ S₂)
    (h13 : Disjoint S₁ S₃) (h23 : Disjoint S₂ S₃) (hv : v ∉ S₁ ∪ S₂ ∪ S₃)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1) (hbθ : b ≤ θ)
    (hA : A1 ≤ A) (sw : Fin 3 → Bool) :
    MCRep θ a b A (KC1 θ a b * (N₁ * N₂ * N₃)) (insert v (S₁ ∪ S₂ ∪ S₃)) (type1F v sw F) := by
  obtain ⟨ι₁, _, f₁, C₁, hf₁, hr₁, hS₁, he₁⟩ := h₁.exists_srep
  obtain ⟨ι₂, _, f₂, C₂, hf₂, hr₂, hS₂, he₂⟩ := h₂.exists_srep
  obtain ⟨ι₃, _, f₃, C₃, hf₃, hr₃, hS₃, he₃⟩ := h₃.exists_srep
  have hD₁ := hS₁.swap (sw 0)
  have hD₂ := hS₂.swap (sw 1)
  have hD₃ := hS₃.swap (sw 2)
  have hS := SRep.case1 hD₁ hD₂ hD₃ hθ0 hθ1 ha hb hab hbθ hA
  have hreg := a1_symReg hD₁ hD₂ hD₃ hθ0 hA
  have hne : ∀ {X Y : Set V} {ιx ιy : Type} {fx : ιx → V} {fy : ιy → V}, Set.range fx = X →
      Set.range fy = Y → Disjoint X Y → ∀ x y, fx x ≠ fy y := by
    intro X Y ιx ιy fx fy hx hy hd x y h
    exact Set.disjoint_left.1 hd (hx ▸ Set.mem_range_self x) (h ▸ hy ▸ Set.mem_range_self y)
  have hv₁ : ∀ x, f₁ x ≠ v := fun x h => hv (Or.inl (Or.inl (h ▸ hr₁ ▸ Set.mem_range_self x)))
  have hv₂ : ∀ x, f₂ x ≠ v := fun x h => hv (Or.inl (Or.inr (h ▸ hr₂ ▸ Set.mem_range_self x)))
  have hv₃ : ∀ x, f₃ x ≠ v := fun x h => hv (Or.inr (h ▸ hr₃ ▸ Set.mem_range_self x))
  refine ⟨((ι₁ ⊕ ι₂) ⊕ ι₃) ⊕ Unit, inferInstance,
    Sum.elim (Sum.elim (Sum.elim f₁ f₂) f₃) (fun _ => v),
    C1 (swapC (sw 0) C₁) (swapC (sw 1) C₂) (swapC (sw 2) C₃), ?_, ?_, hS.nonneg, hS.reg, hS.norm,
    hS.wnorm, fun α t s ht hs => ?_⟩
  · refine ((hf₁.sumElim hf₂ (hne hr₁ hr₂ h12)).sumElim hf₃ ?_).sumElim
      (fun x y _ => Subsingleton.elim x y) ?_
    · rintro (x | x) y
      · exact hne hr₁ hr₃ h13 x y
      · exact hne hr₂ hr₃ h23 x y
    · rintro ((x | x) | x) u
      · exact hv₁ x
      · exact hv₂ x
      · exact hv₃ x
  · rw [Set.Sum.elim_range, Set.Sum.elim_range, Set.Sum.elim_range, hr₁, hr₂, hr₃,
      Set.range_const, Set.insert_eq, Set.union_comm]
  · rw [integral_C1_e2 hD₁.reg hD₂.reg hD₃.reg hreg _ ht hs]
    unfold type1F
    refine intervalIntegral.integral_congr fun t₁ ht₁ =>
      intervalIntegral.integral_congr fun s₁ hs₁ => ?_
    rw [uIcc_of_le ht.1] at ht₁
    rw [uIcc_of_le hs.1] at hs₁
    have ht₁' : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1, ht₁.2.trans ht.2⟩
    have hs₁' : s₁ ∈ Icc (0 : ℝ) 1 := ⟨hs₁.1, hs₁.2.trans hs.2⟩
    simp only [Fin.prod_univ_three]
    rw [swapT_rep he₁ (sw 0) α ht₁' hs₁', swapT_rep he₂ (sw 1) α ht₁' hs₁',
      swapT_rep he₃ (sw 2) α ht₁' hs₁']
    rfl

/-- **DH21 Prop 5.1, Case 1** (L1100–L1112): the expansion (maincoef3) of the type 1 recursion
(newexp1), with `Z = Z₁ ∪ Z₂ ∪ Z₃` (the root variable `v` is never in `Z`). -/
theorem MCExp.type1 {N₁ N₂ N₃ : ℝ} {ζ : V → ℤ} {S₁ S₂ S₃ : Finset V} {v : V}
    {F : Fin 3 → (V → ℝ) → ℝ → ℝ → ℂ} (h₁ : MCExp θ a b A N₁ ζ S₁ (F 0))
    (h₂ : MCExp θ a b A N₂ ζ S₂ (F 1)) (h₃ : MCExp θ a b A N₃ ζ S₃ (F 2))
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃) (h23 : Disjoint S₂ S₃)
    (hv : v ∉ S₁ ∪ S₂ ∪ S₃) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) (hbθ : b ≤ θ) (hA : A1 ≤ A) (sw : Fin 3 → Bool) :
    MCExp θ a b A (KC1 θ a b * (N₁ * N₂ * N₃)) ζ (insert v (S₁ ∪ S₂ ∪ S₃)) (type1F v sw F) := by
  obtain ⟨G₁, hG₁, hF₁⟩ := h₁
  obtain ⟨G₂, hG₂, hF₂⟩ := h₂
  obtain ⟨G₃, hG₃, hF₃⟩ := h₃
  have hN₁ := (hG₁ ∅ (Finset.empty_subset _)).nonneg
  have hN₂ := (hG₂ ∅ (Finset.empty_subset _)).nonneg
  have hN₃ := (hG₃ ∅ (Finset.empty_subset _)).nonneg
  have hN : 0 ≤ KC1 θ a b * (N₁ * N₂ * N₃) := mul_nonneg (KC1_nonneg _ _ _) (by positivity)
  have hd123 : Disjoint (S₁ ∪ S₂) S₃ := Finset.disjoint_union_left.2 ⟨h13, h23⟩
  let G : Finset V → (V → ℝ) → ℝ → ℝ → ℂ := fun Z =>
    if v ∈ Z then fun _ _ _ => 0 else type1F v sw ![G₁ (Z ∩ S₁), G₂ (Z ∩ S₂), G₃ (Z ∩ S₃)]
  refine ⟨G, fun Z hZ => ?_, fun α t s ht hs => ?_⟩
  · by_cases hvZ : v ∈ Z
    · simp only [G, hvZ, ↓reduceIte]
      exact MCRep.zero hN _
    · simp only [G, hvZ, ↓reduceIte]
      have hsd : ∀ {X Y : Finset V}, Disjoint X Y →
          Disjoint (↑(X \ (Z ∩ X)) : Set V) ↑(Y \ (Z ∩ Y)) := fun hXY =>
        Finset.disjoint_coe.2 (Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hXY))
      have hv' : v ∉ (↑(S₁ \ (Z ∩ S₁)) : Set V) ∪ ↑(S₂ \ (Z ∩ S₂)) ∪ ↑(S₃ \ (Z ∩ S₃)) := by
        intro h
        apply hv
        simp only [Set.mem_union, Finset.mem_coe, Finset.mem_sdiff] at h
        simp only [Finset.mem_union]
        tauto
      have key := MCRep.type1 (F := ![G₁ (Z ∩ S₁), G₂ (Z ∩ S₂), G₃ (Z ∩ S₃)])
        (hG₁ _ Finset.inter_subset_right) (hG₂ _ Finset.inter_subset_right)
        (hG₃ _ Finset.inter_subset_right) (hsd h12) (hsd h13) (hsd h23) hv' hθ0 hθ1 ha hb hab
        hbθ hA sw
      have hset : (↑(insert v (S₁ ∪ S₂ ∪ S₃) \ Z) : Set V) =
          insert v ((↑(S₁ \ (Z ∩ S₁)) : Set V) ∪ ↑(S₂ \ (Z ∩ S₂)) ∪ ↑(S₃ \ (Z ∩ S₃))) := by
        ext x
        by_cases hx : x = v
        · subst hx
          simp [hvZ]
        · simp only [Finset.coe_sdiff, Finset.coe_insert, Finset.coe_union, Finset.coe_inter,
            Set.mem_sdiff, Set.mem_insert_iff, Set.mem_union, Finset.mem_coe, Set.mem_inter_iff, hx,
            false_or]
          tauto
      rw [hset]
      exact key
  · -- continuous representatives of the subcouple coefficients
    have key : ∀ {Sx : Finset V} {Nx : ℝ} {Gx : Finset V → (V → ℝ) → ℝ → ℝ → ℂ},
        (∀ Z ⊆ Sx, MCRep θ a b A Nx ↑(Sx \ Z) (Gx Z)) → ∀ Z, ∃ R : ℝ → ℝ → ℂ,
          Continuous (fun p : ℝ × ℝ => R p.1 p.2) ∧ (Z ⊆ Sx → ∀ t s, t ∈ Icc (0 : ℝ) 1 →
            s ∈ Icc (0 : ℝ) 1 → Gx Z α t s = R t s) := by
      intro Sx Nx Gx hGx Z
      by_cases hZ : Z ⊆ Sx
      · obtain ⟨R, hRc, hRe⟩ := (hGx Z hZ).exists_continuous α
        exact ⟨R, hRc, fun _ => hRe⟩
      · exact ⟨fun _ _ => 0, continuous_const, fun h => absurd h hZ⟩
    have hR : ∀ (j : Fin 3) (Z : Finset V), ∃ R : ℝ → ℝ → ℂ,
        Continuous (fun p : ℝ × ℝ => R p.1 p.2) ∧ (Z ⊆ ![S₁, S₂, S₃] j → ∀ t s,
          t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → ![G₁, G₂, G₃] j Z α t s = R t s) := by
      intro j Z
      match j with
      | ⟨0, _⟩ => exact key hG₁ Z
      | ⟨1, _⟩ => exact key hG₂ Z
      | ⟨2, _⟩ => exact key hG₃ Z
    choose R hRc hRe using hR
    have hFj : ∀ (j : Fin 3) (t s : ℝ), t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        F j α t s = ∑ Z ∈ (![S₁, S₂, S₃] j).powerset,
          (∏ z ∈ Z, PhiZ ζ z (α z)) * ![G₁, G₂, G₃] j Z α t s := by
      intro j
      match j with
      | ⟨0, _⟩ => exact hF₁ α
      | ⟨1, _⟩ => exact hF₂ α
      | ⟨2, _⟩ => exact hF₃ α
    calc type1F v sw F α t s
        = type1F v sw (fun j _ t s => ∑ Z ∈ (![S₁, S₂, S₃] j).powerset,
            (∏ z ∈ Z, PhiZ ζ z (α z)) * R j Z t s) α t s := by
          refine type1F_congr α (fun j t s ht hs => ?_) v sw ht hs
          rw [hFj j t s ht hs]
          exact Finset.sum_congr rfl fun Z hZ => by
            rw [hRe j Z (Finset.mem_powerset.1 hZ) t s ht hs]
      _ = ∑ Z₁ ∈ S₁.powerset, ∑ Z₂ ∈ S₂.powerset, ∑ Z₃ ∈ S₃.powerset,
            (∏ z ∈ Z₁, PhiZ ζ z (α z)) * (∏ z ∈ Z₂, PhiZ ζ z (α z)) *
              (∏ z ∈ Z₃, PhiZ ζ z (α z)) *
              type1F v sw ![fun _ => R 0 Z₁, fun _ => R 1 Z₂, fun _ => R 2 Z₃] α t s :=
          type1F_expand α v sw (fun j => (![S₁, S₂, S₃] j).powerset)
            (fun _ Z => ∏ z ∈ Z, PhiZ ζ z (α z)) R hRc t s
      _ = ∑ Z₁ ∈ S₁.powerset, ∑ Z₂ ∈ S₂.powerset, ∑ Z₃ ∈ S₃.powerset,
            (∏ z ∈ Z₁ ∪ Z₂ ∪ Z₃, PhiZ ζ z (α z)) * G (Z₁ ∪ Z₂ ∪ Z₃) α t s := by
          refine Finset.sum_congr rfl fun Z₁ hZ₁ => Finset.sum_congr rfl fun Z₂ hZ₂ =>
            Finset.sum_congr rfl fun Z₃ hZ₃ => ?_
          rw [Finset.mem_powerset] at hZ₁ hZ₂ hZ₃
          have hvZ : v ∉ Z₁ ∪ Z₂ ∪ Z₃ := fun h =>
            hv (Finset.union_subset_union (Finset.union_subset_union hZ₁ hZ₂) hZ₃ h)
          simp only [G, hvZ, ↓reduceIte]
          rw [union3_inter_left h12 h13 hZ₁ hZ₂ hZ₃, union3_inter_mid h12 h23 hZ₁ hZ₂ hZ₃,
            union3_inter_right h13 h23 hZ₁ hZ₂ hZ₃,
            Finset.prod_union (Finset.disjoint_of_subset_left (Finset.union_subset_union hZ₁ hZ₂)
              (Finset.disjoint_of_subset_right hZ₃ hd123)),
            Finset.prod_union (Finset.disjoint_of_subset_left hZ₁
              (Finset.disjoint_of_subset_right hZ₂ h12))]
          congr 1
          refine type1F_congr α (fun j t s ht hs => ?_) v sw ht hs
          match j with
          | ⟨0, _⟩ => exact (hRe 0 Z₁ hZ₁ t s ht hs).symm
          | ⟨1, _⟩ => exact (hRe 1 Z₂ hZ₂ t s ht hs).symm
          | ⟨2, _⟩ => exact (hRe 2 Z₃ hZ₃ t s ht hs).symm
      _ = ∑ Z ∈ (S₁ ∪ S₂ ∪ S₃).powerset, (∏ z ∈ Z, PhiZ ζ z (α z)) * G Z α t s := by
          rw [sum_powerset_union_of_disjoint hd123, sum_powerset_union_of_disjoint h12]
      _ = ∑ Z ∈ (insert v (S₁ ∪ S₂ ∪ S₃)).powerset, (∏ z ∈ Z, PhiZ ζ z (α z)) * G Z α t s := by
          rw [Finset.sum_powerset_insert hv]
          have h0 : ∑ Z ∈ (S₁ ∪ S₂ ∪ S₃).powerset,
              (∏ z ∈ insert v Z, PhiZ ζ z (α z)) * G (insert v Z) α t s = 0 :=
            Finset.sum_eq_zero fun Z _ => by simp [G]
          rw [h0, add_zero]

end Type1Step

end WaveTurbulence.ClassJR
