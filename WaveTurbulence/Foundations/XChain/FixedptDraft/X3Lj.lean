/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Trilinear
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3DerivCpl

/-!
# X3: `ℒ₁`, `ℒ₂`, `ℒ₃` through `a^tr` (T (eqnbk1.5), L2337–L2338)

The slots of `ℒ_j` range over `{b, 𝒥₀, …, 𝒥_{N_{p+1}}}`, and the `𝒥`-slots add up to `a^tr` (`slotSum_one`,
`slotSum_two`, `slotSum_three`, by multilinearity `aNonlin_sum`). With `a = a^tr` and `𝒞(f,g,h) = 𝒞₊(f, ḡ, h)`:
- `ℒ₁ b = ∫ 𝒞(b,a,a) + 𝒞(a,b,a) + 𝒞(a,a,b)`;
- `ℒ₂ b = ∫ 𝒞(b,b,a) + 𝒞(b,a,b) + 𝒞(a,b,b)`;
- `ℒ₃ b = ∫ 𝒞(b,b,b)`.

The `w`-weighted bounds follow from `norm_aNonlin_le_weight`.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set

variable (L γ δ : ℝ) {d : ℕ}

/-- `𝒞(f, g, h)_n = 𝒞₊(f, ḡ, h)_n` at time `s`. -/
noncomputable def C3 (s : ℝ) (f g h : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  aNonlin L γ δ 1 s f (fun m => (starRingEnd ℂ) (g m)) h n

section Fold

variable (s : ℝ) (n : Fin d → ℤ)

theorem C3_sum {ι₁ ι₂ ι₃ : Type*} (A : Finset ι₁) (B : Finset ι₂) (C : Finset ι₃) (f : ι₁ → (Fin d → ℤ) → ℂ)
    (g : ι₂ → (Fin d → ℤ) → ℂ) (h : ι₃ → (Fin d → ℤ) → ℂ) (hf : ∀ i, Summable fun m => ‖f i m‖)
    (hg : ∀ i, Summable fun m => ‖g i m‖) (hh : ∀ i, Summable fun m => ‖h i m‖) :
    C3 L γ δ s (fun m => ∑ i ∈ A, f i m) (fun m => ∑ i ∈ B, g i m) (fun m => ∑ i ∈ C, h i m) n =
      ∑ i ∈ A, ∑ j ∈ B, ∑ k ∈ C, C3 L γ δ s (f i) (g j) (h k) n := by
  unfold C3
  simp only [map_sum]
  exact SysAPI.aNonlin_sum L γ δ 1 s A B C f (fun j m => (starRingEnd ℂ) (g j m)) h hf
    (fun j => by simpa using hg j) hh n

end Fold

/-! ## Regrouping the slot sums -/

section Slots

variable {Ntr : ℕ} (s : ℝ) (n : Fin d → ℤ) (V : Slot Ntr → (Fin d → ℤ) → ℂ)
  (hV : ∀ o, Summable fun m => ‖V o m‖)

/-- The `𝒥`-slots added up. -/
noncomputable def slotA (V : Slot Ntr → (Fin d → ℤ) → ℂ) : (Fin d → ℤ) → ℂ := fun m => ∑ N : Fin (Ntr + 1), V (some N) m

include hV in
theorem C3_some_some (f : (Fin d → ℤ) → ℂ) (hf : Summable fun m => ‖f m‖) :
    (∑ x, ∑ y, C3 L γ δ s f (V (some x)) (V (some y)) n) = C3 L γ δ s f (slotA V) (slotA V) n ∧
    (∑ x, ∑ y, C3 L γ δ s (V (some x)) f (V (some y)) n) = C3 L γ δ s (slotA V) f (slotA V) n ∧
    (∑ x, ∑ y, C3 L γ δ s (V (some x)) (V (some y)) f n) = C3 L γ δ s (slotA V) (slotA V) f n := by
  refine ⟨?_, ?_, ?_⟩
  · calc ∑ x, ∑ y, C3 L γ δ s f (V (some x)) (V (some y)) n
        = ∑ _u ∈ (Finset.univ : Finset Unit), ∑ x, ∑ y, C3 L γ δ s f (V (some x)) (V (some y)) n := by simp
      _ = C3 L γ δ s (fun m => ∑ _u ∈ (Finset.univ : Finset Unit), f m) (fun m => ∑ N, V (some N) m)
            (fun m => ∑ N, V (some N) m) n :=
          (C3_sum L γ δ s n _ _ _ (fun _ => f) (fun N => V (some N)) (fun N => V (some N)) (fun _ => hf)
            (fun _ => hV _) (fun _ => hV _)).symm
      _ = C3 L γ δ s f (slotA V) (slotA V) n := by simp only [Finset.univ_unique, Finset.sum_singleton]; rfl
  · calc ∑ x, ∑ y, C3 L γ δ s (V (some x)) f (V (some y)) n
        = ∑ x, ∑ _u ∈ (Finset.univ : Finset Unit), ∑ y, C3 L γ δ s (V (some x)) f (V (some y)) n := by simp
      _ = C3 L γ δ s (fun m => ∑ N, V (some N) m) (fun m => ∑ _u ∈ (Finset.univ : Finset Unit), f m)
            (fun m => ∑ N, V (some N) m) n :=
          (C3_sum L γ δ s n _ _ _ (fun N => V (some N)) (fun _ => f) (fun N => V (some N)) (fun _ => hV _)
            (fun _ => hf) (fun _ => hV _)).symm
      _ = C3 L γ δ s (slotA V) f (slotA V) n := by simp only [Finset.univ_unique, Finset.sum_singleton]; rfl
  · calc ∑ x, ∑ y, C3 L γ δ s (V (some x)) (V (some y)) f n
        = ∑ x, ∑ y, ∑ _u ∈ (Finset.univ : Finset Unit), C3 L γ δ s (V (some x)) (V (some y)) f n := by simp
      _ = C3 L γ δ s (fun m => ∑ N, V (some N) m) (fun m => ∑ N, V (some N) m)
            (fun m => ∑ _u ∈ (Finset.univ : Finset Unit), f m) n :=
          (C3_sum L γ δ s n _ _ _ (fun N => V (some N)) (fun N => V (some N)) (fun _ => f) (fun _ => hV _)
            (fun _ => hV _) (fun _ => hf)).symm
      _ = C3 L γ δ s (slotA V) (slotA V) f n := by simp only [Finset.univ_unique, Finset.sum_singleton]; rfl

include hV in
theorem C3_some (f g : (Fin d → ℤ) → ℂ) (hf : Summable fun m => ‖f m‖) (hg : Summable fun m => ‖g m‖) :
    (∑ x, C3 L γ δ s f g (V (some x)) n) = C3 L γ δ s f g (slotA V) n ∧
    (∑ x, C3 L γ δ s f (V (some x)) g n) = C3 L γ δ s f (slotA V) g n ∧
    (∑ x, C3 L γ δ s (V (some x)) f g n) = C3 L γ δ s (slotA V) f g n := by
  refine ⟨?_, ?_, ?_⟩
  · calc ∑ x, C3 L γ δ s f g (V (some x)) n
        = ∑ _u ∈ (Finset.univ : Finset Unit), ∑ _v ∈ (Finset.univ : Finset Unit), ∑ x,
            C3 L γ δ s f g (V (some x)) n := by simp
      _ = C3 L γ δ s (fun m => ∑ _u ∈ (Finset.univ : Finset Unit), f m)
            (fun m => ∑ _v ∈ (Finset.univ : Finset Unit), g m) (fun m => ∑ N, V (some N) m) n :=
          (C3_sum L γ δ s n _ _ _ (fun _ => f) (fun _ => g) (fun N => V (some N)) (fun _ => hf) (fun _ => hg)
            (fun _ => hV _)).symm
      _ = C3 L γ δ s f g (slotA V) n := by simp only [Finset.univ_unique, Finset.sum_singleton]; rfl
  · calc ∑ x, C3 L γ δ s f (V (some x)) g n
        = ∑ _u ∈ (Finset.univ : Finset Unit), ∑ x, ∑ _v ∈ (Finset.univ : Finset Unit),
            C3 L γ δ s f (V (some x)) g n := by simp
      _ = C3 L γ δ s (fun m => ∑ _u ∈ (Finset.univ : Finset Unit), f m) (fun m => ∑ N, V (some N) m)
            (fun m => ∑ _v ∈ (Finset.univ : Finset Unit), g m) n :=
          (C3_sum L γ δ s n _ _ _ (fun _ => f) (fun N => V (some N)) (fun _ => g) (fun _ => hf) (fun _ => hV _)
            (fun _ => hg)).symm
      _ = C3 L γ δ s f (slotA V) g n := by simp only [Finset.univ_unique, Finset.sum_singleton]; rfl
  · calc ∑ x, C3 L γ δ s (V (some x)) f g n
        = ∑ x, ∑ _u ∈ (Finset.univ : Finset Unit), ∑ _v ∈ (Finset.univ : Finset Unit),
            C3 L γ δ s (V (some x)) f g n := by simp
      _ = C3 L γ δ s (fun m => ∑ N, V (some N) m) (fun m => ∑ _u ∈ (Finset.univ : Finset Unit), f m)
            (fun m => ∑ _v ∈ (Finset.univ : Finset Unit), g m) n :=
          (C3_sum L γ δ s n _ _ _ (fun N => V (some N)) (fun _ => f) (fun _ => g) (fun _ => hV _) (fun _ => hf)
            (fun _ => hg)).symm
      _ = C3 L γ δ s (slotA V) f g n := by simp only [Finset.univ_unique, Finset.sum_singleton]; rfl

include hV in
theorem slotSum_one :
    ∑ x ∈ (Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
      (fun x => slotCountB x = 1 ∧ (1 = 0 → Ntr ≤ slotOrder x)), C3 L γ δ s (V x.1) (V x.2.1) (V x.2.2) n =
    C3 L γ δ s (V none) (slotA V) (slotA V) n + C3 L γ δ s (slotA V) (V none) (slotA V) n +
      C3 L γ δ s (slotA V) (slotA V) (V none) n := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_option]
  simp [slotCountB]
  obtain ⟨h1, h2, h3⟩ := C3_some_some L γ δ s n V hV (V none) (hV none)
  rw [h1, Finset.sum_add_distrib, h2, h3]
  ring

include hV in
theorem slotSum_two :
    ∑ x ∈ (Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
      (fun x => slotCountB x = 2 ∧ (2 = 0 → Ntr ≤ slotOrder x)), C3 L γ δ s (V x.1) (V x.2.1) (V x.2.2) n =
    C3 L γ δ s (V none) (V none) (slotA V) n + C3 L γ δ s (V none) (slotA V) (V none) n +
      C3 L γ δ s (slotA V) (V none) (V none) n := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_option]
  simp [slotCountB]
  obtain ⟨h1, h2, h3⟩ := C3_some L γ δ s n V hV (V none) (V none) (hV none) (hV none)
  rw [h1, h2, h3]

theorem slotSum_three :
    ∑ x ∈ (Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
      (fun x => slotCountB x = 3 ∧ (3 = 0 → Ntr ≤ slotOrder x)), C3 L γ δ s (V x.1) (V x.2.1) (V x.2.2) n =
    C3 L γ δ s (V none) (V none) (V none) n := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_option]
  simp [slotCountB]

end Slots

/-! ## `ℒ_j` as integrals of trilinear terms -/

section Lj

variable {p : ℕ} (Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
  {Λ : ℝ} {b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ} (hb : b ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ)

/-- The slot values at time `s`. -/
noncomputable def slotV (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (s : ℝ) :
    Slot Ntr → (Fin d → ℤ) → ℂ := fun o => SysAPI.slotVal L γ δ p Ntr aP b o s

include haP hb hΛ in
theorem summable_slotV (hL : 0 < L) (s : ℝ) (o : Slot Ntr) :
    Summable fun m => ‖slotV L γ δ p Ntr aP b s o m‖ := by
  cases o with
  | none =>
    show Summable fun m => ‖Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m‖
    simp only [Set.IccExtend_apply]
    exact zSpace_summable hL hb hΛ _
  | some N => exact SysAPI.summable_norm_treeTermN L γ δ p N haP s

theorem slotA_slotV (s : ℝ) :
    slotA (slotV L γ δ p Ntr aP b s) = fun m => aTr L γ δ p Ntr aP s m := by
  funext m
  unfold slotA slotV aTr
  rw [Finset.sum_range (fun N => treeTermN L γ δ p N aP s m)]
  rfl

include haP hb hΛ in
/-- **`ℒ_j b = ∫_p^t ∑_{slots} 𝒞`**, with the `𝒥`-slots regrouped into `a^tr` by the caller (`slotSum_*`). -/
theorem Lop_eq_integral (hL : 0 < L) (j : ℕ) (t : ℝ) (n : Fin d → ℤ) :
    Lop L γ δ p Ntr aP j b t n = ∫ s in (p : ℝ)..t,
      ∑ x ∈ (Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
        (fun x => slotCountB x = j ∧ (j = 0 → Ntr ≤ slotOrder x)),
        C3 L γ δ s (slotV L γ δ p Ntr aP b s x.1) (slotV L γ δ p Ntr aP b s x.2.1) (slotV L γ δ p Ntr aP b s x.2.2) n := by
  rw [SysAPI.Lop_eq_sum, intervalIntegral.integral_finsetSum (f := fun (x : Slot Ntr × Slot Ntr × Slot Ntr) (s : ℝ) =>
    C3 L γ δ s (slotV L γ δ p Ntr aP b s x.1) (slotV L γ δ p Ntr aP b s x.2.1) (slotV L γ δ p Ntr aP b s x.2.2) n)
    fun x _ => intervalIntegrable_slotTriple L γ δ hL Ntr haP hb hΛ x t n]
  rfl

/-- `‖∫_p^t F‖ ≤ M` if `‖F‖ ≤ M` on `[p, t]` and `t ≤ p + 1`. -/
theorem norm_integral_le_unit {F : ℝ → ℂ} {M : ℝ} {t : ℝ} (ht : t ∈ Icc (p : ℝ) (p + 1)) (hM : 0 ≤ M)
    (hF : ∀ s ∈ Icc (p : ℝ) t, ‖F s‖ ≤ M) : ‖∫ s in (p : ℝ)..t, F s‖ ≤ M := by
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun s hs => ?_).trans ?_
  · exact hF s ⟨by rw [Set.uIoc_of_le ht.1] at hs; exact hs.1.le, by rw [Set.uIoc_of_le ht.1] at hs; exact hs.2⟩
  · rw [abs_of_nonneg (by linarith [ht.1])]
    nlinarith [ht.2]

/-- The constant of the trilinear bound: `|δ/(2L^{d−γ})| · 3^{Λ+1} T²`. -/
noncomputable def triK (d : ℕ) (L γ δ Λ : ℝ) : ℝ := |δ / (2 * L ^ ((d : ℝ) - γ))| * (3 ^ (Λ + 1) * latSum d L ^ 2)

theorem triK_nonneg : 0 ≤ triK d L γ δ Λ := by
  have hT : 0 ≤ latSum d L := tsum_nonneg fun _ => Real.rpow_nonneg (jbr_pos'' _).le _
  unfold triK; positivity

include hΛ in
theorem norm_C3_le (hL1 : 1 ≤ L) (s : ℝ) {f g h : (Fin d → ℤ) → ℂ} {F G H : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hH : 0 ≤ H) (hf : ∀ k, ‖f k‖ ≤ F * wt L Λ k) (hg : ∀ k, ‖g k‖ ≤ G * wt L Λ k)
    (hh : ∀ k, ‖h k‖ ≤ H * wt L Λ k) (n : Fin d → ℤ) :
    ‖C3 L γ δ s f g h n‖ ≤ triK d L γ δ Λ * (F * G * H) * wt L Λ n := by
  have := norm_aNonlin_le_weight L γ δ hL1 hΛ s hF hG hH hf (g := fun m => (starRingEnd ℂ) (g m))
    (fun k => by rw [Complex.norm_conj]; exact hg k) hh n
  unfold C3 triK
  calc _ ≤ _ := this
    _ = _ := by ring

include hb in
theorem slotV_bounds {α : ℝ}
    (hα : ∀ s ∈ Icc (p : ℝ) (p + 1), ∀ k, ‖aTr L γ δ p Ntr aP s k‖ ≤ α * wt L Λ k)
    {s : ℝ} (hs : s ∈ Icc (p : ℝ) (p + 1)) :
    (∀ k, ‖slotV L γ δ p Ntr aP b s none k‖ ≤ (ZNorm L Λ b).toReal * wt L Λ k) ∧
    (∀ k, ‖slotA (slotV L γ δ p Ntr aP b s) k‖ ≤ α * wt L Λ k) := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · show ‖Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k‖ ≤ _
    rw [Set.IccExtend_apply]
    exact (norm_le_of_mem_ZSpace hb _ k).trans (le_of_eq (mul_comm _ _))
  · rw [slotA_slotV]
    exact hα s hs k

include haP hb hΛ in
/-- **`|ℒ_j b|` in the weight `w`**, `j = 1, 2, 3`. Here `β = ‖b‖_Z` and `α` bounds `a^tr` on `[p, p+1]`. -/
theorem norm_Lop_le (hL1 : 1 ≤ L) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : ∀ s ∈ Icc (p : ℝ) (p + 1), ∀ k, ‖aTr L γ δ p Ntr aP s k‖ ≤ α * wt L Λ k)
    {t : ℝ} (ht : t ∈ Icc (p : ℝ) (p + 1)) (n : Fin d → ℤ) :
    ‖Lop L γ δ p Ntr aP 1 b t n‖ ≤ 3 * (triK d L γ δ Λ * ((ZNorm L Λ b).toReal * α * α)) * wt L Λ n ∧
    ‖Lop L γ δ p Ntr aP 2 b t n‖ ≤
      3 * (triK d L γ δ Λ * ((ZNorm L Λ b).toReal * (ZNorm L Λ b).toReal * α)) * wt L Λ n ∧
    ‖Lop L γ δ p Ntr aP 3 b t n‖ ≤
      triK d L γ δ Λ * ((ZNorm L Λ b).toReal * (ZNorm L Λ b).toReal * (ZNorm L Λ b).toReal) * wt L Λ n := by
  have hL : 0 < L := by linarith
  set β := (ZNorm L Λ b).toReal
  have hβ : 0 ≤ β := ENNReal.toReal_nonneg
  have hK := triK_nonneg (d := d) (L := L) (γ := γ) (δ := δ) (Λ := Λ)
  have hw := (wt_pos L Λ n).le
  have hV := summable_slotV L γ δ Ntr haP hb hΛ hL
  have hsub : ∀ s ∈ Icc (p : ℝ) t, s ∈ Icc (p : ℝ) (p + 1) := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Lop_eq_integral L γ δ Ntr haP hb hΛ hL]
    simp_rw [slotSum_one L γ δ _ n _ (hV _)]
    refine norm_integral_le_unit ht (by positivity) fun s hs => ?_
    obtain ⟨hB, hA⟩ := slotV_bounds L γ δ Ntr hb hα (hsub s hs)
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have h1 := norm_C3_le L γ δ hΛ hL1 s hβ hα0 hα0 hB hA hA n
    have h2 := norm_C3_le L γ δ hΛ hL1 s hα0 hβ hα0 hA hB hA n
    have h3 := norm_C3_le L γ δ hΛ hL1 s hα0 hα0 hβ hA hA hB n
    nlinarith [h1, h2, h3]
  · rw [Lop_eq_integral L γ δ Ntr haP hb hΛ hL]
    simp_rw [slotSum_two L γ δ _ n _ (hV _)]
    refine norm_integral_le_unit ht (by positivity) fun s hs => ?_
    obtain ⟨hB, hA⟩ := slotV_bounds L γ δ Ntr hb hα (hsub s hs)
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have h1 := norm_C3_le L γ δ hΛ hL1 s hβ hβ hα0 hB hB hA n
    have h2 := norm_C3_le L γ δ hΛ hL1 s hβ hα0 hβ hB hA hB n
    have h3 := norm_C3_le L γ δ hΛ hL1 s hα0 hβ hβ hA hB hB n
    nlinarith [h1, h2, h3]
  · rw [Lop_eq_integral L γ δ Ntr haP hb hΛ hL]
    simp_rw [slotSum_three L γ δ _ n]
    refine norm_integral_le_unit ht (by positivity) fun s hs => ?_
    obtain ⟨hB, -⟩ := slotV_bounds L γ δ Ntr hb hα (hsub s hs)
    exact norm_C3_le L γ δ hΛ hL1 s hβ hβ hβ hB hB hB n

end Lj

end WaveTurbulence.Fixedpt
