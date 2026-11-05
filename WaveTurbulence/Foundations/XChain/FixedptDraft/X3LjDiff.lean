/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Lj

/-!
# X3: Lipschitz bounds for `ℒ₂`, `ℒ₃` (T L2337–L2338, the contraction)

`𝒞` is additive in each slot (`C3_sub_left`, `C3_sub_mid`, `C3_sub_right`). Hence

`𝒞(f,g,h) − 𝒞(f',g',h') = 𝒞(f−f', g, h) + 𝒞(f', g−g', h) + 𝒞(f', g', h−h')`,

and `norm_Lop_sub_le` bounds `ℒ₂ b − ℒ₂ b'` and `ℒ₃ b − ℒ₃ b'` by `‖b − b'‖_Z`.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set

variable (L γ δ : ℝ) {d : ℕ}

section Sub

variable (s : ℝ) (n : Fin d → ℤ) {f f' g g' h h' : (Fin d → ℤ) → ℂ}

theorem C3_two_sub (A B C : Fin 2 → (Fin d → ℤ) → ℂ) (hA : ∀ i, Summable fun m => ‖A i m‖)
    (hB : ∀ i, Summable fun m => ‖B i m‖) (hC : ∀ i, Summable fun m => ‖C i m‖) (u v w : Fin 2 → ℂ) :
    C3 L γ δ s (fun m => ∑ i, u i * A i m) (fun m => ∑ i, (starRingEnd ℂ) (v i) * B i m)
      (fun m => ∑ i, w i * C i m) n =
      ∑ i, ∑ j, ∑ k, u i * v j * w k * C3 L γ δ s (A i) (B j) (C k) n := by
  rw [C3_sum L γ δ s n Finset.univ Finset.univ Finset.univ (fun i m => u i * A i m)
    (fun j m => (starRingEnd ℂ) (v j) * B j m) (fun k m => w k * C k m)
    (fun i => by simpa [norm_mul] using (hA i).mul_left ‖u i‖)
    (fun j => by simpa [norm_mul] using (hB j).mul_left ‖v j‖)
    (fun k => by simpa [norm_mul] using (hC k).mul_left ‖w k‖)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  unfold C3
  rw [SysAPI.aNonlin_eq_tsum_aNonlinTerm, SysAPI.aNonlin_eq_tsum_aNonlinTerm]
  have hq : ∀ q, SysAPI.aNonlinTerm L γ δ 1 s (fun m => u i * A i m)
      (fun m => (starRingEnd ℂ) ((starRingEnd ℂ) (v j) * B j m)) (fun m => w k * C k m) n q =
      (u i * v j * w k) * SysAPI.aNonlinTerm L γ δ 1 s (A i) (fun m => (starRingEnd ℂ) (B j m)) (C k) n q := by
    intro q
    unfold SysAPI.aNonlinTerm
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [tsum_congr hq, tsum_mul_left]
  ring

theorem C3_sub_left (hf : Summable fun m => ‖f m‖) (hf' : Summable fun m => ‖f' m‖)
    (hg : Summable fun m => ‖g m‖) (hh : Summable fun m => ‖h m‖) :
    C3 L γ δ s (f - f') g h n = C3 L γ δ s f g h n - C3 L γ δ s f' g h n := by
  have := C3_two_sub L γ δ s n ![f, f'] ![g, g] ![h, h]
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
    ![1, -1] ![1, 0] ![1, 0]
  simp [Fin.sum_univ_two] at this
  convert this using 2

theorem C3_sub_mid (hf : Summable fun m => ‖f m‖) (hg : Summable fun m => ‖g m‖)
    (hg' : Summable fun m => ‖g' m‖) (hh : Summable fun m => ‖h m‖) :
    C3 L γ δ s f (g - g') h n = C3 L γ δ s f g h n - C3 L γ δ s f g' h n := by
  have := C3_two_sub L γ δ s n ![f, f] ![g, g'] ![h, h]
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
    ![1, 0] ![1, -1] ![1, 0]
  simp [Fin.sum_univ_two] at this
  convert this using 2

theorem C3_sub_right (hf : Summable fun m => ‖f m‖) (hg : Summable fun m => ‖g m‖)
    (hh : Summable fun m => ‖h m‖) (hh' : Summable fun m => ‖h' m‖) :
    C3 L γ δ s f g (h - h') n = C3 L γ δ s f g h n - C3 L γ δ s f g h' n := by
  have := C3_two_sub L γ δ s n ![f, f] ![g, g] ![h, h']
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
    ![1, 0] ![1, 0] ![1, -1]
  simp [Fin.sum_univ_two] at this
  convert this using 2

end Sub

/-! ## Lipschitz bounds for `ℒ₂`, `ℒ₃` -/

section LjSub

variable {p : ℕ} (Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
  {Λ : ℝ} {b b' : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ} (hb : b ∈ ZSpace L Λ p) (hb' : b' ∈ ZSpace L Λ p)
  (hΛ : (d : ℝ) + 1 ≤ Λ)

theorem slotV_none_sub (s : ℝ) :
    slotV L γ δ p Ntr aP b s none - slotV L γ δ p Ntr aP b' s none = slotV L γ δ p Ntr aP (b - b') s none := by
  funext k
  show Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k - Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b' s k =
    Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) (b - b') s k
  simp only [Set.IccExtend_apply, Pi.sub_apply]

theorem slotA_slotV_eq (s : ℝ) :
    slotA (slotV L γ δ p Ntr aP b' s) = slotA (slotV L γ δ p Ntr aP b s) := by
  rw [slotA_slotV, slotA_slotV]

theorem summable_slotA {V : Slot Ntr → (Fin d → ℤ) → ℂ} (hV : ∀ o, Summable fun m => ‖V o m‖) :
    Summable fun m => ‖slotA V m‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sum_le _ _)
    (summable_sum fun N _ => hV (some N))

include haP hΛ in
theorem intervalIntegrable_slotSum (hL : 0 < L) {c : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ}
    (hc : c ∈ ZSpace L Λ p) (j : ℕ) (t : ℝ) (n : Fin d → ℤ) :
    IntervalIntegrable (fun s => ∑ x ∈ (Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
        (fun x => slotCountB x = j ∧ (j = 0 → Ntr ≤ slotOrder x)),
        C3 L γ δ s (slotV L γ δ p Ntr aP c s x.1) (slotV L γ δ p Ntr aP c s x.2.1)
          (slotV L γ δ p Ntr aP c s x.2.2) n) volume (p : ℝ) t := by
  have h := IntervalIntegrable.sum (μ := volume) (a := (p : ℝ)) (b := t)
    ((Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
      (fun x => slotCountB x = j ∧ (j = 0 → Ntr ≤ slotOrder x)))
    (f := fun x s => C3 L γ δ s (slotV L γ δ p Ntr aP c s x.1) (slotV L γ δ p Ntr aP c s x.2.1)
      (slotV L γ δ p Ntr aP c s x.2.2) n)
    fun x _ => intervalIntegrable_slotTriple L γ δ hL Ntr haP hc hΛ x t n
  rwa [Finset.sum_fn] at h

include haP hb hb' hΛ in
/-- **Lipschitz bounds for `ℒ₂`, `ℒ₃`** in the weight `w` (T L2337–L2338). Here `β = ‖b‖_Z`, `β' = ‖b'‖_Z`,
`η = ‖b − b'‖_Z`, and `α` bounds `a^tr` on `[p, p+1]`. -/
theorem norm_Lop_sub_le (hL1 : 1 ≤ L) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : ∀ s ∈ Icc (p : ℝ) (p + 1), ∀ k, ‖aTr L γ δ p Ntr aP s k‖ ≤ α * wt L Λ k)
    {t : ℝ} (ht : t ∈ Icc (p : ℝ) (p + 1)) (n : Fin d → ℤ) :
    ‖Lop L γ δ p Ntr aP 2 b t n - Lop L γ δ p Ntr aP 2 b' t n‖ ≤
      3 * (triK d L γ δ Λ * (((ZNorm L Λ b).toReal + (ZNorm L Λ b').toReal) * α *
        (ZNorm L Λ (b - b')).toReal)) * wt L Λ n ∧
    ‖Lop L γ δ p Ntr aP 3 b t n - Lop L γ δ p Ntr aP 3 b' t n‖ ≤
      triK d L γ δ Λ * (((ZNorm L Λ b).toReal ^ 2 + (ZNorm L Λ b).toReal * (ZNorm L Λ b').toReal +
        (ZNorm L Λ b').toReal ^ 2) * (ZNorm L Λ (b - b')).toReal) * wt L Λ n := by
  have hL : 0 < L := by linarith
  set β := (ZNorm L Λ b).toReal
  set β' := (ZNorm L Λ b').toReal
  set η := (ZNorm L Λ (b - b')).toReal
  have hβ : 0 ≤ β := ENNReal.toReal_nonneg
  have hβ' : 0 ≤ β' := ENNReal.toReal_nonneg
  have hη : 0 ≤ η := ENNReal.toReal_nonneg
  have hK := triK_nonneg (d := d) (L := L) (γ := γ) (δ := δ) (Λ := Λ)
  have hw := (wt_pos L Λ n).le
  have hbb' := zSpace_sub hb hb'
  have hV := summable_slotV L γ δ Ntr haP hb hΛ hL
  have hV' := summable_slotV L γ δ Ntr haP hb' hΛ hL
  have hsub : ∀ s ∈ Icc (p : ℝ) t, s ∈ Icc (p : ℝ) (p + 1) := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hpt : ∀ s ∈ Icc (p : ℝ) (p + 1),
      (∀ k, ‖slotV L γ δ p Ntr aP b s none k‖ ≤ β * wt L Λ k) ∧
      (∀ k, ‖slotV L γ δ p Ntr aP b' s none k‖ ≤ β' * wt L Λ k) ∧
      (∀ k, ‖(slotV L γ δ p Ntr aP b s none - slotV L γ δ p Ntr aP b' s none) k‖ ≤ η * wt L Λ k) ∧
      (∀ k, ‖slotA (slotV L γ δ p Ntr aP b s) k‖ ≤ α * wt L Λ k) := by
    intro s hs
    obtain ⟨hB, hA⟩ := slotV_bounds L γ δ Ntr hb hα hs
    obtain ⟨hB', -⟩ := slotV_bounds L γ δ Ntr hb' hα hs
    obtain ⟨hD, -⟩ := slotV_bounds L γ δ Ntr hbb' hα hs
    exact ⟨hB, hB', fun k => by rw [slotV_none_sub]; exact hD k, hA⟩
  refine ⟨?_, ?_⟩
  · rw [Lop_eq_integral L γ δ Ntr haP hb hΛ hL, Lop_eq_integral L γ δ Ntr haP hb' hΛ hL,
      ← intervalIntegral.integral_sub (intervalIntegrable_slotSum L γ δ Ntr haP hΛ hL hb 2 t n)
        (intervalIntegrable_slotSum L γ δ Ntr haP hΛ hL hb' 2 t n)]
    simp_rw [slotSum_two L γ δ _ n _ (hV _), slotSum_two L γ δ _ n _ (hV' _),
      slotA_slotV_eq L γ δ Ntr (b := b) (b' := b')]
    refine norm_integral_le_unit ht (by positivity) fun s hs => ?_
    obtain ⟨hB, hB', hD, hA⟩ := hpt s (hsub s hs)
    have sB := hV s none
    have sB' := hV' s none
    have sA := summable_slotA Ntr (hV s)
    set B := slotV L γ δ p Ntr aP b s none
    set B' := slotV L γ δ p Ntr aP b' s none
    set A := slotA (slotV L γ δ p Ntr aP b s)
    have sD : Summable fun m => ‖(B - B') m‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => norm_sub_le _ _) (sB.add sB')
    have e1 : C3 L γ δ s B B A n - C3 L γ δ s B' B' A n =
        C3 L γ δ s (B - B') B A n + C3 L γ δ s B' (B - B') A n := by
      rw [C3_sub_left L γ δ s n sB sB' sB sA, C3_sub_mid L γ δ s n sB' sB sB' sA]; ring
    have e2 : C3 L γ δ s B A B n - C3 L γ δ s B' A B' n =
        C3 L γ δ s (B - B') A B n + C3 L γ δ s B' A (B - B') n := by
      rw [C3_sub_left L γ δ s n sB sB' sA sB, C3_sub_right L γ δ s n sB' sA sB sB']; ring
    have e3 : C3 L γ δ s A B B n - C3 L γ δ s A B' B' n =
        C3 L γ δ s A (B - B') B n + C3 L γ δ s A B' (B - B') n := by
      rw [C3_sub_mid L γ δ s n sA sB sB' sB, C3_sub_right L γ δ s n sA sB' sB sB']; ring
    have hsplit : C3 L γ δ s B B A n + C3 L γ δ s B A B n + C3 L γ δ s A B B n -
        (C3 L γ δ s B' B' A n + C3 L γ δ s B' A B' n + C3 L γ δ s A B' B' n) =
        (C3 L γ δ s (B - B') B A n + C3 L γ δ s B' (B - B') A n) +
        (C3 L γ δ s (B - B') A B n + C3 L γ δ s B' A (B - B') n) +
        (C3 L γ δ s A (B - B') B n + C3 L γ δ s A B' (B - B') n) := by
      rw [← e1, ← e2, ← e3]; ring
    rw [hsplit]
    have h1 := norm_C3_le L γ δ hΛ hL1 s hη hβ hα0 hD hB hA n
    have h2 := norm_C3_le L γ δ hΛ hL1 s hβ' hη hα0 hB' hD hA n
    have h3 := norm_C3_le L γ δ hΛ hL1 s hη hα0 hβ hD hA hB n
    have h4 := norm_C3_le L γ δ hΛ hL1 s hβ' hα0 hη hB' hA hD n
    have h5 := norm_C3_le L γ δ hΛ hL1 s hα0 hη hβ hA hD hB n
    have h6 := norm_C3_le L γ δ hΛ hL1 s hα0 hβ' hη hA hB' hD n
    refine (norm_add₃_le).trans ?_
    have n1 := norm_add_le (C3 L γ δ s (B - B') B A n) (C3 L γ δ s B' (B - B') A n)
    have n2 := norm_add_le (C3 L γ δ s (B - B') A B n) (C3 L γ δ s B' A (B - B') n)
    have n3 := norm_add_le (C3 L γ δ s A (B - B') B n) (C3 L γ δ s A B' (B - B') n)
    linarith
  · rw [Lop_eq_integral L γ δ Ntr haP hb hΛ hL, Lop_eq_integral L γ δ Ntr haP hb' hΛ hL,
      ← intervalIntegral.integral_sub (intervalIntegrable_slotSum L γ δ Ntr haP hΛ hL hb 3 t n)
        (intervalIntegrable_slotSum L γ δ Ntr haP hΛ hL hb' 3 t n)]
    simp_rw [slotSum_three L γ δ _ n]
    refine norm_integral_le_unit ht (by positivity) fun s hs => ?_
    obtain ⟨hB, hB', hD, -⟩ := hpt s (hsub s hs)
    have sB := hV s none
    have sB' := hV' s none
    set B := slotV L γ δ p Ntr aP b s none
    set B' := slotV L γ δ p Ntr aP b' s none
    have hsplit : C3 L γ δ s B B B n - C3 L γ δ s B' B' B' n =
        C3 L γ δ s (B - B') B B n + C3 L γ δ s B' (B - B') B n + C3 L γ δ s B' B' (B - B') n := by
      rw [C3_sub_left L γ δ s n sB sB' sB sB, C3_sub_mid L γ δ s n sB' sB sB' sB,
        C3_sub_right L γ δ s n sB' sB' sB sB']; ring
    rw [hsplit]
    have h1 := norm_C3_le L γ δ hΛ hL1 s hη hβ hβ hD hB hB n
    have h2 := norm_C3_le L γ δ hΛ hL1 s hβ' hη hβ hB' hD hB n
    have h3 := norm_C3_le L γ δ hΛ hL1 s hβ' hβ' hη hB' hB' hD n
    refine (norm_add₃_le).trans ?_
    linarith

end LjSub

end WaveTurbulence.Fixedpt
