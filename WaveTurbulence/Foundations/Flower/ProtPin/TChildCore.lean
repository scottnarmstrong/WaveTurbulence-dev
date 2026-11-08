/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFlat
public import WaveTurbulence.Foundations.Flower.ProtPin.TermCore

/-! # D3 PROT-PIN (P7): the terminal cut with a root-traced side couple

`tc_core`: `term_core` when one side-couple factor is a function `V_e(u)` of the partner clock alone (the root trace of
that couple at the fixed `s`), lifted by `rn_lift`. `tc_cupR_trace`: in (P7) the traced couple's clocks are `s` on the
traced tree and `u` on the other. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **The terminal cut with one factor depending on the partner clock only.** -/
theorem tc_core {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p s q' : ℝ), p < s → s < p + 1 →
      ∀ (A : ι → ℝ) (c : ι → ℂ) (Kp : (Fin 2 → ℝ) → ℂ) (Ki Kq : ι → (Fin 2 → ℝ) → ℂ) (V : ι → ℝ → ℂ),
      Continuous Kp → (∀ i, Continuous (Ki i)) → (∀ i, Continuous (Kq i)) → (∀ i, Continuous (V i)) →
      rn θ (timeBoxGt p p) Kp < ⊤ → (∀ i, rn θ (timeBoxGt p p) (Ki i) < ⊤) →
      (∀ i, rn θ (timeBoxGt p p) (Kq i) < ⊤) → (∀ i, rn θ (win p) (fun y => V i (y 0)) < ⊤) →
      rn θ (timeBoxGt p q') (fun ts => ∑' i, c i * ∫ u in Ioo s (ts 0),
          cutMod (A i) s u * (Kp ![ts 0, u] * (Ki i ![u, s] * (Kq i ![u, s] * V i u)))) ≤
        C * ∑' i, ‖c i‖ₑ * (rn θ (timeBoxGt p p) Kp * (rn θ (timeBoxGt p p) (Ki i) *
          (rn θ (timeBoxGt p p) (Kq i) * rn θ (win p) (fun y => V i (y 0))))) := by
  obtain ⟨Cc, hCc, hcore⟩ := term_core hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨Cc * (T4 * cutNorm θ), ENNReal.mul_lt_top hCc (ENNReal.mul_lt_top hT4f (cutNorm_lt_top θ)), ?_⟩
  intro ι _ p s q' hps hsp A c Kp Ki Kq V hKp hKi hKq hV hfp hfi hfq hfv
  set Vl : ι → (Fin 2 → ℝ) → ℂ := fun i x => V i (x 0) with hVl
  have hVlc : ∀ i, Continuous (Vl i) := fun i => (hV i).comp (continuous_apply 0)
  have hVlb : ∀ i, rn θ (timeBoxGt p p) (Vl i) ≤ cutNorm θ * rn θ (win p) (fun y => V i (y 0)) := fun i =>
    rn_lift hθ0 p p (fun y => V i (y 0))
  have hfl : ∀ i, rn θ (timeBoxGt p p) (Vl i) < ⊤ := fun i =>
    (hVlb i).trans_lt (ENNReal.mul_lt_top (cutNorm_lt_top θ) (hfv i))
  set W : ι → (Fin 2 → ℝ) → ℂ := fun i x => Ki i x * (Kq i x * Vl i x) with hW
  have hqv : ∀ i, rn θ (timeBoxGt p p) (fun x => Kq i x * Vl i x) ≤
      ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Kq i) * rn θ (timeBoxGt p p) (Vl i) := fun i =>
    rn_mul_le hθ0 (timeBoxGt_cl p) (Kq i) (Vl i) (hVlc i) (hfq i) (hfl i)
  have hqvf : ∀ i, rn θ (timeBoxGt p p) (fun x => Kq i x * Vl i x) < ⊤ := fun i =>
    (hqv i).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfq i)) (hfl i))
  have hWb : ∀ i, rn θ (timeBoxGt p p) (W i) ≤ T4 * cutNorm θ * (rn θ (timeBoxGt p p) (Ki i) *
      (rn θ (timeBoxGt p p) (Kq i) * rn θ (win p) (fun y => V i (y 0)))) := fun i => by
    refine (rn_mul_le hθ0 (timeBoxGt_cl p) (Ki i) (fun x => Kq i x * Vl i x) ((hKq i).mul (hVlc i))
      (hfi i) (hqvf i)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Ki i) * rn θ (timeBoxGt p p) (fun x => Kq i x * Vl i x)
        ≤ ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Ki i) *
            (ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Kq i) *
              (cutNorm θ * rn θ (win p) (fun y => V i (y 0)))) :=
          mul_le_mul' le_rfl ((hqv i).trans (mul_le_mul' le_rfl (hVlb i)))
      _ = _ := by rw [hT4]; ring
  have hWc : ∀ i, Continuous (W i) := fun i => (hKi i).mul ((hKq i).mul (hVlc i))
  have hWf : ∀ i, rn θ (timeBoxGt p p) (W i) < ⊤ := fun i => (hWb i).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hT4f (cutNorm_lt_top θ))
      (ENNReal.mul_lt_top (hfi i) (ENNReal.mul_lt_top (hfq i) (hfv i))))
  have he : (fun ts : Fin 2 → ℝ => ∑' i, c i * ∫ u in Ioo s (ts 0),
      cutMod (A i) s u * (Kp ![ts 0, u] * (Ki i ![u, s] * (Kq i ![u, s] * V i u)))) =
      fun ts => ∑' i, c i * ∫ u in Ioo s (ts 0), cutMod (A i) s u * (Kp ![ts 0, u] * W i ![u, s]) := by
    funext ts
    rfl
  rw [he]
  refine (hcore ι p s q' hps hsp A c Kp W hKp hWc hfp hWf).trans ?_
  calc Cc * ∑' i, ‖c i‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W i))
      ≤ Cc * ∑' i, ‖c i‖ₑ * (rn θ (timeBoxGt p p) Kp * (T4 * cutNorm θ * (rn θ (timeBoxGt p p) (Ki i) *
          (rn θ (timeBoxGt p p) (Kq i) * rn θ (win p) (fun y => V i (y 0)))))) :=
        mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl (mul_le_mul' le_rfl (hWb i)))
    _ = _ := by
        rw [show (fun i => ‖c i‖ₑ * (rn θ (timeBoxGt p p) Kp * (T4 * cutNorm θ * (rn θ (timeBoxGt p p) (Ki i) *
            (rn θ (timeBoxGt p p) (Kq i) * rn θ (win p) (fun y => V i (y 0))))))) =
          fun i => T4 * cutNorm θ * (‖c i‖ₑ * (rn θ (timeBoxGt p p) Kp * (rn θ (timeBoxGt p p) (Ki i) *
            (rn θ (timeBoxGt p p) (Kq i) * rn θ (win p) (fun y => V i (y 0)))))) from funext fun i => by ring,
          ENNReal.tsum_mul_left]
        ring

/-! ### The clocks of the traced couple -/

theorem tc_cupR_trace {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {j : Fin 2} {i : Fin 3}
    (hj : rBase m inner ζ j = bPath m inner ++ [i]) (u s : ℝ) (t : Fin 2) :
    cupR m inner ζ u s t = if t = j then s else u := by
  by_cases ht : t = j
  · rw [if_pos ht, ht]; exact cupR_of_bot hj u s
  · rw [if_neg ht]
    rcases rBase_cases m inner ζ t with h | h
    · exact cupR_top h
    · exfalso
      rcases rBase_cases m inner ζ j with h' | h'
      · rw [h'] at hj
        have := congrArg List.length hj
        simp [bPath] at this
      · exact ht (rBase_injective m inner ζ (h.trans h'.symm))

theorem tc_cupG_trace {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {j : Fin 2} {i : Fin 3}
    (hj : gBase m inner ζ j = bPath m inner ++ [i]) (u s : ℝ) (t : Fin 2) :
    cupG m inner ζ u s t = if t = j then s else u := by
  by_cases ht : t = j
  · rw [if_pos ht, ht]; exact cupG_of_bot hj u s
  · rw [if_neg ht]
    rcases gBase_cases m inner ζ t with h | h
    · exact cupG_top h
    · exfalso
      rcases gBase_cases m inner ζ j with h' | h'
      · rw [h'] at hj
        have := congrArg List.length hj
        simp [bPath] at this
      · exact ht (gBase_injective m inner ζ (h.trans h'.symm))

/-- The non-lone children of the terminal node carry the red and green trees. -/
theorem tc_child_cases (m : MiniTreeCode) (i : Fin 3) (hi : i ≠ m.lone) : i = m.red.2 ∨ i = m.green.2 := by
  revert i hi
  obtain ⟨c, b⟩ := m
  fin_cases c <;> fin_cases b <;> decide

end WaveTurbulence.Flower.ProtPin
