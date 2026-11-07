/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCSquare
/-! # VINE-COUNT part 8: moving along a circulation changes the chart coordinates by integer multiples.

For a chart `A` of a vine and a zero-flow integer function `z` on the internal bonds, `k ↦ k + z e₀` preserves the flow
fibre, and (each chart coordinate being a difference of two origins) shifts the coordinate `i` by
`(z(p_i) - z(q_i)) e₀`. Combined with the phases of a chart rung this gives, for an adjacent-rung square `Q`,
the vector identity `ι (k_p - k_{p'}) = -λ r` with an integer `|λ| ≤ 4`, where `λ ≠ 0` forces `(ζ₀, ζ₁) ≠ 0`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Shift
variable {M : Molecule V D} {S : Finset V} {a b : V} {E : Type} [AddCommGroup E] {r : E}

/-- Shift a flow-fibre point by a zero-flow integer function. -/
def shiftFib (k : FlowFiber M S a b E r) (z : D → ℤ) (hz : ∀ v, ∑ e : Bond M S, incidence M v e.1 * z e.1 = 0)
    (e0 : E) : FlowFiber M S a b E r :=
  ⟨fun e => k.1 e + z e.1 • e0, by
    have : ∀ v, flow M S (fun e : Bond M S => k.1 e + z e.1 • e0) v = flow M S k.1 v := by
      intro v
      unfold flow
      simp only [smul_add, Finset.sum_add_distrib, smul_smul]
      rw [← Finset.sum_smul, hz v, zero_smul, add_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [this]; exact k.2.1
    · rw [this]; exact k.2.2.1
    · intro v hv hva hvb; rw [this]; exact k.2.2.2 v hv hva hvb⟩

/-- The extension of an integer function on darts to the origins `Bond ⊕ Fin 2` (zero on the boundary origins). -/
def zOrigin (z : D → ℤ) : Bond M S ⊕ Fin 2 → ℤ
  | .inl e => z e.1
  | .inr _ => 0

end Shift

section Chart
variable {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (A : FullVineChart M X S a b)

/-- The origin pair of the `i`-th chart coordinate. -/
noncomputable def pq (i : Fin A.indexing.shape.n) : (Bond M S ⊕ Fin 2) × (Bond M S ⊕ Fin 2) :=
  (Classical.choose (A.difference i), Classical.choose (Classical.choose_spec (A.difference i)))

theorem pq_spec (i : Fin A.indexing.shape.n) {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber M S a b E r) :
    A.chart g r k i = origin M S k.1 g r (pq A i).1 - origin M S k.1 g r (pq A i).2 :=
  Classical.choose_spec (Classical.choose_spec (A.difference i)) g r k

theorem chart_shift {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber M S a b E r) (z : D → ℤ)
    (hz : ∀ v, ∑ e : Bond M S, incidence M v e.1 * z e.1 = 0) (e0 : E) (i : Fin A.indexing.shape.n) :
    A.chart g r (shiftFib k z hz e0) i - A.chart g r k i =
      (zOrigin (S := S) (M := M) z (pq A i).1 - zOrigin (S := S) (M := M) z (pq A i).2) • e0 := by
  rw [pq_spec A i g r (shiftFib k z hz e0), pq_spec A i g r k]
  have h : ∀ p : Bond M S ⊕ Fin 2, origin M S (shiftFib k z hz e0).1 g r p = origin M S k.1 g r p + zOrigin z p • e0 := by
    intro p
    rcases p with e | j
    · simp [origin, shiftFib, zOrigin]
    · simp [origin, zOrigin]
  rw [h, h, sub_smul]
  abel

theorem rung_sum_phase {d : ℕ} (g r : Mom d) (k : FlowFiber M S a b (Mom d) r) (j : Fin A.indexing.shape.m) :
    energy M S k.1 (A.indexing.atom (A.indexing.shape.xSlot j)).1 +
        energy M S k.1 (A.indexing.atom (A.indexing.shape.ySlot j)).1 =
      2 * inner ℝ r ((A.ζc j 0 : ℝ) • A.chart g r k (A.indexing.shape.xSlot j) +
        (A.ζc j 1 : ℝ) • A.chart g r k (A.indexing.shape.ySlot j) + (A.ζc j 2 : ℝ) • r) := by
  have ht := A.rung_t_phase d g r (A.chart g r k) j
  have hs := A.rung_s_phase d g r (A.chart g r k) j
  rw [Equiv.symm_apply_apply] at ht hs
  have hx : A.indexing.shape.xSlot j ≠ A.indexing.shape.x0 := by
    intro h
    have := congrArg Fin.val h
    simp [Shape.xSlot, Shape.x0] at this
  have hy : A.indexing.shape.ySlot j ≠ A.indexing.shape.x0 := by
    intro h
    have := congrArg Fin.val h
    simp [Shape.ySlot, Shape.x0] at this
  unfold nodeResonance at ht hs
  rw [if_neg hx, add_zero] at ht
  rw [if_neg hy, add_zero] at hs
  rw [ht, hs]
  ring

theorem zOrigin_abs (z : D → ℤ) (hz : ∀ e, |z e| ≤ 1) (p : Bond M S ⊕ Fin 2) : |zOrigin (S := S) (M := M) z p| ≤ 1 := by
  rcases p with e | j
  · exact hz e.1
  · simp [zOrigin]

end Chart

section Lambda
variable {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (A : FullVineChart M X S a b)
variable {t s t' s' : V} (Q : Square M S t s t' s')

theorem rung_lambda (j : Fin A.indexing.shape.m)
    (hj : ((A.indexing.atom (A.indexing.shape.xSlot j)).1 = t ∧ (A.indexing.atom (A.indexing.shape.ySlot j)).1 = s) ∨
      ((A.indexing.atom (A.indexing.shape.xSlot j)).1 = s ∧ (A.indexing.atom (A.indexing.shape.ySlot j)).1 = t)) :
    ∃ lam : ℤ, |lam| ≤ 4 ∧ (lam ≠ 0 → A.ζc j 0 ≠ 0 ∨ A.ζc j 1 ≠ 0) ∧
      ∀ (d : ℕ) (g r : Mom d) (k : FlowFiber M S a b (Mom d) r),
        (incidence M t Q.p : ℝ) • (k.1 ⟨Q.p, Q.p_mem⟩ - k.1 ⟨Q.p', Q.p'_mem⟩) = -(lam : ℝ) • r := by
  set ix := A.indexing.shape.xSlot j
  set iy := A.indexing.shape.ySlot j
  set cx : ℤ := zOrigin (S := S) (M := M) Q.zfun (pq A ix).1 - zOrigin (S := S) (M := M) Q.zfun (pq A ix).2 with hcx
  set cy : ℤ := zOrigin (S := S) (M := M) Q.zfun (pq A iy).1 - zOrigin (S := S) (M := M) Q.zfun (pq A iy).2 with hcy
  have hcx2 : |cx| ≤ 2 := by
    have h1 := zOrigin_abs (S := S) (M := M) Q.zfun Q.zfun_abs (pq A ix).1
    have h2 := zOrigin_abs (S := S) (M := M) Q.zfun Q.zfun_abs (pq A ix).2
    calc |cx| ≤ |zOrigin (S := S) (M := M) Q.zfun (pq A ix).1| + |zOrigin (S := S) (M := M) Q.zfun (pq A ix).2| :=
          abs_sub _ _
      _ ≤ 2 := by linarith
  have hcy2 : |cy| ≤ 2 := by
    have h1 := zOrigin_abs (S := S) (M := M) Q.zfun Q.zfun_abs (pq A iy).1
    have h2 := zOrigin_abs (S := S) (M := M) Q.zfun Q.zfun_abs (pq A iy).2
    calc |cy| ≤ |zOrigin (S := S) (M := M) Q.zfun (pq A iy).1| + |zOrigin (S := S) (M := M) Q.zfun (pq A iy).2| :=
          abs_sub _ _
      _ ≤ 2 := by linarith
  have hζ0 := A.ζ_unit j 0
  have hζ1 := A.ζ_unit j 1
  have hab : ∀ z : ℤ, UnitCoeff z → |z| ≤ 1 := by
    intro z hz; rcases hz with rfl | rfl | rfl <;> simp
  refine ⟨A.ζc j 0 * cx + A.ζc j 1 * cy, ?_, ?_, ?_⟩
  · calc |A.ζc j 0 * cx + A.ζc j 1 * cy| ≤ |A.ζc j 0 * cx| + |A.ζc j 1 * cy| := abs_add_le _ _
      _ = |A.ζc j 0| * |cx| + |A.ζc j 1| * |cy| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 2 + 1 * 2 := by
        gcongr
        · exact hab _ hζ0
        · exact hab _ hζ1
      _ = 4 := by norm_num
  · intro hne
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [hcon.1, hcon.2]; simp
  · intro d g r k
    have hflow := Q.zfun_flow (S := S)
    obtain ⟨w, hw⟩ : ∃ w : Mom d, w = ((A.ζc j 0 * cx + A.ζc j 1 * cy : ℤ) : ℝ) • r +
        (incidence M t Q.p : ℝ) • (k.1 ⟨Q.p, Q.p_mem⟩ - k.1 ⟨Q.p', Q.p'_mem⟩) := ⟨_, rfl⟩
    -- for every e0 the two computations of the change of E_t + E_s agree
    have key : ∀ e0 : Mom d, (A.ζc j 0 * cx + A.ζc j 1 * cy : ℤ) * inner ℝ r e0 =
        -(incidence M t Q.p : ℝ) * inner ℝ (k.1 ⟨Q.p, Q.p_mem⟩ - k.1 ⟨Q.p', Q.p'_mem⟩) e0 := by
      intro e0
      have h1 := Q.energy_shift (d := d) k.1 e0
      have hk' : (shiftFib k Q.zfun hflow e0).1 = fun e => k.1 e + (Q.zfun e.1 : ℝ) • e0 := by
        funext e
        simp [shiftFib, Int.cast_smul_eq_zsmul]
      have hs0 := rung_sum_phase A g r k j
      have hs1 := rung_sum_phase A g r (shiftFib k Q.zfun hflow e0) j
      rw [hk'] at hs1
      have hdx := chart_shift A g r k Q.zfun hflow e0 ix
      have hdy := chart_shift A g r k Q.zfun hflow e0 iy
      have eq_ts : energy M S k.1 (A.indexing.atom ix).1 + energy M S k.1 (A.indexing.atom iy).1 =
          energy M S k.1 t + energy M S k.1 s := by
        rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2]; ring
      have eq_ts' : energy M S (fun e => k.1 e + (Q.zfun e.1 : ℝ) • e0) (A.indexing.atom ix).1 +
          energy M S (fun e => k.1 e + (Q.zfun e.1 : ℝ) • e0) (A.indexing.atom iy).1 =
          energy M S (fun e => k.1 e + (Q.zfun e.1 : ℝ) • e0) t + energy M S (fun e => k.1 e + (Q.zfun e.1 : ℝ) • e0) s := by
        rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2]; ring
      rw [eq_ts] at hs0
      rw [eq_ts'] at hs1
      set x := A.chart g r k
      set x' := A.chart g r (shiftFib k Q.zfun hflow e0)
      have hx' : x' ix = x ix + cx • e0 := by
        have := hdx; rw [hcx]; rw [sub_eq_iff_eq_add'] at this; rw [this]
      have hy' : x' iy = x iy + cy • e0 := by
        have := hdy; rw [hcy]; rw [sub_eq_iff_eq_add'] at this; rw [this]
      have hdiff : (energy M S (fun e => k.1 e + (Q.zfun e.1 : ℝ) • e0) t + energy M S (fun e => k.1 e + (Q.zfun e.1 : ℝ) • e0) s) -
          (energy M S k.1 t + energy M S k.1 s) = 2 * ((A.ζc j 0 * cx + A.ζc j 1 * cy : ℤ) * inner ℝ r e0) := by
        rw [hs1, hs0, hx', hy']
        simp only [← Int.cast_smul_eq_zsmul ℝ, smul_add, inner_add_right, real_inner_smul_right]
        push_cast
        ring
      rw [hdiff] at h1
      linarith
    have hw0 : inner ℝ w w = (0 : ℝ) := by
      have h1 : inner ℝ w w = inner ℝ (((A.ζc j 0 * cx + A.ζc j 1 * cy : ℤ) : ℝ) • r +
          (incidence M t Q.p : ℝ) • (k.1 ⟨Q.p, Q.p_mem⟩ - k.1 ⟨Q.p', Q.p'_mem⟩)) w := congrArg (fun u => inner ℝ u w) hw
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at h1
      have h2 := key w
      linarith
    have hw1 : w = 0 := inner_self_eq_zero.mp hw0
    rw [hw] at hw1
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right hw1

end Lambda

end WaveTurbulence.VineCount
