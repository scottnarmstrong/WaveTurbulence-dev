/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.TreeKink
public import WaveTurbulence.Foundations.Flower.ProtRT.TreeUp
public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ASum
public import WaveTurbulence.Foundations.Flower.ProtPin.RootPair

/-! # RT-GATE (i): the port cases of a root-pinned multi-layer tree

At one output, D2c's root identity at `σ = T = s` writes clause (i)'s kernel on the R189 box as
`Σ'_i c_i ∫_{R} e^{πiA_i(s−u)} Ks(u, ts₁) W_i(s, u) du` (with a suffix) or `Σ'_i c_i ∫_{R ∩ {u > ts₁}} … W_i(s, u) du`
(one pair), `R = (ℓb, ℓb+1) ∩ (0, s)`, `ℓb` the layer of the closing node, the root in layer `p ≥ ℓb`, the port window
`q' ≤ ℓb`:
* `q' < ℓb`: the port never meets the closing node: a fixed-interval trace (`tc2a_sum_ivl`, D3-HELPER) with a suffix,
  a constant without;
* `q' = ℓb < p`: the kink at the window end `ℓb + 1` (`rtk_mirror_kink2`, `rtk_mirror_kink`), the closing-pair pieces
  read at the fixed root time `s` (`rn_trace`);
* `q' = ℓb = p`: D3's (P1) kink at `t = s`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin

/-- **A continuous function on a set inside the closure of the interior of a larger set.** -/
theorem rt_rn_closure {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {B B' : Set (Fin r → ℝ)}
    (hB : ∀ t ∈ B, t ∈ closure (interior B)) (hB' : B' ⊆ closure (interior B)) {f : (Fin r → ℝ) → ℂ}
    (hf : Continuous f) : rn θ B' f ≤ rn θ B f := by
  by_cases hfin : rn θ B f = ⊤
  · rw [hfin]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨g, hgc, hgB, -, hgle⟩ := exists_cont_ext hθ hB hf (lt_top_iff_ne_top.2 hfin) (ε := (ε : ℝ≥0∞))
    (by exact_mod_cast hε) ENNReal.coe_ne_top
  refine (rn_le θ (g := g) fun t ht => ?_).trans hgle
  have h1 : Set.EqOn g f (interior B) := fun t ht => hgB t (interior_subset ht)
  exact h1.closure hgc hf (hB' ht)

/-- A full box below an ordered box: `timeBox q q' ⊆ closure (interior (timeBoxGt q q'))` when `q' + 1 ≤ q`. -/
theorem rt_box_sub_cl {q q' : ℝ} (h : q' + 1 ≤ q) : timeBox q q' ⊆ closure (interior (timeBoxGt q q')) := by
  set O : Set (Fin 2 → ℝ) := Set.pi univ fun i => Ioo (![q, q'] i) (![q, q'] i + 1) with hO
  have hOo : IsOpen O := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hOsub : O ⊆ timeBoxGt q q' := by
    intro x hx
    have h0 := hx 0 (mem_univ _)
    have h1 := hx 1 (mem_univ _)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    exact ⟨⟨⟨h0.1.le, h0.2.le⟩, ⟨h1.1.le, h1.2.le⟩⟩, by linarith [h0.1, h1.2]⟩
  intro x hx
  refine closure_mono (interior_maximal hOsub hOo) ?_
  rw [hO, closure_pi_set]
  intro i _
  show x i ∈ closure (Ioo (![q, q'] i) (![q, q'] i + 1))
  rw [closure_Ioo (by linarith)]
  fin_cases i
  · simpa using hx.1
  · simpa using hx.2

theorem rt_rootPh_split (A s t u : ℝ) : rootPh A s u = rootPh A s t * rootPh A t u := by
  unfold rootPh
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rt_update_vec (s t u : ℝ) : Function.update (![t, u] : Fin 2 → ℝ) 0 s = ![s, u] := by
  funext j
  fin_cases j <;> simp

/-- The integration range of the root cut at `σ = T = s` (D2c's `rootU`). -/
def rtR (ℓb : ℕ) (s : ℝ) : Set ℝ := {u | (ℓb : ℝ) < u ∧ u < ℓb + 1 ∧ 0 < u ∧ u < s ∧ u < s}

theorem measurableSet_rtR (ℓb : ℕ) (s : ℝ) : MeasurableSet (rtR ℓb s) := by
  unfold rtR
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter
      ((measurableSet_lt measurable_const measurable_id).inter
        ((measurableSet_lt measurable_id measurable_const).inter
          (measurableSet_lt measurable_id measurable_const))))

theorem rtR_low {ℓb p : ℕ} {s : ℝ} (h : ℓb < p) (hps : (p : ℝ) < s) : rtR ℓb s = Ioo (ℓb : ℝ) (ℓb + 1) := by
  have h' : (ℓb : ℝ) + 1 ≤ p := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ℓb := Nat.cast_nonneg _
  ext u
  simp only [rtR, Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by linarith, by linarith, by linarith⟩

theorem rtR_top {p : ℕ} {s : ℝ} (hsp : s < p + 1) : rtR p s = Ioo (p : ℝ) s := by
  have h0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  ext u
  simp only [rtR, Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, -, -, h4, -⟩; exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, by linarith, h2, h2⟩

/-- The trace of a closing-pair product at the fixed root time `s`, on the ordered box of the closing node. -/
theorem rt_W_trace {θ : ℝ} (hθ0 : 0 ≤ θ) {p ℓb : ℕ} (h : ℓb < p) {s : ℝ} (hps : (p : ℝ) < s) (hsp : s < p + 1)
    (W : (Fin 2 → ℝ) → ℂ) (hW : Continuous W) :
    rn θ (timeBoxGt (ℓb : ℝ) ℓb) (fun x => W (Function.update x 0 s)) ≤
      Regref.traceConst (r := 2) θ VineEstS3.chiUnit * rn θ (timeBoxGt (p : ℝ) ℓb) W := by
  have h' : (ℓb : ℝ) + 1 ≤ p := by exact_mod_cast h
  have hbp : (ℓb : ℝ) ≤ p := by linarith
  refine rn_trace hθ0 (fun _ => (ℓb : ℝ)) (B := timeBoxGt (p : ℝ) ℓb) ?_ W hW 0 s ?_
  · intro x hx i
    fin_cases i
    · exact hx.1.1
    · exact hx.1.2
  · intro x hx
    refine VineEstS3.timeBoxGt_subset_closure_interior hbp ?_
    have hx1 := hx.1.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [Function.update_self]; exact ⟨hps.le, hsp.le⟩
    · rw [Function.update_of_ne (by decide)]; exact hx1
    · rw [Function.update_self, Function.update_of_ne (by decide)]; linarith [hx1.2]

end WaveTurbulence.Flower.ProtRT
