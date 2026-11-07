/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.GateData
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TraceBox
public import WaveTurbulence.Foundations.RegularAsymptotics.RegularAppContinuity

/-! # P4-W1: analysis for the separated expansions (continuity, null sets, traces across boxes)

* `eqOn_zero_of_ae`: a continuous function vanishing a.e. on `B ⊆ closure (interior B)` vanishes on `B`.
* `XNorm00Restr_le_of_ae_eq`, `XNorm00Restr_congr_on`: the restriction norm does not see a.e. changes on `B`, nor changes off `B`.
* `XNorm00Restr_trace_cross`: the trace `t ↦ h(t[j ↦ c])` on a set `Bt` in a unit cube is bounded by `traceConst · ‖h‖` on a SOURCE
  set `B`, as soon as the trace points lie in `closure (interior B)` (`XNorm00Restr_trace` of `VineEstS3.TraceBox` is the case
  `Bt = B`, `c = q j`).  This is the trace used for the constant extension of an approximant past the right end of its unit window
  (TARGET L1913-L1919).
* `continuous_couple_app`, `continuous_tree_app`: the source approximants `SourceApp.couple/tree` are continuous in `(t, s)`.
* `leafwise_cont`: a `LeafwiseSeparated` expansion of a time-continuous function on `T ⊆ closure (interior T)` can be taken with
  continuous time factors `J i`, with the same bounds.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine MeasureTheory Set Filter TTree WaveTurbulence.Reg
open scoped ENNReal ContDiff

section Null
variable {r : ℕ}

/-- A continuous function vanishing a.e. on `B` vanishes on `B` when `B ⊆ closure (interior B)`. -/
theorem eqOn_zero_of_ae {g : (Fin r → ℝ) → ℂ} (hg : Continuous g) {B : Set (Fin r → ℝ)}
    (hB : B ⊆ closure (interior B)) (h : ∀ᵐ t, t ∈ B → g t = 0) : ∀ t ∈ B, g t = 0 := by
  have hU : ∀ t ∈ interior B, g t = 0 := by
    intro t ht
    by_contra hne
    have hWo : IsOpen (interior B ∩ g ⁻¹' {0}ᶜ) := isOpen_interior.inter (isOpen_compl_singleton.preimage hg)
    have hpos := hWo.measure_pos (volume : Measure (Fin r → ℝ)) ⟨t, ht, hne⟩
    have h0 : volume (interior B ∩ g ⁻¹' {0}ᶜ) = 0 := by
      rw [ae_iff] at h
      refine measure_mono_null (fun x hx => ?_) h
      exact fun hx' => hx.2 (hx' (interior_subset hx.1))
    exact hpos.ne' h0
  intro t ht
  exact closure_minimal hU (isClosed_singleton.preimage hg) (hB ht)

variable {V : Type*}

/-- The restriction norm does not see a.e. changes on `B`. -/
theorem XNorm00Restr_le_of_ae_eq (θ : ℝ) {B : Set (Fin r → ℝ)} (K : Set V) {F F' : (Fin r → ℝ) → V → ℂ}
    (h : ∀ᵐ t, t ∈ B → ∀ v ∈ K, F t v = F' t v) : XNorm00Restr θ B K F' ≤ XNorm00Restr θ B K F := by
  classical
  unfold XNorm00Restr
  refine le_iInf₂ fun G hG => ?_
  let G' : (Fin r → ℝ) → V → ℂ := fun t v => if t ∈ B ∧ v ∈ K then F' t v else G t v
  have hG' : ∀ t ∈ B, ∀ v ∈ K, G' t v = F' t v := fun t ht v hv => by simp only [G', if_pos (And.intro ht hv)]
  refine (iInf₂_le G' hG').trans (le_of_eq ?_)
  refine WaveTurbulence.VineEstS3.Mink.XNorm00_congr_ae θ fun v => ?_
  filter_upwards [h] with t ht
  by_cases hb : t ∈ B ∧ v ∈ K
  · simp only [G', if_pos hb]
    rw [← ht hb.1 v hb.2, hG t hb.1 v hb.2]
  · simp only [G', if_neg hb]

/-- The restriction norm only sees the values on `B × K`. -/
theorem XNorm00Restr_congr_on (θ : ℝ) {B : Set (Fin r → ℝ)} (K : Set V) {F F' : (Fin r → ℝ) → V → ℂ}
    (h : ∀ t ∈ B, ∀ v ∈ K, F t v = F' t v) : XNorm00Restr θ B K F' = XNorm00Restr θ B K F :=
  le_antisymm (XNorm00Restr_le_of_ae_eq θ K (Eventually.of_forall h))
    (XNorm00Restr_le_of_ae_eq θ K (Eventually.of_forall fun t ht v hv => (h t ht v hv).symm))

end Null

section Trace
variable {r : ℕ} {V : Type*}

/-- **Trace across boxes.**  For `h` continuous in time, a target set `Bt` inside the unit cube at `qt`, and trace points
`t[j ↦ c]` (`t ∈ Bt`) in `closure (interior B)`: `‖h(·[j ↦ c])‖_{𝔛^{θ,0,0}(Bt)} ≤ traceConst θ χ₀ · ‖h‖_{𝔛^{θ,0,0}(B)}`. -/
theorem XNorm00Restr_trace_cross {θ : ℝ} (hθ : 0 ≤ θ) (qt : Fin r → ℝ) {B Bt : Set (Fin r → ℝ)}
    (hBt : ∀ t ∈ Bt, ∀ i, t i ∈ Icc (qt i) (qt i + 1)) {K : Set V} (h : (Fin r → ℝ) → V → ℂ)
    (hh : ∀ v ∈ K, Continuous fun t => h t v) (j : Fin r) (c : ℝ)
    (hcl : ∀ t ∈ Bt, Function.update t j c ∈ closure (interior B)) :
    XNorm00Restr θ Bt K (fun t v => h (Function.update t j c) v) ≤
      Regref.traceConst (r := r) θ chiUnit * XNorm00Restr θ B K h := by
  set St : Set (Fin r → ℝ) := (fun s => s + qt) ⁻¹' Bt with hSt
  set S : Set (Fin r → ℝ) := (fun s => s + qt) ⁻¹' B with hS
  have hupd : ∀ s : Fin r → ℝ, Function.update (s + qt) j c = Function.update s j (c - qt j) + qt := by
    intro s; funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  have e1 : XNorm00Restr θ Bt K (fun t v => h (Function.update t j c) v) ≤
      XNorm00Restr θ St K (fun s v => h (Function.update s j (c - qt j) + qt) v) := by
    refine XNorm00Restr_shift_le θ qt (fun t ht => ?_) (fun t ht v hv => ?_)
    · show t - qt + qt ∈ Bt
      simpa using ht
    · show h (Function.update t j c) v = h (Function.update (t - qt) j (c - qt j) + qt) v
      rw [← hupd]; simp
  have hhh : ∀ v ∈ K, Continuous fun s => h (s + qt) v := fun v hv => (hh v hv).comp (continuous_id.add continuous_const)
  have hcl' : ∀ s ∈ St, Function.update s j (c - qt j) ∈ closure (interior S) := by
    intro s hs
    have h1 := hcl (s + qt) hs
    rw [hupd] at h1
    have hhome : S = (Homeomorph.addRight qt) ⁻¹' B := rfl
    rw [hhome, ← Homeomorph.preimage_interior, ← Homeomorph.preimage_closure]
    exact h1
  have e2 : XNorm00Restr θ St K (fun s v => h (Function.update s j (c - qt j) + qt) v) ≤
      Regref.traceConst (r := r) θ chiUnit * XNorm00Restr θ S K (fun s v => h (s + qt) v) := by
    rw [NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00, NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00]
    exact Regref.mixedRestrictionNorm00_trace_le (θ := θ) hθ chiUnit_contDiff chiUnit_hasCompactSupport
      (B := S) (T := St) (K := K) (fun s v => h (s + qt) v) hhh j (c - qt j) hcl' (fun s hs => by
        refine coordinateCutoff_chiUnit fun i => ?_
        have := hBt (s + qt) hs i
        simp only [Pi.add_apply] at this
        constructor <;> linarith [this.1, this.2])
  have e3 : XNorm00Restr θ S K (fun s v => h (s + qt) v) ≤ XNorm00Restr θ B K h := by
    refine XNorm00Restr_shift_le θ (-qt) (fun t ht => ?_) (fun t ht v hv => ?_)
    · show t - -qt ∈ B
      rw [sub_neg_eq_add]
      exact ht
    · simp
  exact e1.trans (e2.trans (mul_le_mul' le_rfl e3))

end Trace

section Cont
variable {d : ℕ}

theorem continuous_cplApp (δ r : ℝ) (F : Mom d → ℝ) (Q : RegCpl) (k : Mom d) {f g : (Fin 2 → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun ts => Q.app δ r F (f ts) (g ts) k :=
  (continuous_RegCpl_app δ r F Q k).comp (hf.prodMk hg)

theorem continuous_chainApp (δ r : ℝ) (F : Mom d → ℝ) (X : RegChain) (ζ : ℤˣ) (k : Mom d) {f g : (Fin 2 → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun ts => X.app δ r F ζ (f ts) (g ts) k :=
  (continuous_RegChain_app δ r F X ζ k).comp (hf.prodMk hg)

/-- The couple source approximant is continuous in `(t, s)`. -/
theorem continuous_couple_app (δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (Q : RegCpl) (q q' : ℕ) (k : Mom d) :
    Continuous fun ts : Fin 2 → ℝ => SourceApp.couple δ F LG Q q q' (ts 0) (ts 1) k := by
  have h0 : Continuous fun ts : Fin 2 → ℝ => ts 0 := continuous_apply 0
  have h1 : Continuous fun ts : Fin 2 → ℝ => ts 1 := continuous_apply 1
  unfold SourceApp.couple
  by_cases hq : q = q'
  · simp only [hq, if_true]; exact continuous_cplApp _ _ _ _ _ h0 h1
  · simp only [hq, if_false]
    cases Q with
    | triv =>
      dsimp only
      split_ifs
      · exact continuous_cplApp _ _ _ _ _ continuous_const h1
      · exact continuous_cplApp _ _ _ _ _ h0 continuous_const
    | type1 c Q₁ Q₂ Q₃ =>
      dsimp only
      split_ifs
      · exact continuous_cplApp _ _ _ _ _ continuous_const h1
      · exact continuous_cplApp _ _ _ _ _ h0 continuous_const
    | type2 Xp Xm Qlp =>
      dsimp only
      split_ifs
      · exact (continuous_const.mul (continuous_chainApp _ _ _ _ _ _ h0 continuous_const)).mul
          (continuous_cplApp _ _ _ _ _ continuous_const h1)
      · exact (continuous_const.mul (continuous_chainApp _ _ _ _ _ _ h1 continuous_const)).mul
          (continuous_cplApp _ _ _ _ _ h0 continuous_const)

/-- The tree source approximant is continuous in `(t, s)`. -/
theorem continuous_tree_app (δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) (X : RegChain) (q q' : ℕ) (k : Mom d) :
    Continuous fun ts : Fin 2 → ℝ => SourceApp.tree δ F LG X q q' (ts 0) (ts 1) k := by
  have h0 : Continuous fun ts : Fin 2 → ℝ => ts 0 := continuous_apply 0
  have h1 : Continuous fun ts : Fin 2 → ℝ => ts 1 := continuous_apply 1
  unfold SourceApp.tree
  by_cases hq : q = q'
  · simp only [hq, if_true]; exact continuous_chainApp _ _ _ _ _ _ h0 h1
  · simp only [hq, if_false]
    exact (continuous_const.mul (continuous_chainApp _ _ _ _ _ _ h0 continuous_const)).mul
      (continuous_chainApp _ _ _ _ _ _ continuous_const h1)

end Cont

section Leafwise
variable {P : WTParams}

/-- **A `LeafwiseSeparated` expansion with continuous time factors.**  If the expanded function is continuous in time and
`T ⊆ closure (interior T)`, the time factors can be replaced by their continuous representatives (`restr_ae_cont`), keeping the
expansion on all of `T` and the bounds. -/
theorem leafwise_cont {n W : ℕ} {T : Set (Fin 2 → ℝ)} (hi : T ⊆ closure (interior T)) (hθ : 0 ≤ 1 - P.η)
    {F : (Fin 2 → ℝ) → Mom P.d → ℂ} (hF : ∀ k, Continuous fun ts => F ts k) {cost : ℝ}
    (h : LeafwiseSeparated P n W T F cost) :
    ∃ (m : ℕ) (J : Fin m → (Fin 2 → ℝ) → ℂ) (M : Fin m → Mom P.d → ℝ), m ≤ 2 ^ n ∧ (∀ i, Continuous (J i)) ∧
      (∀ ts ∈ T, ∀ k, F ts k = ∑ i, (P.δ : ℂ) ^ n * J i ts * (M i k : ℂ)) ∧
      (∀ i, XNorm00Restr (V := Unit) (1 - P.η) T Set.univ (fun ts _ => J i ts) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      ∀ i, SNormR (30 * P.d) W (M i) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n * cost) := by
  obtain ⟨m, J, M, hm, hexp, hJ, hM⟩ := h
  have hfin : ∀ i, XNorm00Restr (V := Unit) (1 - P.η) T Set.univ (fun ts _ => J i ts) < ⊤ := fun i =>
    lt_of_le_of_lt (hJ i) ENNReal.ofReal_lt_top
  choose J' hJc hJae using fun i => VineEstS5C.P2.restr_ae_cont hθ (hfin i)
  have hall : ∀ᵐ t : Fin 2 → ℝ, ∀ i, t ∈ T → J i t = J' i t := ae_all_iff.2 hJae
  refine ⟨m, J', M, hm, hJc, ?_, fun i => ?_, hM⟩
  · intro ts hts k
    have hg : Continuous fun ts : Fin 2 → ℝ => F ts k - ∑ i, (P.δ : ℂ) ^ n * J' i ts * (M i k : ℂ) :=
      (hF k).sub (continuous_finset_sum _ fun i _ => (continuous_const.mul (hJc i)).mul continuous_const)
    have hz := eqOn_zero_of_ae hg hi (by
      filter_upwards [hall] with t ht htT
      rw [hexp t htT k, sub_eq_zero]
      exact Finset.sum_congr rfl fun i _ => by rw [ht i htT])
    exact sub_eq_zero.mp (hz ts hts)
  · refine (XNorm00Restr_le_of_ae_eq (1 - P.η) (Set.univ : Set Unit) ?_).trans (hJ i)
    filter_upwards [hJae i] with t ht htT v _
    exact ht htT

end Leafwise

end WaveTurbulence.VineEstS5C.P4.W13
