/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.Oracle
public import WaveTurbulence.Foundations.Spine.PL2330Draft.Piece3

/-! # FILT-COH: traces of single-layer kernel bounds (the pieces of a coherent object)

Main's PL2330 piece bounds (`couple_bottom_bounds30`, `tree_bottom_bounds30`, `tree_top_bounds30`,
`tree_middle_bounds30`), first conjuncts, for the kernel itself instead of the error, at any weight `θ ≥ 0`. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.NormBridgeScratch

variable {d : ℕ}

/-- **The bottom couple**, frozen at `t = q' + 1`, as a function of `s`. -/
theorem couple_bottom_kernel {L γ δ θ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ : 0 ≤ θ) {q' : ℕ}
    {Q : RegCpl} {LG : LayeredGarden 2} (hQ : Q.Decodes LG.garden) {H : LeafProfiles 2 d}
    {B : (Fin 2 × Path) → NNReal} (hH : LeafwiseControlled LG H B) {e : ℝ}
    (hE : XNormRestr θ (30 * d) (30 * d) (timeBox q' q') Set.univ
      (fun ts k => coupleLeaves L γ δ LG H (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox) :
    rN θ (30 * d) (30 * d) T' (fun ts k => coupleLeaves L γ δ LG H (q' + 1) (ts 1) k) ≤
      ENNReal.ofReal (Ktr θ * e) := by
  have hΛ : 30 * d ≠ 0 := by omega
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hpt : ∀ ts ∈ T', Function.update (ts + ![b₀, -(q' : ℝ)]) 0 1 + ![(q' : ℝ), q'] =
      ![(q' : ℝ) + 1, ts 1] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      ring
    · simp [Function.update]
      rfl
  set h : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k => coupleLeaves L γ δ LG H (ts 0) (ts 1) k with hh
  have hc : ∀ k, Continuous fun ts => h ts k := fun k =>
    continuous_coupleLeaves_time L γ δ H LG hplain k (hH.summable_coset hd hL k)
  have htr := rN_trace_transport (Λ₂ := 30 * d) hΛ hθ (B := timeBox (q' : ℝ) q') (T' := T') h hc
    ![(q' : ℝ), q'] ![b₀, -(q' : ℝ)] 0 1 hT' (trace_line_couple q')
  have hgate : rN θ (30 * d) (30 * d) (timeBox (q' : ℝ) q') h ≤ ENNReal.ofReal e := by
    rw [← XNormRestr_eq_rN]
    exact hE
  have hcongr := restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 30 * d) T' (Set.univ : Set (Mom d))
    (F := fun ts k => h (Function.update (ts + ![b₀, -(q' : ℝ)]) 0 1 + ![(q' : ℝ), q']) k)
    (G := fun ts k => coupleLeaves L γ δ LG H (q' + 1) (ts 1) k) fun ts hts k _ => by
    rw [hpt ts hts, hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine hcongr.symm.le.trans (htr.trans ?_)
  rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
  exact mul_le_mul_right hgate _

/-- **The bottom tree factor**, frozen at `t = r + 1`, as a function of `s`. -/
theorem tree_bottom_kernel {L γ δ θ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ : 0 ≤ θ) {r q'' : ℕ} (hq : q'' ≤ r)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden) {H : LeafProfiles 1 d}
    {B : (Fin 1 × Path) → NNReal} (hH : LeafwiseControlled LG H B) {e : ℝ}
    (hE : XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q'' : ℝ)] ∈ Layered.unitBox) :
    rN θ (30 * d) 0 T' (fun ts k => treeLeaves L γ δ LG H (r + 1) (ts 1) k) ≤
      ENNReal.ofReal (Ktr θ * e) := by
  have hΛ : 30 * d ≠ 0 := by omega
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)
  have hpt : ∀ ts ∈ T', Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q''] =
      ![(r : ℝ) + 1, ts 1] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      try ring
    · simp [Function.update]
      try rfl
  set h : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k with hh
  have hc : ∀ k, Continuous fun ts => h ts k := fun k =>
    continuous_treeLeaves_time L γ δ LG H hfl (card_lone_le_of_decodesTree hX) k (hH.summable_coset hd hL k)
  have htr := rN_trace_transport (Λ₂ := 0) hΛ hθ (B := timeBoxGt (r : ℝ) q'') (T' := T') h hc
    ![(r : ℝ), q''] ![b₀, -(q'' : ℝ)] 0 1 hT' (trace_line_tree_bot hq)
  have hgate : rN θ (30 * d) 0 (timeBoxGt (r : ℝ) q'') h ≤ ENNReal.ofReal e := by
    rw [← XNormRestr_eq_rN]
    exact hE
  have hcongr := restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) T' (Set.univ : Set (Mom d))
    (F := fun ts k => h (Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q'']) k)
    (G := fun ts k => treeLeaves L γ δ LG H (r + 1) (ts 1) k) fun ts hts k _ => by
    rw [hpt ts hts, hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine hcongr.symm.le.trans (htr.trans ?_)
  rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
  exact mul_le_mul_right hgate _

/-- **The top tree factor**, frozen at `s = r`, as a function of `t`. -/
theorem tree_top_kernel {L γ δ θ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ : 0 ≤ θ) {r q'' : ℕ} (hq : q'' < r)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r)
    {H : LeafProfiles 1 d} {B : (Fin 1 × Path) → NNReal} (hH : LeafwiseControlled LG H B) {e : ℝ}
    (hE : XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (T' : Set (Fin 2 → ℝ)) (b₁ : ℝ) (hT' : ∀ ts ∈ T', ts + ![-(r : ℝ), b₁] ∈ Layered.unitBox) :
    rN θ (30 * d) 0 T' (fun ts k => treeLeaves L γ δ LG H (ts 0) r k) ≤ ENNReal.ofReal (Ktr θ * e) := by
  have hΛ : 30 * d ≠ 0 := by omega
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  have hlow : (q'' : ℝ) + 1 / 2 ≤ r := by linarith
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)
  have hpt : ∀ ts ∈ T', Function.update (ts + ![-(r : ℝ), b₁]) 1 (1 / 2) + ![(r : ℝ), q''] =
      ![ts 0, (q'' : ℝ) + 1 / 2] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      rfl
    · simp [Function.update]
      ring
  set h : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k with hh
  have hc : ∀ k, Continuous fun ts => h ts k := fun k =>
    continuous_treeLeaves_time L γ δ LG H hfl (card_lone_le_of_decodesTree hX) k (hH.summable_coset hd hL k)
  have htr := rN_trace_transport (Λ₂ := 0) hΛ hθ (B := timeBoxGt (r : ℝ) q'') (T' := T') h hc
    ![(r : ℝ), q''] ![-(r : ℝ), b₁] 1 (1 / 2) hT' (trace_line_tree hq)
  have hgate : rN θ (30 * d) 0 (timeBoxGt (r : ℝ) q'') h ≤ ENNReal.ofReal e := by
    rw [← XNormRestr_eq_rN]
    exact hE
  have hcongr := restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) T' (Set.univ : Set (Mom d)) (F := fun ts k =>
      h (Function.update (ts + ![-(r : ℝ), b₁]) 1 (1 / 2) + ![(r : ℝ), q'']) k)
    (G := fun ts k => treeLeaves L γ δ LG H (ts 0) r k) fun ts hts k _ => by
    rw [hpt ts hts, hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [treeLeaves_lower_eq L γ δ LG H hfl _ k (s' := r) fun b _ => by
        rw [lone_parent_layer hX hlay b]
        exact ⟨hlow, le_rfl⟩]
  refine hcongr.symm.le.trans (htr.trans ?_)
  rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
  exact mul_le_mul_right hgate _

/-- **The middle tree factor** at the fixed times `(r + 1, r)`: a spatial profile. -/
theorem tree_middle_kernel {L γ δ θ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ : 0 ≤ θ) {r q'' : ℕ} (hq : q'' < r)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r)
    {H : LeafProfiles 1 d} {B : (Fin 1 × Path) → NNReal} (hH : LeafwiseControlled LG H B) {e : ℝ}
    (hE : XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤ ENNReal.ofReal e) :
    spatialNorm (30 * d) 0 (fun k => treeLeaves L γ δ LG H (r + 1) r k) ≤ ENNReal.ofReal e := by
  have hΛ : 30 * d ≠ 0 := by omega
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  have hp := mem_timeBoxGt_mid hq (u := (r : ℝ) + 1) ⟨by linarith, le_rfl⟩
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)
  have hlow : (q'' : ℝ) + 1 / 2 ≤ r := by linarith
  have hKs : ∀ k, treeLeaves L γ δ LG H (r + 1) ((q'' : ℝ) + 1 / 2) k =
      treeLeaves L γ δ LG H (r + 1) r k := fun k =>
    treeLeaves_lower_eq L γ δ LG H hfl _ k fun b _ => by
      rw [lone_parent_layer hX hlay b]
      exact ⟨hlow, le_rfl⟩
  have hh : ∀ k, Continuous fun ts : Fin 2 → ℝ => treeLeaves L γ δ LG H (ts 0) (ts 1) k := fun k =>
    continuous_treeLeaves_time L γ δ LG H hfl (card_lone_le_of_decodesTree hX) k (hH.summable_coset hd hL k)
  have hfin : rN θ (30 * d) 0 (timeBoxGt (r : ℝ) q'') (fun ts k =>
      treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤ ENNReal.ofReal e := by
    rw [← XNormRestr_eq_rN]
    exact hE
  obtain ⟨-, hS⟩ := spatialNorm_point_rN_le (Λ₂ := 0) hθ hΛ (B := timeBoxGt (r : ℝ) q'')
    (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) hh
    (t₀ := ![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2]) (mem_closure_interior_timeBoxGt hp) hfin
    ENNReal.ofReal_lt_top
  have hfe : (fun k => treeLeaves L γ δ LG H ((r : ℝ) + 1) r k) =
      fun k => treeLeaves L γ δ LG H (![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2] 0)
        (![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2] 1) k := by
    funext k
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hKs k]
  rw [hfe]
  exact hS

end WaveTurbulence.Flower.FiltCoh
