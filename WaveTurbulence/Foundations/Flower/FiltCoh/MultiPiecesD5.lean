/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiStep
public import WaveTurbulence.Foundations.Flower.FiltCoh.D5Oracle

/-! # FILT-COH (D5d-d1): traces of multiplied single-layer kernel bounds

Milestone (a)'s `MultiPieces` (main's PL2330 piece bounds, for the kernel itself) for the multiplied kernels
`kernelLeavesW … m` with a bounded decoration multiplier `m` (the D5 multiplier `d5Mult` is bounded by
`norm_d5Mult_le`):
* `coupleKW`, `treeKW`: the multiplied couple / paired-tree kernels at times `(t, s)`;
* `kernelLeavesW_congr_domain`, `coupleKW_upper_eq`, `treeKW_upper_eq`, `treeKW_lower_eq`: main's time freezing
  (`PL234.TimeIndep`) with a multiplier (the multiplier sees no times);
* `continuous_coupleKW_time`, `continuous_coupleKW_snd`, `continuous_treeKW_time`, `continuous_treeKW_snd`;
* `coupleKW_bottom_kernel`, `treeKW_bottom_kernel`, `treeKW_top_kernel`, `treeKW_middle_kernel`. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.NormBridgeScratch
open WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

/-- The multiplied couple kernel at times `(t, s)` (`+` tree at `t`, `-` tree at `s`). -/
@[expose] noncomputable def coupleKW (L γ δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (t s : ℝ) (k : Mom d) : ℂ :=
  Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0 m

/-- The multiplied paired-tree kernel at times `(t, s)` (branching nodes at `t`, lone leaf at `s`). -/
@[expose] noncomputable def treeKW (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (t s : ℝ) (k : Mom d) : ℂ :=
  Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0 m

/-! ### Time freezing -/

/-- **Equal time domains give equal multiplied kernels** (no flower parents). -/
theorem kernelLeavesW_congr_domain {w : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b) {up up' : GBranch LG.garden.tree → ℝ} {s s' : ℝ}
    (hD : kDomain LG up s = kDomain LG up' s') (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m =
      Flower.Stage1W.kernelLeavesW L γ δ LG H up' s' k₀ nroot nfl m := by
  have hE : ∀ τ, LG.garden.extendTime s τ = LG.garden.extendTime s' τ := fun τ =>
    extendTime_congr_s hfl s s' τ
  simp only [Flower.Stage1W.kernelLeavesW, phaseIntegral, hD, hE]

/-- **The `+` time of a multiplied couple above its `+` tree's layers.** -/
theorem coupleKW_upper_eq (L γ δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b) {t t' : ℝ} (s : ℝ) (k : Mom d)
    (ht : ∀ b : GBranch LG.garden.tree, b.1.1 = 0 → (LG.layer b.toNode : ℝ) + 1 ≤ t ∧
      (LG.layer b.toNode : ℝ) + 1 ≤ t') :
    coupleKW L γ δ LG H m t s k = coupleKW L γ δ LG H m t' s k := by
  unfold coupleKW
  refine kernelLeavesW_congr_domain L γ δ LG H hfl ?_ k _ _ m
  ext τ
  simp only [kDomain, mem_ofPred_eq]
  refine forall_congr' fun b => ?_
  by_cases hb : b.1.1 = 0
  · obtain ⟨h1, h2⟩ := ht b hb
    simp only [hb, ↓reduceIte]
    constructor
    · rintro ⟨a1, a2, a3, -, a5, a6⟩
      exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h2, a5, a6⟩
    · rintro ⟨a1, a2, a3, -, a5, a6⟩
      exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h1, a5, a6⟩
  · simp only [hb, ↓reduceIte]

/-- **The upper time of a multiplied tree above its layers.** -/
theorem treeKW_upper_eq (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b) {t t' : ℝ} (s : ℝ) (k : Mom d)
    (ht : ∀ b : GBranch LG.garden.tree, (LG.layer b.toNode : ℝ) + 1 ≤ t ∧
      (LG.layer b.toNode : ℝ) + 1 ≤ t') :
    treeKW L γ δ LG H m t s k = treeKW L γ δ LG H m t' s k := by
  unfold treeKW
  refine kernelLeavesW_congr_domain L γ δ LG H hfl ?_ k _ _ m
  ext τ
  simp only [kDomain, mem_ofPred_eq]
  refine forall_congr' fun b => ?_
  obtain ⟨h1, h2⟩ := ht b
  constructor
  · rintro ⟨a1, a2, a3, -, a5, a6⟩
    exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h2, a5, a6⟩
  · rintro ⟨a1, a2, a3, -, a5, a6⟩
    exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h1, a5, a6⟩

/-- **The lone-leaf time of a multiplied tree below its lone parent's layer.** -/
theorem treeKW_lower_eq (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b) (t : ℝ) {s s' : ℝ} (k : Mom d)
    (hs : ∀ b : GBranch LG.garden.tree, LG.garden.IsLoneParent b →
      s ≤ LG.layer b.toNode ∧ s' ≤ LG.layer b.toNode) :
    treeKW L γ δ LG H m t s k = treeKW L γ δ LG H m t s' k := by
  unfold treeKW
  refine kernelLeavesW_congr_domain L γ δ LG H hfl ?_ k _ _ m
  ext τ
  simp only [kDomain, mem_ofPred_eq]
  refine forall_congr' fun b => ?_
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a1, a2, a3, a4, a5, fun hb => lt_of_le_of_lt (hs b hb).2 a1⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a1, a2, a3, a4, a5, fun hb => lt_of_le_of_lt (hs b hb).1 a1⟩

/-! ### Time continuity -/

theorem continuous_coupleKW_time (L γ δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (hplain : LG.garden.IsPlain) (m : (GNode LG.garden.tree → Mom d) → ℂ) (Mb : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ Mb)
    (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => coupleKW L γ δ LG H m (ts 0) (ts 1) k) := by
  have hc := Flower.Stage1WNoVine.continuous_kernelLeavesW_time L γ δ H LG k (fun _ => 0) 0 m Mb hm
    (no_flowerParent_of_plain LG.garden hplain) (card_lone_le_one_of_plain LG.garden hplain) hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) :=
    fun ts => ((fun b => if b.1.1 = 0 then ts 0 else ts 1), 0)
  have hu : Continuous u := by
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro b
    by_cases h : b.1.1 = 0
    · simpa only [h, ite_true] using (continuous_apply (0 : Fin 2))
    · simpa only [h, ite_false] using (continuous_apply (1 : Fin 2))
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    Flower.Stage1W.kernelLeavesW L γ δ LG H x.1 x.2 k (fun _ => 0) 0 m) ∘ u)
  exact hc.comp hu

theorem continuous_coupleKW_snd (L γ δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (hplain : LG.garden.IsPlain) (m : (GNode LG.garden.tree → Mom d) → ℂ) (Mb : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ Mb)
    (c : ℝ) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous fun ts : Fin 2 → ℝ => coupleKW L γ δ LG H m c (ts 1) k := by
  have hc := continuous_coupleKW_time L γ δ LG H hplain m Mb hm k hF
  have hg : Continuous (fun ts : Fin 2 → ℝ => (![c, ts 1] : Fin 2 → ℝ)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_apply 1
  exact (hc.comp hg).congr fun _ => rfl

theorem continuous_treeKW_time (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (m : (GNode LG.garden.tree → Mom d) → ℂ) (Mb : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ Mb)
    (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => treeKW L γ δ LG H m (ts 0) (ts 1) k) := by
  have hc := Flower.Stage1WNoVine.continuous_kernelLeavesW_time L γ δ H LG k (fun _ => 0) 0 m Mb hm
    (noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)) (card_lone_le_of_decodesTree hX) hF
  have hu : Continuous (fun ts : Fin 2 → ℝ =>
      ((fun _ : GBranch LG.garden.tree => ts 0), ts 1)) :=
    (continuous_pi fun _ => continuous_apply 0).prodMk (continuous_apply 1)
  exact (hc.comp hu).congr fun _ => rfl

theorem continuous_treeKW_snd (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (m : (GNode LG.garden.tree → Mom d) → ℂ) (Mb : ℝ) (hm : ∀ κ, ‖m κ‖ ≤ Mb)
    (c : ℝ) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous fun ts : Fin 2 → ℝ => treeKW L γ δ LG H m c (ts 1) k := by
  have hc := continuous_treeKW_time L γ δ LG H hX m Mb hm k hF
  have hg : Continuous (fun ts : Fin 2 → ℝ => (![c, ts 1] : Fin 2 → ℝ)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_apply 1
  exact (hc.comp hg).congr fun _ => rfl

/-! ### The pieces -/

/-- **The bottom multiplied couple**, frozen at `t = q' + 1`, as a function of `s`. -/
theorem coupleKW_bottom_kernel {L γ δ θ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ : 0 ≤ θ) {q' : ℕ}
    {Q : RegCpl} {LG : LayeredGarden 2} (hQ : Q.Decodes LG.garden) {H : LeafProfiles 2 d}
    {B : (Fin 2 × Path) → NNReal} (hH : LeafwiseControlled LG H B)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) {Mb : ℝ} (hm : ∀ κ, ‖m κ‖ ≤ Mb) {e : ℝ}
    (hE : XNormRestr θ (30 * d) (30 * d) (timeBox q' q') Set.univ
      (fun ts k => coupleKW L γ δ LG H m (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox) :
    rN θ (30 * d) (30 * d) T' (fun ts k => coupleKW L γ δ LG H m (q' + 1) (ts 1) k) ≤
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
  set h : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k => coupleKW L γ δ LG H m (ts 0) (ts 1) k with hh
  have hc : ∀ k, Continuous fun ts => h ts k := fun k =>
    continuous_coupleKW_time L γ δ LG H hplain m Mb hm k (hH.summable_coset hd hL k)
  have htr := rN_trace_transport (Λ₂ := 30 * d) hΛ hθ (B := timeBox (q' : ℝ) q') (T' := T') h hc
    ![(q' : ℝ), q'] ![b₀, -(q' : ℝ)] 0 1 hT' (trace_line_couple q')
  have hgate : rN θ (30 * d) (30 * d) (timeBox (q' : ℝ) q') h ≤ ENNReal.ofReal e := by
    rw [← XNormRestr_eq_rN]
    exact hE
  have hcongr := restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 30 * d) T' (Set.univ : Set (Mom d))
    (F := fun ts k => h (Function.update (ts + ![b₀, -(q' : ℝ)]) 0 1 + ![(q' : ℝ), q']) k)
    (G := fun ts k => coupleKW L γ δ LG H m (q' + 1) (ts 1) k) fun ts hts k _ => by
    rw [hpt ts hts, hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine hcongr.symm.le.trans (htr.trans ?_)
  rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
  exact mul_le_mul_right hgate _

/-- **The bottom multiplied tree factor**, frozen at `t = r + 1`, as a function of `s`. -/
theorem treeKW_bottom_kernel {L γ δ θ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ : 0 ≤ θ) {r q'' : ℕ} (hq : q'' ≤ r)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden) {H : LeafProfiles 1 d}
    {B : (Fin 1 × Path) → NNReal} (hH : LeafwiseControlled LG H B)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) {Mb : ℝ} (hm : ∀ κ, ‖m κ‖ ≤ Mb) {e : ℝ}
    (hE : XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeKW L γ δ LG H m (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q'' : ℝ)] ∈ Layered.unitBox) :
    rN θ (30 * d) 0 T' (fun ts k => treeKW L γ δ LG H m (r + 1) (ts 1) k) ≤
      ENNReal.ofReal (Ktr θ * e) := by
  have hΛ : 30 * d ≠ 0 := by omega
  have hpt : ∀ ts ∈ T', Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q''] =
      ![(r : ℝ) + 1, ts 1] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      try ring
    · simp [Function.update]
      try rfl
  set h : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k => treeKW L γ δ LG H m (ts 0) (ts 1) k with hh
  have hc : ∀ k, Continuous fun ts => h ts k := fun k =>
    continuous_treeKW_time L γ δ LG H hX m Mb hm k (hH.summable_coset hd hL k)
  have htr := rN_trace_transport (Λ₂ := 0) hΛ hθ (B := timeBoxGt (r : ℝ) q'') (T' := T') h hc
    ![(r : ℝ), q''] ![b₀, -(q'' : ℝ)] 0 1 hT' (trace_line_tree_bot hq)
  have hgate : rN θ (30 * d) 0 (timeBoxGt (r : ℝ) q'') h ≤ ENNReal.ofReal e := by
    rw [← XNormRestr_eq_rN]
    exact hE
  have hcongr := restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) T' (Set.univ : Set (Mom d))
    (F := fun ts k => h (Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q'']) k)
    (G := fun ts k => treeKW L γ δ LG H m (r + 1) (ts 1) k) fun ts hts k _ => by
    rw [hpt ts hts, hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine hcongr.symm.le.trans (htr.trans ?_)
  rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
  exact mul_le_mul_right hgate _

/-- **The top multiplied tree factor**, frozen at `s = r`, as a function of `t`. -/
theorem treeKW_top_kernel {L γ δ θ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ : 0 ≤ θ) {r q'' : ℕ} (hq : q'' < r)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r)
    {H : LeafProfiles 1 d} {B : (Fin 1 × Path) → NNReal} (hH : LeafwiseControlled LG H B)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) {Mb : ℝ} (hm : ∀ κ, ‖m κ‖ ≤ Mb) {e : ℝ}
    (hE : XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeKW L γ δ LG H m (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (T' : Set (Fin 2 → ℝ)) (b₁ : ℝ) (hT' : ∀ ts ∈ T', ts + ![-(r : ℝ), b₁] ∈ Layered.unitBox) :
    rN θ (30 * d) 0 T' (fun ts k => treeKW L γ δ LG H m (ts 0) r k) ≤ ENNReal.ofReal (Ktr θ * e) := by
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
  set h : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k => treeKW L γ δ LG H m (ts 0) (ts 1) k with hh
  have hc : ∀ k, Continuous fun ts => h ts k := fun k =>
    continuous_treeKW_time L γ δ LG H hX m Mb hm k (hH.summable_coset hd hL k)
  have htr := rN_trace_transport (Λ₂ := 0) hΛ hθ (B := timeBoxGt (r : ℝ) q'') (T' := T') h hc
    ![(r : ℝ), q''] ![-(r : ℝ), b₁] 1 (1 / 2) hT' (trace_line_tree hq)
  have hgate : rN θ (30 * d) 0 (timeBoxGt (r : ℝ) q'') h ≤ ENNReal.ofReal e := by
    rw [← XNormRestr_eq_rN]
    exact hE
  have hcongr := restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) T' (Set.univ : Set (Mom d)) (F := fun ts k =>
      h (Function.update (ts + ![-(r : ℝ), b₁]) 1 (1 / 2) + ![(r : ℝ), q'']) k)
    (G := fun ts k => treeKW L γ δ LG H m (ts 0) r k) fun ts hts k _ => by
    rw [hpt ts hts, hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [treeKW_lower_eq L γ δ LG H m hfl _ k (s' := r) fun b _ => by
        rw [lone_parent_layer hX hlay b]
        exact ⟨hlow, le_rfl⟩]
  refine hcongr.symm.le.trans (htr.trans ?_)
  rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
  exact mul_le_mul_right hgate _

/-- **The middle multiplied tree factor** at the fixed times `(r + 1, r)`: a spatial profile. -/
theorem treeKW_middle_kernel {L γ δ θ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ : 0 ≤ θ) {r q'' : ℕ} (hq : q'' < r)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r)
    {H : LeafProfiles 1 d} {B : (Fin 1 × Path) → NNReal} (hH : LeafwiseControlled LG H B)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) {Mb : ℝ} (hm : ∀ κ, ‖m κ‖ ≤ Mb) {e : ℝ}
    (hE : XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeKW L γ δ LG H m (ts 0) (ts 1) k) ≤ ENNReal.ofReal e) :
    spatialNorm (30 * d) 0 (fun k => treeKW L γ δ LG H m (r + 1) r k) ≤ ENNReal.ofReal e := by
  have hΛ : 30 * d ≠ 0 := by omega
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  have hp := mem_timeBoxGt_mid hq (u := (r : ℝ) + 1) ⟨by linarith, le_rfl⟩
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)
  have hlow : (q'' : ℝ) + 1 / 2 ≤ r := by linarith
  have hKs : ∀ k, treeKW L γ δ LG H m (r + 1) ((q'' : ℝ) + 1 / 2) k =
      treeKW L γ δ LG H m (r + 1) r k := fun k =>
    treeKW_lower_eq L γ δ LG H m hfl _ k fun b _ => by
      rw [lone_parent_layer hX hlay b]
      exact ⟨hlow, le_rfl⟩
  have hh : ∀ k, Continuous fun ts : Fin 2 → ℝ => treeKW L γ δ LG H m (ts 0) (ts 1) k := fun k =>
    continuous_treeKW_time L γ δ LG H hX m Mb hm k (hH.summable_coset hd hL k)
  have hfin : rN θ (30 * d) 0 (timeBoxGt (r : ℝ) q'') (fun ts k =>
      treeKW L γ δ LG H m (ts 0) (ts 1) k) ≤ ENNReal.ofReal e := by
    rw [← XNormRestr_eq_rN]
    exact hE
  obtain ⟨-, hS⟩ := spatialNorm_point_rN_le (Λ₂ := 0) hθ hΛ (B := timeBoxGt (r : ℝ) q'')
    (fun ts k => treeKW L γ δ LG H m (ts 0) (ts 1) k) hh
    (t₀ := ![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2]) (mem_closure_interior_timeBoxGt hp) hfin
    ENNReal.ofReal_lt_top
  have hfe : (fun k => treeKW L γ δ LG H m ((r : ℝ) + 1) r k) =
      fun k => treeKW L γ δ LG H m (![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2] 0)
        (![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2] 1) k := by
    funext k
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hKs k]
  rw [hfe]
  exact hS

end WaveTurbulence.Flower.FiltCoh
