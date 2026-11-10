/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiCoupleD5
public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltWickOracle

/-! # FILT-COH (D5d-d1): the gate `FiltCoherentBoundGate` from the single-layer D5 oracles

* `D5SingleLayerBoundsA A`: the prefix form of the single-layer oracles `D5CoupleKOracleA`/`D5TreeKOracleA` at weight
  `1/4` for the filter data of a class `A L` (single-layer couples and trees in one layer, star weights, all orders
  `Nmax ≤ (log L)^A`). `D5SingleLayerBounds` is its literal version with main-interface oracles
  `D5CoupleKOracle`/`D5TreeKOracle` (class `filtScaled L`): the deliverable of D5d-d2, a HYPOTHESIS here.
* `filtCoherentBoundA_gate`: `WTPrefix (FiltCoherentBoundAtA A)` from `D5SingleLayerBoundsA A` and the stability of
  the class, assembled as milestone (a)'s `GatePlain` (the multi-layer replay `coupleKW_coherent_kernel`,
  `treeKW_coherent_kernel` at `θ = 1/4`, `θ ≤ 1/4` by monotonicity of `XNormRestr` in `θ`, `C₁ = treeG d (1/4) C`,
  `δ₀ = 1/2`, orders via `le_logPow_ordExp`).
* **`filtCoherentBoundGate_of_single : D5SingleLayerBounds → ProtDefs.FiltCoherentBoundGate`** (the target, class
  `filtScaled`).
* **`filtCoherentBoundStarGate`** (unconditional): the target's star-weighted, unfiltered branch `F = Fu = ∅` (class
  `filtNone`), from D5d-c's `single_layer_star_bounds`.
* **`filtCoherentBoundGate : ProtDefs.FiltCoherentBoundGate`** (unconditional): the hypothesis discharged by D5d-d2's
  `filt_single_layer_oracles`. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links
open WaveTurbulence.Regref

/-! ### Hypothesis forms -/

/-- **The single-layer D5 bounds in prefix form, for a filter class `A L`.** -/
@[expose] def D5SingleLayerBoundsA (A : ℝ → FiltClass) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0:ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, δ ∈ Ioc (0:ℝ) (1/2) → ∀ a : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    ∀ Nmax : ℕ, (Nmax : ℝ) ≤ Real.log L ^ a →
      D5CoupleKOracleA (A L) d L γ δ (1/4) Nmax C ∧ D5TreeKOracleA (A L) d L γ δ (1/4) Nmax C

/-- **The single-layer D5 bounds in prefix form** (the D5d-d2 deliverable): at weight `1/4`, for every order bound
`Nmax ≤ (log L)^A`, the couple and tree oracles `D5CoupleKOracle`/`D5TreeKOracle` hold with one constant `C`. -/
@[expose] def D5SingleLayerBounds : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0:ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, δ ∈ Ioc (0:ℝ) (1/2) → ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    ∀ Nmax : ℕ, (Nmax : ℝ) ≤ Real.log L ^ A →
      D5CoupleKOracle d L γ δ (1/4) Nmax C ∧ D5TreeKOracle d L γ δ (1/4) Nmax C

theorem D5SingleLayerBounds.toScaled (h : D5SingleLayerBounds) : D5SingleLayerBoundsA filtScaled := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη => ?_⟩
  obtain ⟨C, hC, H⟩ := H η hη
  refine ⟨C, hC, fun δ hδ a => ?_⟩
  obtain ⟨L₀, H⟩ := H δ hδ a
  exact ⟨L₀, fun L hL Nmax hN => ⟨(H L hL Nmax hN).1.toScaled, (H L hL Nmax hN).2.toScaled⟩⟩

/-! ### The gate for a filter class -/

/-- `ProtDefs.FiltCoherentBoundAt` for the filter data of the class `A P.L` (kernels written as `coupleKW`/`treeKW`
with the multiplier `d5Mult`). -/
@[expose] def FiltCoherentBoundAtA (A : ℝ → FiltClass) (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ),
        A P.L 2 LG.garden F M Fu Mu →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => coupleKW P.L P.γ P.δ LG H (d5Mult S ω F ann M Fu Mu) (ts 0) (ts 1) k) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ),
        A P.L 1 LG.garden F M Fu Mu →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => treeKW P.L P.γ P.δ LG H (d5Mult S ω F ann M Fu Mu) (ts 0) (ts 1) k) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B))

/-- The star product of the target as the real factor `∏ max (c a) 0`. -/
theorem prod_ofReal_eq_ofReal_starCost {ι : Type*} (S : Finset ι) (c : ι → ℝ) :
    ∏ a ∈ S, ENNReal.ofReal (c a) = ENNReal.ofReal (∏ a ∈ S, max (c a) 0) := by
  have h := ofReal_mul_prod_ofReal S c zero_le_one
  rwa [ENNReal.ofReal_one, one_mul, one_mul] at h

/-- The right side of the target from the right side of the multi-layer replay. -/
theorem target_rhs_eq (G δ β : ℝ) (n : ℕ) {ι : Type*} (S : Finset ι) (c : ι → ℝ) (hG : 0 ≤ G) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (G * (G * δ) ^ n * (β * ∏ a ∈ S, max (c a) 0)) =
      (∏ a ∈ S, ENNReal.ofReal (c a)) * ENNReal.ofReal (G * (G * δ) ^ n) * ENNReal.ofReal β := by
  have hs := starCost_nonneg S c
  rw [prod_ofReal_eq_ofReal_starCost, ← ENNReal.ofReal_mul hs, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **The gate for a stable filter class**, from its single-layer oracles. -/
theorem filtCoherentBoundA_gate (A : ℝ → FiltClass) (hst : ∀ L, (A L).Stable) (hS : D5SingleLayerBoundsA A) :
    WTPrefix (FiltCoherentBoundAtA A) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, Hs⟩ := hS d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin _ τs _ φ _ => ?_⟩
  obtain ⟨C, hC, Hs2⟩ := Hs η hη
  have hθq0 : (0:ℝ) ≤ 1/4 := by norm_num
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, -, hG1⟩ := le_treeG hd1 hθq0 hC
  refine ⟨treeG d (1/4) C, hG1, 1, one_pos, fun ν _ => ⟨1/2, by norm_num, fun δ hδ D _ _ => ?_⟩⟩
  obtain ⟨L₀, Hs3⟩ := Hs2 δ ⟨hδ.1, hδ.2⟩ (ordExp d D)
  refine ⟨1, le_rfl, max (max L₀ 2) (Real.exp 1),
    le_max_of_le_left (le_max_right _ _), fun L hL => ?_⟩
  set P : WTParams := ⟨d, γ, η, φin, τs, φ, treeG d (1/4) C, ν, δ, D, 1, L⟩ with hPdef
  have hL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : 2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hL)
  intro p hp n hn θ hθ0 hθ1
  have hN : ((P.N (p + 1) ^ 4 : ℕ) : ℝ) ≤ Real.log L ^ ((ordExp d D : ℕ) : ℝ) :=
    le_logPow_ordExp P hd1 hlog p _ le_rfl
  obtain ⟨OC, OT⟩ := Hs3 L hL₀ (P.N (p + 1) ^ 4) hN
  have hreg : regBound P n 0 = ENNReal.ofReal (treeG d (1/4) C * (treeG d (1/4) C * δ) ^ n) := by
    simp only [regBound, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    rfl
  have hδ0 : 0 ≤ δ := hδ.1.le
  have hLd : (1:ℝ) ≤ L := by linarith
  have hG0 : 0 ≤ treeG d (1/4) C := zero_le_one.trans hG1
  refine ⟨fun Q LG q q' hqq hqp hsize hcoh S ω cω hpres F ann M Fu Mu hA H B hH => ?_,
    fun X LG q q' hqq hqp hsize hcoh S ω cω hpres F ann M Fu Mu hA H B hH => ?_⟩
  · have hk := coupleKW_coherent_kernel P (θ := 1/4) OT OC (hst L) hC hd1 hLd hθq0 (by norm_num) hδ0 hqq hqp hn
      Q hsize LG hcoh H B hH S ω cω hpres F ann M Fu Mu hA
    rw [hreg, ← target_rhs_eq _ _ _ n S cω hG0 hδ0]
    exact (VineEstS3.XNormRestr_mono_theta hθ1 _ _ _ _ _).trans hk
  · have hk := treeKW_coherent_kernel (θ := 1/4) OT (hst L) hC hd1 hLd hθq0 (by norm_num) hδ0 hqq hn X hsize LG
      hcoh H B hH S ω cω hpres F ann M Fu Mu hA
    rw [hreg, ← target_rhs_eq _ _ _ n S cω hG0 hδ0]
    exact (VineEstS3.XNormRestr_mono_theta hθ1 _ _ _ _ _).trans hk

/-- Monotonicity of the parameter prefix in its body. -/
theorem prefix_mono {Q Q' : WTParams → Prop} (h : WTPrefix Q) (hQ : ∀ P, Q P → Q' P) : WTPrefix Q' := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hQ _ (H L hL)⟩

/-! ### The target -/

theorem filtCoherentBoundAt_of_scaled (P : WTParams) (h : FiltCoherentBoundAtA filtScaled P) :
    ProtDefs.FiltCoherentBoundAt P := by
  intro p hp n hn θ hθ0 hθ1
  obtain ⟨hc, ht⟩ := h p hp n hn θ hθ0 hθ1
  exact ⟨fun Q LG q q' hqq hqp hsize hcoh S ω cω hpres F ann M hM Fu Mu hMu H B hH =>
      hc Q LG q q' hqq hqp hsize hcoh S ω cω hpres F ann M Fu Mu ⟨hM, hMu⟩ H B hH,
    fun X LG q q' hqq hqp hsize hcoh S ω cω hpres F ann M hM Fu Mu hMu H B hH =>
      ht X LG q q' hqq hqp hsize hcoh S ω cω hpres F ann M Fu Mu ⟨hM, hMu⟩ H B hH⟩

/-- **`FiltCoherentBoundGate` from the single-layer D5 oracles** (the multi-layer replay and the prefix). -/
theorem filtCoherentBoundGate_of_single (hS : D5SingleLayerBounds) : ProtDefs.FiltCoherentBoundGate :=
  prefix_mono (filtCoherentBoundA_gate filtScaled filtScaled_stable hS.toScaled) filtCoherentBoundAt_of_scaled

/-! ### The star-weighted, unfiltered branch (unconditional) -/

/-- **`FiltCoherentBoundAt` at `F = Fu = ∅`**: any star weights, no filter (the flags and scales are arbitrary and
irrelevant). -/
@[expose] def FiltCoherentBoundStarAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (ann : GBranch LG.garden.tree → Bool) (M Mu : GBranch LG.garden.tree → ℝ),
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1)
          0 k (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * ProtDefs.filtWeight ∅ ann M κ *
            ProtDefs.filtWeight ∅ (fun _ => false) Mu κ)) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (ann : GBranch LG.garden.tree → Bool) (M Mu : GBranch LG.garden.tree → ℝ),
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
          (fun κ => Flower.IncTop.starWeight S ω κ * ProtDefs.filtWeight ∅ ann M κ *
            ProtDefs.filtWeight ∅ (fun _ => false) Mu κ)) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B))

@[expose] def FiltCoherentBoundStarGate : Prop := WTPrefix FiltCoherentBoundStarAt

/-- The single-layer star bounds of D5d-c as oracles of the class `filtNone`. -/
theorem d5SingleLayerBounds_none : D5SingleLayerBoundsA (fun _ => filtNone) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := single_layer_star_bounds d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη => ?_⟩
  obtain ⟨C, hC, H⟩ := H η hη
  refine ⟨C, hC, fun δ hδ a => ?_⟩
  obtain ⟨L₀, H⟩ := H δ hδ a
  refine ⟨L₀, fun L hL Nmax hN => ⟨?_, ?_⟩⟩
  · intro r m hm Q hwf hsz LG hQ hlay Hp B hH S ω cω hp F ann M Fu Mu hA
    obtain ⟨rfl, rfl⟩ := hA
    rw [d5Mult_empty]
    exact (H L hL m ((Nat.cast_le.mpr hm).trans hN)).1 r Q hwf hsz LG hQ hlay Hp B hH S ω cω hp
  · intro r q'' m hm X hq hwf hsz LG hX hlay Hp B hH S ω cω hp F ann M Fu Mu hA
    obtain ⟨rfl, rfl⟩ := hA
    rw [d5Mult_empty]
    exact (H L hL m ((Nat.cast_le.mpr hm).trans hN)).2 r q'' X hq hwf hsz LG hX hlay Hp B hH S ω cω hp

theorem filtCoherentBoundStarAt_of_none (P : WTParams) (h : FiltCoherentBoundAtA (fun _ => filtNone) P) :
    FiltCoherentBoundStarAt P := by
  intro p hp n hn θ hθ0 hθ1
  obtain ⟨hc, ht⟩ := h p hp n hn θ hθ0 hθ1
  exact ⟨fun Q LG q q' hqq hqp hsize hcoh S ω cω hpres ann M Mu H B hH =>
      hc Q LG q q' hqq hqp hsize hcoh S ω cω hpres ∅ ann M ∅ Mu ⟨rfl, rfl⟩ H B hH,
    fun X LG q q' hqq hqp hsize hcoh S ω cω hpres ann M Mu H B hH =>
      ht X LG q q' hqq hqp hsize hcoh S ω cω hpres ∅ ann M ∅ Mu ⟨rfl, rfl⟩ H B hH⟩

/-- **The star-weighted, unfiltered branch of the target** (unconditional): every coherent regular couple and paired
tree, every `0 ≤ θ ≤ 1/4`, any star weights presented with `30d`-th moments, `F = Fu = ∅`. -/
theorem filtCoherentBoundStarGate : FiltCoherentBoundStarGate :=
  prefix_mono (filtCoherentBoundA_gate (fun _ => filtNone) (fun _ => filtNone_stable) d5SingleLayerBounds_none)
    filtCoherentBoundStarAt_of_none

/-! ### The target (unconditional) -/

/-- D5d-d2's filtered single-layer oracles are the hypothesis `D5SingleLayerBounds`. -/
theorem d5SingleLayerBounds : D5SingleLayerBounds := filt_single_layer_oracles

/-- **D5d: `FiltCoherentBoundGate`** (o82 Thm 11.3 / Props 15.1–15.2 bound-only: every coherent regular couple and paired
tree, every `0 ≤ θ ≤ 1/4`, star weights and both filter layers, bound `(∏ cω) · regBound P n 0 · ∏ B_ℓ`). -/
theorem filtCoherentBoundGate : ProtDefs.FiltCoherentBoundGate :=
  filtCoherentBoundGate_of_single d5SingleLayerBounds

/-! ### Exact-type checks -/

example : ProtDefs.FiltCoherentBoundGate := filtCoherentBoundGate

example : WTPrefix ProtDefs.FiltCoherentBoundAt := filtCoherentBoundGate

example (hS : D5SingleLayerBounds) : ProtDefs.FiltCoherentBoundGate := filtCoherentBoundGate_of_single hS

example (hS : D5SingleLayerBounds) : WTPrefix ProtDefs.FiltCoherentBoundAt := filtCoherentBoundGate_of_single hS

example : WTPrefix FiltCoherentBoundStarAt := filtCoherentBoundStarGate

/-- The star branch in the literal form of `ProtDefs.FiltCoherentBoundAt` at `F = Fu = ∅`. -/
example (P : WTParams) (h : FiltCoherentBoundStarAt P) {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ) (h1 : q' ≤ q)
    (h2 : q ≤ p) (h3 : Q.size = 2 * n) (h4 : IsCoherentCoupleAt p q q' Q LG)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hω : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (ann : GBranch LG.garden.tree → Bool) (M Mu : GBranch LG.garden.tree → ℝ)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B) :
    XNormRestr θ (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1)
        0 k (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ *
          ProtDefs.filtWeight (∅ : Finset (GBranch LG.garden.tree)) ann M κ *
          ProtDefs.filtWeight (∅ : Finset (GBranch LG.garden.tree)) (fun _ => false) Mu κ)) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B) :=
  (h p hp n hn θ hθ0 hθ1).1 Q LG q q' h1 h2 h3 h4 S ω cω hω ann M Mu H B hH

end WaveTurbulence.Flower.FiltCoh
