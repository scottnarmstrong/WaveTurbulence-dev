/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiCoupleGate
public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ThetaMono
public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.Orders

/-! # FILT-COH milestone (a): the unfiltered, unweighted branch of `FiltCoherentBoundAt`

`FiltCoherentBoundPlainAt` is `ProtDefs.FiltCoherentBoundAt` with empty star set and empty filter layers
(`S = F = Fu = ∅`, so the multiplier is `1`): every coherent regular couple and paired tree, every
`0 ≤ θ ≤ 1/4`, bound `regBound P n 0 · ∏ B_ℓ` (no `L` power). This is F-D0-5: `X^{1/4}` for unfiltered regular
objects, which main lacks. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links
open WaveTurbulence.Regref

/-- **Milestone (a)**: `FiltCoherentBoundAt` at `S = ∅`, `F = Fu = ∅` (the star family `ω`, the flags and the
scales are arbitrary and irrelevant). -/
@[expose] def FiltCoherentBoundPlainAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      ∀ (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ) (ann : GBranch LG.garden.tree → Bool)
        (M Mu : GBranch LG.garden.tree → ℝ),
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1)
          0 k (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight ∅ ω κ * ProtDefs.filtWeight ∅ ann M κ *
            ProtDefs.filtWeight ∅ (fun _ => false) Mu κ)) ≤
        regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      ∀ (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ) (ann : GBranch LG.garden.tree → Bool)
        (M Mu : GBranch LG.garden.tree → ℝ),
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
          (fun κ => Flower.IncTop.starWeight ∅ ω κ * ProtDefs.filtWeight ∅ ann M κ *
            ProtDefs.filtWeight ∅ (fun _ => false) Mu κ)) ≤
        regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B))

@[expose] def FiltCoherentBoundPlainGate : Prop := WTPrefix FiltCoherentBoundPlainAt

/-- With the multiplier `1`, the weighted kernel is the leafwise kernel. -/
theorem kernelLeavesW_unit {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (hm : ∀ k, m k = 1) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = kernelLeaves L γ δ LG H up s k₀ nroot nfl := by
  unfold Flower.Stage1W.kernelLeavesW kernelLeaves
  simp only [hm, one_mul]

theorem emptyMultiplier_eq_one {w d : ℕ} {G : Garden w} (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ) (κ : GNode G.tree → Mom d) :
    Flower.IncTop.starWeight ∅ ω κ * ProtDefs.filtWeight ∅ ann M κ *
      ProtDefs.filtWeight ∅ (fun _ => false) Mu κ = 1 := by
  simp [Flower.IncTop.starWeight, ProtDefs.filtWeight]

/-- **Milestone (a) of D5d.** -/
theorem filtCoherentBoundPlainGate : FiltCoherentBoundPlainGate := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, Hs⟩ := single_layer_bounds d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin _ τs _ φ _ => ?_⟩
  obtain ⟨C, hC, Hs2⟩ := Hs η hη
  have hθq0 : (0:ℝ) ≤ 1/4 := by norm_num
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hCG', -, hG1⟩ := le_treeG hd1 hθq0 hC
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
  have hord : ∀ m, m ≤ P.N (p + 1) ^ 4 → (m : ℝ) ≤ Real.log L ^ ((ordExp d D : ℕ) : ℝ) := fun m hm =>
    le_logPow_ordExp P hd1 hlog p m hm
  have OT : TreeKOracle d L γ δ (1/4) (P.N (p + 1) ^ 4) C := by
    intro r q'' m hq hm X hwf hsz LG hX hlay H B hH
    exact (Hs3 L hL₀ m (hord m hm)).2 r q'' X hq hwf hsz LG hX hlay H B hH
  have OC : CoupleKOracle d L γ δ (1/4) (P.N (p + 1) ^ 4) C := by
    intro r m hm Q hwf hsz LG hQ hlay H B hH
    exact (Hs3 L hL₀ m (hord m hm)).1 r Q hwf hsz LG hQ hlay H B hH
  have hreg : regBound P n 0 = ENNReal.ofReal (treeG d (1/4) C * (treeG d (1/4) C * δ) ^ n) := by
    simp only [regBound, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    rfl
  have hδ0 : 0 ≤ δ := hδ.1.le
  have hLd : (1:ℝ) ≤ L := by linarith
  refine ⟨fun Q LG q q' hqq hqp hsize hcoh ω ann M Mu H B hH => ?_,
    fun X LG q q' hqq hqp hsize hcoh ω ann M Mu H B hH => ?_⟩
  · have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have he : (fun (ts : Fin 2 → ℝ) (k : Mom d) => Flower.Stage1W.kernelLeavesW L γ δ LG H
        (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
        (fun κ => Flower.IncTop.starWeight ∅ ω κ * ProtDefs.filtWeight ∅ ann M κ *
          ProtDefs.filtWeight ∅ (fun _ => false) Mu κ)) =
        fun ts k => coupleLeaves L γ δ LG H (ts 0) (ts 1) k := by
      funext ts k
      rw [kernelLeavesW_unit _ _ _ _ _ _ _ _ _ _ _ (emptyMultiplier_eq_one ω ann M Mu)]
      rfl
    show XNormRestr θ (30 * d) (30 * d) (timeBox q q') Set.univ (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H
        (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
        (fun κ => Flower.IncTop.starWeight ∅ ω κ * ProtDefs.filtWeight ∅ ann M κ *
          ProtDefs.filtWeight ∅ (fun _ => false) Mu κ)) ≤ _
    rw [he, hreg, ← ENNReal.ofReal_mul (by positivity)]
    refine (VineEstS3.XNormRestr_mono_theta hθ1 _ _ _ _ _).trans ?_
    exact couple_coherent_kernel P (θ := 1/4) OT OC hC hd1 hLd hθq0 (by norm_num) hδ0 hqq hqp hn Q hsize LG
      hcoh H B hH
  · have hβ0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have he : (fun (ts : Fin 2 → ℝ) (k : Mom d) => Flower.Stage1W.kernelLeavesW L γ δ LG H
        (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (fun κ => Flower.IncTop.starWeight ∅ ω κ * ProtDefs.filtWeight ∅ ann M κ *
          ProtDefs.filtWeight ∅ (fun _ => false) Mu κ)) =
        fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k := by
      funext ts k
      rw [kernelLeavesW_unit _ _ _ _ _ _ _ _ _ _ _ (emptyMultiplier_eq_one ω ann M Mu)]
      rfl
    show XNormRestr θ (30 * d) 0 (timeBoxGt q q') Set.univ (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H
        (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (fun κ => Flower.IncTop.starWeight ∅ ω κ * ProtDefs.filtWeight ∅ ann M κ *
          ProtDefs.filtWeight ∅ (fun _ => false) Mu κ)) ≤ _
    rw [he, hreg, ← ENNReal.ofReal_mul (by positivity)]
    refine (VineEstS3.XNormRestr_mono_theta hθ1 _ _ _ _ _).trans ?_
    exact tree_coherent_kernel OT hC hd1 hLd hθq0 (by norm_num) hδ0 hqq hn X hsize LG hcoh H B hH

end WaveTurbulence.Flower.FiltCoh
