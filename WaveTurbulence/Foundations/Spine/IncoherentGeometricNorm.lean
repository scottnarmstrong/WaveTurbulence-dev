/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentUniform
public import WaveTurbulence.Foundations.Spine.CoherentChoiceENNReal
/-! A garden-independent geometric bound for each actual incoherent regular couple. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset NormBridgeScratch
open scoped ENNReal

theorem incoherent_SNorm_geometric (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hwf : Q.wf = true) (hsize : Q.size = 2 * n)
    (LG : LayeredGarden 2) (hQ : Q.Decodes LG.garden) (hlayer : ∀ a, LG.layer a ≤ p)
    (hq : q ≤ p) (hq' : q' ≤ p)
    (hroot : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hroot' : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hi : 1 ≤ LG.incoherency Q.links)
    (A m : ℕ) (H : LeafProfiles 2 P.d) (C₁ C₂ U : NNReal)
    (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + A : ℕ) (H l.1))
    (hlow : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C₁ : ℝ))
    (hhigh : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + A) (40 * P.d + 4 * m) (H l.1) ≤
      ENNReal.ofReal (U : ℝ))
    (hcostC₂ : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1))
    (K : ℝ) (hK : 0 ≤ K) (ho : LG.garden.order = 2 * n)
    (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ K * 8 ^ n) :
    SNorm A (4 * m) (fun k => coupleLeaves P.L P.γ P.δ LG H t s k) ≤
      ENNReal.ofReal ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * LG.incoherency Q.links)) *
        (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))) := by
  have hh := incoherent_SNorm_uniform P hsource hd hL hη hp hn Q hwf hsize LG hQ hlayer hq hq'
    hroot hroot' hi A m H C₁ C₂ U hC₁ hC₂ hc hlow hhigh hcostC₂ t s ht hs
  apply hh.trans
  have hcost := coherent_choice_cost_le LG.garden hQ.1.1 ho K C₁ C₂
    (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hchoice
  apply (mul_le_mul_of_nonneg_left hcost (by positivity)).trans_eq
  exact (ENNReal.ofReal_mul' (by positivity)).symm

end WaveTurbulence.LGSpine
