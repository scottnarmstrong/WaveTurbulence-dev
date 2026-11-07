/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerReg.IncoherentSub
public import WaveTurbulence.Foundations.XChain.SNormPointwise
public import WaveTurbulence.Foundations.Spine.CoherentSmallParameters
public import WaveTurbulence.Foundations.Spine.IncoherentSmallParameters
/-! FLOWER-REG: pointwise bound for an arbitrary finite family of canonical regular couples.

At fixed parameters `P`, with the explicit input bounds of LG-SPINE's coherent/incoherent legs
(`CoherentLegPrefix`, `IncoherentLegPrefix`), the sum of `K_𝒬(t, k)` over a finite family `V` of canonical regular
couples of order `2n` (`n ≥ 1`) is bounded by `jbr k ^ (-4m) * (Cc + 1) * δ^{n/2}`. The coherent couples of `V`
(code incoherency `0`) go through `coherent_sub_SNorm_absorbed`, the incoherent ones through
`incoherent_sub_SNorm_absorbed`, and the spatial norm is turned into a pointwise bound by `WaveTurbulence.Induct.SNorm_pointwise`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerReg
open WaveTurbulence WaveTurbulence.LGSpine Set Finset WaveTurbulence.Reg
open scoped ENNReal

theorem norm_le_of_SNorm_le {d A B : ℕ} (F : Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : SNorm A B F ≤ ENNReal.ofReal C) (k : Mom d) :
    ‖F k‖ ≤ jbr k ^ (-(B : ℝ)) * C := by
  have hb := WaveTurbulence.Induct.SNorm_pointwise F C hC h k
  have hpos : 0 < jbr k ^ B := pow_pos (WaveTurbulence.Induct.jbr_pos k) B
  have hd : ‖F k‖ ≤ C / (jbr k ^ B) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hb)
  simpa only [Real.rpow_neg (WaveTurbulence.Induct.jbr_pos k).le, Real.rpow_natCast, div_eq_mul_inv, mul_comm] using hd

theorem regular_family_pointwise (P : WTParams)
    (hsC : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hsI : LeafwiseIncoherentDecayAt P) (hs : CoherentSmallParameters P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hC₁ : 1 ≤ P.C₁)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hn1 : 1 ≤ n)
    (m : ℕ) (hm : 0 < m) (F : ℕ → Mom P.d → ℝ) (U Kc : NNReal)
    (hKc : (1 : ℝ) ≤ Kc) (hU : (1 : ℝ) ≤ U)
    (hcF : ∀ r ≤ p, ContDiff ℝ (40 * P.d + 4 * m : ℕ) (F r))
    (hlowF : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (F r) ≤ ENNReal.ofReal P.C₁)
    (hhighF : ∀ r ≤ p, SNormR (40 * P.d + 4 * m) (40 * P.d + 4 * m) (F r) ≤ ENNReal.ofReal (U : ℝ))
    (hhighP : SNormR (40 * P.d + 1 + 4 * m) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + 4 * m) * U) ≤ Kc)
    (D : ℝ) (hD : 1 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ (4 * m) *
        (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2)
    (hlargeI : D * (Kc : ℝ) ^ (4 * m + 4 * m) * (2 : ℝ) ^ (9 * p) *
      P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (k : Mom P.d)
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsRegularCouple LG.garden) :
    ‖∑ LG ∈ V, KQ P.L P.γ P.δ F LG t k‖ ≤
      jbr k ^ (-(4 * m : ℝ)) * (D * P.C₁ * (Kc : ℝ) ^ (4 * m + 4 * m) + 1) * P.δ ^ ((n : ℝ) / 2) := by
  classical
  have hδ := hs.delta_pos
  have hη0 := hs.eta_pos.le
  have ha : 0 < P.gamma1 - Real.sqrt P.η :=
    lt_of_le_of_lt (by positivity : 0 ≤ 2 * P.η ^ 20) hs.exponent_reserve
  have hA : 4 * m ≠ 0 := by omega
  have hsplit := (Finset.sum_filter_add_sum_filter_not V IsCoherentCouple
    (fun LG => KQ P.L P.γ P.δ F LG t k)).symm
  have hcoh : ∀ LG ∈ V.filter IsCoherentCouple,
      IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsCoherentCouple LG := fun LG hLG => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hLG
    exact ⟨(hV LG h1).1, (hV LG h1).2.1, h2⟩
  have hinc : ∀ LG ∈ V.filter (fun LG => ¬ IsCoherentCouple LG),
      IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsRegularCouple LG.garden ∧
        ¬ IsCoherentCouple LG := fun LG hLG => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hLG
    exact ⟨(hV LG h1).1, (hV LG h1).2.1, (hV LG h1).2.2, h2⟩
  have hDnn : 0 ≤ D := by linarith
  have hcohS := coherent_sub_SNorm_absorbed P hsC hL hδ hC₁ hs.eta_le hd hη0 ha hp hn hn1
    (4 * m) m hA F U Kc hKc hU (hlowF p le_rfl) hhighP hmod D hDnn hchoice hs.tail_delta t ht
    (V.filter IsCoherentCouple) hcoh
  have hincS := incoherent_sub_SNorm_absorbed P hsI hd hL hη0 hC₁ hδ.le hp hn (4 * m) m hA F
    ⟨P.C₁, by linarith⟩ Kc U (show (1 : ℝ) ≤ P.C₁ from hC₁) hKc hcF hlowF hhighF hmod t ht D hDnn hchoice
    (V.filter (fun LG => ¬ IsCoherentCouple LG)) hinc hr hn1
    (incoherent_smallness_of_coherent P hC₁ hs) 0 (by simpa using hlargeI)
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hKnn := NNReal.coe_nonneg Kc
  have h1 := norm_le_of_SNorm_le _ _ (by positivity) hcohS k
  have h2 := norm_le_of_SNorm_le _ _ (by positivity) hincS k
  have hcast : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
  rw [hcast] at h1 h2
  simp only [neg_zero, Real.rpow_zero, mul_one] at h2
  calc _ ≤ jbr k ^ (-(4 * (m : ℝ))) * (D * P.C₁ * (Kc : ℝ) ^ (4 * m + 4 * m) * P.δ ^ ((n : ℝ) / 2)) +
        jbr k ^ (-(4 * (m : ℝ))) * (P.δ ^ ((n : ℝ) / 2)) := add_le_add h1 h2
    _ = _ := by ring

end WaveTurbulence.FlowerReg
