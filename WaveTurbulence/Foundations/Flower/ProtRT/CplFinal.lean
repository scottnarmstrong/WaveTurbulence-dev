/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.CplMain

/-! # RT-GATE (ii): the couple clause on one lattice ball (`rt_cpl_ball`)

The per-output bound `rt_cpl_perk` (`rtCr · L^a · termRb(c') · ⟨c₀⟩^{-2d}`, `a = 4` at `c' = 0`, `a = 1` at
`c' = 4d`), the local output extension (`L^{31d}`) and D3's `term_star_alg` (the one-cut size condition) give
`L^{31d + 4c' + 2 + a} · regBound ≤ L^{47d+5} · regBound`, times `⟨c₀⟩^{-2d}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The exponent budget of clause (ii). -/
theorem rt_cpl_exp {P : WTParams} {θ c' : ℝ} (hθc : PieceLoss P θ c') (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) :
    P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) * P.L ^ (if c' = 0 then 4 else 1) ≤ P.L ^ (47 * (P.d : ℝ) + 5) := by
  have hL0 : 0 < P.L := by linarith
  have hdR : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  have hpow : ∀ m : ℕ, P.L ^ m = P.L ^ (m : ℝ) := fun m => (Real.rpow_natCast _ _).symm
  split_ifs with hc
  · rw [hpow 4, ← Real.rpow_add hL0]
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    rw [hc]; push_cast; linarith
  · rw [hpow 1, ← Real.rpow_add hL0]
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    have hc' : c' = 4 * P.d := by
      rcases hθc with ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd h hc
      · exact h
    rw [hc']; push_cast; linarith

/-- **Clause (ii) on one lattice ball** (given the prefix facts). -/
theorem rt_cpl_ball {θ c' Ct₁ Ct₂ : ℝ} (hθ0 : 0 ≤ θ) (hCt₁ : 0 ≤ Ct₁) (hCt₂ : 0 ≤ Ct₂) (h1 : RtOne θ c' Ct₁)
    (h2 : RtBoth θ Ct₂) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) (hFC : TcFC P)
    (hC11 : 1 ≤ P.C₁) (hθc : PieceLoss P θ c') (hδC : P.δ * P.C₁ ≤ 1) {CL : ℝ} (hCL1 : 1 ≤ CL)
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig : termK CL (rtCr θ Ct₁ Ct₂ P.d) P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {s : ℝ} (hps : (p : ℝ) < s) (hsp : s < p + 1)
    (Rt : Fin 2 → Prop) (hRt : ∃ j, Rt j) (hboth : Rt 0 ∧ Rt 1 → PieceLoss P θ 0 ∧ c' = 0)
    (Q : RegCpl) (LG : LayeredGarden 2) (hwf : Q.wf = true) (hsz : Q.size = 2 * n) (hdec : Q.Decodes LG.garden)
    (hle : ∀ a, LG.layer a ≤ p)
    (hpin : ∀ j, Rt j → ([] : TTree.Path) ∈ (LG.garden.tree j).branching ∧ LG.layer (GNode.root LG.garden.tree j) = p)
    {q q' : ℕ} (hq : q ≤ p) (hq' : q' ≤ p) (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q') (hamb : MkSlotsO.CplAmbient p q q' Q LG)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B) (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (timeBox q q' ∩ {ts | ∀ j, Rt j → s ≤ ts j}) (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ)
        (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 5)) *
        regBound P n (LG.incoherency Q.links) * ENNReal.ofReal (leafSizeProduct LG B) *
        ENNReal.ofReal ((jbr c₀ ^ (2 * P.d))⁻¹) := by
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  set W : ℝ := (jbr c₀ ^ (2 * P.d))⁻¹ with hW
  have hW0 : 0 ≤ W := inv_nonneg.2 (pow_nonneg (jbr_pos c₀).le _)
  set Cr := rtCr θ Ct₁ Ct₂ P.d with hCrd
  have hCr : 0 ≤ Cr := by have := rtCr_one_le (θ := θ) hCt₁ hCt₂ P.d; linarith
  have hn1 : 1 ≤ n := by
    obtain ⟨j, hj⟩ := hRt
    exact tc_size_pos hwf hdec (hpin j hj).1 hsz
  set a : ℕ := if c' = 0 then 4 else 1 with ha
  set g := LG.incoherency Q.links with hg
  have hperk : ∀ k ∈ latticeBall P.L b₀ c₀, XNorm00Restr θ (timeBox (q : ℝ) q' ∩ {ts | ∀ j, Rt j → s ≤ ts j}) {k}
      (fun ts k => kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ)
        (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (Cr * (P.L ^ a * termRb P c' n g (leafSizeProduct LG B) (starCost S cω)) * W) := fun k hk =>
    (XNorm00Restr_single_le_rn θ _ _ k).trans (rt_cpl_perk hθ0 hCt₁ hCt₂ h1 h2 K hFC hC11 hθc hδC hCL1 hbig hp hn
      hps hsp Rt hRt hboth Q LG hwf hsz hdec hle hpin hq hq' hr0 hr1 hamb S ω cω hpres H B hH hk)
  refine (hLOE P.L hL1 _ b₀ c₀ _ _ hperk).trans ?_
  have hr := rb_nonneg hC1 K.hδ hL0 (n - 1) g
  have hβ : 0 ≤ P.L ^ a * W := mul_nonneg (pow_nonneg hL0 _) hW0
  have hc'0 : 0 ≤ c' := hθc.nonneg
  have halg := term_star_alg (P := P) (Cr := Cr) (CL := CL) (K := termK CL Cr P.d) (β := P.L ^ a * W)
    (CS := starCost S cω) (leaf := leafSizeProduct LG B) (r := rb P (n - 1) g) (c := 31 * (P.d : ℝ) + 4 * c' + 2)
    (c' := c') hL1 K.hδ hC1 hCr (by linarith) hβ hCS hleaf hr rfl hbig le_rfl
  have hexp := rt_cpl_exp hθc hd1 hL1
  have hLc : 0 ≤ P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) := Real.rpow_nonneg hL0 _
  have hrn : rb P n g = P.C₁ * P.δ * rb P (n - 1) g := rb_succ P hn1 g
  have hrb0 : 0 ≤ rb P n g := rb_nonneg hC1 K.hδ hL0 n g
  rw [prod_ofReal_starCost, regBound_eq_rb, ← ENNReal.ofReal_mul (mul_nonneg (by linarith) (pow_nonneg hL0 _)),
    ← ENNReal.ofReal_mul hCS, ← ENNReal.ofReal_mul (mul_nonneg hCS (Real.rpow_nonneg hL0 _)),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCS (Real.rpow_nonneg hL0 _)) hrb0),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hCS (Real.rpow_nonneg hL0 _)) hrb0) hleaf)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc CL * P.L ^ (31 * P.d) * (Cr * (P.L ^ a * termRb P c' n g (leafSizeProduct LG B) (starCost S cω)) * W)
      = CL * P.L ^ (31 * P.d) * ((P.L ^ a * W) * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG B * starCost S cω))) := by
        unfold termRb; ring
    _ ≤ starCost S cω * P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) * (P.C₁ * P.δ * rb P (n - 1) g) *
          ((P.L ^ a * W) * leafSizeProduct LG B) := halg
    _ = starCost S cω * (P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) * P.L ^ a) * rb P n g * leafSizeProduct LG B * W := by
        rw [hrn]; ring
    _ ≤ starCost S cω * P.L ^ (47 * (P.d : ℝ) + 5) * rb P n g * leafSizeProduct LG B * W := by
        have hX : 0 ≤ rb P n g * leafSizeProduct LG B * W := by positivity
        have := mul_le_mul_of_nonneg_left hexp hCS
        nlinarith [mul_le_mul_of_nonneg_right this hX]

end WaveTurbulence.Flower.ProtRT
