/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceApp
public import WaveTurbulence.Foundations.XChain.SNormAddBounds
public import WaveTurbulence.Foundations.Spine.InputLeafCount
public import WaveTurbulence.Foundations.RegStruct.CodeOrders

/-!
# TARGET Prop 6.1 (L1097–1111): `CoherentApproximationGate`

The layer-indexed inputs `F_r = φ(δr) + R_r` are the leaf profiles `H_F z = F(𝔏 z)` (`SliceApp`), each bounded in
`𝔖^{40d,40d}` by `b = β_φ + 1` (`input_bound`). The leafwise gate (`lcaBody_of`) at `H_F`, with leaf cost
`b^{#inputs} ≤ b^{4n+4}`, gives the common gate at `C₁ = g61 · b⁴`:

* **`coherentApproximationGate`**: `RegularAsymptoticsGate → LeafwiseRegularAsymptoticsGate →
  CoherentApproximationGate`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- **The size of the layer inputs**: `‖F_r‖_{𝔖^{40d,40d}} ≤ β_φ + 1` for `r ≤ p < 𝔇`. -/
theorem input_bound (P : WTParams) (hS : Standing P (η61 P.d P.γ)) {p : ℕ} (hp : p < P.D)
    {R : ℕ → Mom P.d → ℝ} (hR : ∀ r ≤ p, InputRemainder P (R r) r) {r : ℕ} (hr : r ≤ p) :
    SNormR (40 * P.d) (40 * P.d) (inputsF P R r) ≤ ENNReal.ofReal (βφ (preC₁ P) + 1) := by
  have hA : 40 * P.d ≠ 0 := by have := hS.d_ge; omega
  have hδ : 0 ≤ P.δ := hS.δ_pos.le
  have hτ : P.δ * r ∈ Icc 0 (preC₁ P).τstar := by
    refine ⟨mul_nonneg hδ (Nat.cast_nonneg r), ?_⟩
    show P.δ * r ≤ P.τstar
    rw [hS.τstar_eq]
    have : (r : ℝ) ≤ P.D := by exact_mod_cast (hr.trans hp.le)
    nlinarith
  have hφ : SNormR (40 * P.d) (40 * P.d) (P.φ (P.δ * r)) ≤ ENNReal.ofReal (βφ (preC₁ P)) :=
    SNormR_le_βφ (preC₁ P) hS.wke.1 hτ
  have hRr : SNormR (40 * P.d) (40 * P.d) (R r) ≤ ENNReal.ofReal 1 := by
    refine (hR r hr).trans (ENNReal.ofReal_le_ofReal ?_)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hS.L_ge]) (neg_nonpos.mpr (theta_nonneg P r))
  unfold SNormR at hφ hRr ⊢
  have e : (fun k => ((inputsF P R r k : ℝ) : ℂ)) =
      (fun k => ((P.φ (P.δ * r) k : ℝ) : ℂ)) + fun k => ((R r k : ℝ) : ℂ) := by
    funext k
    simp [inputsF]
  rw [e]
  exact SNorm_add_bound _ _ (contDiff_of_SNorm_le hA _ _ hφ) (contDiff_of_SNorm_le hA _ _ hRr) _ _
    (by linarith [one_le_βφ (preC₁ P)]) zero_le_one hφ hRr

/-- The nodes of a coherent couple carrier are in layers `≤ p`. -/
theorem coherentCouple_layer_le {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} (hqq : q' ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q q' Q LG) (z : GNode LG.garden.tree) : LG.layer z ≤ p := by
  have hQ := hcoh.2.1
  cases Q with
  | triv => rw [layers_type1 hqq hcoh rfl z]; omega
  | type1 c Q₁ Q₂ Q₃ => rw [layers_type1 hqq hcoh rfl z]; omega
  | type2 Xp Xm Qlp =>
    have F := cohFacts_of_coherent hqq hqp hcoh
    rw [← layerAt_node]
    have ha := addrExt_mem_cplNodes hQ ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) z
    have hae : addrExt (if z.1.1 = 0 then ((0 : Fin 2), ([] : Path)) else ((1 : Fin 2), ([] : Path))) z.1.2 =
        z.1 := by
      obtain ⟨⟨j, q⟩, _⟩ := z
      fin_cases j <;> simp [addrExt]
    rw [hae] at ha
    rcases mem_cplNodes_type2.mp ha with h | h | h
    · exact F.high _ h
    · rw [F.minus _ h]; omega
    · rw [F.lp _ h]; omega

/-- The nodes of a coherent tree carrier are in layers `≤ q`. -/
theorem coherentTree_layer_le {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1} (hqq : q' ≤ q)
    (hcoh : IsCoherentTreeAt p q q' X LG) (z : GNode LG.garden.tree) : LG.layer z ≤ q := by
  have F := treeCohFacts_of_coherent hcoh
  rw [← layerAt_node]
  rcases addrExt_mem_chainNodes F.dec ((0 : Fin 1), []) z with h | h
  · have e : addrExt ((0 : Fin 1), ([] : Path)) z.1.2 = z.1 := by
      obtain ⟨⟨j, q⟩, _⟩ := z
      fin_cases j
      simp [addrExt]
    rw [e] at h
    exact F.high _ h
  · have e : z.1 = ((0 : Fin 1), X.lonePath) := Prod.ext (Subsingleton.elim _ _) h
    rw [e, F.lone]
    exact hqq

theorem card_inputLeaves_tree_le {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) {n : ℕ}
    (hsize : X.size = 2 * n) : (inputLeaves G).card ≤ 4 * n + 1 := by
  have h1 := Finset.card_le_univ (inputLeaves G)
  rw [Comb.card_gleaf, Fin.sum_univ_one, hX.1, code_plug_order] at h1
  simp only [TTree.order, add_zero] at h1
  omega

/-! ### Constants -/

/-- The constant of the common Prop 6.1. -/
noncomputable def gC (P₀ : WTParams) (x y : ℝ) : ℝ := g61 P₀ x y * (βφ P₀ + 1) ^ 4

theorem one_le_gC (P₀ : WTParams) (x y : ℝ) : 1 ≤ gC P₀ x y := by
  unfold gC
  have h1 : 1 ≤ g61 P₀ x y := le_max_left _ _
  have h2 : (1 : ℝ) ≤ (βφ P₀ + 1) ^ 4 := one_le_pow₀ (by linarith [one_le_βφ P₀])
  nlinarith

theorem regBound_absorb (P : WTParams) {G b : ℝ} (hG : 0 ≤ G) (hb : 1 ≤ b) (hδ : 0 ≤ P.δ) (hL : 0 < P.L)
    {n c : ℕ} (hc : c ≤ 4 * n + 4) :
    regBound { P with C₁ := G } n 1 * ENNReal.ofReal (b ^ c) ≤ regBound { P with C₁ := G * b ^ 4 } n 1 := by
  have hΛ : 0 ≤ gainΛ P := Real.rpow_nonneg hL.le _
  have h1 : regBound { P with C₁ := G } n 1 = ENNReal.ofReal (G * (G * P.δ) ^ n * gainΛ P) := rfl
  have h2 : regBound { P with C₁ := G * b ^ 4 } n 1 = ENNReal.ofReal (G * b ^ 4 * (G * b ^ 4 * P.δ) ^ n * gainΛ P) :=
    rfl
  rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hbc : b ^ c ≤ b ^ (4 * n + 4) := pow_le_pow_right₀ hb hc
  have e : G * b ^ 4 * (G * b ^ 4 * P.δ) ^ n * gainΛ P = G * (G * P.δ) ^ n * gainΛ P * b ^ (4 * n + 4) := by
    rw [mul_pow, mul_pow, mul_pow, show 4 * n + 4 = 4 + 4 * n by ring, pow_add, pow_mul]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hbc (by positivity)

theorem sep_absorb {G b : ℝ} (hG : 0 ≤ G) (hb : 1 ≤ b) {n c : ℕ} (hc : c ≤ 4 * n + 4) :
    G * G ^ n * b ^ c ≤ G * b ^ 4 * (G * b ^ 4) ^ n := by
  have hbc : b ^ c ≤ b ^ (4 * n + 4) := pow_le_pow_right₀ hb hc
  have e : G * b ^ 4 * (G * b ^ 4) ^ n = G * G ^ n * b ^ (4 * n + 4) := by
    rw [mul_pow, show 4 * n + 4 = 4 + 4 * n by ring, pow_add, pow_mul]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hbc (by positivity)

theorem sep_absorb₀ {G b : ℝ} (hG : 0 ≤ G) (hb : 1 ≤ b) (n : ℕ) : G * G ^ n ≤ G * b ^ 4 * (G * b ^ 4) ^ n := by
  have h := sep_absorb hG hb (n := n) (c := 0) (by omega)
  simpa using h

/-! ### The gate -/


end WaveTurbulence.PL234
