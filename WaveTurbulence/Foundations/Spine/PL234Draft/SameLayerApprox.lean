/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SameLayer
public import WaveTurbulence.Foundations.Spine.PL234Draft.Bodies

/-!
# Single-layer leading terms: inputs, constants and the separated form (TARGET (regref1-3))

* `kernelK_congr_inputs`: the kernel depends on the inputs only at the input leaves;
* `regBound_mono`, `sourceSeparated_mono`: the bounds are monotone in `C₁`;
* `XNorm00_const_mul_le`, `XNorm00Restr_const_mul_le`: scalars come out of the order-zero norms;
* `norm_app_coeff_le`: the coefficient `2^{-n(𝒬)} ζ(𝒬) ∏_{𝔫∈Z} (−ζ_𝔫 π i)^{-1}` has modulus at most `1`;
* `sourceSeparated_app_couple`, `sourceSeparated_app_tree`: B2's single-layer leading term is a sum of at
  most `2^n` terms `δ^n 𝒥(t,s) ℳ(k)` (TARGET (layerregest4)), with the factor bounds of B2.1 (3).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

/-! ### Inputs -/

/-- The one kernel depends on the input family only at the layers of the input leaves. -/
theorem kernelK_congr_inputs (L γ δ : ℝ) {d w : ℕ} (F F' : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ)
    (h : ∀ ℓ ∈ inputLeaves LG.garden, F (LG.layer ℓ.toNode) = F' (LG.layer ℓ.toNode)) :
    kernelK L γ δ F LG up s k₀ nroot nfl = kernelK L γ δ F' LG up s k₀ nroot nfl := by
  unfold kernelK
  congr 1
  refine tsum_congr fun κ => ?_
  congr 1
  refine Finset.prod_congr rfl fun ℓ hℓ => ?_
  rw [h ℓ hℓ]

theorem KQstar_congr_layer (L γ δ : ℝ) {d : ℕ} (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) {r : ℕ}
    (hr : ∀ a, LG.layer a = r) (t s : ℝ) (k : Mom d) :
    KQstar L γ δ F LG t s k = KQstar L γ δ (fun _ => F r) LG t s k :=
  kernelK_congr_inputs L γ δ _ _ LG _ _ _ _ _ fun ℓ _ => by rw [hr]

theorem KTstar_congr_layer (L γ δ : ℝ) {d : ℕ} (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) {r : ℕ}
    (hr : ∀ ℓ ∈ inputLeaves LG.garden, LG.layer ℓ.toNode = r) (t s : ℝ) (k : Mom d) :
    KTstar L γ δ F LG t s k = KTstar L γ δ (fun _ => F r) LG t s k :=
  kernelK_congr_inputs L γ δ _ _ LG _ _ _ _ _ fun ℓ hℓ => by rw [hr ℓ hℓ]

/-! ### Monotonicity in `C₁` -/

theorem regBound_mono (P : WTParams) {C : ℝ} (h0 : 0 ≤ P.C₁) (hC : P.C₁ ≤ C) (hδ : 0 ≤ P.δ)
    (hL : 0 ≤ P.L) (n g : ℕ) : regBound P n g ≤ regBound { P with C₁ := C } n g := by
  unfold regBound
  refine ENNReal.ofReal_le_ofReal ?_
  have hLp : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g) := Real.rpow_nonneg hL _
  change P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g) ≤
    C * (C * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)
  have hC0 : 0 ≤ C := h0.trans hC
  gcongr

theorem sourceSeparated_mono {P : WTParams} {C : ℝ} (h1 : 1 ≤ P.C₁) (hC : P.C₁ ≤ C) {n W : ℕ}
    {B : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → Mom P.d → ℂ} (h : SourceSeparated P n W B f) :
    SourceSeparated { P with C₁ := C } n W B f := by
  obtain ⟨m, J, M, hm, hf, hJ, hM⟩ := h
  have hle : ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ≤ ENNReal.ofReal (C * C ^ n) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ P.C₁ := by linarith
    have : 0 ≤ C := by linarith
    gcongr
  exact ⟨m, J, M, hm, hf, fun i => (hJ i).trans hle, fun i => (hM i).trans hle⟩

/-! ### Scalars in the order-zero norms -/

theorem XNorm00_const_mul_le {r : ℕ} {V : Type*} (θ : ℝ) (c : ℂ) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00 θ (fun t v => c * F t v) ≤ ‖c‖ₑ * XNorm00 θ F := by
  by_cases hc : c = 0
  · subst hc
    have h0 : XNorm00 θ (fun (t : Fin r → ℝ) (v : V) => (0 : ℂ) * F t v) = 0 := by
      unfold XNorm00
      simp [timeFT]
    rw [h0]
    exact zero_le
  · unfold XNorm00
    split_ifs with hcF hF hF
    · rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_mono fun lam => ?_
      have hft : ∀ v, timeFT (fun t v => c * F t v) lam v = c * timeFT F lam v := by
        intro v
        unfold timeFT
        rw [← integral_const_mul]
        congr 1
        funext t
        ring
      simp only [hft, enorm_mul]
      rw [← ENNReal.mul_iSup]
      rw [mul_left_comm]
    · simp [ENNReal.mul_top, hc]
    · exact absurd (fun v => (hF v).const_mul c) hcF
    · simp [ENNReal.mul_top, hc]

theorem XNorm00Restr_const_mul_le {r : ℕ} {V : Type*} (θ : ℝ) (c : ℂ) (B : Set (Fin r → ℝ))
    (K : Set V) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00Restr θ B K (fun t v => c * F t v) ≤ ‖c‖ₑ * XNorm00Restr θ B K F := by
  by_cases hc : c = 0
  · subst hc
    refine (iInf₂_le (fun _ _ => (0 : ℂ)) fun t _ v _ => by simp).trans ?_
    have h0 : XNorm00 θ (fun (_ : Fin r → ℝ) (_ : V) => (0 : ℂ)) = 0 := by
      unfold XNorm00
      simp [timeFT]
    rw [h0]
    exact zero_le
  · unfold XNorm00Restr
    rw [ENNReal.mul_iInf_of_ne (by simpa using hc) enorm_ne_top]
    refine le_iInf fun G => ?_
    rw [ENNReal.mul_iInf_of_ne (by simpa using hc) enorm_ne_top]
    refine le_iInf fun hG => ?_
    refine (iInf₂_le (fun t v => c * G t v) fun t ht v hv => by
      simp only [hG t ht v hv]).trans ?_
    exact XNorm00_const_mul_le θ c G

/-! ### The coefficient of a leading term -/

theorem norm_zetaOfTrees {w : ℕ} (σ : Fin w → ℤˣ) (T : Fin w → TTree) :
    ‖zetaOfTrees σ T‖ = 1 := by
  unfold zetaOfTrees
  rw [norm_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [norm_prod]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  rcases Int.units_eq_one_or (pathSign (σ j) p) with h | h <;> simp [h]

theorem norm_specialWeight_le {w : ℕ} (σ : Fin w → ℤˣ) (Z : Finset (Fin w × Path)) :
    ‖specialWeight σ Z‖ ≤ 1 := by
  unfold specialWeight
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun z _ => ?_
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [norm_inv, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one]
  rcases Int.units_eq_one_or (nodeSign σ z) with h | h <;>
    simp [h, Complex.norm_real, abs_of_pos Real.pi_pos, inv_le_one_of_one_le₀ hpi]

theorem norm_app_coeff_le {w : ℕ} (m : ℕ) (σ : Fin w → ℤˣ) (T : Fin w → TTree)
    (Z : Finset (Fin w × Path)) :
    ‖(2 : ℂ)⁻¹ ^ m * zetaOfTrees σ T * specialWeight σ Z‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_zetaOfTrees, mul_one, norm_pow, norm_inv]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  calc (2⁻¹ : ℝ) ^ m * ‖specialWeight σ Z‖ ≤ 1 * 1 := by
        gcongr
        · exact pow_le_one₀ (by norm_num) (by norm_num)
        · exact norm_specialWeight_le σ Z
    _ = 1 := one_mul 1

/-! ### Counting special subsets -/

theorem card_specialSets_couple_le {Q : RegCpl} {n : ℕ} (hsize : Q.size = 2 * n) :
    (specialSets Q.links).card ≤ 2 ^ n := by
  have hc := card_chosenSet Q
  have hn : (chosenSet Q.links).card = n := by omega
  unfold specialSets
  refine (card_filter_le _ _).trans ?_
  rw [card_powerset, hn]

theorem card_specialSets_tree_le {X : RegChain} {n : ℕ} (hsize : X.size = 2 * n) (ζ : ℤˣ) :
    (specialSets (X.treeLinks ζ)).card ≤ 2 ^ n := by
  have hl := chain_linksAt_length X ζ ((0 : Fin 1), ([] : Path))
  have hlen : (X.treeLinks ζ).length = n := by
    unfold RegChain.treeLinks
    omega
  have hc : (chosenSet (X.treeLinks ζ)).card ≤ n := by
    unfold chosenSet
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map, hlen]
  unfold specialSets
  refine (card_filter_le _ _).trans ?_
  rw [card_powerset]
  exact Nat.pow_le_pow_right (by norm_num) hc

/-! ### The separated form of a single-layer leading term -/

/-- **B2's leading term of a couple code is separated** (TARGET (layerregest4)–(layerregest5)): at most
`2^n` terms `δ^n 𝒥(t,s) ℳ(k)`, given the factor bounds of B2.1 (3) on dominant codes. -/
theorem sourceSeparated_app_couple (P : WTParams) {n W : ℕ} (B : Set (Fin 2 → ℝ)) (r : ℝ)
    (F : Mom P.d → ℝ) (Q : RegCpl) (hsize : Q.size = 2 * n)
    (hfac : Q.dominant = true →
      XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤
          ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
        ∀ Z ∈ specialSets Q.links,
          SNormR (30 * P.d) W (Q.Mstar F Z (0, []) (1, [])) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) :
    SourceSeparated P n W B (fun ts k => Q.app P.δ r F (ts 0) (ts 1) k) := by
  by_cases hdom : Q.dominant = true
  · obtain ⟨hJ, hM⟩ := hfac hdom
    set S := specialSets Q.links with hS
    let e : Fin S.card ≃ S := S.equivFin.symm
    let c₀ : ℂ := (2 : ℂ)⁻¹ ^ Q.size * zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2]
    refine ⟨S.card, fun i ts => c₀ * specialWeight ![1, -1] (e i).1 * (Q.JB r (ts 0) (ts 1) : ℂ),
      fun i k => Q.Mstar F (e i).1 (0, []) (1, []) k, card_specialSets_couple_le hsize, ?_, ?_,
      fun i => hM _ (e i).2⟩
    · intro ts _ k
      have hn : Q.size / 2 = n := by omega
      simp only [RegCpl.app, hdom, ite_true, hn]
      rw [Finset.mul_sum, ← Finset.sum_coe_sort S, ← e.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [c₀]
      ring
    · intro i
      refine (XNorm00Restr_const_mul_le (1 - P.η) (c₀ * specialWeight ![1, -1] (e i).1) B Set.univ
        (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ))).trans ?_
      have hc : ‖c₀ * specialWeight ![1, -1] (e i).1‖ₑ ≤ 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (norm_app_coeff_le _ _ _ _)
      calc _ ≤ 1 * ENNReal.ofReal (P.C₁ * P.C₁ ^ n) := by gcongr
        _ = _ := one_mul _
  · refine ⟨0, Fin.elim0, Fin.elim0, Nat.zero_le _, fun ts _ k => ?_, fun i => i.elim0,
      fun i => i.elim0⟩
    simp [RegCpl.app, hdom]

/-- **B2's leading term of a tree code is separated** (TARGET (layerregest4), (layerregest6)). -/
theorem sourceSeparated_app_tree (P : WTParams) {n W : ℕ} (B : Set (Fin 2 → ℝ)) (r : ℝ)
    (F : Mom P.d → ℝ) (X : RegChain) (ζ : ℤˣ) (hsize : X.size = 2 * n)
    (hfac : X.dominant = true →
      XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤
          ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
        ∀ Z ∈ specialSets (X.treeLinks ζ),
          SNormR (30 * P.d) W (X.Nstar F Z ζ (0, [])) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) :
    SourceSeparated P n W B (fun ts k => X.app P.δ r F ζ (ts 0) (ts 1) k) := by
  by_cases hdom : X.dominant = true
  · obtain ⟨hJ, hM⟩ := hfac hdom
    set S := specialSets (X.treeLinks ζ) with hS
    let e : Fin S.card ≃ S := S.equivFin.symm
    let c₀ : ℂ := (2 : ℂ)⁻¹ ^ X.size * zetaOfTrees ![ζ] ![X.plug ζ .leaf]
    refine ⟨S.card, fun i ts => c₀ * specialWeight ![ζ] (e i).1 * (X.JBtree r (ts 0) (ts 1) : ℂ),
      fun i k => X.Nstar F (e i).1 ζ (0, []) k, card_specialSets_tree_le hsize ζ, ?_, ?_,
      fun i => hM _ (e i).2⟩
    · intro ts _ k
      have hn : X.size / 2 = n := by omega
      simp only [RegChain.app, hdom, ite_true, hn]
      rw [Finset.mul_sum, ← Finset.sum_coe_sort S, ← e.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [c₀]
      ring
    · intro i
      refine (XNorm00Restr_const_mul_le (1 - P.η) (c₀ * specialWeight ![ζ] (e i).1) B Set.univ
        (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ))).trans ?_
      have hc : ‖c₀ * specialWeight ![ζ] (e i).1‖ₑ ≤ 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (norm_app_coeff_le _ _ _ _)
      calc _ ≤ 1 * ENNReal.ofReal (P.C₁ * P.C₁ ^ n) := by gcongr
        _ = _ := one_mul _
  · refine ⟨0, Fin.elim0, Fin.elim0, Nat.zero_le _, fun ts _ k => ?_, fun i => i.elim0,
      fun i => i.elim0⟩
    simp [RegChain.app, hdom]

end WaveTurbulence.PL234
