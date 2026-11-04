/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.Telescope

/-!
# Shifting a single-layer couple from layer `r` to layer `0` (TARGET L1173)

TARGET's proof of Prop `regref1` (L1173): "`K*_𝒬` and `K*_𝒯` are clearly invariant after translating all the time
variables by the same value `r`". For a layered couple with all nodes in layer `r`:

* `phaseProd_shift`: translating all times multiplies the phase by `e^{πiδL^{2γ}c∑ζ_𝔫Ω_𝔫}`, which is `1` for couple
  decorations (`sum_sign_omega_couple`);
* `kDomain_shift`: `τ + r ∈ kDomain LG up 0 ↔ τ ∈ kDomain LG₀ (up − r) 0` (`LG₀`: the same garden in layer `0`);
* **`KQstar_shift`**: `K*_𝒬[LG](t, s, k) = K*_𝒬[LG₀](t − r, s − r, k)`;
* **`JB_shift`**, **`app_shift`**: B2's `𝒥ℬ*_𝒬` in layer `r` is the layer-`0` one at `(t − r, s − r)`, hence so is
  `(K*_𝒬)_app`.
-/

@[expose] public section

open MeasureTheory Set Finset

namespace WaveTurbulence.Regref

open TTree

variable {w d : ℕ}

/-- The same garden with every node in layer `0`. -/
abbrev layer0 (LG : LayeredGarden w) : LayeredGarden w :=
  ⟨LG.garden, fun _ => 0, ⟨fun _ _ => le_rfl, fun _ => rfl⟩⟩

theorem phaseProd_shift (L γ δ : ℝ) (G : Garden w) (k : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ)
    (c : ℝ) (h0 : ∑ b : GBranch G.tree, (((G.sign b.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G k b = 0) :
    phaseProd L γ δ G k (fun b => τ b + c) = phaseProd L γ δ G k τ := by
  unfold phaseProd
  have hsplit : ∀ b : GBranch G.tree,
      Complex.exp ((Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G k b *
        (τ b + c) : ℝ) * Complex.I) =
      Complex.exp ((Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G k b *
        τ b : ℝ) * Complex.I) *
      Complex.exp (((Real.pi * δ * L ^ (2 * γ) * c) *
        ((((G.sign b.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G k b) : ℝ) * Complex.I) := by
    intro b
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [Finset.prod_congr rfl fun b _ => hsplit b, Finset.prod_mul_distrib]
  have : ∑ b : GBranch G.tree, ((((Real.pi * δ * L ^ (2 * γ) * c) *
      ((((G.sign b.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G k b) : ℝ) : ℂ) * Complex.I) = 0 := by
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.mul_sum, h0]
    simp
  have h1 : ∏ b : GBranch G.tree, Complex.exp ((((Real.pi * δ * L ^ (2 * γ) * c) *
      ((((G.sign b.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G k b) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_sum, this, Complex.exp_zero]
  rw [h1, mul_one]

theorem kDomain_shift (LG : LayeredGarden w) (r : ℕ) (hr : ∀ a, LG.layer a = r)
    (up : GBranch LG.garden.tree → ℝ) (x : GBranch LG.garden.tree → ℝ) :
    (fun b => x b + r) ∈ kDomain LG up 0 ↔ x ∈ kDomain (layer0 LG) (fun b => up b - r) 0 := by
  simp only [kDomain, Set.mem_ofPred_eq, layer0, hr, Nat.cast_zero, zero_add]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  constructor
  · intro h b
    obtain ⟨h1, h2, -, h4, h5, -⟩ := h b
    refine ⟨by linarith, by linarith, by linarith, by linarith, fun b' hb' => ?_, fun _ => by linarith⟩
    have := h5 b' hb'
    linarith
  · intro h b
    obtain ⟨h1, h2, -, h4, h5, -⟩ := h b
    refine ⟨by linarith, by linarith, by linarith, by linarith, fun b' hb' => ?_, fun _ => by linarith⟩
    have := h5 b' hb'
    linarith

theorem not_flowerParent_of_plain {G : Garden w} (hP : G.IsPlain) (b : GBranch G.tree) :
    ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hfl, -⟩
  unfold Garden.IsFlower at hfl
  rw [hP ℓ] at hfl
  simp at hfl

theorem phaseIntegral_shift (L γ δ : ℝ) (LG : LayeredGarden w) (hP : LG.garden.IsPlain) (r : ℕ)
    (hr : ∀ a, LG.layer a = r) (up : GBranch LG.garden.tree → ℝ) (k : GNode LG.garden.tree → Mom d)
    (h0 : ∑ b : GBranch LG.garden.tree, (((LG.garden.sign b.toNode : ℤˣ) : ℤ) : ℝ) *
      omegaNode LG.garden k b = 0) :
    phaseIntegral L γ δ LG.garden (kDomain LG up 0) 0 k =
      phaseIntegral L γ δ LG.garden (kDomain (layer0 LG) (fun b => up b - r) 0) 0 k := by
  unfold phaseIntegral
  rw [← integral_add_right_eq_self (μ := volume) _ (fun _ => (r : ℝ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have hext : LG.garden.extendTime 0 (τ + fun _ => (r : ℝ)) =
      fun b => LG.garden.extendTime 0 τ b + r := by
    funext b
    simp only [Garden.extendTime, not_flowerParent_of_plain hP b, ↓reduceDIte]
    rfl
  show (kDomain LG up 0).indicator (phaseProd L γ δ LG.garden k)
      (LG.garden.extendTime 0 (τ + fun _ => (r : ℝ))) =
    (kDomain (layer0 LG) (fun b => up b - r) 0).indicator (phaseProd L γ δ LG.garden k)
      (LG.garden.extendTime 0 τ)
  rw [hext]
  by_cases hm : LG.garden.extendTime 0 τ ∈ kDomain (layer0 LG) (fun b => up b - r) 0
  · have hm' := (kDomain_shift LG r hr up _).2 hm
    rw [Set.indicator_of_mem hm', Set.indicator_of_mem hm]
    exact phaseProd_shift L γ δ _ k _ _ h0
  · have hm' : (fun b => LG.garden.extendTime 0 τ b + r) ∉ kDomain LG up 0 :=
      fun h => hm ((kDomain_shift LG r hr up _).1 h)
    rw [Set.indicator_of_notMem hm', Set.indicator_of_notMem hm]

/-- **Shifting a single-layer couple to layer `0`** (TARGET L1173). -/
theorem KQstar_shift (L γ δ : ℝ) (F : Mom d → ℝ) (LG : LayeredGarden 2) (hG : IsCouple LG.garden) (r : ℕ)
    (hr : ∀ a, LG.layer a = r) (t s : ℝ) (k : Mom d) :
    KQstar L γ δ (fun _ => F) LG t s k = KQstar L γ δ (fun _ => F) (layer0 LG) (t - r) (s - r) k := by
  unfold KQstar kernelK
  congr 1
  refine tsum_congr fun κ => ?_
  congr 2
  have hpair : ∀ ℓ : GLeaf LG.garden.tree, cosetDecoration LG.garden L k κ.1 ℓ.toNode =
      cosetDecoration LG.garden L k κ.1 (LG.garden.pair ℓ).toNode := fun ℓ => by
    simp only [cosetDecoration, κ.2.1.2 ℓ]
  have hroot : cosetDecoration LG.garden L k κ.1 (GNode.root LG.garden.tree 0) =
      cosetDecoration LG.garden L k κ.1 (GNode.root LG.garden.tree 1) := by
    simp only [cosetDecoration, κ.2.2.1 0, κ.2.2.1 1]
  rw [phaseIntegral_shift L γ δ LG hG.1 r hr _ _
    (sum_sign_omega_couple LG.garden hG _ hpair hroot)]
  congr 2
  funext b
  split_ifs <;> rfl

/-! ### The time factors -/

mutual
/-- **`𝒥ℬ*` in layer `r` is the layer-`0` one at shifted times.** -/
theorem JB_shift (r : ℝ) : (Q : RegCpl) → ∀ t s : ℝ, Q.JB r t s = Q.JB 0 (t - r) (s - r)
  | .triv, _, _ => rfl
  | .type1 _ Q₁ Q₂ Q₃, t, s => by
    simp only [RegCpl.JB]
    congr 1
    have hc := intervalIntegral.integral_comp_sub_right
      (fun τ => Q₁.JB 0 τ τ * Q₂.JB 0 τ τ * Q₃.JB 0 τ τ) r (a := r) (b := min t s)
    rw [sub_self] at hc
    rw [show min (t - r) (s - r) = min t s - r from min_sub_sub_right t s r, ← hc]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp only [JB_shift r Q₁, JB_shift r Q₂, JB_shift r Q₃]
  | .type2 Xp Xm Qlp, t, s => by
    simp only [RegCpl.JB]
    rw [JBchain_shift r Xp r t, sub_self]
    congr 1
    funext u
    rw [JBchain_shift r Xm r s, sub_self]
    congr 1
    funext v
    rw [JB_shift r Qlp, add_sub_cancel_right, add_sub_cancel_right]

theorem JBchain_shift (r : ℝ) : (X : RegChain) → ∀ (lo t : ℝ) (G : ℝ → ℝ),
    X.JBchain r lo t G = X.JBchain 0 (lo - r) (t - r) (fun u => G (u + r))
  | .nil, _, t, G => by simp [RegChain.JBchain]
  | .pair _ Qr Qg _ rest, lo, t, G => by
    simp only [RegChain.JBchain]
    rw [← intervalIntegral.integral_comp_sub_right
      (fun τ => Qr.JB 0 τ τ * Qg.JB 0 τ τ * rest.JBchain 0 (lo - r) τ fun u => G (u + r)) r]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp only [JB_shift r Qr, JB_shift r Qg, JBchain_shift r rest lo τ G]
end

/-- **`(K*_𝒬)_app` in layer `r` is the layer-`0` one at shifted times.** -/
theorem app_shift (δ r : ℝ) (F : Mom d → ℝ) (Q : RegCpl) (t s : ℝ) (k : Mom d) :
    Q.app δ r F t s k = Q.app δ 0 F (t - r) (s - r) k := by
  simp only [RegCpl.app, JB_shift r Q t s]

end WaveTurbulence.Regref
