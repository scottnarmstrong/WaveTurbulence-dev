/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.Translate
public import WaveTurbulence.Foundations.IncohInst.Enhanced.TreeIncoh1
public import WaveTurbulence.Foundations.RegularAsymptotics.PairedTreeContinuity

/-!
# Regular trees: translation in time, relayering of the lone leaf, independence of `s` (TARGET L1173)

For a decoded regular tree (`RegChain.DecodesTree`):

* `sum_sign_omega_tree`: `∑_𝔫 ζ_𝔫 Ω_𝔫 = 0` for decorations with paired leaves equal and `k_{ℓ_lo} = k_𝔯` (the leaf
  terms cancel in pairs; the lone leaf has the sign of the root, C5 `Links.pathSign_lone`);
* **`KTstar_shift`**: all nodes in layer `r` ⇒ `K*_𝒯(t, s, k) = K*_𝒯[layer 0](t − r, s − r, k)` (the lone-parent
  constraint `t_𝔫 > s` translates with the times);
* `KTstar_relayer`, `KTstar_indep_of_le`, `app_of_le` (proofs of the independent B2 audit's probes
  `b2-audit/Q3.lean`, `Q1.lean`, reproduced here): `K*_𝒯` sees the layering only through the branching nodes, and
  for `s ≤ r` neither `K*_𝒯` nor `(K*_𝒯)_app` depends on `s` (B2-CL-13);
* **`JBtree_shift`**, **`JBtree_of_le`**: `𝒥ℬ*_𝒯` in layer `r` is the layer-`0` one at `(t − r, s − r)`; for `s ≤ r`
  it is its value at `s = r`.
-/

@[expose] public section

open MeasureTheory Set Finset

namespace WaveTurbulence.Regref

open TTree

variable {d : ℕ}

theorem sign_lone_eq_sig {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    G.sign (Links.loneLeaf hX).toNode = G.sig 0 := by
  have h1 := Links.pathSign_lone hX
  have h2 := Links.pathSign_one_eq (Links.loneLeaf hX)
  change ((pathSign 1 X.lonePath : ℤˣ) : ℤ) = _ at h2
  rw [h1] at h2
  have h3 : G.sig 0 * G.sign (Links.loneLeaf hX).toNode = 1 := Units.ext (by
    rw [Units.val_mul, Units.val_one]; exact h2.symm)
  calc G.sign (Links.loneLeaf hX).toNode = G.sig 0 * G.sig 0 * G.sign (Links.loneLeaf hX).toNode := by
        rw [← sq, Int.units_sq, one_mul]
    _ = G.sig 0 := by rw [mul_assoc, h3, mul_one]

theorem pair_ne_self_of_ne_lone {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) {ℓ : GLeaf G.tree}
    (h : ℓ ≠ Links.loneLeaf hX) : G.pair ℓ ≠ ℓ := by
  rw [Ne, Links.tree_pair_eq_iff hX]
  intro hp
  exact h (Subtype.ext (Prod.ext (Links.fin_one_eq _) hp))

/-- A decoded tree carrier is a paired tree. -/
theorem isPairedTree_of_decodesTree {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) : IsPairedTree G := by
  classical
  have hm : ∀ ℓ : GLeaf G.tree, G.mark ℓ ≠ none ↔ ℓ = Links.loneLeaf hX := by
    intro ℓ
    rw [← G.pair_eq_iff, Links.tree_pair_eq_iff hX]
    constructor
    · intro h
      exact Subtype.ext (Prod.ext (Links.fin_one_eq _) h)
    · rintro rfl
      rfl
  refine ⟨?_, fun ℓ h => ?_⟩
  · have : (univ.filter fun ℓ : GLeaf G.tree => G.mark ℓ ≠ none) = {Links.loneLeaf hX} := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hm ℓ]
    rw [this, Finset.card_singleton]
  · have hp : ℓ.1.2 = X.lonePath := by rw [(hm ℓ).1 h]; rfl
    unfold Garden.IsLone
    rw [hX.2.1 ℓ]
    simp [hp]

/-- **Translation invariance of the phase for regular trees**: `∑ ζ_𝔫 Ω_𝔫 = 0`. -/
theorem sum_sign_omega_tree {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) (k : GNode G.tree → Mom d)
    (hpair : ∀ ℓ : GLeaf G.tree, k ℓ.toNode = k (G.pair ℓ).toNode)
    (hlone : k (Links.loneLeaf hX).toNode = k (GNode.root G.tree 0)) :
    ∑ b : GBranch G.tree, (((G.sign b.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G k b = 0 := by
  classical
  rw [sum_sign_omega]
  set ℓ₀ := Links.loneLeaf hX
  set f : GLeaf G.tree → ℝ := fun ℓ => (((G.sign ℓ.toNode : ℤˣ) : ℤ) : ℝ) * ‖k ℓ.toNode‖ ^ 2 with hf
  have hsplit : ∑ ℓ : GLeaf G.tree, f ℓ = f ℓ₀ + ∑ ℓ ∈ univ.erase ℓ₀, f ℓ :=
    (Finset.add_sum_erase _ _ (mem_univ _)).symm
  have hzero : ∑ ℓ ∈ univ.erase ℓ₀, f ℓ = 0 := by
    refine Finset.sum_involution (fun ℓ _ => G.pair ℓ) (fun ℓ hℓ => ?_) (fun ℓ hℓ _ => ?_)
      (fun ℓ hℓ => ?_) (fun ℓ _ => G.pair_pair ℓ)
    · have hne := pair_ne_self_of_ne_lone hX (Finset.ne_of_mem_erase hℓ)
      have hs : G.sign (G.pair ℓ).toNode = -G.sign ℓ.toNode := G.pair_sign ℓ hne
      simp only [hf]
      rw [hs, ← hpair ℓ]
      push_cast
      ring
    · exact pair_ne_self_of_ne_lone hX (Finset.ne_of_mem_erase hℓ)
    · refine Finset.mem_erase.2 ⟨fun h => Finset.ne_of_mem_erase hℓ ?_, mem_univ _⟩
      rw [← G.pair_pair ℓ, h]
      exact (Links.tree_pair_eq_iff hX ℓ₀).2 rfl
  change ∑ ℓ : GLeaf G.tree, f ℓ - _ = 0
  rw [hsplit, hzero, add_zero, Fin.sum_univ_one]
  simp only [hf, hlone]
  rw [show G.sign ℓ₀.toNode = G.sig 0 from sign_lone_eq_sig hX, sub_self]

/-- The time domain with a general lower time, translated by `r` (all nodes in layer `r`). -/
theorem kDomain_shift' {w : ℕ} (LG : LayeredGarden w) (r : ℕ) (hr : ∀ a, LG.layer a = r)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (x : GBranch LG.garden.tree → ℝ) :
    (fun b => x b + r) ∈ kDomain LG up s ↔ x ∈ kDomain (layer0 LG) (fun b => up b - r) (s - r) := by
  simp only [kDomain, Set.mem_ofPred_eq, layer0, hr, Nat.cast_zero, zero_add]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  constructor
  · intro h b
    obtain ⟨h1, h2, -, h4, h5, h6⟩ := h b
    refine ⟨by linarith, by linarith, by linarith, by linarith, fun b' hb' => ?_, fun hb => ?_⟩
    · have := h5 b' hb'
      linarith
    · have := h6 hb
      linarith
  · intro h b
    obtain ⟨h1, h2, -, h4, h5, h6⟩ := h b
    refine ⟨by linarith, by linarith, by linarith, by linarith, fun b' hb' => ?_, fun hb => ?_⟩
    · have := h5 b' hb'
      linarith
    · have := h6 hb
      linarith

theorem phaseIntegral_shift' (L γ δ : ℝ) {w : ℕ} (LG : LayeredGarden w)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b) (r : ℕ)
    (hr : ∀ a, LG.layer a = r) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : GNode LG.garden.tree → Mom d)
    (h0 : ∑ b : GBranch LG.garden.tree, (((LG.garden.sign b.toNode : ℤˣ) : ℤ) : ℝ) *
      omegaNode LG.garden k b = 0) :
    phaseIntegral L γ δ LG.garden (kDomain LG up s) s k =
      phaseIntegral L γ δ LG.garden (kDomain (layer0 LG) (fun b => up b - r) (s - r)) (s - r) k := by
  unfold phaseIntegral
  rw [← integral_add_right_eq_self (μ := volume) _ (fun _ => (r : ℝ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have hext : LG.garden.extendTime s (τ + fun _ => (r : ℝ)) =
      fun b => LG.garden.extendTime (s - r) τ b + r := by
    funext b
    simp only [Garden.extendTime, hfl b, ↓reduceDIte]
    rfl
  show (kDomain LG up s).indicator (phaseProd L γ δ LG.garden k)
      (LG.garden.extendTime s (τ + fun _ => (r : ℝ))) =
    (kDomain (layer0 LG) (fun b => up b - r) (s - r)).indicator (phaseProd L γ δ LG.garden k)
      (LG.garden.extendTime (s - r) τ)
  rw [hext]
  by_cases hm : LG.garden.extendTime (s - r) τ ∈ kDomain (layer0 LG) (fun b => up b - r) (s - r)
  · have hm' := (kDomain_shift' LG r hr up s _).2 hm
    rw [Set.indicator_of_mem hm', Set.indicator_of_mem hm]
    exact phaseProd_shift L γ δ _ k _ _ h0
  · have hm' : (fun b => LG.garden.extendTime (s - r) τ b + r) ∉ kDomain LG up s :=
      fun h => hm ((kDomain_shift' LG r hr up s _).1 h)
    rw [Set.indicator_of_notMem hm', Set.indicator_of_notMem hm]

/-- **Shifting a single-layer regular tree to layer `0`** (TARGET L1173). -/
theorem KTstar_shift (L γ δ : ℝ) (F : Mom d → ℝ) (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (r : ℕ) (hr : ∀ a, LG.layer a = r) (t s : ℝ) (k : Mom d) :
    KTstar L γ δ (fun _ => F) LG t s k = KTstar L γ δ (fun _ => F) (layer0 LG) (t - r) (s - r) k := by
  have hT := LGSpine.no_flowerParent_of_pairedTree LG.garden (isPairedTree_of_decodesTree hX)
  unfold KTstar kernelK
  congr 1
  refine tsum_congr fun κ => ?_
  congr 2
  have hpair : ∀ ℓ : GLeaf LG.garden.tree, cosetDecoration LG.garden L k κ.1 ℓ.toNode =
      cosetDecoration LG.garden L k κ.1 (LG.garden.pair ℓ).toNode := fun ℓ => by
    simp only [cosetDecoration, κ.2.1.2 ℓ]
  have hlone : cosetDecoration LG.garden L k κ.1 (Links.loneLeaf hX).toNode =
      cosetDecoration LG.garden L k κ.1 (GNode.root LG.garden.tree 0) := by
    simp only [cosetDecoration, Links.tree_root_eq_lone hX κ.2.1]
  exact phaseIntegral_shift' L γ δ LG hT r hr _ s _ (sum_sign_omega_tree hX _ hpair hlone)

/-! ### Relayering and independence of `s` (B2 audit probes Q1, Q3, reproduced) -/

/-- `K*_𝒯` with input family `fun _ => F` depends on the layering only through the branching nodes
(`b2-audit/Q3.lean`). -/
theorem KTstar_relayer (L γ δ : ℝ) (F : Mom d → ℝ) (LG : LayeredGarden 1)
    (layer' : GNode LG.garden.tree → ℕ) (h' : IsLayering LG.garden layer')
    (hb : ∀ b : GBranch LG.garden.tree, layer' b.toNode = LG.layer b.toNode) (t s : ℝ) (k : Mom d) :
    KTstar L γ δ (fun _ => F) ⟨LG.garden, layer', h'⟩ t s k = KTstar L γ δ (fun _ => F) LG t s k := by
  have hD : kDomain (⟨LG.garden, layer', h'⟩ : LayeredGarden 1) (fun _ => t) s =
      kDomain LG (fun _ => t) s := by
    ext τ
    simp only [kDomain, Set.mem_ofPred_eq, hb]
  unfold KTstar kernelK phaseIntegral
  rw [hD]

/-- For `s, s'` below every lone parent, `K*_𝒯(t, s) = K*_𝒯(t, s')` (`b2-audit/Q1.lean`). -/
theorem KTstar_indep_of_le (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1)
    (hP : IsPairedTree LG.garden) (t s s' : ℝ) (k : Mom d)
    (hs : ∀ b, LG.garden.IsLoneParent b → s ≤ LG.layer b.toNode ∧ s' ≤ LG.layer b.toNode) :
    KTstar L γ δ F LG t s k = KTstar L γ δ F LG t s' k := by
  have hfl := LGSpine.no_flowerParent_of_pairedTree LG.garden hP
  have hD : kDomain LG (fun _ => t) s = kDomain LG (fun _ => t) s' := by
    ext τ
    simp only [kDomain, Set.mem_ofPred_eq]
    constructor
    · intro h b
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := h b
      exact ⟨h1, h2, h3, h4, h5, fun hb => lt_of_le_of_lt (by exact_mod_cast (hs b hb).2) h1⟩
    · intro h b
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := h b
      exact ⟨h1, h2, h3, h4, h5, fun hb => lt_of_le_of_lt (by exact_mod_cast (hs b hb).1) h1⟩
  have hE : ∀ τ, LG.garden.extendTime s τ = LG.garden.extendTime s' τ := fun τ => by
    funext b
    simp only [Garden.extendTime, hfl b, ↓reduceDIte]
  simp only [KTstar, kernelK, phaseIntegral, hD, hE]

/-- `(K*_𝒯)_app(t, s, k) = (K*_𝒯)_app(t, r, k)` once `s ≤ r` (`b2-audit/Q1.lean`, B2-CL-13). -/
theorem app_of_le (δ r : ℝ) (F : Mom d → ℝ) (X : RegChain) (ζ : ℤˣ) (t s : ℝ) (k : Mom d)
    (h : s ≤ r) : X.app δ r F ζ t s k = X.app δ r F ζ t r k := by
  simp only [RegChain.app, RegChain.JBtree, max_eq_right h, max_self]

theorem JBtree_of_le (r : ℝ) (X : RegChain) (t s : ℝ) (h : s ≤ r) : X.JBtree r t s = X.JBtree r t r := by
  simp only [RegChain.JBtree, max_eq_right h, max_self]

/-- **`𝒥ℬ*_𝒯` in layer `r` is the layer-`0` one at shifted times.** -/
theorem JBtree_shift (r : ℝ) (X : RegChain) (t s : ℝ) : X.JBtree r t s = X.JBtree 0 (t - r) (s - r) := by
  simp only [RegChain.JBtree]
  rw [JBchain_shift r X (max s r) t, ← max_sub_sub_right s r r, sub_self]

/-- **`(K*_𝒯)_app` in layer `r` is the layer-`0` one at shifted times.** -/
theorem treeApp_shift (δ r : ℝ) (F : Mom d → ℝ) (X : RegChain) (ζ : ℤˣ) (t s : ℝ) (k : Mom d) :
    X.app δ r F ζ t s k = X.app δ 0 F ζ (t - r) (s - r) k := by
  simp only [RegChain.app, JBtree_shift r X t s]

end WaveTurbulence.Regref
