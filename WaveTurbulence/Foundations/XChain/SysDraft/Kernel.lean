/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SysDraft.API
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite

/-!
# D2 SYS-DEFS API, part 2: the kernels `KG` and the truncated sums (scratch, snapshot 4)

* **Locality in the inputs.**
  - `kernelK`/`KG` see the inputs `F` only at the layers of their nodes.
  - `truncSum q`/`truncSumC q` see only `F_0, …, F_{q-1}` (layers of `𝒢^tr_q`/`𝒞^tr_q` are `< q`,
    CANON `layer_le_of_isCanonGC`).
  - Hence `truncSum (inputsF P R) q` depends only on `R_0, …, R_{q-1}`. This is the induction structure of
    `propansatz`.
* **Absolute summability** of the `KG` decoration sums for plain gardens (from the B1 obligation
  `summable_kernelK_summand`).
* **Gauge vanishing.**
  - A plain garden has `∑_j ζ_j = 0`: the sum rule with the constant decoration `1`, and the pairing
    involution reverses leaf signs.
  - So `truncSum q N t ζ n = 0` unless `∑ ζ_j = 0`.
  - Momentum vanishing (`∑ ζ_j n_j ≠ 0`) is CANON's `truncSum_eq_zero_of_unbalanced`.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.SysAPI

section Locality

variable (L γ δ : ℝ) {d w : ℕ}

/-- `kernelK` depends on the inputs only through their values at the layers of the garden's nodes. -/
theorem kernelK_congr_inputs {F F' : ℕ → Mom d → ℝ} (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) (h : ∀ a : GNode LG.garden.tree, F (LG.layer a) = F' (LG.layer a)) :
    kernelK L γ δ F LG up s k₀ nroot nfl = kernelK L γ δ F' LG up s k₀ nroot nfl := by
  unfold kernelK
  simp only [h]

theorem KG_congr_inputs {F F' : ℕ → Mom d → ℝ} (LG : LayeredGarden w) (t : ℝ)
    (n : Fin w → (Fin d → ℤ)) (h : ∀ a : GNode LG.garden.tree, F (LG.layer a) = F' (LG.layer a)) :
    KG L γ δ F LG t n = KG L γ δ F' LG t n :=
  kernelK_congr_inputs L γ δ LG _ _ _ _ _ h

theorem KQ_congr_inputs {F F' : ℕ → Mom d → ℝ} (LG : LayeredGarden 2) (t : ℝ) (k : Mom d)
    (h : ∀ a : GNode LG.garden.tree, F (LG.layer a) = F' (LG.layer a)) :
    KQ L γ δ F LG t k = KQ L γ δ F' LG t k :=
  kernelK_congr_inputs L γ δ LG _ _ _ _ _ h

/-- **Locality of `truncSum`:** `𝒦^tr_q` uses only the inputs `F_0, …, F_{q-1}`. -/
theorem truncSum_congr_inputs (P : WTParams) {F F' : ℕ → Mom P.d → ℝ} (q N : ℕ) {w : ℕ} (t : ℝ)
    (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) (h : ∀ r < q, F r = F' r) :
    truncSum P F q N t ζ n = truncSum P F' q N t ζ n := by
  unfold truncSum
  refine finsum_congr fun LG => finsum_congr fun hLG => ?_
  rcases q with _ | p
  · exact absurd hLG.1 (by simp [IsCanonGC])
  · exact KG_congr_inputs _ _ _ LG t n fun a =>
      h _ (Nat.lt_succ_of_le (Canon.layer_le_of_isCanonGC hLG.1 a))

/-- **Locality of `truncSumC`.** -/
theorem truncSumC_congr_inputs (P : WTParams) {F F' : ℕ → Mom P.d → ℝ} (q N : ℕ) (t : ℝ)
    (k : Mom P.d) (h : ∀ r < q, F r = F' r) :
    truncSumC P F q N t k = truncSumC P F' q N t k := by
  unfold truncSumC
  refine finsum_congr fun LG => finsum_congr fun hLG => ?_
  rcases q with _ | p
  · exact absurd hLG.1 (by simp [IsCanonC])
  · exact KQ_congr_inputs _ _ _ LG t k fun a =>
      h _ (Nat.lt_succ_of_le (Canon.layer_le_of_isCanonC hLG.1 a))

/-- `truncSum (inputsF P R) q` depends only on `R_0, …, R_{q-1}`. -/
theorem truncSum_inputsF_congr (P : WTParams) {R R' : ℕ → Mom P.d → ℝ} (q N : ℕ) {w : ℕ} (t : ℝ)
    (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) (h : ∀ r < q, R r = R' r) :
    truncSum P (inputsF P R) q N t ζ n = truncSum P (inputsF P R') q N t ζ n :=
  truncSum_congr_inputs P q N t ζ n fun r hr => by
    funext k
    simp only [inputsF, h r hr]

theorem truncSumC_inputsF_congr (P : WTParams) {R R' : ℕ → Mom P.d → ℝ} (q N : ℕ) (t : ℝ)
    (k : Mom P.d) (h : ∀ r < q, R r = R' r) :
    truncSumC P (inputsF P R) q N t k = truncSumC P (inputsF P R') q N t k :=
  truncSumC_congr_inputs P q N t k fun r hr => by
    funext k
    simp only [inputsF, h r hr]

end Locality

/-! ## Absolute summability of the `KG` decoration sums -/

section Summability

variable (L γ δ : ℝ) {d w : ℕ}

/-- For a plain garden (no marked leaves; every `𝒢^tr_q`, `𝒞^tr_q`), the decoration sum of
`K_𝒢(t, n⃗)` converges absolutely when the inputs have summable lattice values. -/
theorem summable_KG_summand (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (hplain : LG.garden.IsPlain) (t : ℝ) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ r, Summable fun m : Fin d → ℤ => |F r (latticePoint L m)|) :
    Summable fun κ : GenDecoration LG.garden d n 0 =>
      ‖(epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) 0) 0
          (cosetDecoration LG.garden L 0 κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L 0 κ.1 ℓ.toNode) : ℂ)‖ := by
  have hnl : ∀ ℓ, ¬ LG.garden.IsLone ℓ := fun ℓ h => by simp [Garden.IsLone, hplain ℓ] at h
  refine summable_kernelK_summand L γ δ F LG _ 0 0 n 0 (fun j => ?_) fun ℓ _ => ?_
  · simp [hnl]
  · simpa only [zero_add] using hF (LG.layer ℓ.toNode)

end Summability

/-! ## Gauge vanishing -/

section Gauge

variable {w : ℕ}

/-- In a plain garden the signature sums to zero: `∑_j ζ_j = 0`. -/
theorem Garden.sum_sig_eq_zero (G : Garden w) (hG : G.IsPlain) : ∑ j, ((G.sig j : ℤˣ) : ℤ) = 0 := by
  classical
  -- the sum rule with the constant labelling `1` at the roots
  have hroot : ∀ j, ((G.sig j : ℤˣ) : ℤ) =
      ∑ ℓ ∈ (GNode.root G.tree j).leavesBelow, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) := by
    intro j
    have h := sum_rule G.sig (fun _ : GNode G.tree => (1 : ℤ)) (fun _ => by ring) (GNode.root G.tree j)
    simp only [smul_eq_mul, mul_one] at h
    rw [← h]
    simp [nodeSign, TTree.pathSign, GNode.root]
  -- the leaves below the roots partition all leaves
  have hpart : ∑ j, ∑ ℓ ∈ (GNode.root G.tree j).leavesBelow, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) =
      ∑ ℓ : GLeaf G.tree, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) := by
    have hmem : ∀ j (ℓ : GLeaf G.tree), ℓ ∈ (GNode.root G.tree j).leavesBelow ↔ ℓ.1.1 = j := by
      intro j ℓ
      rw [GNode.leavesBelow, Finset.mem_filter]
      exact ⟨fun h => h.2.1.symm, fun h => ⟨Finset.mem_univ _, h.symm, List.nil_prefix⟩⟩
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (GLeaf G.tree)) (fun ℓ => ℓ.1.1)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr ?_ fun _ _ => rfl
    ext ℓ
    simp [hmem]
  -- the pairing involution reverses the leaf signs
  have hinv : ∑ ℓ : GLeaf G.tree, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) =
      -∑ ℓ : GLeaf G.tree, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) := by
    have hpe : Function.Bijective G.pair :=
      Function.Involutive.bijective fun ℓ => G.pair_pair ℓ
    rw [← Finset.sum_neg_distrib]
    refine (Fintype.sum_bijective G.pair hpe _ _ fun ℓ => ?_).symm
    have hne : G.pair ℓ ≠ ℓ := fun h => ((G.pair_eq_iff ℓ).1 h) (hG ℓ)
    rw [G.pair_sign ℓ hne, Units.val_neg]
  have h2 : ∑ ℓ : GLeaf G.tree, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) = 0 := by linarith
  rw [Finset.sum_congr rfl fun j _ => hroot j, hpart, h2]

/-- **Gauge vanishing:** `𝒦^tr_q(t; ζ⃗, n⃗) = 0` unless `∑_j ζ_j = 0`. -/
theorem truncSum_eq_zero_of_sum_sig_ne_zero (P : WTParams) (F : ℕ → Mom P.d → ℝ) (q N : ℕ)
    (t : ℝ) (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) (hζ : ∑ j, ((ζ j : ℤˣ) : ℤ) ≠ 0) :
    truncSum P F q N t ζ n = 0 := by
  classical
  unfold truncSum
  refine finsum_eq_zero_of_forall_eq_zero fun LG => ?_
  rw [finsum_eq_if]
  split_ifs with hLG
  · rcases q with _ | p
    · exact absurd hLG.1 (by simp [IsCanonGC])
    · exact absurd (hLG.2.2.1 ▸ Garden.sum_sig_eq_zero LG.garden hLG.1.1) hζ
  · rfl

end Gauge

end WaveTurbulence.SysAPI
