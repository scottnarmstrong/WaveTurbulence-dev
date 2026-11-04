/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Chain
public import WaveTurbulence.Foundations.ClassJR.Lemma58

/-!
# DH21 Lemma 5.10: the expansion of `I_{β₁+λ₁} ⋯ I_{β_{2m}+λ_{2m}}`

For a legal code `c` (pairs `q, q+1, …`), `pchain c q` is the kernel of the pure regular chain
`I_{β₁+λ₁} ⋯ I_{β_{2m}+λ_{2m}}`: it is `chainX` with every `X_a = Id` (`chainX_none`). DH21 Lemma 5.10
(L1084–L1096) expands it as `∑_{Z ⊆ adj} ∏_{j∈Z} χ_∞(α_j)/(ε_jπiα_j) · Ĩ_Z` over the subsets `Z` of the
set `adj` of adjacent pairs `{a, a+1}` (`adjSet`). Each adjacent pair contributes, by Lemma 5.8,
`I_{εα_j}I_{μ_j-εα_j} = Φ(εα_j) 𝒥_{α[ ],μ_j} + (𝒥_{α_j,μ_j} + ℛ_{α_j,μ_j})` with
`𝒥_{α[ ],μ_j} = -I_{μ_j}` (`T0`) and `𝒥 + ℛ = I I - Φ 𝒥_{α[ ]}` (`TR58`). The term `Ĩ_Z` is
`tildeP Z c q`. It is class `J` plus class `R` in the variables `α_j`, `j ∉ Z ∩ adj` (`Wv_eq`),
with norm `≤ C510 θ ^ m` (`tildeP_MJR`). The identity holds pointwise (`pchain_expand`).
`lemma510` packages the three statements.

`Ĩ_Z` is built by the Catalan recursion:
* an adjacent pair contributes its Lemma 5.8 piece (`piece58`);
* a non-adjacent pair contributes the sandwich `I_{εα_q} Ĩ I_{μ_q-εα_q}` of the inner expansion
  (Lemmas 5.6–5.7);
* consecutive blocks are composed (Lemmas 5.3–5.5).

This is DH21's construction (remove the adjacent pairs, then apply Lemma 5.9 to the rest) done in
one recursion.
-/

public section

open MeasureTheory Filter Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Defs

variable {P : Type*} {V : Type} (σ : ℕ → V) (ε : ℕ → ℤ) (μf : ℕ → P → ℝ)

/-- `I_{ε_qα_q} I_{μ_q - ε_qα_q}`. -/
@[expose] noncomputable def sw0 (q : ℕ) : P → (V → ℝ) → ℝ → ℝ → ℂ :=
  fun p α => kcomp (iker (ε q * α (σ q))) (iker (μf q p - ε q * α (σ q)))

/-- `𝒥_{α[ ],μ_q} = -I_{μ_q}`. -/
@[expose] noncomputable def T0 (q : ℕ) : P → (V → ℝ) → ℝ → ℝ → ℂ :=
  fun p _ t s => -iker (μf q p) t s

/-- `Φ(ε_qα_q) = χ_∞(α_q)/(ε_qπiα_q)` (`phiR_sign`). -/
@[expose] noncomputable def phiQ (q : ℕ) (α : V → ℝ) : ℂ := phiR (ε q * α (σ q))

/-- `𝒥_{α_q,μ_q} + ℛ_{α_q,μ_q} = I_{ε_qα_q} I_{μ_q-ε_qα_q} - Φ(ε_qα_q) 𝒥_{α[ ],μ_q}`. -/
@[expose] noncomputable def TR58 (q : ℕ) : P → (V → ℝ) → ℝ → ℝ → ℂ :=
  fun p α t s => sw0 σ ε μf q p α t s - phiQ σ ε q α * T0 μf q p α t s

/-- **The pure regular chain kernel** `I_{β₁+λ₁} ⋯ I_{β_{2m}+λ_{2m}}` (meaningful for `c ≠ nil`). -/
@[expose] noncomputable def pchain : LegalCode → ℕ → P → (V → ℝ) → ℝ → ℝ → ℂ
  | .nil, _ => fun _ _ _ _ => 0
  | .node .nil .nil, q => sw0 σ ε μf q
  | .node .nil (.node a b), q => fun p α => kcomp (sw0 σ ε μf q p α) (pchain (.node a b) (q + 1) p α)
  | .node (.node a b) .nil, q => sandw (ε q) (σ q) (μf q) (pchain (.node a b) (q + 1))
  | .node (.node a b) (.node c d), q => fun p α =>
      kcomp (sandw (ε q) (σ q) (μf q) (pchain (.node a b) (q + 1)) p α)
        (pchain (.node c d) (q + (LegalCode.node a b).size + 1) p α)

/-- The adjacent pairs `{a, a+1}` of a code. -/
@[expose] def adjSet : LegalCode → ℕ → Finset ℕ
  | .nil, _ => ∅
  | .node .nil r, q => insert q (adjSet r (q + 1))
  | .node (.node a b) r, q => adjSet (.node a b) (q + 1) ∪ adjSet r (q + (LegalCode.node a b).size + 1)

variable (Z : Finset ℕ)

/-- The Lemma 5.8 piece of an adjacent pair: `𝒥_{α[ ]}` if the pair is in `Z`, `𝒥 + ℛ` otherwise. -/
@[expose] noncomputable def piece58 (q : ℕ) : P → (V → ℝ) → ℝ → ℝ → ℂ :=
  if q ∈ Z then T0 μf q else TR58 σ ε μf q

/-- **The operator `Ĩ_Z`** of DH21 Lemma 5.10. -/
@[expose] noncomputable def tildeP : LegalCode → ℕ → P → (V → ℝ) → ℝ → ℝ → ℂ
  | .nil, _ => fun _ _ _ _ => 0
  | .node .nil .nil, q => piece58 σ ε μf Z q
  | .node .nil (.node a b), q => fun p α =>
      kcomp (piece58 σ ε μf Z q p α) (tildeP (.node a b) (q + 1) p α)
  | .node (.node a b) .nil, q => sandw (ε q) (σ q) (μf q) (tildeP (.node a b) (q + 1))
  | .node (.node a b) (.node c d), q => fun p α =>
      kcomp (sandw (ε q) (σ q) (μf q) (tildeP (.node a b) (q + 1)) p α)
        (tildeP (.node c d) (q + (LegalCode.node a b).size + 1) p α)

/-- The variables `α_j`, `j ∉ Z`, of `Ĩ_Z`. -/
@[expose] def Wv : LegalCode → ℕ → Set V
  | .nil, _ => ∅
  | .node .nil r, q => (if q ∈ Z then ∅ else {σ q}) ∪ Wv r (q + 1)
  | .node (.node a b) r, q => insert (σ q) (Wv (.node a b) (q + 1)) ∪
      Wv r (q + (LegalCode.node a b).size + 1)

end Defs

/-! ### Supports -/

section Support

variable {P : Type*} {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

theorem mem_adjSet : ∀ (c : LegalCode) (q j : ℕ), j ∈ adjSet c q → q ≤ j ∧ j < q + c.size
  | .nil, q, j, h => by simp [adjSet] at h
  | .node .nil r, q, j, h => by
    simp only [adjSet, Finset.mem_insert] at h
    simp only [LegalCode.size]
    rcases h with rfl | h
    · omega
    · have := mem_adjSet r (q + 1) j h; omega
  | .node (.node a b) r, q, j, h => by
    simp only [adjSet, Finset.mem_union] at h
    have hs : (LegalCode.node (.node a b) r).size = (LegalCode.node a b).size + r.size + 1 := rfl
    rw [hs]
    rcases h with h | h
    · have := mem_adjSet (.node a b) (q + 1) j h; omega
    · have := mem_adjSet r _ j h; omega

theorem card_adjSet_le : ∀ (c : LegalCode) (q : ℕ), (adjSet c q).card ≤ c.size
  | .nil, q => by simp [adjSet, LegalCode.size]
  | .node .nil r, q => by
    simp only [adjSet, LegalCode.size]
    have := card_adjSet_le r (q + 1)
    have := Finset.card_insert_le q (adjSet r (q + 1))
    omega
  | .node (.node a b) r, q => by
    simp only [adjSet]
    have hs : (LegalCode.node (.node a b) r).size = (LegalCode.node a b).size + r.size + 1 := rfl
    rw [hs]
    have := card_adjSet_le (.node a b) (q + 1)
    have := card_adjSet_le r (q + (LegalCode.node a b).size + 1)
    have := Finset.card_union_le (adjSet (.node a b) (q + 1))
      (adjSet r (q + (LegalCode.node a b).size + 1))
    omega

theorem piece58_congr {Z Z' : Finset ℕ} {q : ℕ} (h : q ∈ Z ↔ q ∈ Z') :
    piece58 σ ε μf Z q = piece58 σ ε μf Z' q := by
  simp only [piece58, h]

/-- `Ĩ_Z` only depends on `Z ∩ adj`. -/
theorem tildeP_congr : ∀ (c : LegalCode) (q : ℕ) {Z Z' : Finset ℕ},
    (∀ j ∈ adjSet c q, j ∈ Z ↔ j ∈ Z') → tildeP σ ε μf Z c q = tildeP σ ε μf Z' c q
  | .nil, q, Z, Z', _ => by simp only [tildeP]
  | .node .nil .nil, q, Z, Z', h => by
    simp only [tildeP]
    exact piece58_congr (h q (by simp [adjSet]))
  | .node .nil (.node a b), q, Z, Z', h => by
    have h1 : ∀ j ∈ adjSet (.node a b) (q + 1), j ∈ Z ↔ j ∈ Z' := fun j hj =>
      h j (by simp only [adjSet]; exact Finset.mem_insert_of_mem hj)
    simp only [tildeP]
    rw [piece58_congr (h q (by simp [adjSet])), tildeP_congr (.node a b) (q + 1) h1]
  | .node (.node a b) .nil, q, Z, Z', h => by
    have h1 : ∀ j ∈ adjSet (.node a b) (q + 1), j ∈ Z ↔ j ∈ Z' := fun j hj =>
      h j (by simp only [adjSet]; exact Finset.mem_union_left _ hj)
    simp only [tildeP]
    rw [tildeP_congr (.node a b) (q + 1) h1]
  | .node (.node a b) (.node c d), q, Z, Z', h => by
    have h1 : ∀ j ∈ adjSet (.node a b) (q + 1), j ∈ Z ↔ j ∈ Z' := fun j hj =>
      h j (by simp only [adjSet]; exact Finset.mem_union_left _ hj)
    have h2 : ∀ j ∈ adjSet (.node c d) (q + (LegalCode.node a b).size + 1), j ∈ Z ↔ j ∈ Z' :=
      fun j hj => h j (by simp only [adjSet]; exact Finset.mem_union_right _ hj)
    simp only [tildeP]
    rw [tildeP_congr (.node a b) (q + 1) h1, tildeP_congr (.node c d) _ h2]

theorem Wv_subset (Z : Finset ℕ) :
    ∀ (c : LegalCode) (q : ℕ), Wv σ Z c q ⊆ σ '' Set.Ico q (q + c.size)
  | .nil, q => by simp [Wv]
  | .node .nil r, q => by
    simp only [Wv]
    refine Set.union_subset ?_ ((Wv_subset Z r (q + 1)).trans (Set.image_mono ?_))
    · split_ifs
      · exact Set.empty_subset _
      · exact Set.singleton_subset_iff.2 ⟨q, ⟨le_rfl, by simp [LegalCode.size]⟩, rfl⟩
    · intro j hj; simp only [Set.mem_Ico, LegalCode.size] at hj ⊢; omega
  | .node (.node a b) r, q => by
    simp only [Wv]
    have hs : (LegalCode.node (.node a b) r).size = (LegalCode.node a b).size + r.size + 1 := rfl
    rw [hs]
    refine Set.union_subset (Set.insert_subset ⟨q, ⟨le_rfl, by omega⟩, rfl⟩
      ((Wv_subset Z _ (q + 1)).trans (Set.image_mono ?_)))
      ((Wv_subset Z r _).trans (Set.image_mono ?_))
    · intro j hj; simp only [Set.mem_Ico] at hj ⊢; omega
    · intro j hj; simp only [Set.mem_Ico] at hj ⊢; omega

theorem disjoint_image_of_injOn {U S₁ S₂ : Set ℕ} (hinj : Set.InjOn σ U) (h₁ : S₁ ⊆ U)
    (h₂ : S₂ ⊆ U) (hd : Disjoint S₁ S₂) : Disjoint (σ '' S₁) (σ '' S₂) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, hji⟩
  exact Set.disjoint_left.1 hd hi (hinj (h₂ hj) (h₁ hi) hji ▸ hj)

end Support

/-! ### Continuity and linearity -/

section Linear

variable {P : Type*} {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

theorem kcomp_finsetSum_right {ι : Type*} (S : Finset ι) (K : ℝ → ℝ → ℂ) (L : ι → ℝ → ℝ → ℂ)
    (hK : Continuous fun x : ℝ × ℝ => K x.1 x.2)
    (hL : ∀ i, Continuous fun x : ℝ × ℝ => L i x.1 x.2) (t s : ℝ) :
    kcomp K (fun t s => ∑ i ∈ S, L i t s) t s = ∑ i ∈ S, kcomp K (L i) t s := by
  simp only [kcomp, Finset.mul_sum]
  exact intervalIntegral.integral_finsetSum fun i _ =>
    ((hK.comp (continuous_const.prodMk continuous_id)).mul
      ((hL i).comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _

theorem kcomp_finsetSum_left {ι : Type*} (S : Finset ι) (K : ι → ℝ → ℝ → ℂ) (L : ℝ → ℝ → ℂ)
    (hK : ∀ i, Continuous fun x : ℝ × ℝ => K i x.1 x.2)
    (hL : Continuous fun x : ℝ × ℝ => L x.1 x.2) (t s : ℝ) :
    kcomp (fun t s => ∑ i ∈ S, K i t s) L t s = ∑ i ∈ S, kcomp (K i) L t s := by
  simp only [kcomp, Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i _ =>
    (((hK i).comp (continuous_const.prodMk continuous_id)).mul
      (hL.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _

theorem kcomp_const_mul_right (c : ℂ) (K L : ℝ → ℝ → ℂ) (t s : ℝ) :
    kcomp K (fun t s => c * L t s) t s = c * kcomp K L t s := by
  have e : ∀ z, K t z * (c * L z s) = c * (K t z * L z s) := fun z => by ring
  simp only [kcomp, e]
  exact intervalIntegral.integral_const_mul _ _

theorem continuous_const_mul_kernel (c : ℂ) {K : ℝ → ℝ → ℂ}
    (hK : Continuous fun x : ℝ × ℝ => K x.1 x.2) :
    Continuous fun x : ℝ × ℝ => c * K x.1 x.2 :=
  continuous_const.mul hK

/-- `K (Σ bⱼ Lⱼ) = Σ bⱼ K Lⱼ`. -/
theorem kcomp_sum_smul_right {ι : Type*} (S : Finset ι) (b : ι → ℂ) (K : ℝ → ℝ → ℂ)
    (L : ι → ℝ → ℝ → ℂ) (hK : Continuous fun x : ℝ × ℝ => K x.1 x.2)
    (hL : ∀ i, Continuous fun x : ℝ × ℝ => L i x.1 x.2) (t s : ℝ) :
    kcomp K (fun t s => ∑ i ∈ S, b i * L i t s) t s = ∑ i ∈ S, b i * kcomp K (L i) t s := by
  rw [kcomp_finsetSum_right S K (fun i t s => b i * L i t s) hK
    (fun i => continuous_const.mul (hL i))]
  exact Finset.sum_congr rfl fun i _ => kcomp_const_mul_right _ _ _ _ _

/-- `(Σ aᵢ Kᵢ) L = Σ aᵢ Kᵢ L`. -/
theorem kcomp_sum_smul_left {ι : Type*} (S : Finset ι) (a : ι → ℂ) (K : ι → ℝ → ℝ → ℂ)
    (L : ℝ → ℝ → ℂ) (hK : ∀ i, Continuous fun x : ℝ × ℝ => K i x.1 x.2)
    (hL : Continuous fun x : ℝ × ℝ => L x.1 x.2) (t s : ℝ) :
    kcomp (fun t s => ∑ i ∈ S, a i * K i t s) L t s = ∑ i ∈ S, a i * kcomp (K i) L t s := by
  rw [kcomp_finsetSum_left S (fun i t s => a i * K i t s) L
    (fun i => continuous_const.mul (hK i)) hL]
  exact Finset.sum_congr rfl fun i _ => kcomp_const_mul _ _ _ _ _

/-- `Σ_{Z ⊆ A ∪ B} F Z = Σ_{Z₁ ⊆ A} Σ_{Z₂ ⊆ B} F (Z₁ ∪ Z₂)` for disjoint `A`, `B`. -/
theorem sum_powerset_union {M : Type*} [AddCommMonoid M] {B : Finset ℕ} :
    ∀ {A : Finset ℕ}, Disjoint A B → ∀ F : Finset ℕ → M,
      ∑ Z ∈ (A ∪ B).powerset, F Z = ∑ Z₁ ∈ A.powerset, ∑ Z₂ ∈ B.powerset, F (Z₁ ∪ Z₂) := by
  intro A
  induction A using Finset.induction_on with
  | empty => intro _ F; simp
  | insert a A ha ih =>
    intro hd F
    have hdA : Disjoint A B := Finset.disjoint_of_subset_left (Finset.subset_insert a A) hd
    have haB : a ∉ B := Finset.disjoint_left.1 hd (Finset.mem_insert_self a A)
    have haAB : a ∉ A ∪ B := by simp [ha, haB]
    rw [Finset.insert_union, Finset.sum_powerset_insert haAB, Finset.sum_powerset_insert ha,
      ih hdA F, ih hdA fun Z => F (insert a Z)]
    congr 1
    exact Finset.sum_congr rfl fun Z₁ _ => Finset.sum_congr rfl fun Z₂ _ => by
      rw [Finset.insert_union]

theorem prod_union_of_sub {w : ℕ → ℂ} {A B Z₁ Z₂ : Finset ℕ} (hd : Disjoint A B) (h₁ : Z₁ ⊆ A)
    (h₂ : Z₂ ⊆ B) : ∏ j ∈ Z₁ ∪ Z₂, w j = (∏ j ∈ Z₁, w j) * ∏ j ∈ Z₂, w j :=
  Finset.prod_union (Finset.disjoint_of_subset_left h₁ (Finset.disjoint_of_subset_right h₂ hd))

/-- **Composing two expansions.** -/
theorem kcomp_expand {A B : Finset ℕ} (hd : Disjoint A B) (w : ℕ → ℂ) (K L : ℝ → ℝ → ℂ)
    (F G H : Finset ℕ → ℝ → ℝ → ℂ)
    (hK : ∀ t s, K t s = ∑ Z ∈ A.powerset, (∏ j ∈ Z, w j) * F Z t s)
    (hL : ∀ t s, L t s = ∑ Z ∈ B.powerset, (∏ j ∈ Z, w j) * G Z t s)
    (hF : ∀ Z, Continuous fun x : ℝ × ℝ => F Z x.1 x.2)
    (hG : ∀ Z, Continuous fun x : ℝ × ℝ => G Z x.1 x.2)
    (hH : ∀ Z₁ ⊆ A, ∀ Z₂ ⊆ B, H (Z₁ ∪ Z₂) = kcomp (F Z₁) (G Z₂)) (t s : ℝ) :
    kcomp K L t s = ∑ Z ∈ (A ∪ B).powerset, (∏ j ∈ Z, w j) * H Z t s := by
  have eK : K = fun t s => ∑ Z ∈ A.powerset, (∏ j ∈ Z, w j) * F Z t s := funext fun t => funext (hK t)
  have eL : L = fun t s => ∑ Z ∈ B.powerset, (∏ j ∈ Z, w j) * G Z t s := funext fun t => funext (hL t)
  have hcL : Continuous fun x : ℝ × ℝ => L x.1 x.2 := by
    rw [eL]; exact continuous_finsetSum _ fun Z _ => continuous_const.mul (hG Z)
  have e1 : ∀ Z₁, kcomp (F Z₁) L t s =
      ∑ Z₂ ∈ B.powerset, (∏ j ∈ Z₂, w j) * kcomp (F Z₁) (G Z₂) t s := fun Z₁ => by
    rw [eL]; exact kcomp_sum_smul_right _ _ _ _ (hF Z₁) hG t s
  rw [eK, kcomp_sum_smul_left _ _ _ _ hF hcL, sum_powerset_union hd]
  refine Finset.sum_congr rfl fun Z₁ hZ₁ => ?_
  rw [e1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z₂ hZ₂ => ?_
  rw [Finset.mem_powerset] at hZ₁ hZ₂
  rw [prod_union_of_sub hd hZ₁ hZ₂, hH Z₁ hZ₁ Z₂ hZ₂]
  ring

/-- **Sandwiching an expansion.** -/
theorem sandwich_expand {A : Finset ℕ} (w : ℕ → ℂ) (K Lft Rgt : ℝ → ℝ → ℂ)
    (F : Finset ℕ → ℝ → ℝ → ℂ) (hK : ∀ t s, K t s = ∑ Z ∈ A.powerset, (∏ j ∈ Z, w j) * F Z t s)
    (hF : ∀ Z, Continuous fun x : ℝ × ℝ => F Z x.1 x.2)
    (hl : Continuous fun x : ℝ × ℝ => Lft x.1 x.2) (hr : Continuous fun x : ℝ × ℝ => Rgt x.1 x.2)
    (t s : ℝ) :
    kcomp (kcomp Lft K) Rgt t s =
      ∑ Z ∈ A.powerset, (∏ j ∈ Z, w j) * kcomp (kcomp Lft (F Z)) Rgt t s := by
  have eK : K = fun t s => ∑ Z ∈ A.powerset, (∏ j ∈ Z, w j) * F Z t s := funext fun t => funext (hK t)
  have e1 : kcomp Lft K = fun t s => ∑ Z ∈ A.powerset, (∏ j ∈ Z, w j) * kcomp Lft (F Z) t s := by
    funext t s; rw [eK]; exact kcomp_sum_smul_right _ _ _ _ hl hF t s
  rw [e1]
  exact kcomp_sum_smul_left _ _ _ _ (fun Z => continuous_kcomp hl (hF Z)) hr t s

theorem continuous_sw0 (q : ℕ) (p : P) (α : V → ℝ) :
    Continuous fun x : ℝ × ℝ => sw0 σ ε μf q p α x.1 x.2 :=
  continuous_kcomp (continuous_iker _) (continuous_iker _)

theorem continuous_T0 (q : ℕ) (p : P) (α : V → ℝ) :
    Continuous fun x : ℝ × ℝ => T0 μf q p α x.1 x.2 :=
  (continuous_iker _).neg

theorem continuous_piece58 (Z : Finset ℕ) (q : ℕ) (p : P) (α : V → ℝ) :
    Continuous fun x : ℝ × ℝ => piece58 σ ε μf Z q p α x.1 x.2 := by
  unfold piece58
  split_ifs
  · exact continuous_T0 q p α
  · exact (continuous_sw0 q p α).sub (continuous_const.mul (continuous_T0 q p α))

theorem continuous_sandw {e : ℤ} {v : V} {m : P → ℝ} {T : P → (V → ℝ) → ℝ → ℝ → ℂ} {p : P}
    {α : V → ℝ} (hT : Continuous fun x : ℝ × ℝ => T p α x.1 x.2) :
    Continuous fun x : ℝ × ℝ => sandw e v m T p α x.1 x.2 :=
  continuous_kcomp (continuous_kcomp (continuous_iker _) hT) (continuous_iker _)

theorem continuous_tildeP (Z : Finset ℕ) (p : P) (α : V → ℝ) :
    ∀ (c : LegalCode) (q : ℕ), Continuous fun x : ℝ × ℝ => tildeP σ ε μf Z c q p α x.1 x.2
  | .nil, q => by simp only [tildeP]; exact continuous_const
  | .node .nil .nil, q => by simp only [tildeP]; exact continuous_piece58 Z q p α
  | .node .nil (.node a b), q => by
    simp only [tildeP]
    exact continuous_kcomp (continuous_piece58 Z q p α) (continuous_tildeP Z p α _ _)
  | .node (.node a b) .nil, q => by
    simp only [tildeP]
    exact continuous_sandw (continuous_tildeP Z p α _ _)
  | .node (.node a b) (.node c d), q => by
    simp only [tildeP]
    exact continuous_kcomp (continuous_sandw (continuous_tildeP Z p α _ _))
      (continuous_tildeP Z p α _ _)

end Linear

/-! ### The expansion identity -/

section Expand

variable {P : Type*} {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

/-- `I_{ε_qα_q} I_{μ_q-ε_qα_q} = Φ(ε_qα_q) 𝒥_{α[ ],μ_q} + (𝒥 + ℛ)` as a sum over `Z ⊆ {q}`. -/
theorem sw0_expand (q : ℕ) (p : P) (α : V → ℝ) (t s : ℝ) :
    sw0 σ ε μf q p α t s = ∑ Z ∈ ({q} : Finset ℕ).powerset,
      (∏ j ∈ Z, phiQ σ ε j α) * piece58 σ ε μf Z q p α t s := by
  rw [← insert_empty_eq q, Finset.sum_powerset_insert (Finset.notMem_empty q)]
  simp [piece58, TR58]

theorem mem_union_iff_left {A B Z₁ Z₂ : Finset ℕ} (hd : Disjoint A B) (h₂ : Z₂ ⊆ B) {j : ℕ}
    (hj : j ∈ A) : j ∈ Z₁ ∪ Z₂ ↔ j ∈ Z₁ := by
  simp only [Finset.mem_union, or_iff_left_iff_imp]
  intro h; exact absurd (h₂ h) (Finset.disjoint_left.1 hd hj)

theorem mem_union_iff_right {A B Z₁ Z₂ : Finset ℕ} (hd : Disjoint A B) (h₁ : Z₁ ⊆ A) {j : ℕ}
    (hj : j ∈ B) : j ∈ Z₁ ∪ Z₂ ↔ j ∈ Z₂ := by
  simp only [Finset.mem_union, or_iff_right_iff_imp]
  intro h; exact absurd hj (Finset.disjoint_left.1 hd (h₁ h))

theorem disjoint_adjSet_nil (r : LegalCode) (q : ℕ) : Disjoint ({q} : Finset ℕ) (adjSet r (q + 1)) := by
  rw [Finset.disjoint_singleton_left]
  intro h; have := mem_adjSet r (q + 1) q h; omega

theorem disjoint_adjSet_node (a b r : LegalCode) (q : ℕ) :
    Disjoint (adjSet (.node a b) (q + 1)) (adjSet r (q + (LegalCode.node a b).size + 1)) := by
  rw [Finset.disjoint_left]
  intro j h1 h2
  have := mem_adjSet _ _ j h1; have := mem_adjSet _ _ j h2; omega

/-- **The expansion identity of DH21 Lemma 5.10**: `I_{β₁+λ₁} ⋯ I_{β_{2m}+λ_{2m}} =
∑_{Z ⊆ adj} ∏_{j ∈ Z} Φ(ε_jα_j) · Ĩ_Z`, pointwise. -/
theorem pchain_expand (p : P) (α : V → ℝ) : ∀ (c : LegalCode) (q : ℕ) (t s : ℝ),
    pchain σ ε μf c q p α t s = ∑ Z ∈ (adjSet c q).powerset,
      (∏ j ∈ Z, phiQ σ ε j α) * tildeP σ ε μf Z c q p α t s
  | .nil, q, t, s => by simp [pchain, adjSet, tildeP]
  | .node .nil .nil, q, t, s => by
    simp only [pchain, adjSet, tildeP, Finset.insert_empty]
    exact sw0_expand q p α t s
  | .node .nil (.node a b), q, t, s => by
    simp only [pchain]
    have hA := disjoint_adjSet_nil (.node a b) q
    have e : adjSet (.node .nil (.node a b)) q = {q} ∪ adjSet (.node a b) (q + 1) := by
      simp only [adjSet]; exact Finset.insert_eq _ _
    rw [e]
    refine kcomp_expand hA _ _ _ (fun Z => piece58 σ ε μf Z q p α)
      (fun Z => tildeP σ ε μf Z (.node a b) (q + 1) p α)
      (fun Z => tildeP σ ε μf Z (.node .nil (.node a b)) q p α)
      (sw0_expand q p α) (pchain_expand p α (.node a b) (q + 1))
      (fun Z => continuous_piece58 Z q p α) (fun Z => continuous_tildeP Z p α _ _)
      (fun Z₁ h₁ Z₂ h₂ => ?_) t s
    simp only [tildeP]
    rw [piece58_congr (mem_union_iff_left hA h₂ (Finset.mem_singleton_self q)),
      tildeP_congr (.node a b) (q + 1) fun j hj => mem_union_iff_right hA h₁ hj]
  | .node (.node a b) .nil, q, t, s => by
    simp only [pchain, sandw, tildeP]
    have e : adjSet (.node (.node a b) .nil) q = adjSet (.node a b) (q + 1) := by
      simp [adjSet]
    rw [e]
    exact sandwich_expand _ _ _ _ (fun Z => tildeP σ ε μf Z (.node a b) (q + 1) p α)
      (pchain_expand p α (.node a b) (q + 1)) (fun Z => continuous_tildeP Z p α _ _)
      (continuous_iker _) (continuous_iker _) t s
  | .node (.node a b) (.node c d), q, t, s => by
    simp only [pchain]
    have hA := disjoint_adjSet_node a b (.node c d) q
    have e : adjSet (.node (.node a b) (.node c d)) q = adjSet (.node a b) (q + 1) ∪
        adjSet (.node c d) (q + (LegalCode.node a b).size + 1) := by
      simp only [adjSet]
    rw [e]
    refine kcomp_expand hA _ _ _ (fun Z => sandw (ε q) (σ q) (μf q) (tildeP σ ε μf Z (.node a b) (q + 1)) p α)
      (fun Z => tildeP σ ε μf Z (.node c d) (q + (LegalCode.node a b).size + 1) p α)
      (fun Z => tildeP σ ε μf Z (.node (.node a b) (.node c d)) q p α)
      (fun t s => sandwich_expand _ _ _ _ (fun Z => tildeP σ ε μf Z (.node a b) (q + 1) p α)
        (pchain_expand p α (.node a b) (q + 1)) (fun Z => continuous_tildeP Z p α _ _)
        (continuous_iker _) (continuous_iker _) t s)
      (pchain_expand p α (.node c d) _)
      (fun Z => continuous_sandw (continuous_tildeP Z p α _ _)) (fun Z => continuous_tildeP Z p α _ _)
      (fun Z₁ h₁ Z₂ h₂ => ?_) t s
    simp only [tildeP]
    rw [tildeP_congr (.node a b) (q + 1) fun j hj => mem_union_iff_left hA h₂ hj,
      tildeP_congr (.node c d) _ fun j hj => mem_union_iff_right hA h₁ hj]

end Expand

/-! ### The chain operator with all `X_a = Id` -/

section Link

variable {P : Type*} {V : Type} (σ : ℕ → V) (ε : ℕ → ℤ) (μf : ℕ → P → ℝ)

theorem chainX_node (X : ℕ → Option (P → (V → ℝ) → ℝ → ℝ → ℂ)) (i r : LegalCode) (o q : ℕ) :
    chainX X σ ε μf (.node i r) o q = ocomp (X o) (ocomp (some (swO (ε q) (σ q) (μf q)
      (chainX X σ ε μf i (o + 1) (q + 1)))) (chainX X σ ε μf r (o + 2 * i.size + 2) (q + i.size + 1))) :=
  rfl

/-- `pchain` is the regular chain operator of Lemma 5.9 with every `X_a` the identity. -/
theorem chainX_none : ∀ (c : LegalCode) (o q : ℕ), c ≠ .nil →
    chainX (fun _ => none) σ ε μf c o q = some (pchain σ ε μf c q)
  | .nil, _, _, h => absurd rfl h
  | .node .nil .nil, o, q, _ => rfl
  | .node .nil (.node a b), o, q, _ => by
    rw [chainX_node, chainX_none (.node a b) _ _ (by simp)]
    simp only [LegalCode.size, add_zero]
    rfl
  | .node (.node a b) .nil, o, q, _ => by
    rw [chainX_node, chainX_none (.node a b) (o + 1) (q + 1) (by simp)]
    rfl
  | .node (.node a b) (.node c d), o, q, _ => by
    rw [chainX_node, chainX_none (.node a b) (o + 1) (q + 1) (by simp),
      chainX_none (.node c d) _ _ (by simp)]
    rfl

end Link

/-! ### The class bounds -/

section Bounds

variable {P : Type*} [MeasurableSpace P] {V : Type} {θ A : ℝ}
variable {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

theorem injective_of_subsingleton' {ι : Type} [Subsingleton ι] (f : ι → V) : Function.Injective f :=
  fun _ _ _ => Subsingleton.elim _ _

/-- `𝒥_{α[ ],μ_q} = -I_{μ_q}` is class `J` in no variables (Lemma 5.8). -/
theorem T0_MJ (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {q : ℕ} (hε : ε q = 1 ∨ ε q = -1)
    (hμ : Measurable (μf q)) : MJ θ A CM0 (∅ : Set V) (T0 μf q) := by
  obtain ⟨T₀, TJ, TR, h₀, _hJ, _hR, hT0, _he⟩ := iker_comp_decompP (A := A) h0 h1 hA hε
  exact ⟨Empty, inferInstance, isEmptyElim, injective_of_subsingleton' _, Set.range_eq_empty _,
    fun p => T₀ (μf q p), h₀.comap hμ, fun p α => (hT0 (μf q p) _).symm⟩

/-- `𝒥_{α_q,μ_q} + ℛ_{α_q,μ_q}` is class `J` plus class `R` in the variable `α_q` (Lemma 5.8). -/
theorem TR58_MJR (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {q : ℕ} (hε : ε q = 1 ∨ ε q = -1)
    (hμ : Measurable (μf q)) : MJR θ A (C58J θ + CM0 * 2) {σ q} (TR58 σ ε μf q) := by
  obtain ⟨T₀, TJ, TR, _h₀, hJ, hR, hT0, he⟩ := iker_comp_decompP (A := A) h0 h1 hA hε
  have hJm : MJ θ A (C58J θ) {σ q} fun p α => TJ (μf q p) (α ∘ fun _ => σ q) :=
    ⟨Option Empty, inferInstance, fun _ => σ q, injective_of_subsingleton' _, Set.range_const,
      fun p => TJ (μf q p), hJ.comap hμ, fun p α => KEqOn.refl _⟩
  have hRm : MR θ A (CM0 * 2) {σ q} (σ q) fun p α => TR (μf q p) (α ∘ fun _ => σ q) :=
    ⟨Empty, inferInstance, fun _ => σ q, injective_of_subsingleton' _, Set.range_const, rfl,
      fun p => TR (μf q p), hR.comap hμ, fun p α => KEqOn.refl _⟩
  refine ⟨_, _, _, _, hJm, Or.inl ⟨σ q, hRm⟩, le_rfl, fun p α t s h0 h1 h2 => ?_⟩
  have e1 := he (μf q p) (α ∘ fun _ => σ q) t s h0 h1 h2
  have e2 := hT0 (μf q p) isEmptyElim t s h0 h1 h2
  simp only [Function.comp_apply] at e1
  simp only [TR58, sw0, phiQ, T0]
  rw [e1, e2]
  ring

/-- The norm of the Lemma 5.8 pieces. -/
@[expose] noncomputable def N58 (θ : ℝ) : ℝ := max CM0 (C58J θ + CM0 * 2)

/-- The variables of the Lemma 5.8 piece of the pair `q`. -/
@[expose] def pieceVars (σ : ℕ → V) (Z : Finset ℕ) (q : ℕ) : Set V :=
  if q ∈ Z then ∅ else {σ q}

theorem piece58_MJR (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {q : ℕ} (hε : ε q = 1 ∨ ε q = -1)
    (hμ : Measurable (μf q)) (Z : Finset ℕ) :
    MJR θ A (N58 θ) (pieceVars σ Z q) (piece58 σ ε μf Z q) := by
  unfold piece58 pieceVars
  split_ifs
  · exact (MJR.of_MJ (T0_MJ h0 h1 hA hε hμ)).mono (le_max_left _ _)
  · exact (TR58_MJR h0 h1 hA hε hμ).mono (le_max_right _ _)

/-- The constant of DH21 Lemma 5.10: `‖Ĩ_Z‖ ≤ C510 θ ^ m`. -/
@[expose] noncomputable def C510 (θ : ℝ) : ℝ := max 1 (Ccp θ) * max 1 (Csw θ) * max 1 (N58 θ)

theorem one_le_C510 (θ : ℝ) : 1 ≤ C510 θ := by
  unfold C510
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _)
    (le_max_left _ _)) (le_max_left _ _)

theorem le_C510 : max 1 (N58 θ) ≤ C510 θ := by
  unfold C510
  exact le_mul_of_one_le_left (zero_le_one.trans (le_max_left _ _))
    (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))

theorem Ccp_nonneg' (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 ≤ Ccp θ := by
  have := CJJ_nonneg; have := CJR_nonneg h0 h1; have := CRR_nonneg θ; unfold Ccp; positivity

theorem C510_bound_comp {N₁ N₂ : ℝ} (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (h₁ : N₁ ≤ max 1 (N58 θ)) : Ccp θ * N₁ * N₂ ≤ C510 θ * N₂ := by
  refine mul_le_mul_of_nonneg_right ?_ hN₂
  unfold C510
  have a := le_max_right 1 (Ccp θ)
  have b : (1 : ℝ) ≤ max 1 (Csw θ) := le_max_left _ _
  have c : (0 : ℝ) ≤ max 1 (Ccp θ) := zero_le_one.trans (le_max_left _ _)
  calc Ccp θ * N₁ ≤ max 1 (Ccp θ) * max 1 (N58 θ) :=
        mul_le_mul a h₁ hN₁ c
    _ ≤ max 1 (Ccp θ) * max 1 (Csw θ) * max 1 (N58 θ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (zero_le_one.trans
          (le_max_left _ _)) b) c

theorem C510_bound_sw (h0 : 0 ≤ θ) (h1 : θ < 1) {N : ℝ} (hN : 0 ≤ N) :
    Csw θ * N ≤ C510 θ * N := by
  refine mul_le_mul_of_nonneg_right ?_ hN
  unfold C510
  have := Csw_nonneg h0 h1
  calc Csw θ ≤ max 1 (Csw θ) := le_max_right _ _
    _ ≤ max 1 (Ccp θ) * max 1 (Csw θ) :=
        le_mul_of_one_le_left (this.trans (le_max_right _ _)) (le_max_left _ _)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (le_max_left _ _)

theorem C510_bound_swcomp (h0 : 0 ≤ θ) (h1 : θ < 1) {N₁ N₂ : ℝ} (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂) :
    Ccp θ * (Csw θ * N₁) * N₂ ≤ C510 θ * N₁ * N₂ := by
  refine mul_le_mul_of_nonneg_right ?_ hN₂
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hN₁
  unfold C510
  have hsw := Csw_nonneg h0 h1
  calc Ccp θ * Csw θ ≤ max 1 (Ccp θ) * max 1 (Csw θ) :=
        mul_le_mul (le_max_right _ _) (le_max_right _ _) hsw (zero_le_one.trans (le_max_left _ _))
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (le_max_left _ _)

/-- **The class bounds of DH21 Lemma 5.10** (L1084–L1096): `Ĩ_Z` is class `J` plus class `R` in the
variables `Wv Z c q` (the `α_j`, `j ∉ Z`), with norm `≤ C510 θ ^ m`, when the variables `α_j` of
the `m` pairs are distinct. -/
theorem tildeP_MJR (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hμ : ∀ j, Measurable (μf j)) (Z : Finset ℕ) :
    ∀ (c : LegalCode) (q : ℕ), c ≠ .nil → Set.InjOn σ (Set.Ico q (q + c.size)) →
      MJR θ A (C510 θ ^ c.size) (Wv σ Z c q) (tildeP σ ε μf Z c q)
  | .nil, _, h, _ => absurd rfl h
  | .node .nil .nil, q, _, _ => by
    have hp := piece58_MJR (σ := σ) h0 h1 hA (hε q) (hμ q) Z
    have hsz : (LegalCode.node .nil .nil).size = 1 := rfl
    simp only [tildeP, Wv, Set.union_empty, hsz, pow_one]
    unfold pieceVars at hp
    exact hp.mono ((le_max_right _ _).trans le_C510)
  | .node .nil (.node a b), q, _, hinj => by
    have hsz : (LegalCode.node .nil (.node a b)).size = (LegalCode.node a b).size + 1 := by
      simp [LegalCode.size]
    rw [hsz] at hinj ⊢
    have hr := tildeP_MJR h0 h1 hA hε hμ Z (.node a b) (q + 1) (by simp)
      (hinj.mono fun j hj => by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hp := piece58_MJR (σ := σ) h0 h1 hA (hε q) (hμ q) Z
    have hd : Disjoint (pieceVars σ Z q) (Wv σ Z (.node a b) (q + 1)) := by
      refine Set.disjoint_of_subset_left ?_ (Set.disjoint_of_subset_right (Wv_subset Z _ _)
        (disjoint_image_of_injOn hinj (S₁ := {q}) ?_ ?_ ?_))
      · unfold pieceVars; split_ifs
        · exact Set.empty_subset _
        · rw [Set.image_singleton]
      · intro j hj; simp only [Set.mem_singleton_iff] at hj; subst hj; simp
      · intro j hj; simp only [Set.mem_Ico] at hj ⊢; omega
      · rw [Set.disjoint_singleton_left]; simp
    have hc := MJR.comp h0 h1 hA (hp.mono (le_max_right 1 _)) hr hd
    simp only [tildeP, Wv]
    unfold pieceVars at hc
    refine (MJR.of_MJ hc).mono ?_
    rw [pow_succ']
    exact (C510_bound_comp (zero_le_one.trans (le_max_left _ _)) hr.nonneg le_rfl)
  | .node (.node a b) .nil, q, _, hinj => by
    have hsz : (LegalCode.node (.node a b) .nil).size = (LegalCode.node a b).size + 1 := by
      simp [LegalCode.size]
    rw [hsz] at hinj ⊢
    have hi := tildeP_MJR h0 h1 hA hε hμ Z (.node a b) (q + 1) (by simp)
      (hinj.mono fun j hj => by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hv : σ q ∉ Wv σ Z (.node a b) (q + 1) := by
      intro h
      obtain ⟨j, hj, hjq⟩ := Wv_subset Z _ _ h
      have := hinj (by simp only [Set.mem_Ico] at hj ⊢; omega) (by simp) hjq
      simp only [Set.mem_Ico] at hj; omega
    have hs := MJR.sandwich h0 h1 hA (hε q) hi hv (hμ q)
    simp only [tildeP, Wv, Set.union_empty]
    refine hs.mono ?_
    rw [pow_succ']
    exact C510_bound_sw h0 h1 hi.nonneg
  | .node (.node a b) (.node c d), q, _, hinj => by
    have hsz : (LegalCode.node (.node a b) (.node c d)).size =
        (LegalCode.node a b).size + (LegalCode.node c d).size + 1 := rfl
    rw [hsz] at hinj ⊢
    have hi := tildeP_MJR h0 h1 hA hε hμ Z (.node a b) (q + 1) (by simp)
      (hinj.mono fun j hj => by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hr := tildeP_MJR h0 h1 hA hε hμ Z (.node c d) (q + (LegalCode.node a b).size + 1)
      (by simp) (hinj.mono fun j hj => by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hv : σ q ∉ Wv σ Z (.node a b) (q + 1) := by
      intro h
      obtain ⟨j, hj, hjq⟩ := Wv_subset Z _ _ h
      have := hinj (by simp only [Set.mem_Ico] at hj ⊢; omega) (by simp) hjq
      simp only [Set.mem_Ico] at hj; omega
    have hs := MJR.sandwich h0 h1 hA (hε q) hi hv (hμ q)
    have hd : Disjoint (insert (σ q) (Wv σ Z (.node a b) (q + 1)))
        (Wv σ Z (.node c d) (q + (LegalCode.node a b).size + 1)) := by
      refine Set.disjoint_of_subset_left ?_ (Set.disjoint_of_subset_right (Wv_subset Z _ _)
        (disjoint_image_of_injOn hinj (S₁ := Set.Ico q (q + (LegalCode.node a b).size + 1)) ?_ ?_ ?_))
      · refine Set.insert_subset ⟨q, by simp, rfl⟩ ((Wv_subset Z _ _).trans (Set.image_mono ?_))
        intro j hj; simp only [Set.mem_Ico] at hj ⊢; omega
      · intro j hj; simp only [Set.mem_Ico] at hj ⊢; omega
      · intro j hj; simp only [Set.mem_Ico] at hj ⊢; omega
      · rw [Set.disjoint_left]; intro j h1 h2; simp only [Set.mem_Ico] at h1 h2; omega
    have hc := MJR.comp h0 h1 hA hs hr hd
    simp only [tildeP, Wv]
    refine (MJR.of_MJ hc).mono ?_
    rw [pow_add, pow_succ']
    have := C510_bound_swcomp h0 h1 hi.nonneg hr.nonneg
    calc _ ≤ C510 θ * C510 θ ^ (LegalCode.node a b).size * C510 θ ^ (LegalCode.node c d).size :=
          this
      _ = _ := by ring

end Bounds

/-! ### The variables of `Ĩ_Z` and the statement of Lemma 5.10 -/

section Statement

variable {P : Type*} [MeasurableSpace P] {V : Type} {θ A : ℝ}
variable {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}

/-- The variables of `Ĩ_Z` are the `α_j` of the pairs `j` of the chain outside `Z ∩ adj`. -/
theorem Wv_eq (Z : Finset ℕ) : ∀ (c : LegalCode) (q : ℕ),
    Wv σ Z c q = σ '' (Set.Ico q (q + c.size) \ (↑Z ∩ ↑(adjSet c q)))
  | .nil, q => by simp [Wv, LegalCode.size]
  | .node .nil r, q => by
    have hB := mem_adjSet r (q + 1)
    have hsz : (LegalCode.node .nil r).size = r.size + 1 := by simp [LegalCode.size]
    rw [hsz]
    simp only [Wv, Wv_eq Z r (q + 1), adjSet]
    have e : (if q ∈ Z then (∅ : Set V) else {σ q}) = σ '' (if q ∈ Z then ∅ else {q}) := by
      split_ifs <;> simp
    rw [e, ← Set.image_union]
    congr 1
    ext j
    have := hB j
    by_cases hq : q ∈ Z <;> by_cases hjq : j = q
    · subst hjq; simp [hq]
    · simp only [hq, ite_true, Set.empty_union, Set.mem_sdiff, Set.mem_Ico, Set.mem_inter_iff,
        Finset.mem_coe, Finset.mem_insert, hjq, false_or]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
    · subst hjq
      simp [hq]
    · simp only [hq, ite_false, Set.mem_union, Set.mem_singleton_iff, hjq, false_or,
        Set.mem_sdiff, Set.mem_Ico, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
  | .node (.node a b) r, q => by
    have hA := mem_adjSet (.node a b) (q + 1)
    have hB := mem_adjSet r (q + (LegalCode.node a b).size + 1)
    have hsz : (LegalCode.node (.node a b) r).size = (LegalCode.node a b).size + r.size + 1 := rfl
    rw [hsz]
    simp only [Wv, Wv_eq Z (.node a b) (q + 1), Wv_eq Z r _, adjSet]
    rw [← Set.image_insert_eq, ← Set.image_union]
    congr 1
    ext j
    have h1 := hA j
    have h2 := hB j
    by_cases hjq : j = q
    · subst hjq
      simp only [Set.mem_insert_iff, true_or, Set.mem_union, true_iff, Set.mem_sdiff, Set.mem_Ico,
        Set.mem_inter_iff, Finset.mem_coe, Finset.coe_union]
      refine ⟨⟨le_rfl, by omega⟩, ?_⟩
      rintro ⟨-, h | h⟩
      · have := h1 h; omega
      · have := h2 h; omega
    · simp only [Set.mem_insert_iff, hjq, false_or, Set.mem_union, Set.mem_sdiff, Set.mem_Ico,
        Set.mem_inter_iff, Finset.mem_coe, Finset.coe_union]
      constructor
      swap
      · rintro ⟨⟨h3, h4⟩, h5⟩
        by_cases hji : j < q + (LegalCode.node a b).size + 1
        · left; refine ⟨⟨by omega, by omega⟩, fun ⟨hz, ha⟩ => h5 ⟨hz, Or.inl ha⟩⟩
        · right; refine ⟨⟨by omega, by omega⟩, fun ⟨hz, hb⟩ => h5 ⟨hz, Or.inr hb⟩⟩
      · rintro (⟨⟨h3, h4⟩, h5⟩ | ⟨⟨h3, h4⟩, h5⟩)
        · refine ⟨⟨by omega, by omega⟩, ?_⟩
          rintro ⟨hz, ha | hb⟩
          · exact h5 ⟨hz, ha⟩
          · have := h2 hb; omega
        · refine ⟨⟨by omega, by omega⟩, ?_⟩
          rintro ⟨hz, ha | hb⟩
          · have := h1 ha; omega
          · exact h5 ⟨hz, hb⟩

/-- `∏_{j ∈ Z} Φ(ε_jα_j) = ∏_{j ∈ Z} χ_∞(α_j)/(ε_jπiα_j)`. -/
theorem prod_phiQ (hε : ∀ j, ε j = 1 ∨ ε j = -1) (Z : Finset ℕ) (α : V → ℝ) :
    ∏ j ∈ Z, phiQ σ ε j α =
      ∏ j ∈ Z, (Fourier.chiInfinity (α (σ j)) : ℂ) / (ε j * π * I * α (σ j)) :=
  Finset.prod_congr rfl fun j _ => phiR_sign (hε j) _

/-- **DH21 Lemma 5.10** (L1084–L1096). Let `c` be a legal partition of `{1, …, 2m}` (`m ≥ 1`) in
Catalan form, with pairs `q, …, q+m-1`, signs `ε_j = ±1`, distinct variables `α_j = α (σ j)` and
measurable parameters `μ_j = μf j p`. Then on the whole square
`I_{β₁+λ₁} ⋯ I_{β_{2m}+λ_{2m}} = ∑_{Z ⊆ adj} ∏_{j∈Z} χ_∞(α_j)/(ε_jπiα_j) · Ĩ_Z`, where `adj` is the
set of adjacent pairs `{a, a+1}` (`adjSet`, at most `m` of them, so at most `2^m` terms) and each
`Ĩ_Z` is class `J` plus class `R` in the variables `α_j`, `j ∉ Z`, with norm `≤ C510 θ ^ m`. -/
theorem lemma510 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hμ : ∀ j, Measurable (μf j)) {c : LegalCode} (hc : c ≠ .nil) {q : ℕ}
    (hinj : Set.InjOn σ (Set.Ico q (q + c.size))) :
    (adjSet c q).card ≤ c.size ∧
    (∀ (p : P) (α : V → ℝ) (t s : ℝ), pchain σ ε μf c q p α t s =
      ∑ Z ∈ (adjSet c q).powerset,
        (∏ j ∈ Z, (Fourier.chiInfinity (α (σ j)) : ℂ) / (ε j * π * I * α (σ j))) *
          tildeP σ ε μf Z c q p α t s) ∧
    ∀ Z : Finset ℕ, MJR θ A (C510 θ ^ c.size)
      (σ '' (Set.Ico q (q + c.size) \ (↑Z ∩ ↑(adjSet c q)))) (tildeP σ ε μf Z c q) := by
  refine ⟨card_adjSet_le c q, fun p α t s => ?_, fun Z => ?_⟩
  · rw [pchain_expand p α c q t s]
    exact Finset.sum_congr rfl fun Z _ => by rw [prod_phiQ hε]
  · rw [← Wv_eq]
    exact tildeP_MJR h0 h1 hA hε hμ Z c q hc hinj

end Statement

end WaveTurbulence.ClassJR

