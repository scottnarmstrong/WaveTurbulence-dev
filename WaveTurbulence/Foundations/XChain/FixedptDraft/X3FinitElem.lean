/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3ZModel

/-!
# X3 FinitElem: finitely many representatives (T Lemma `finitelem`, L2435)

**Statement** (`finitelem`). Let `1 ≤ L`, `0 ≤ M`, and let `S ⊆ ℤ^d` be any set. Then there is a finite
`Rep ⊆ S` with
`|Rep| ≤ (d+1) · ((2⌊LM⌋+1)^d · (2⌊L²M⌋+1))^d`
such that every `k ∈ S` has a representative `k_* ∈ Rep`. A representative satisfies, for every `z ∈ ℤ^d`
with `|z/L| ≤ M`:
* `|⟨k/L, z/L⟩| ≤ M ↔ |⟨k_*/L, z/L⟩| ≤ M`;
* `|⟨k/L, z/L⟩| ≤ M → ⟨k/L, z/L⟩ = ⟨k_*/L, z/L⟩`.

Here `k/L` is `latticePoint L k`.

Allowing an arbitrary `S` lets us choose large representatives (`S = {|k/L| ≥ M₁^{10}}`), as T L2328 needs.

Proof (T's, without Gram–Schmidt). Let `H(k) = {z : |z/L| ≤ M, |⟨k/L, z/L⟩| ≤ M}`. A **system** is a list of at
most `d` pairs `(w_j, y_j)`, with `w_j` in the ball and `y_j ∈ ℤ`, `|y_j| ≤ L²M`. It **represents** `k` if:
- every `z ∈ H(k)` lies in `span(w_j/L)`;
- `∑ k·w_j = y_j` for each `j`.

Every `k` is represented by a maximal independent family in `H(k)`. Two vectors represented by the same system
satisfy the property above, by linearity of `⟨k/L, ·⟩` on the span. Choose one representative per realized
system.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open Set

variable {d : ℕ}

/-! ## Lattice inner products -/

/-- `⟨k/L, z/L⟩`. -/
noncomputable def ipL (L : ℝ) (k z : Fin d → ℤ) : ℝ := inner ℝ (latticePoint L k) (latticePoint L z)

/-- The integer dot product `∑_j k_j z_j`. -/
def dotZ (k z : Fin d → ℤ) : ℤ := ∑ j, k j * z j

theorem ipL_eq (L : ℝ) (k z : Fin d → ℤ) : ipL L k z = (dotZ k z : ℝ) / L ^ 2 := by
  have h : inner ℝ (latticePoint L k) (latticePoint L z) = ∑ j, ((k j : ℝ) / L) * ((z j : ℝ) / L) := by
    simp [latticePoint, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  unfold ipL dotZ
  rw [h, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem abs_le_of_norm_latticePoint_le {L M : ℝ} (hL : 0 < L) {z : Fin d → ℤ} (hz : ‖latticePoint L z‖ ≤ M)
    (j : Fin d) : |(z j : ℝ)| ≤ L * M := by
  have h1 : ‖(latticePoint L z) j‖ ≤ ‖latticePoint L z‖ := PiLp.norm_apply_le _ j
  have h2 : ‖(latticePoint L z) j‖ = |(z j : ℝ)| / L := by
    simp [latticePoint, Real.norm_eq_abs, abs_of_pos hL]
  rw [h2, div_le_iff₀ hL] at h1
  linarith [h1.trans (mul_le_mul_of_nonneg_right hz hL.le)]

/-! ## The ball and the values -/

open Classical in
/-- The integer vectors `z` with `|z/L| ≤ M`. -/
noncomputable def ballZ (L M : ℝ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(⌊L * M⌋₊ : ℤ)) ⌊L * M⌋₊).filter fun z => ‖latticePoint L z‖ ≤ M

theorem mem_ballZ {L M : ℝ} (hL : 0 < L) (hM : 0 ≤ M) {z : Fin d → ℤ} :
    z ∈ ballZ L M ↔ ‖latticePoint L z‖ ≤ M := by
  classical
  unfold ballZ
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun j => ?_, h⟩⟩
  have hj := abs_le_of_norm_latticePoint_le hL h j
  have hLM : 0 ≤ L * M := mul_nonneg hL.le hM
  have hfl : ((z j).natAbs : ℝ) ≤ L * M := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact hj
  have hn : (z j).natAbs ≤ ⌊L * M⌋₊ := Nat.le_floor hfl
  rw [Finset.mem_Icc]
  constructor <;> omega

theorem card_ballZ_le (L M : ℝ) : (ballZ (d := d) L M).card ≤ (2 * ⌊L * M⌋₊ + 1) ^ d := by
  classical
  unfold ballZ
  refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
  congr 1
  omega

/-- The admissible values `y ∈ ℤ`, `|y| ≤ L²M`. -/
noncomputable def valZ (L M : ℝ) : Finset ℤ := Finset.Icc (-(⌊L ^ 2 * M⌋₊ : ℤ)) ⌊L ^ 2 * M⌋₊

theorem card_valZ (L M : ℝ) : (valZ L M).card = 2 * ⌊L ^ 2 * M⌋₊ + 1 := by
  unfold valZ
  rw [Int.card_Icc]
  omega

theorem dotZ_mem_valZ {L M : ℝ} (hL : 0 < L) {k z : Fin d → ℤ} (h : |ipL L k z| ≤ M) :
    dotZ k z ∈ valZ L M := by
  rw [ipL_eq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < L ^ 2), div_le_iff₀ (by positivity)] at h
  have hfl : ((dotZ k z).natAbs : ℝ) ≤ L ^ 2 * M := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    linarith
  have hn : (dotZ k z).natAbs ≤ ⌊L ^ 2 * M⌋₊ := Nat.le_floor hfl
  unfold valZ
  rw [Finset.mem_Icc]
  constructor <;> omega

/-! ## Systems -/

/-- A system: at most `d` pairs `(w_j, y_j)`. -/
abbrev Sys (d : ℕ) : Type := Σ q : Fin (d + 1), Fin q → (Fin d → ℤ) × ℤ

/-- The finite set of systems with `w_j` in the ball and admissible `y_j`. -/
noncomputable def sysSet (L M : ℝ) : Finset (Sys d) :=
  Finset.univ.sigma fun _ => Fintype.piFinset fun _ => ballZ L M ×ˢ valZ L M

/-- `σ` **represents** `k`. -/
def Represents (L M : ℝ) (k : Fin d → ℤ) (σ : Sys d) : Prop :=
  (∀ z ∈ ballZ L M, |ipL L k z| ≤ M →
    latticePoint L z ∈ Submodule.span ℝ (Set.range fun j => latticePoint L (σ.2 j).1)) ∧
  ∀ j, dotZ k (σ.2 j).1 = (σ.2 j).2

theorem ipL_eq_of_represents {L M : ℝ} {k k' : Fin d → ℤ} {σ : Sys d} (hk : Represents L M k σ)
    (hk' : Represents L M k' σ) {z : Fin d → ℤ} (hz : z ∈ ballZ L M) (h : |ipL L k z| ≤ M) :
    ipL L k z = ipL L k' z := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hk.1 z hz h)
  have key : ∀ k'' : Fin d → ℤ, Represents L M k'' σ →
      ipL L k'' z = ∑ j, c j * (((σ.2 j).2 : ℤ) : ℝ) / L ^ 2 := fun k'' hk'' => by
    unfold ipL
    rw [← hc, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right]
    have := ipL_eq L k'' (σ.2 j).1
    unfold ipL at this
    rw [this, hk''.2 j]
    ring
  rw [key k hk, key k' hk']

theorem represents_iff {L M : ℝ} {k k' : Fin d → ℤ} {σ : Sys d} (hk : Represents L M k σ)
    (hk' : Represents L M k' σ) {z : Fin d → ℤ} (hz : z ∈ ballZ L M) :
    (|ipL L k z| ≤ M ↔ |ipL L k' z| ≤ M) ∧ (|ipL L k z| ≤ M → ipL L k z = ipL L k' z) :=
  ⟨⟨fun h => by rw [← ipL_eq_of_represents hk hk' hz h]; exact h,
    fun h => by rw [← ipL_eq_of_represents hk' hk hz h]; exact h⟩,
    fun h => ipL_eq_of_represents hk hk' hz h⟩

theorem latticePoint_injective {L : ℝ} (hL : L ≠ 0) : Function.Injective (latticePoint (d := d) L) := by
  intro a b h
  funext j
  have := congrArg (fun v : Mom d => v j) h
  simp only [latticePoint] at this
  have h' : (a j : ℝ) / L = (b j : ℝ) / L := this
  rw [div_left_inj' hL] at h'
  exact_mod_cast h'

/-- **Every `k` is represented by a system of `sysSet`.** -/
theorem exists_represents {L M : ℝ} (hL : 0 < L) (k : Fin d → ℤ) :
    ∃ σ ∈ sysSet (d := d) L M, Represents L M k σ := by
  classical
  set H : Finset (Fin d → ℤ) := (ballZ L M).filter fun z => |ipL L k z| ≤ M
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℝ (latticePoint L '' (H : Set (Fin d → ℤ)))
  set W : Finset (Fin d → ℤ) := H.filter fun z => latticePoint L z ∈ b
  have hinj := latticePoint_injective (d := d) hL.ne'
  -- `W` is linearly independent, hence has at most `d` elements
  have hliW : LinearIndependent ℝ fun w : W => latticePoint L (w : Fin d → ℤ) := by
    let g : W → b := fun w => ⟨latticePoint L w, (Finset.mem_filter.1 w.2).2⟩
    have hg : Function.Injective g := fun w w' h => Subtype.ext (hinj (congrArg Subtype.val h))
    exact hli.comp g hg
  have hq : W.card ≤ d := by
    have := hliW.fintype_card_le_finrank
    rwa [Fintype.card_coe, finrank_euclideanSpace_fin] at this
  let e := W.equivFin
  refine ⟨⟨⟨W.card, Nat.lt_succ_of_le hq⟩, fun j => ((e.symm j).1, dotZ k (e.symm j).1)⟩, ?_, ?_, fun j => rfl⟩
  · refine Finset.mem_sigma.2 ⟨Finset.mem_univ _, Fintype.mem_piFinset.2 fun j => ?_⟩
    have hj := (e.symm j).2
    have hH := (Finset.mem_filter.1 hj).1
    obtain ⟨hball, habs⟩ := Finset.mem_filter.1 hH
    exact Finset.mem_product.2 ⟨hball, dotZ_mem_valZ hL habs⟩
  · intro z hz h
    have hzH : z ∈ H := Finset.mem_filter.2 ⟨hz, h⟩
    have h1 : latticePoint L z ∈ Submodule.span ℝ (latticePoint L '' (H : Set (Fin d → ℤ))) :=
      Submodule.subset_span ⟨z, hzH, rfl⟩
    rw [← hspan] at h1
    refine Submodule.span_mono ?_ h1
    rintro v hv
    obtain ⟨z', hz'H, rfl⟩ := hbs hv
    have hz'W : z' ∈ W := Finset.mem_filter.2 ⟨hz'H, hv⟩
    exact ⟨e ⟨z', hz'W⟩, by simp⟩

/-! ## The representatives -/

theorem card_sysSet_le (L M : ℝ) (hM : 0 ≤ M) (hL : 0 < L) :
    (sysSet (d := d) L M).card ≤ (d + 1) * ((2 * ⌊L * M⌋₊ + 1) ^ d * (2 * ⌊L ^ 2 * M⌋₊ + 1)) ^ d := by
  classical
  unfold sysSet
  rw [Finset.card_sigma]
  have h0 : 1 ≤ (ballZ (d := d) L M).card * (valZ L M).card := by
    have hb : 0 < (ballZ (d := d) L M).card :=
      Finset.card_pos.2 ⟨0, (mem_ballZ hL hM).2 (by
        have : latticePoint L (0 : Fin d → ℤ) = 0 := by ext j; simp [latticePoint]
        rw [this, norm_zero]; exact hM)⟩
    have hv : 0 < (valZ L M).card := by rw [card_valZ]; omega
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hb.ne' hv.ne')
  calc ∑ q : Fin (d + 1), (Fintype.piFinset fun _ : Fin q => ballZ (d := d) L M ×ˢ valZ L M).card
      = ∑ q : Fin (d + 1), ((ballZ (d := d) L M).card * (valZ L M).card) ^ (q : ℕ) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.card_product]
    _ ≤ ∑ _q : Fin (d + 1), ((ballZ (d := d) L M).card * (valZ L M).card) ^ d :=
        Finset.sum_le_sum fun q _ => Nat.pow_le_pow_right h0 (Nat.lt_succ_iff.1 q.2)
    _ = (d + 1) * ((ballZ (d := d) L M).card * (valZ L M).card) ^ d := by simp
    _ ≤ (d + 1) * ((2 * ⌊L * M⌋₊ + 1) ^ d * (2 * ⌊L ^ 2 * M⌋₊ + 1)) ^ d := by
        rw [card_valZ]
        gcongr
        exact card_ballZ_le L M

/-- **`finitelem`** (T L2435). -/
theorem finitelem {L M : ℝ} (hL : 1 ≤ L) (hM : 0 ≤ M) (S : Set (Fin d → ℤ)) :
    ∃ Rep : Finset (Fin d → ℤ), (↑Rep : Set (Fin d → ℤ)) ⊆ S ∧
      Rep.card ≤ (d + 1) * ((2 * ⌊L * M⌋₊ + 1) ^ d * (2 * ⌊L ^ 2 * M⌋₊ + 1)) ^ d ∧
      ∀ k ∈ S, ∃ k' ∈ Rep, ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
        (|ipL L k z| ≤ M ↔ |ipL L k' z| ≤ M) ∧ (|ipL L k z| ≤ M → ipL L k z = ipL L k' z) := by
  classical
  have hL0 : 0 < L := by linarith
  set real := (sysSet (d := d) L M).filter fun σ => ∃ k ∈ S, Represents L M k σ
  let rep : Sys d → Fin d → ℤ := fun σ => if h : ∃ k ∈ S, Represents L M k σ then h.choose else 0
  have hrep : ∀ σ ∈ real, rep σ ∈ S ∧ Represents L M (rep σ) σ := fun σ hσ => by
    have h := (Finset.mem_filter.1 hσ).2
    simp only [rep, h, ↓reduceDIte]
    exact h.choose_spec
  refine ⟨real.image rep, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hk
    exact (hrep σ hσ).1
  · exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans (card_sysSet_le L M hM hL0)
  · intro k hk
    obtain ⟨σ, hσ, hkσ⟩ := exists_represents (M := M) hL0 k
    have hσr : σ ∈ real := Finset.mem_filter.2 ⟨hσ, k, hk, hkσ⟩
    refine ⟨rep σ, Finset.mem_image.2 ⟨σ, hσr, rfl⟩, fun z hz => ?_⟩
    exact represents_iff hkσ (hrep σ hσr).2 ((mem_ballZ hL0 hM).2 hz)

end WaveTurbulence.Fixedpt
