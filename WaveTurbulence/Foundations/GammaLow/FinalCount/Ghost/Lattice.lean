/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriLattice
/-! **L6E GHOST, part 1: lattice counts** (M1-R2 NOTES §5, REF-M1R2 §4.6).

Integer-point counts by coordinate elimination (no volume argument):
* `card_le_mul_restrict`: a coordinate confined to an interval of length `K` over each fibre of the other coordinates;
* `card_slab_gen`: one slab `|n · u| ≤ r` in a box, for a real normal `n` and any finite index type;
* `card_twoSlab_gen` (**Lemma 5.1, two slabs**): two slabs; the second is read through the component of `n₂` that is
  transverse to `n₁` along the eliminated coordinate;
* `card_cone` (**Lemma 5.2, cone**): integer vectors of length `≤ ρ` within angle `θ` of a line. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The other coordinates of `u` (all but `i0`). -/
def restrictNe (i0 : ι) (u : ι → ℤ) : {j // j ≠ i0} → ℤ := fun j => u j.1

theorem card_subtype_ne (i0 : ι) : Fintype.card {j // j ≠ i0} = Fintype.card ι - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- **Fibre lemma.** If, over each fibre of the other coordinates, the coordinate `i0` lies in an interval of length
`K`, then `#S ≤ (K + 1) · #(S restricted to the other coordinates)`. -/
theorem card_le_mul_restrict (S : Finset (ι → ℤ)) (i0 : ι) (K : ℕ) (lo : ({j // j ≠ i0} → ℤ) → ℤ)
    (hS : ∀ u ∈ S, lo (restrictNe i0 u) ≤ u i0 ∧ u i0 ≤ lo (restrictNe i0 u) + K) :
    S.card ≤ (K + 1) * (S.image (restrictNe i0)).card := by
  refine Finset.card_le_mul_card_image S (K + 1) fun b _ => ?_
  have hcard : (Finset.Icc (0 : ℤ) K).card = K + 1 := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun u => u i0 - lo b) ?_ ?_
  · intro u hu
    rw [Finset.mem_coe, Finset.mem_filter] at hu
    obtain ⟨hu, hb⟩ := hu
    have := hS u hu
    rw [hb] at this
    rw [Finset.mem_coe, Finset.mem_Icc]
    dsimp only
    constructor <;> omega
  · intro u hu u' hu' h
    rw [Finset.mem_coe, Finset.mem_filter] at hu hu'
    simp only at h
    have hi0 : u i0 = u' i0 := by omega
    funext j
    by_cases hj : j = i0
    · subst hj; exact hi0
    · have := congrFun (hu.2.trans hu'.2.symm) ⟨j, hj⟩
      exact this

/-- The box `[-m, m]^ι` of integer vectors. -/
def boxG (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m

theorem card_boxG (m : ℕ) : (boxG ι m).card = (2 * m + 1) ^ Fintype.card ι := by
  unfold boxG
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ]
  congr 1; omega

theorem mem_boxG {m : ℕ} {u : ι → ℤ} : u ∈ boxG ι m ↔ ∀ i, |u i| ≤ m := by
  unfold boxG
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_Icc, abs_le]

theorem sum_split (i0 : ι) (n : ι → ℝ) (u : ι → ℤ) :
    ∑ j, n j * (u j : ℝ) = n i0 * (u i0 : ℝ) + ∑ j : {j // j ≠ i0}, n j.1 * (restrictNe i0 u j : ℝ) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i0]
  rfl

/-- The real interval `|a x + s| ≤ r` (`|a| ≥ ν > 0`) meets the integers in an interval of length `⌊2r/ν⌋`. -/
theorem coord_interval {a s r ν : ℝ} (x : ℤ) (hν : 0 < ν) (ha : ν ≤ |a|) (hx : |a * (x : ℝ) + s| ≤ r) :
    ⌈-s / a - r / |a|⌉ ≤ x ∧ x ≤ ⌈-s / a - r / |a|⌉ + (⌊2 * r / ν⌋₊ : ℕ) := by
  have ha0 : a ≠ 0 := by intro h; rw [h, abs_zero] at ha; linarith
  have hta : 0 < |a| := abs_pos.2 ha0
  have hr : 0 ≤ r := (abs_nonneg _).trans hx
  have h3 : |a| * |(x : ℝ) + s / a| ≤ r := by
    rw [← abs_mul]
    convert hx using 2
    field_simp
  have h4 : |(x : ℝ) + s / a| ≤ r / |a| := by
    rw [le_div_iff₀ hta]; linarith
  have h5 := abs_le.mp h4
  have e : -s / a = -(s / a) := by ring
  constructor
  · apply Int.ceil_le.mpr
    linarith [h5.1]
  · have hlo : -s / a - r / |a| ≤ (⌈-s / a - r / |a|⌉ : ℝ) := Int.le_ceil _
    have hdiff : (x : ℝ) - ⌈-s / a - r / |a|⌉ ≤ 2 * r / ν := by
      have e2 : 2 * r / |a| = r / |a| + r / |a| := by ring
      have h6 : 2 * r / |a| ≤ 2 * r / ν := div_le_div_of_nonneg_left (by linarith) hν ha
      linarith [h5.2]
    have h7 : (x - ⌈-s / a - r / |a|⌉ : ℤ) ≤ ⌊2 * r / ν⌋ := by
      apply Int.le_floor.mpr; push_cast; exact hdiff
    have h8 := Int.natCast_floor_eq_floor (a := 2 * r / ν) (by positivity)
    omega

/-- **One slab** `|n · u| ≤ r` in the box `[-m, m]^ι`, read along a coordinate `i0` with `|n i0| ≥ ν`. -/
theorem card_slab_gen (S : Finset (ι → ℤ)) (m : ℕ) (n : ι → ℝ) (r : ℝ) (i0 : ι) (ν : ℝ) (hν : 0 < ν)
    (hn : ν ≤ |n i0|) (hS : ∀ u ∈ S, (∀ j, |u j| ≤ m) ∧ |∑ j, n j * (u j : ℝ)| ≤ r) :
    S.card ≤ (⌊2 * r / ν⌋₊ + 1) * (2 * m + 1) ^ (Fintype.card ι - 1) := by
  let lo : ({j // j ≠ i0} → ℤ) → ℤ := fun b =>
    ⌈-(∑ j : {j // j ≠ i0}, n j.1 * (b j : ℝ)) / n i0 - r / |n i0|⌉
  have h1 := card_le_mul_restrict S i0 ⌊2 * r / ν⌋₊ lo fun u hu => by
    have hu' := (hS u hu).2
    rw [sum_split i0] at hu'
    exact coord_interval (u i0) hν hn hu'
  refine h1.trans (Nat.mul_le_mul le_rfl ?_)
  rw [← card_subtype_ne i0, ← card_boxG]
  refine Finset.card_le_card fun b hb => ?_
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hb
  rw [mem_boxG]
  intro j
  exact (hS u hu).1 j.1

/-- **Two slabs** (M1-R2 Lemma 5.1, lattice form).  Eliminate the coordinate `i0` with the first slab; the second
slab then constrains the other coordinates through `p = n₂ - (n₂ i0 / n₁ i0) n₁` (which vanishes at `i0`),
read along a coordinate `i1` with `|p i1| ≥ ν₂`. -/
theorem card_twoSlab_gen (S : Finset (ι → ℤ)) (m : ℕ) (n₁ n₂ : ι → ℝ) (r₁ r₂ : ℝ) (i0 i1 : ι) (ν₁ ν₂ : ℝ)
    (hν₁ : 0 < ν₁) (hn₁ : ν₁ ≤ |n₁ i0|) (hν₂ : 0 < ν₂) (hn₂ : ν₂ ≤ |n₂ i1 - n₂ i0 / n₁ i0 * n₁ i1|)
    (hS : ∀ u ∈ S, (∀ j, |u j| ≤ m) ∧ |∑ j, n₁ j * (u j : ℝ)| ≤ r₁ ∧ |∑ j, n₂ j * (u j : ℝ)| ≤ r₂) :
    S.card ≤ (⌊2 * r₁ / ν₁⌋₊ + 1) *
      ((⌊2 * (r₂ + |n₂ i0 / n₁ i0| * r₁) / ν₂⌋₊ + 1) * (2 * m + 1) ^ (Fintype.card ι - 2)) := by
  have hn10 : n₁ i0 ≠ 0 := by intro h; rw [h, abs_zero] at hn₁; linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = n₂ i0 / n₁ i0 := ⟨_, rfl⟩
  rw [← hlam] at hn₂ ⊢
  let p : {j // j ≠ i0} → ℝ := fun j => n₂ j.1 - lam * n₁ j.1
  have hi1 : i1 ≠ i0 := by
    intro h; subst h
    have : n₂ i1 - lam * n₁ i1 = 0 := by rw [hlam]; field_simp; ring
    rw [this, abs_zero] at hn₂; linarith
  let lo : ({j // j ≠ i0} → ℤ) → ℤ := fun b =>
    ⌈-(∑ j : {j // j ≠ i0}, n₁ j.1 * (b j : ℝ)) / n₁ i0 - r₁ / |n₁ i0|⌉
  have h1 := card_le_mul_restrict S i0 ⌊2 * r₁ / ν₁⌋₊ lo fun u hu => by
    have hu' := (hS u hu).2.1
    rw [sum_split i0] at hu'
    exact coord_interval (u i0) hν₁ hn₁ hu'
  refine h1.trans (Nat.mul_le_mul le_rfl ?_)
  have hsub : ∀ b ∈ S.image (restrictNe i0), (∀ j, |b j| ≤ m) ∧
      |∑ j, p j * (b j : ℝ)| ≤ r₂ + |lam| * r₁ := by
    intro b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨hbox, h1u, h2u⟩ := hS u hu
    refine ⟨fun j => hbox j.1, ?_⟩
    have e : ∑ j, p j * (restrictNe i0 u j : ℝ) =
        ∑ j, n₂ j * (u j : ℝ) - lam * ∑ j, n₁ j * (u j : ℝ) := by
      rw [sum_split i0 n₂, sum_split i0 n₁]
      have : n₂ i0 - lam * n₁ i0 = 0 := by rw [hlam]; field_simp; ring
      have e2 : ∑ j : {j // j ≠ i0}, p j * (restrictNe i0 u j : ℝ) =
          ∑ j : {j // j ≠ i0}, (n₂ j.1 * (restrictNe i0 u j : ℝ) - lam * (n₁ j.1 * (restrictNe i0 u j : ℝ))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [p]; ring
      rw [e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
      linear_combination (-(u i0 : ℝ)) * this
    rw [e]
    calc |∑ j, n₂ j * (u j : ℝ) - lam * ∑ j, n₁ j * (u j : ℝ)|
        ≤ |∑ j, n₂ j * (u j : ℝ)| + |lam * ∑ j, n₁ j * (u j : ℝ)| := abs_sub _ _
      _ = |∑ j, n₂ j * (u j : ℝ)| + |lam| * |∑ j, n₁ j * (u j : ℝ)| := by rw [abs_mul]
      _ ≤ r₂ + |lam| * r₁ := by gcongr
  have h2 := card_slab_gen (S.image (restrictNe i0)) m p (r₂ + |lam| * r₁) ⟨i1, hi1⟩ ν₂ hν₂ hn₂ hsub
  rw [card_subtype_ne i0] at h2
  have e3 : Fintype.card ι - 1 - 1 = Fintype.card ι - 2 := by omega
  rw [e3] at h2
  exact h2

/-- **Coordinate-wise intervals over one coordinate.**  If the coordinate `i0` ranges in `[-N, N]` and every other
coordinate lies in an interval of length `K` determined by `u i0`, then `#S ≤ (2N + 1)(K + 1)^(|ι| - 1)`. -/
theorem card_le_of_fibers (S : Finset (ι → ℤ)) (i0 : ι) (N K : ℕ) (lo : ι → ℤ → ℤ)
    (hS : ∀ u ∈ S, |u i0| ≤ N ∧ ∀ j, j ≠ i0 → lo j (u i0) ≤ u j ∧ u j ≤ lo j (u i0) + K) :
    S.card ≤ (2 * N + 1) * (K + 1) ^ (Fintype.card ι - 1) := by
  let tgt : Finset (ℤ × ({j // j ≠ i0} → ℤ)) :=
    Finset.Icc (-(N : ℤ)) N ×ˢ Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) K
  have hcard : tgt.card = (2 * N + 1) * (K + 1) ^ (Fintype.card ι - 1) := by
    simp only [tgt, Finset.card_product, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const,
      Finset.card_univ, card_subtype_ne i0]
    congr 1; omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun u => (u i0, fun j => u j.1 - lo j.1 (u i0))) ?_ ?_
  · intro u hu
    rw [Finset.mem_coe] at hu
    obtain ⟨h0, hj⟩ := hS u hu
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Fintype.mem_piFinset]
    refine ⟨abs_le.mp h0, fun j => ?_⟩
    have := hj j.1 j.2
    rw [Finset.mem_Icc]; dsimp only; constructor <;> omega
  · intro u _ u' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h0, h1⟩ := h
    funext j
    by_cases hj : j = i0
    · subst hj; exact h0
    · have := congrFun h1 ⟨j, hj⟩
      simp only at this
      rw [h0] at this
      omega

/-- **The cone** (M1-R2 Lemma 5.2, lattice form).  Integer vectors `n` with `|n| ≤ ρ` and
`|n|²|c|² - ⟨n, c⟩² ≤ θ²|n|²|c|²` (angle `≤ θ` with the line `ℝc`, `c ≠ 0`). -/
theorem card_cone (S : Finset (ι → ℤ)) (c : ι → ℝ) (hc : c ≠ 0) (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ)
    (hS : ∀ n ∈ S, ∑ j, (n j : ℝ) ^ 2 ≤ ρ ^ 2 ∧
      (∑ j, (n j : ℝ) ^ 2) * (∑ j, c j ^ 2) - (∑ j, (n j : ℝ) * c j) ^ 2 ≤
        θ ^ 2 * ((∑ j, (n j : ℝ) ^ 2) * (∑ j, c j ^ 2))) :
    S.card ≤ (2 * ⌊ρ⌋₊ + 1) * (⌊4 * θ * ρ⌋₊ + 1) ^ (Fintype.card ι - 1) := by
  classical
  have hcj : ∃ j, c j ≠ 0 := by by_contra h'; push Not at h'; exact hc (funext h')
  obtain ⟨j₀, -⟩ := hcj
  -- the coordinate of `c` of largest absolute value
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => |c j|) ⟨j₀, mem_univ _⟩
  have hc0 : c i0 ≠ 0 := by
    intro h0
    apply hc; funext j
    have := hi0 j (mem_univ j); rw [h0, abs_zero] at this
    exact abs_nonpos_iff.1 this
  have hci : 0 < |c i0| := abs_pos.2 hc0
  have hB : 0 < ∑ j, c j ^ 2 := by
    refine lt_of_lt_of_le (by positivity : 0 < c i0 ^ 2) ?_
    exact Finset.single_le_sum (f := fun j => c j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i0)
  set B := ∑ j, c j ^ 2 with hBdef
  -- every vector of `S` is within `θρ` of the line, coordinate-wise
  have key : ∀ n ∈ S, ∀ j, |(n j : ℝ) - (∑ k, (n k : ℝ) * c k) / B * c j| ≤ θ * ρ := by
    intro n hn j
    obtain ⟨hA, hcone⟩ := hS n hn
    set A := ∑ k, (n k : ℝ) ^ 2
    set P := ∑ k, (n k : ℝ) * c k
    have hsq : ∑ k, ((n k : ℝ) - P / B * c k) ^ 2 = (A * B - P ^ 2) / B := by
      have e : ∀ k, ((n k : ℝ) - P / B * c k) ^ 2 = (n k : ℝ) ^ 2 - 2 * (P / B) * ((n k : ℝ) * c k) +
          (P / B) ^ 2 * c k ^ 2 := fun k => by ring
      simp_rw [e]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      field_simp
      ring
    have hj : ((n j : ℝ) - P / B * c j) ^ 2 ≤ θ ^ 2 * ρ ^ 2 := by
      have h1 : ((n j : ℝ) - P / B * c j) ^ 2 ≤ ∑ k, ((n k : ℝ) - P / B * c k) ^ 2 :=
        Finset.single_le_sum (f := fun k => ((n k : ℝ) - P / B * c k) ^ 2) (fun k _ => sq_nonneg _) (mem_univ j)
      rw [hsq] at h1
      have h2 : (A * B - P ^ 2) / B ≤ θ ^ 2 * A := by
        rw [div_le_iff₀ hB]; linarith
      have h3 : θ ^ 2 * A ≤ θ ^ 2 * ρ ^ 2 := mul_le_mul_of_nonneg_left hA (sq_nonneg θ)
      linarith
    have : |(n j : ℝ) - P / B * c j| ≤ |θ * ρ| := sq_le_sq.mp (by rw [mul_pow]; exact hj)
    rwa [abs_of_nonneg (mul_nonneg hθ hρ)] at this
  refine card_le_of_fibers S i0 ⌊ρ⌋₊ ⌊4 * θ * ρ⌋₊
    (fun j x => ⌈c j / c i0 * (x : ℝ) - 2 * θ * ρ⌉) fun n hn => ⟨?_, fun j hj => ?_⟩
  · -- `|n i0| ≤ ρ`
    have h1 : (n i0 : ℝ) ^ 2 ≤ ρ ^ 2 :=
      (Finset.single_le_sum (f := fun k => (n k : ℝ) ^ 2) (fun k _ => sq_nonneg _) (mem_univ i0)).trans
        (hS n hn).1
    have h2 : |(n i0 : ℝ)| ≤ ρ := by
      have := sq_le_sq.mp h1; rwa [abs_of_nonneg hρ] at this
    have h3 : (|n i0| : ℤ) ≤ ⌊ρ⌋ := Int.le_floor.mpr (by push_cast; exact h2)
    have h4 := Int.natCast_floor_eq_floor hρ
    omega
  · set P := ∑ k, (n k : ℝ) * c k
    have hk0 := key n hn i0
    have hkj := key n hn j
    have hratio : |c j / c i0| ≤ 1 := by
      rw [abs_div, div_le_one hci]; exact hi0 j (mem_univ j)
    -- `n j - (c j / c i0) n i0 = (n j - t c j) - (c j / c i0)(n i0 - t c i0)`
    have hdev : |(n j : ℝ) - c j / c i0 * (n i0 : ℝ)| ≤ 2 * θ * ρ := by
      have e : (n j : ℝ) - c j / c i0 * (n i0 : ℝ) =
          ((n j : ℝ) - P / B * c j) - c j / c i0 * ((n i0 : ℝ) - P / B * c i0) := by
        field_simp; ring
      rw [e]
      calc _ ≤ |(n j : ℝ) - P / B * c j| + |c j / c i0 * ((n i0 : ℝ) - P / B * c i0)| := abs_sub _ _
        _ = |(n j : ℝ) - P / B * c j| + |c j / c i0| * |(n i0 : ℝ) - P / B * c i0| := by rw [abs_mul]
        _ ≤ θ * ρ + 1 * (θ * ρ) := by gcongr
        _ = 2 * θ * ρ := by ring
    have hd := abs_le.mp hdev
    have hθρ : 0 ≤ θ * ρ := mul_nonneg hθ hρ
    constructor
    · exact Int.ceil_le.mpr (by linarith)
    · have hlo : c j / c i0 * (n i0 : ℝ) - 2 * θ * ρ ≤ (⌈c j / c i0 * (n i0 : ℝ) - 2 * θ * ρ⌉ : ℝ) :=
        Int.le_ceil _
      have h7 : (n j - ⌈c j / c i0 * (n i0 : ℝ) - 2 * θ * ρ⌉ : ℤ) ≤ ⌊4 * θ * ρ⌋ := by
        apply Int.le_floor.mpr; push_cast; linarith
      have h8 := Int.natCast_floor_eq_floor (a := 4 * θ * ρ) (by positivity)
      omega

end WaveTurbulence.GammaLow.FinalCount.Ghost
