/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.LadderMain
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The weighted layering sum over a ladder (TARGET layerlad, `sumofexp0`)

Molecule-level form: any molecule, any layering functions with a parent property for degree-four atoms.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
  {m : ℕ} {u v : Fin (m + 1) → V}

theorem intAtoms_ladder_sub (hL : M.IsLadder u v) :
    intAtoms (ladderRungSeq M hL).u (ladderRungSeq M hL).v (m - 1) ⊆ Molecule.ladderAtoms u v := by
  intro a ha
  unfold intAtoms at ha
  simp only [mem_union, mem_image, mem_Ico, ladderRungSeq_u, ladderRungSeq_v] at ha
  unfold Molecule.ladderAtoms
  simp only [mem_union, mem_image, mem_univ, true_and]
  have hm := ladder_pos M hL
  rcases ha with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · left; exact ⟨⟨i, by omega⟩, (lad_of_le u (show i ≤ m by omega)).symm⟩
  · right; exact ⟨⟨i, by omega⟩, (lad_of_le v (show i ≤ m by omega)).symm⟩

theorem card_ends_le (hL : M.IsLadder u v) :
    (Molecule.ladderAtoms u v \ intAtoms (ladderRungSeq M hL).u (ladderRungSeq M hL).v (m - 1)).card ≤ 4 := by
  have hm := ladder_pos M hL
  have hsub : Molecule.ladderAtoms u v \ intAtoms (ladderRungSeq M hL).u (ladderRungSeq M hL).v (m - 1) ⊆
      {u ⟨0, by omega⟩, v ⟨0, by omega⟩, u ⟨m, by omega⟩, v ⟨m, by omega⟩} := by
    intro a ha
    rw [mem_sdiff] at ha
    obtain ⟨ha1, ha2⟩ := ha
    unfold Molecule.ladderAtoms at ha1
    simp only [mem_union, mem_image, mem_univ, true_and] at ha1
    simp only [mem_insert, mem_singleton]
    rcases ha1 with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · by_cases h0 : j.1 = 0
      · left; congr 1; exact Fin.ext h0
      · by_cases hjm : j.1 = m
        · right; right; left; congr 1; exact Fin.ext hjm
        · exfalso; apply ha2
          unfold intAtoms
          simp only [mem_union, mem_image, mem_Ico, ladderRungSeq_u, ladderRungSeq_v]
          left; refine ⟨j.1, by omega, ?_⟩
          rw [lad_of_le u (by omega)]
    · by_cases h0 : j.1 = 0
      · right; left; congr 1; exact Fin.ext h0
      · by_cases hjm : j.1 = m
        · right; right; right; congr 1; exact Fin.ext hjm
        · exfalso; apply ha2
          unfold intAtoms
          simp only [mem_union, mem_image, mem_Ico, ladderRungSeq_u, ladderRungSeq_v]
          right; refine ⟨j.1, by omega, ?_⟩
          rw [lad_of_le v (by omega)]
  exact (card_le_card hsub).trans Finset.card_le_four

theorem incCnt_le_index (hL : M.IsLadder u v) (f : V → ℕ) :
    incCnt (fun i => f (lad u i)) (fun i => f (lad v i)) 1 (m - 1) ≤
      incoherencyIndex f (ladderGroups u v) := by
  have hm := ladder_pos M hL
  rw [incoherencyIndex_ladderGroups]
  have e : ∑ j : Fin (m + 1), (if f (u j) = f (v j) then 0 else 1) =
      ∑ i ∈ range (m + 1), (if f (lad u i) = f (lad v i) then 0 else 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if f (lad u i) = f (lad v i) then 0 else 1) (m + 1)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [lad_of_le u (show j.1 ≤ m by omega), lad_of_le v (show j.1 ≤ m by omega)]
  rw [e]
  unfold incCnt
  rw [show m - 1 + 1 = m by omega]
  apply Finset.sum_le_sum_of_subset
  intro i hi; simp only [mem_Ico, mem_range] at hi ⊢; omega

/-- **Pointwise bond exponent of a ladder** (TARGET layerlad, proof): at most `𝔇 (10 g + 18)`. -/
theorem ladder_bondExp_le (hM : M.IsMolecule) (hL : M.IsLadder u v) {f depth : V → ℕ} {𝔇 : ℕ}
    (hf : ∀ x, f x ≤ 𝔇) (hP : ParentProp M f depth) :
    bondExp M (Molecule.ladderAtoms u v) f ≤ 𝔇 * (10 * incoherencyIndex f (ladderGroups u v) + 18) := by
  set R := ladderRungSeq M hL with hR
  have h1 := two_mul_bondExp_le M (Molecule.ladderAtoms u v) f
  have h2 := dartExp_le_split M hM (intAtoms_ladder_sub M hL) hf
  have h3 := interior_dartSum_bound M hM R hf hP (fun i => f (lad u i)) (fun i => f (lad v i))
    (fun i => by rw [ladderRungSeq_u]) (fun i => by rw [ladderRungSeq_v]) (incCnt_le_index M hL f)
  have h4 := card_ends_le M hL
  have h5 : 4 * 𝔇 * (Molecule.ladderAtoms u v \ intAtoms R.u R.v (m - 1)).card ≤ 4 * 𝔇 * 4 :=
    Nat.mul_le_mul_left _ h4
  nlinarith [h3.2]

/-- **Counting the layerings of a ladder** (TARGET layerlad, `sumofexp0`, count step): a family of layerings
that are pairwise distinct on the atoms of the ladder and have incoherency index `g` has at most
`(𝔇+1)^6 · 3^{2(m-1)+16𝔇(g+1)}` members. -/
theorem ladder_card_le (hM : M.IsMolecule) (hL : M.IsLadder u v) {depth : V → ℕ} {𝔇 : ℕ}
    (𝓕 : Finset (V → ℕ)) (hf : ∀ f ∈ 𝓕, (∀ x, f x ≤ 𝔇) ∧ ParentProp M f depth)
    (hinj : ∀ f ∈ 𝓕, ∀ g ∈ 𝓕, (∀ x ∈ Molecule.ladderAtoms u v, f x = g x) → f = g) (g : ℕ)
    (hg : ∀ f ∈ 𝓕, incoherencyIndex f (ladderGroups u v) = g) :
    𝓕.card ≤ (𝔇 + 1) ^ 6 * 3 ^ (2 * (m - 1) + 16 * 𝔇 * (g + 1)) := by
  classical
  have hm := ladder_pos M hL
  set R := ladderRungSeq M hL with hR
  set X : Finset (ℕ × ℕ × ℕ × ℕ) := range (𝔇 + 1) ×ˢ range (𝔇 + 1) ×ˢ range (𝔇 + 1) ×ˢ range (𝔇 + 1) with hX
  have hXc : X.card = (𝔇 + 1) ^ 4 := by simp [hX]; ring
  have hbound : ∀ f ∈ 𝓕, tvab (fun i => f (lad u i)) (fun i => f (lad v i)) 1 (m - 1) ≤ 8 * 𝔇 * (g + 1) := by
    intro f hf'
    have hk : incCnt (fun i => f (lad u i)) (fun i => f (lad v i)) 1 (m - 1) ≤ g :=
      (incCnt_le_index M hL f).trans (hg f hf').le
    exact (interior_dartSum_bound M hM R (hf f hf').1 (hf f hf').2 (fun i => f (lad u i)) (fun i => f (lad v i))
      (fun i => by rw [ladderRungSeq_u]) (fun i => by rw [ladderRungSeq_v]) hk).1
  have hc := card_configs_le' 𝓕 (fun f i => f (lad u i)) (fun f i => f (lad v i)) X
    (fun f => (f (u ⟨0, by omega⟩), f (v ⟨0, by omega⟩), f (u ⟨m, by omega⟩), f (v ⟨m, by omega⟩)))
    (by
      intro f hf'
      simp only [hX, mem_product, mem_range]
      have := (hf f hf').1
      refine ⟨by have := this (u ⟨0, by omega⟩); omega, by have := this (v ⟨0, by omega⟩); omega,
        by have := this (u ⟨m, by omega⟩); omega, by have := this (v ⟨m, by omega⟩); omega⟩)
    (m - 1) 𝔇 (8 * 𝔇 * (g + 1))
    (by
      intro f hf' i _ _
      exact ⟨(hf f hf').1 _, (hf f hf').1 _⟩)
    (by
      intro f hf'
      have := hbound f hf'
      rw [tvab_eq] at this
      omega)
    (by
      intro f hf' f2 hf2 hcfg hend
      apply hinj f hf' f2 hf2
      intro x hx
      unfold Molecule.ladderAtoms at hx
      simp only [mem_union, mem_image, mem_univ, true_and] at hx
      simp only [Prod.mk.injEq] at hend
      obtain ⟨e1, e2, e3, e4⟩ := hend
      rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · by_cases h0 : j.1 = 0
        · have : j = ⟨0, by omega⟩ := Fin.ext h0
          rw [this]; exact e1
        · by_cases hjm : j.1 = m
          · have : j = ⟨m, by omega⟩ := Fin.ext hjm
            rw [this]; exact e3
          · have := (hcfg j.1 (by omega) (by omega)).1
            simpa [lad_of_le u (show j.1 ≤ m by omega)] using this
      · by_cases h0 : j.1 = 0
        · have : j = ⟨0, by omega⟩ := Fin.ext h0
          rw [this]; exact e2
        · by_cases hjm : j.1 = m
          · have : j = ⟨m, by omega⟩ := Fin.ext hjm
            rw [this]; exact e4
          · have := (hcfg j.1 (by omega) (by omega)).2
            simpa [lad_of_le v (show j.1 ≤ m by omega)] using this)
  rw [hXc] at hc
  refine hc.trans ?_
  have e : (𝔇 + 1) ^ 4 * ((𝔇 + 1) * 3 ^ (m - 1 + 8 * 𝔇 * (g + 1))) ^ 2 =
      (𝔇 + 1) ^ 6 * 3 ^ (2 * (m - 1) + 16 * 𝔇 * (g + 1)) := by
    rw [mul_pow, ← pow_mul]
    rw [show 2 * (m - 1) + 16 * 𝔇 * (g + 1) = (m - 1 + 8 * 𝔇 * (g + 1)) * 2 by ring]
    ring
  exact e.le

theorem nat_const_le (m 𝔇 g : ℕ) :
    (𝔇 + 1) ^ 6 * 3 ^ (2 * (m - 1) + 16 * 𝔇 * (g + 1)) ≤ 9 ^ m * (2 ^ (6 * 𝔇) * 3 ^ (16 * 𝔇)) ^ (g + 1) := by
  have h1 : (𝔇 + 1) ^ 6 ≤ (2 ^ (6 * 𝔇)) ^ (g + 1) := by
    have : 𝔇 + 1 ≤ 2 ^ 𝔇 := Nat.lt_two_pow_self
    calc (𝔇 + 1) ^ 6 ≤ (2 ^ 𝔇) ^ 6 := Nat.pow_le_pow_left this 6
      _ = 2 ^ (6 * 𝔇) := by rw [← pow_mul]; ring_nf
      _ ≤ (2 ^ (6 * 𝔇)) ^ (g + 1) := Nat.le_self_pow (by omega) _
  have h2 : 3 ^ (2 * (m - 1) + 16 * 𝔇 * (g + 1)) ≤ 9 ^ m * (3 ^ (16 * 𝔇)) ^ (g + 1) := by
    rw [pow_add, ← pow_mul, show 16 * 𝔇 * (g + 1) = 16 * 𝔇 * (g + 1) from rfl]
    have : 3 ^ (2 * (m - 1)) ≤ 9 ^ m := by
      calc 3 ^ (2 * (m - 1)) = 9 ^ (m - 1) := by rw [pow_mul]; norm_num
        _ ≤ 9 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 3 ^ (16 * 𝔇 * (g + 1)) = (3 ^ (16 * 𝔇)) ^ (g + 1) := by rw [← pow_mul]
    rw [h3]
    exact Nat.mul_le_mul_right _ this
  calc (𝔇 + 1) ^ 6 * 3 ^ (2 * (m - 1) + 16 * 𝔇 * (g + 1))
      ≤ (2 ^ (6 * 𝔇)) ^ (g + 1) * (9 ^ m * (3 ^ (16 * 𝔇)) ^ (g + 1)) := Nat.mul_le_mul h1 h2
    _ = 9 ^ m * (2 ^ (6 * 𝔇) * 3 ^ (16 * 𝔇)) ^ (g + 1) := by rw [mul_pow]; ring

/-- **The weighted layering sum over a ladder** (TARGET layerlad (`sumofexp0`); molecule-level form).
`B` is the base of the bond weights `B^{|𝔏_v − 𝔏_{v'}|}` (TARGET's `C_0` in the product). -/
theorem ladder_sum_le (hM : M.IsMolecule) (hL : M.IsLadder u v) {depth : V → ℕ} {𝔇 : ℕ}
    (B : ℝ) (hB : 1 ≤ B) (𝓕 : Finset (V → ℕ)) (hf : ∀ f ∈ 𝓕, (∀ x, f x ≤ 𝔇) ∧ ParentProp M f depth)
    (hinj : ∀ f ∈ 𝓕, ∀ g ∈ 𝓕, (∀ x ∈ Molecule.ladderAtoms u v, f x = g x) → f = g) (g : ℕ) :
    ∑ f ∈ 𝓕.filter (fun f => incoherencyIndex f (ladderGroups u v) = g),
        B ^ bondExp M (Molecule.ladderAtoms u v) f ≤
      (9 : ℝ) ^ m * (((2 : ℝ) ^ 6 * 3 ^ 16 * B ^ 28) ^ 𝔇) ^ (g + 1) := by
  classical
  set 𝓕' := 𝓕.filter (fun f => incoherencyIndex f (ladderGroups u v) = g) with h𝓕'
  have hsub : ∀ f ∈ 𝓕', f ∈ 𝓕 ∧ incoherencyIndex f (ladderGroups u v) = g := fun f hf' => by
    simpa [h𝓕'] using hf'
  have hcard := ladder_card_le M hM hL 𝓕' (fun f hf' => hf f (hsub f hf').1)
    (fun f hf' f2 hf2 h => hinj f (hsub f hf').1 f2 (hsub f2 hf2).1 h) g (fun f hf' => (hsub f hf').2)
  have hterm : ∀ f ∈ 𝓕', B ^ bondExp M (Molecule.ladderAtoms u v) f ≤ B ^ (𝔇 * (10 * g + 18)) := by
    intro f hf'
    apply pow_le_pow_right₀ hB
    have := ladder_bondExp_le M hM hL (hf f (hsub f hf').1).1 (hf f (hsub f hf').1).2
    rwa [(hsub f hf').2] at this
  have hsum : ∑ f ∈ 𝓕', B ^ bondExp M (Molecule.ladderAtoms u v) f ≤ 𝓕'.card * B ^ (𝔇 * (10 * g + 18)) := by
    calc _ ≤ ∑ f ∈ 𝓕', B ^ (𝔇 * (10 * g + 18)) := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine hsum.trans ?_
  have hN : (𝓕'.card : ℝ) ≤ (9 : ℝ) ^ m * ((2 ^ (6 * 𝔇) * 3 ^ (16 * 𝔇) : ℕ) : ℝ) ^ (g + 1) := by
    have := hcard.trans (nat_const_le m 𝔇 g)
    exact_mod_cast this
  have hB' : B ^ (𝔇 * (10 * g + 18)) ≤ (B ^ (28 * 𝔇)) ^ (g + 1) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hB
    nlinarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  calc (𝓕'.card : ℝ) * B ^ (𝔇 * (10 * g + 18))
      ≤ ((9 : ℝ) ^ m * ((2 ^ (6 * 𝔇) * 3 ^ (16 * 𝔇) : ℕ) : ℝ) ^ (g + 1)) * (B ^ (28 * 𝔇)) ^ (g + 1) :=
        mul_le_mul hN hB' (by positivity) (by positivity)
    _ = (9 : ℝ) ^ m * (((2 : ℝ) ^ 6 * 3 ^ 16 * B ^ 28) ^ 𝔇) ^ (g + 1) := by
        push_cast
        rw [mul_assoc, ← mul_pow]
        congr 2
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]

end WaveTurbulence.LayerCnt
