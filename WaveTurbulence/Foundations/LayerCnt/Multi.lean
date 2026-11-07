/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Ladder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Several rung sequences plus a bounded set of extra atoms (TARGET layervine, L1519)

"`𝕍` consists of at most three ladders plus less than `20` extra atoms, so we can apply Proposition `layerlad`
to the part involving atoms and bonds in one of these ladders, while the part involving the extra atoms
contributes at most `C_0^{100𝔇} ≤ C_2`." Generic form: a finite family of `FullRungSequence`s with disjoint
interiors inside an atom set `S`, the other atoms of `S` being `r` extra atoms.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
  {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → ℕ}

/-- All interior atoms of a family of rung sequences. -/
@[expose] def allInt (Q : ∀ c, FullRungSequence M (k c)) : Finset V :=
  Finset.univ.biUnion fun c => intAtoms (Q c).u (Q c).v (k c)

theorem multi_dartExp_le (hM : M.IsMolecule) (Q : ∀ c, FullRungSequence M (k c)) {S : Finset V}
    (hS : ∀ c, intAtoms (Q c).u (Q c).v (k c) ⊆ S)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (intAtoms (Q c).u (Q c).v (k c)) (intAtoms (Q c').u (Q c').v (k c')))
    {f depth : V → ℕ} {𝔇 : ℕ} (hf : ∀ x, f x ≤ 𝔇) (hP : ParentProp M f depth) {G : ℕ}
    (hG : ∀ c, incCnt (fun i => f ((Q c).u i)) (fun i => f ((Q c).v i)) 1 (k c) ≤ G) :
    (∀ c, tvab (fun i => f ((Q c).u i)) (fun i => f ((Q c).v i)) 1 (k c) ≤ 8 * 𝔇 * (G + 1)) ∧
    dartExp M S f ≤ Fintype.card ι * (20 * 𝔇 * (G + 1)) + 4 * 𝔇 * (S \ allInt M Q).card := by
  have hsub : allInt M Q ⊆ S := by
    intro x hx
    unfold allInt at hx
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hx
    exact hS c hc
  have h1 := dartExp_le_split M hM hsub hf
  have h2 : ∀ c, tvab (fun i => f ((Q c).u i)) (fun i => f ((Q c).v i)) 1 (k c) ≤ 8 * 𝔇 * (G + 1) ∧
      ∑ a ∈ intAtoms (Q c).u (Q c).v (k c), ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x))) ≤
        20 * 𝔇 * (G + 1) := fun c => interior_dartSum_bound M hM (Q c) hf hP _ _ (fun i => rfl) (fun i => rfl) (hG c)
  refine ⟨fun c => (h2 c).1, ?_⟩
  have h3 : ∑ a ∈ allInt M Q, ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x))) =
      ∑ c, ∑ a ∈ intAtoms (Q c).u (Q c).v (k c), ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x))) := by
    unfold allInt
    rw [Finset.sum_biUnion]
    intro c _ c' _ hcc
    exact hdisj c c' hcc
  have h4 : ∑ c, ∑ a ∈ intAtoms (Q c).u (Q c).v (k c), ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x))) ≤
      ∑ _c : ι, 20 * 𝔇 * (G + 1) := Finset.sum_le_sum (fun c _ => (h2 c).2)
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h4
  omega

/-- The weighted layering sum over `S` = (family of rung-sequence interiors) ∪ (`r` extra atoms). -/
theorem multi_sum_le (hM : M.IsMolecule) (Q : ∀ c, FullRungSequence M (k c)) {S : Finset V}
    (hS : ∀ c, intAtoms (Q c).u (Q c).v (k c) ⊆ S)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (intAtoms (Q c).u (Q c).v (k c)) (intAtoms (Q c').u (Q c').v (k c')))
    {depth : V → ℕ} {𝔇 G N r K : ℕ} (hN : Fintype.card ι ≤ N) (hr : (S \ allInt M Q).card ≤ r)
    (hK : ∑ c, k c ≤ K) (B : ℝ) (hB : 1 ≤ B) (𝓕 : Finset (V → ℕ))
    (hf : ∀ f ∈ 𝓕, (∀ x, f x ≤ 𝔇) ∧ ParentProp M f depth)
    (hG : ∀ f ∈ 𝓕, ∀ c, incCnt (fun i => f ((Q c).u i)) (fun i => f ((Q c).v i)) 1 (k c) ≤ G)
    (hinj : ∀ f ∈ 𝓕, ∀ g ∈ 𝓕, (∀ x ∈ S, f x = g x) → f = g) :
    ∑ f ∈ 𝓕, B ^ bondExp M S f ≤
      ((𝔇 + 1) ^ (r + 2 * N) * 3 ^ (2 * K + 16 * N * 𝔇 * (G + 1)) : ℕ) *
        B ^ (10 * 𝔇 * N * (G + 1) + 2 * 𝔇 * r) := by
  classical
  have hcl := fun f (hf' : f ∈ 𝓕) => multi_dartExp_le M hM Q hS hdisj (hf f hf').1 (hf f hf').2 (hG f hf')
  -- pointwise exponent bound
  have hterm : ∀ f ∈ 𝓕, B ^ bondExp M S f ≤ B ^ (10 * 𝔇 * N * (G + 1) + 2 * 𝔇 * r) := by
    intro f hf'
    apply pow_le_pow_right₀ hB
    have h1 := two_mul_bondExp_le M S f
    have h2 := (hcl f hf').2
    have h3 : Fintype.card ι * (20 * 𝔇 * (G + 1)) ≤ N * (20 * 𝔇 * (G + 1)) := Nat.mul_le_mul_right _ hN
    have h4 : 4 * 𝔇 * (S \ allInt M Q).card ≤ 4 * 𝔇 * r := Nat.mul_le_mul_left _ hr
    nlinarith
  -- count
  set R : Finset V := S \ allInt M Q with hR
  set Xr : Finset (↥R → ℕ) := Fintype.piFinset (fun _ : ↥R => range (𝔇 + 1)) with hXr
  have hXc : Xr.card = (𝔇 + 1) ^ R.card := by
    simp [hXr, Fintype.card_piFinset]
  have hcount := multi_card_le 𝓕 (fun c f i => f ((Q c).u i)) (fun c f i => f ((Q c).v i)) k Xr
    (fun f => fun x : ↥R => f x)
    (by
      intro f hf'
      simp only [hXr, Fintype.mem_piFinset, mem_range]
      intro x
      have := (hf f hf').1 x
      omega)
    𝔇 (8 * 𝔇 * (G + 1))
    (by intro f hf' c i _ _; exact ⟨(hf f hf').1 _, (hf f hf').1 _⟩)
    (by
      intro f hf' c
      have := (hcl f hf').1 c
      rw [tvab_eq] at this
      omega)
    (by
      intro f hf' g hg hcfg hE
      apply hinj f hf' g hg
      intro x hx
      by_cases hxI : x ∈ allInt M Q
      · unfold allInt at hxI
        obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hxI
        unfold intAtoms at hc
        simp only [mem_union, mem_image, mem_Ico] at hc
        rcases hc with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
        · exact (hcfg c i (by omega) (by omega)).1
        · exact (hcfg c i (by omega) (by omega)).2
      · have hxR : x ∈ R := mem_sdiff.mpr ⟨hx, hxI⟩
        exact congrFun hE ⟨x, hxR⟩)
  rw [hXc] at hcount
  have hsum : ∑ f ∈ 𝓕, B ^ bondExp M S f ≤ 𝓕.card * B ^ (10 * 𝔇 * N * (G + 1) + 2 * 𝔇 * r) := by
    calc _ ≤ ∑ f ∈ 𝓕, B ^ (10 * 𝔇 * N * (G + 1) + 2 * 𝔇 * r) := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine hsum.trans ?_
  have hcard : 𝓕.card ≤ (𝔇 + 1) ^ (r + 2 * N) * 3 ^ (2 * K + 16 * N * 𝔇 * (G + 1)) := by
    refine hcount.trans ?_
    rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
    have e1 : (𝔇 + 1) ^ R.card * (((𝔇 + 1) ^ Fintype.card ι) ^ 2 * (3 ^ ∑ c, (k c + 8 * 𝔇 * (G + 1))) ^ 2) ≤
        (𝔇 + 1) ^ (r + 2 * N) * 3 ^ (2 * K + 16 * N * 𝔇 * (G + 1)) := by
      have a1 : (𝔇 + 1) ^ R.card ≤ (𝔇 + 1) ^ r := Nat.pow_le_pow_right (by omega) hr
      have a2 : ((𝔇 + 1) ^ Fintype.card ι) ^ 2 ≤ (𝔇 + 1) ^ (2 * N) := by
        rw [← pow_mul, mul_comm]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have a3 : (3 ^ ∑ c, (k c + 8 * 𝔇 * (G + 1))) ^ 2 ≤ 3 ^ (2 * K + 16 * N * 𝔇 * (G + 1)) := by
        rw [← pow_mul]
        apply Nat.pow_le_pow_right (by norm_num)
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        have y1 : Fintype.card ι * (8 * 𝔇 * (G + 1)) ≤ N * (8 * 𝔇 * (G + 1)) := Nat.mul_le_mul_right _ hN
        nlinarith [y1, hK]
      calc _ ≤ (𝔇 + 1) ^ r * ((𝔇 + 1) ^ (2 * N) * 3 ^ (2 * K + 16 * N * 𝔇 * (G + 1))) :=
            Nat.mul_le_mul a1 (Nat.mul_le_mul a2 a3)
        _ = _ := by ring
    refine le_trans (le_of_eq ?_) e1
    rw [mul_pow, Finset.card_univ]
  have hc2 : (𝓕.card : ℝ) ≤ (((𝔇 + 1) ^ (r + 2 * N) * 3 ^ (2 * K + 16 * N * 𝔇 * (G + 1)) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hc2 (by positivity)

end WaveTurbulence.LayerCnt
