/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ChainMol
public import WaveTurbulence.Foundations.Spine.LadderBridge
/-! # Integer conservation from molecule decorations (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {d : ℕ}

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
lemma dartSign_eq_sgn (x : D) : M.dartSign x = ((sgn M x : ℤ) : ℝ) := by
  unfold Molecule.dartSign sgn
  split_ifs <;> simp

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
lemma sum_sgn_four (f : Fin 4 → D) (hout : (univ.filter fun k => M.out (f k) = true).card = 2) :
    ∑ k, sgn M (f k) = 0 := by
  have h1 : ∑ k, sgn M (f k) = ∑ k, (if M.out (f k) = true then (1 : ℤ) else -1) := rfl
  rw [h1, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have h3 : (univ.filter fun k => M.out (f k) = true).card +
      (univ.filter fun k => ¬ M.out (f k) = true).card = 4 := by
    rw [Finset.card_filter_add_card_filter_not]; simp
  omega

/-- Integer conservation at a degree-four atom whose source vanishes. -/
theorem int_conservation (a : V) (f : Fin 4 → D) (hf : Function.Injective f)
    (hd : M.dartsAt a = univ.image f)
    (hout : (univ.filter fun k => M.out (f k) = true).card = 2)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (κ : D → (Fin d → ℤ)) (c : V → Mom d)
    (hc : c a = 0)
    (h : ∀ v ∈ M.atoms, ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L base κ x = c v)
    (ha : a ∈ M.atoms) :
    ∑ k, sgn M (f k) • κ (f k) = 0 := by
  have h0 := h a ha
  rw [hc, hd, Finset.sum_image (fun x _ y _ hxy => hf hxy)] at h0
  simp only [dartSign_eq_sgn, Molecule.kvec] at h0
  have hs := sum_sgn_four f hout
  have e : ∑ k, ((sgn M (f k) : ℤ) : ℝ) • (base + latticePoint L (κ (f k))) =
      latticePoint L (∑ k, sgn M (f k) • κ (f k)) := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have : (∑ k, ((sgn M (f k) : ℤ) : ℝ)) = 0 := by exact_mod_cast hs
    rw [this, zero_smul, zero_add]
    ext j
    simp [latticePoint, Finset.sum_apply, Finset.sum_div, mul_div_assoc]
  rw [e] at h0
  exact latticePoint_injective hL (h0.trans (by ext j; simp [latticePoint]))

/-- The converse: integer conservation at a 2-out/2-in atom gives the real (momentum) conservation. -/
theorem real_conservation (a : V) (f : Fin 4 → D) (hf : Function.Injective f)
    (hd : M.dartsAt a = univ.image f)
    (hout : (univ.filter fun k => M.out (f k) = true).card = 2)
    (L : ℝ) (base : Mom d) (κ : D → (Fin d → ℤ))
    (h : ∑ k, sgn M (f k) • κ (f k) = 0) :
    ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L base κ x = 0 := by
  rw [hd, Finset.sum_image (fun x _ y _ hxy => hf hxy)]
  simp only [dartSign_eq_sgn, Molecule.kvec]
  have hs := sum_sgn_four f hout
  have e : ∑ k, ((sgn M (f k) : ℤ) : ℝ) • (base + latticePoint L (κ (f k))) =
      latticePoint L (∑ k, sgn M (f k) • κ (f k)) := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have : (∑ k, ((sgn M (f k) : ℤ) : ℝ)) = 0 := by exact_mod_cast hs
    rw [this, zero_smul, zero_add]
    ext j
    simp [latticePoint, Finset.sum_apply, Finset.sum_div, mul_div_assoc]
  rw [e, h]
  ext j; simp [latticePoint]

end WaveTurbulence.LadderDecay
