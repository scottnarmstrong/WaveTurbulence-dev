/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.VineGroups
public import WaveTurbulence.Foundations.LayerCnt.GardenParents
public import WaveTurbulence.Foundations.LayerCnt.LadderSum

/-! # TARGET Proposition `layervine`, first bound (L1513–L1521)

The weighted layering sum over any vine of `𝕄(𝒢)` is at most `C_0^m C_2^{g+1}`: a vine consists of at most
three ladders (the inserted rungs of its slots) plus the at most `15` atoms of its template.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine TTree

theorem vine_nat_const_le (m 𝔇 g : ℕ) :
    (𝔇 + 1) ^ (15 + 2 * 3) * 3 ^ (2 * m + 16 * 3 * 𝔇 * (g + 1)) ≤
      9 ^ m * (2 ^ (21 * 𝔇) * 3 ^ (48 * 𝔇)) ^ (g + 1) := by
  have h1 : (𝔇 + 1) ^ (15 + 2 * 3) ≤ (2 ^ (21 * 𝔇)) ^ (g + 1) := by
    have : 𝔇 + 1 ≤ 2 ^ 𝔇 := Nat.lt_two_pow_self
    calc (𝔇 + 1) ^ (15 + 2 * 3) ≤ (2 ^ 𝔇) ^ (15 + 2 * 3) := Nat.pow_le_pow_left this _
      _ = 2 ^ (21 * 𝔇) := by rw [← pow_mul]; ring_nf
      _ ≤ (2 ^ (21 * 𝔇)) ^ (g + 1) := Nat.le_self_pow (by omega) _
  have h2 : 3 ^ (2 * m + 16 * 3 * 𝔇 * (g + 1)) = 9 ^ m * (3 ^ (48 * 𝔇)) ^ (g + 1) := by
    rw [pow_add, ← pow_mul]
    have e1 : (3 : ℕ) ^ (2 * m) = 9 ^ m := by rw [pow_mul]; norm_num
    rw [e1]
  rw [h2]
  calc (𝔇 + 1) ^ (15 + 2 * 3) * (9 ^ m * (3 ^ (48 * 𝔇)) ^ (g + 1))
      ≤ (2 ^ (21 * 𝔇)) ^ (g + 1) * (9 ^ m * (3 ^ (48 * 𝔇)) ^ (g + 1)) := Nat.mul_le_mul_right _ h1
    _ = 9 ^ m * (2 ^ (21 * 𝔇) * 3 ^ (48 * 𝔇)) ^ (g + 1) := by rw [mul_pow]; ring

variable {w : ℕ}

/-- **Core vine bound**: `∑ B^{bondExp} ≤ 9^m ((2^21 3^48 B^60)^𝔇)^{g+1}` over a family of pre-layerings with values
`≤ 𝔇` and incoherency index `g`, pairwise distinct on the vine atoms. -/
theorem vine_sum_le (B : ℝ) (hB : 1 ≤ B) (G : Garden w) (X : VineType) (S : Finset (GBranch G.tree))
    (a b : GBranch G.tree) (R : VineRealization G.molecule X S a b) (m : ℕ)
    (hbad : X.IsBad = true → S.card = 2 * m + 2) (hnorm : X.IsBad = false → S.card = 2 * m + 5)
    (𝔇 g : ℕ) (𝓕 : Finset (GBranch G.tree → ℕ))
    (hf : ∀ f ∈ 𝓕, LFTwist.IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇)
    (hinj : ∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ S, f x = f' x) → f = f') :
    ∑ f ∈ 𝓕.filter (fun f => realizedIncoherencyIndex R f = g), B ^ bondExp G.molecule S f ≤
      (9 : ℝ) ^ m * (((2 : ℝ) ^ 21 * 3 ^ 48 * B ^ 60) ^ 𝔇) ^ (g + 1) := by
  set 𝓕' := 𝓕.filter (fun f => realizedIncoherencyIndex R f = g) with h𝓕'
  have hsub : ∀ f ∈ 𝓕', f ∈ 𝓕 ∧ realizedIncoherencyIndex R f = g := fun f hf' => by
    simpa [h𝓕'] using hf'
  have hK : ∑ c, kSlot R c ≤ m := by
    rw [sum_kSlot]
    have hS := card_S R
    have h1 := template_n_ge X
    cases hb : X.IsBad
    · have := hnorm hb; have := h1.2 hb; omega
    · have := hbad hb; have := h1.1; omega
  have hN : Fintype.card (Fin X.template.slots.length) ≤ 3 := by
    rw [Fintype.card_fin]; exact template_slots_le X
  have hr : (S \ allInt G.molecule (slotQ R)).card ≤ 15 := by
    rw [card_rest]; exact template_n_le X
  have key := multi_sum_le G.molecule (Mole.garden_isMolecule G) (slotQ R) (fun c => slotInt_sub R c)
    (fun c c' h => slotInt_disjoint R h) (depth := depthB G) (𝔇 := 𝔇) (G := g) hN hr hK B hB 𝓕'
    (fun f hf' => ⟨(hf f (hsub f hf').1).2, fun x hx => garden_parent_step G (hf f (hsub f hf').1).1 x hx⟩)
    (fun f hf' c => (incCnt_slot_le R c f).trans (hsub f hf').2.le)
    (fun f hf' f' hf2 h => hinj f (hsub f hf').1 f' (hsub f' hf2).1 h)
  refine key.trans ?_
  have hN' := vine_nat_const_le m 𝔇 g
  have hcastN : ((((𝔇 + 1) ^ (15 + 2 * 3) * 3 ^ (2 * m + 16 * 3 * 𝔇 * (g + 1)) : ℕ)) : ℝ) ≤
      (9 : ℝ) ^ m * ((2 ^ (21 * 𝔇) * 3 ^ (48 * 𝔇) : ℕ) : ℝ) ^ (g + 1) := by exact_mod_cast hN'
  have hB' : B ^ (10 * 𝔇 * 3 * (g + 1) + 2 * 𝔇 * 15) ≤ (B ^ (60 * 𝔇)) ^ (g + 1) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hB
    nlinarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  calc (((𝔇 + 1) ^ (15 + 2 * 3) * 3 ^ (2 * m + 16 * 3 * 𝔇 * (g + 1)) : ℕ) : ℝ) *
        B ^ (10 * 𝔇 * 3 * (g + 1) + 2 * 𝔇 * 15)
      ≤ ((9 : ℝ) ^ m * ((2 ^ (21 * 𝔇) * 3 ^ (48 * 𝔇) : ℕ) : ℝ) ^ (g + 1)) * (B ^ (60 * 𝔇)) ^ (g + 1) :=
        mul_le_mul hcastN hB' (by positivity) (by positivity)
    _ = (9 : ℝ) ^ m * (((2 : ℝ) ^ 21 * 3 ^ 48 * B ^ 60) ^ 𝔇) ^ (g + 1) := by
        push_cast
        rw [mul_assoc, ← mul_pow]
        congr 2
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]

/-- **TARGET `layervine`, first bound** (L1513–L1521). `R` is a realization of the vine `𝕍` (atom set `S`,
joints `a, b`, type `X`) in `𝕄(𝒢)`; its groups give the incoherency index (`cohmol`). `S` has `2m+2` atoms for a
bad vine (types (I), (II)) and `2m+5` for a normal vine, and incoherency index `g` (`≤ m` resp. `≤ m+1`). For every
finite family `𝓕` of pre-layerings of `𝒢` with values `≤ 𝔇`, pairwise distinct on the atoms of `𝕍`, the sum over the
members of incoherency index `g` of `∏_ℓ B^{|𝔏_v − 𝔏_{v'}|}` over the bonds `ℓ` joining atoms of `𝕍` is at most
`C_0^m C_2^{g+1}` (constants as in `layerlad`). Neither (CL) nor canonicity is needed for this bound; with `𝒢` the
skeleton `𝒢_sk` and `f` the induced pre-layering (T.L1463) this is the source statement. -/
theorem layervine_bound (B : ℝ) (hB : 1 ≤ B) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (G : Garden w) (X : VineType) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree),
      G.molecule.IsVine X S a b → ∀ (R : VineRealization G.molecule X S a b) (m : ℕ),
      (X.IsBad = true → S.card = 2 * m + 2) → (X.IsBad = false → S.card = 2 * m + 5) →
      ∀ (𝔇 : ℕ) (C₂ : ℝ), C₀ ^ (𝔇 + 1) ≤ C₂ → ∀ g : ℕ,
      (X.IsBad = true → g ≤ m) → (X.IsBad = false → g ≤ m + 1) →
      ∀ 𝓕 : Finset (GBranch G.tree → ℕ),
        (∀ f ∈ 𝓕, LFTwist.IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇) →
        (∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ S, f x = f' x) → f = f') →
        ∑ f ∈ 𝓕.filter (fun f => realizedIncoherencyIndex R f = g),
            ∏ x ∈ bondsIn G.molecule S,
              B ^ dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) ≤
          C₀ ^ m * C₂ ^ (g + 1) := by
  refine ⟨max 9 ((2 : ℝ) ^ 21 * 3 ^ 48 * B ^ 60), le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro G X S a b _ R m hbad hnorm 𝔇 C₂ hC₂ g _ _ 𝓕 hf hinj
  set C₀ : ℝ := max 9 ((2 : ℝ) ^ 21 * 3 ^ 48 * B ^ 60) with hC₀
  have hC1 : 1 ≤ C₀ := le_trans (by norm_num) (le_max_left _ _)
  have hpr : ∀ f : GBranch G.tree → ℕ,
      ∏ x ∈ bondsIn G.molecule S,
        B ^ dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) =
      B ^ bondExp G.molecule S f := fun f => by
    unfold bondExp; rw [Finset.prod_pow_eq_pow_sum]
  simp only [hpr]
  refine (vine_sum_le B hB G X S a b R m hbad hnorm 𝔇 g 𝓕 hf hinj).trans ?_
  have h9 : (9 : ℝ) ^ m ≤ C₀ ^ m := pow_le_pow_left₀ (by norm_num) (le_max_left _ _) m
  have hK1 : ((2 : ℝ) ^ 21 * 3 ^ 48 * B ^ 60) ^ 𝔇 ≤ C₂ := by
    calc _ ≤ C₀ ^ 𝔇 := pow_le_pow_left₀ (by positivity) (le_max_right _ _) 𝔇
      _ ≤ C₀ ^ (𝔇 + 1) := pow_le_pow_right₀ hC1 (by omega)
      _ ≤ C₂ := hC₂
  exact mul_le_mul h9 (pow_le_pow_left₀ (by positivity) hK1 (g + 1)) (by positivity) (by positivity)

end WaveTurbulence.LayerCnt
