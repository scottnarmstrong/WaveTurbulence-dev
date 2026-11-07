/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4Vine3
public import WaveTurbulence.Foundations.FinalCount.Case5Final
public import WaveTurbulence.Foundations.FinalCount.Arith96b
public import WaveTurbulence.Foundations.FinalCount.Interp96
public import WaveTurbulence.Foundations.FinalCount.EvenCase96
public import WaveTurbulence.Foundations.FinalCount.Rough96
public import WaveTurbulence.Foundations.FinalCount.OpD
public import WaveTurbulence.Foundations.FinalCount.OpC
public import WaveTurbulence.Foundations.FinalCount.G8R.ThmA
import Mathlib.Tactic

/-! # Prop 9.6, case (4): `V_α = 0`, `V_β = 2` (DH23 L1883-L1886), conditional on the non-exceptional input

For the closure `𝕄₁` of `𝕄₀` (each `β`-chain replaced by a bond):
* `𝕄₁` Y-exceptional of `T`-type: Theorem A (`theorem_A`, `theorem_A_one`; case-4 note);
* `𝕄₁` Y-exceptional of `Q`-type: `𝕄₀` is a vine (II) (`c4_two_vine`), hence LG (`FinalDec.vineLG`), and operation (c)
  with Prop 10.1′ (`chain_A_bound`) gives `L^{-η/2}`; for one chain `Q`-type is impossible (a `Z_m(Q)` has two end rungs);
* `𝕄₁` not Y-exceptional: the **named input** `Case4NonExc` (DH23 Prop 10.4(2) consumed at L1883; findings F6-1, F6-2).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4

/-- **The final interpolation of case (4)**: `A ≤ L^{E₁}` (roughbd, two atoms of degree `2`) and `A ≤ L^{-η/128}` give
(finalcount) for `V_α = 0`, `V_β = 2`. -/
theorem case4_finish {d : ℕ} (hd : 3 ≤ d) {γ η L ρ : ℝ} {A : ℝ≥0∞} (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ (1 - γ) / 1000) (hL : 1 ≤ L) (hρ : 0 ≤ ρ)
    (hA1 : A ≤ ENNReal.ofReal (L ^ (-η ^ 2 * ρ + (16 * (d : ℝ) + 28) * (2 + 1))))
    (hA2 : A ≤ ENNReal.ofReal (L ^ (-(η / 128)))) : A ≤ ENNReal.ofReal (L ^ (-η ^ 2 - η ^ 5 * ρ)) := by
  obtain ⟨s1, s2, s3, s4⟩ := small_facts hd hγ1 hγ2 hη hsm
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have h := interp_L hL hA1 hA2 hθ0 hθ1
  refine h.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL ?_))
  have hη3 : η ^ 3 ≤ 1 / 100 := by nlinarith [pow_pos hη 2]
  have hη2 : η ^ 2 ≤ η / 6000 := by nlinarith
  have e2 : η ^ 3 * (-η ^ 2 * ρ) = -(η ^ 5 * ρ) := by ring
  nlinarith [pow_pos hη 2, pow_pos hη 3, mul_pos hη hη]

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- At most one pair with three bonds in `closureOne`. -/
theorem trip_closureOne (M : Molecule V D) (b b' : V) (x₁ x₂ : D) (hle2 : ∀ p q, M.bondsBetween p q ≤ 2)
    (hAt : (closureOne M b b' x₁ x₂).atoms = M.atoms \ {b, b'}) :
    (tripSet (closureOne M b b' x₁ x₂)).card ≤ 2 := by
  classical
  have hsub : tripSet (closureOne M b b' x₁ x₂) ⊆ {s(M.atom (M.mate x₁), M.atom (M.mate x₂))} := by
    intro e he
    obtain ⟨p, q, rfl, h3⟩ := tripSet_iff.mp he
    have hpq := bb_pos_mem (N := closureOne M b b' x₁ x₂) (p := p) (q := q) (by omega)
    rw [hAt] at hpq
    obtain ⟨hp, hq⟩ := hpq
    have hbb : (closureOne M b b' x₁ x₂).bondsBetween p q = M.bondsBetween p q +
        (if s(M.atom (M.mate x₁), M.atom (M.mate x₂)) = s(p, q) then 1 else 0) := by
      change (Mole.addBond (Degen.eraseAtoms M {b, b'}) _ _).bondsBetween p q = _
      rw [addBond_bondsBetween, Degen.bondsBetween_erase_eq M {b, b'} (mem_sdiff.mp hp).2 (mem_sdiff.mp hq).2]
    rw [hbb] at h3
    have := hle2 p q
    simp only [mem_singleton]
    by_cases h1 : s(M.atom (M.mate x₁), M.atom (M.mate x₂)) = s(p, q)
    · exact h1.symm
    · rw [if_neg h1] at h3; omega
  exact (card_le_card hsub).trans (by simp)

/-- A `Z_m(Q)` ladder cannot arise from a single new bond. -/
theorem zq_no_single {N : Molecule V D} {m : ℕ} {φ : Bool × ℕ → V} {c d : V} (hZ : IsZQ N m φ)
    (hle : ∀ p q, N.bondsBetween p q ≤ 2 + (if s(c, d) = s(p, q) then 1 else 0)) : False := by
  classical
  by_cases hm : m = 0
  · subst hm
    have h4 : N.bondsBetween (φ (false, 0)) (φ (true, 0)) = 4 := by
      rw [hZ.bb _ _ (by simp) (by simp)]; simp [zBB]
    have := hle (φ (false, 0)) (φ (true, 0))
    split_ifs at this <;> omega
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have h3 : ∀ j, j ≤ m → (j = 0 ∨ j = m) → N.bondsBetween (φ (false, j)) (φ (true, j)) = 3 := by
      intro j hj hj'
      rw [hZ.bb _ _ (by simpa using hj) (by simpa using hj)]
      simp [zBB, hm, hj']
    have hR : ∀ j, j ≤ m → (j = 0 ∨ j = m) → s(c, d) = s(φ (false, j), φ (true, j)) := by
      intro j hj hj'
      have := hle (φ (false, j)) (φ (true, j))
      rw [h3 j hj hj'] at this
      by_contra hne
      rw [if_neg hne] at this; omega
    have e := (hR 0 (Nat.zero_le _) (Or.inl rfl)).symm.trans (hR m le_rfl (Or.inr rfl))
    rcases Sym2.eq_iff.mp e with ⟨h1, _⟩ | ⟨h1, _⟩
    · have := hZ.inj _ _ (by simp) (by simp) h1; simp at this; omega
    · have := hZ.inj _ _ (by simp) (by simp) h1; simp at this

end

/-- **The non-exceptional input of case (4)** (NAMED; findings F6-1, F6-2). DH23 L1883-L1886 consumes Prop 10.4(2): if the
closure `𝕄₁` (each `β`-chain replaced by a bond) is not Y-exceptional, then `𝔄₀ ≲ L^{-η/128}`. Two chains / one chain. This is
the decoration-level consumption of `SplitBound` (the `Q`-split of `prop104_two_proved`) through operations (c), (d), which the
abstract `OpCAt`/`OpDAt` cannot carry, together with the `¬YReachesSmallCell` hypothesis of `prop104_two_proved`
(an `X`-route counterexample shows it is not derivable from the shape of `𝕄₀`, F6-2). It is NOT proved here. -/
structure Case4NonExc (d : ℕ) (γ η : ℝ) : Prop where
  two : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → (∃ v₂ : V, v₂ ∉ M.atoms) → ¬ odd →
      (¬ ∀ a ∈ M.atoms, M.deg a = 2) → ((alphaAtoms M.atoms cls).card = 0 ∧ (betaAtoms M.atoms cls).card = 2) →
      ∀ (b b' : V) (y₁ y₂ y₃ y₄ : D), Case4TwoData M cls b b' y₁ y₂ y₃ y₄ →
        ¬ YReachesQT (closureTwo M b b' y₁ y₂ y₃ y₄) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128)))
  one : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → (∃ v₂ : V, v₂ ∉ M.atoms) → ¬ odd →
      (¬ ∀ a ∈ M.atoms, M.deg a = 2) → ((alphaAtoms M.atoms cls).card = 0 ∧ (betaAtoms M.atoms cls).card = 2) →
      ∀ (b b' : V) (x₁ x₂ y y' : D), Case4OneData M cls b b' x₁ x₂ y y' →
        ¬ YReachesQT (closureOne M b b' x₁ x₂) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128)))

/-- The numerical bound of operation (c) at the LG scale `ρ = L^{-γ+η}`. -/
theorem chain_num {d : ℕ} {γ η δ L : ℝ} (hL1 : 1 ≤ L) (hδ : 0 < δ) (hη : 0 < η) (hηγ : η ≤ 1 - γ)
    (hlogC : 3 ^ d * ((d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) ≤ L ^ (η / 2)) :
    3 ^ d * ((d : ℝ) * δ⁻¹ * (L ^ (-γ + η))⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ) ≤ L ^ (-(η / 20)) := by
  have hLp : 0 < L := by linarith
  have e1 : (L ^ (-γ + η))⁻¹ * L ^ (-γ) = L ^ (-η) := by
    rw [← Real.rpow_neg hLp.le, ← Real.rpow_add hLp]; congr 1; ring
  have e2 : L ^ (γ - 1) ≤ L ^ (-η) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hlog0 : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (Real.log_nonneg hL1) _
  have hpos : 0 ≤ L ^ (-η) := Real.rpow_nonneg hLp.le _
  calc 3 ^ d * ((d : ℝ) * δ⁻¹ * (L ^ (-γ + η))⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)
      ≤ 3 ^ d * ((d : ℝ) * δ⁻¹ * L ^ (-η) + L ^ (-η)) * Real.log L ^ (8 : ℝ) := by
        rw [mul_assoc ((d : ℝ) * δ⁻¹), e1]; gcongr
    _ = (3 ^ d * ((d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ)) * L ^ (-η) := by ring
    _ ≤ L ^ (η / 2) * L ^ (-η) := mul_le_mul_of_nonneg_right hlogC hpos
    _ = L ^ (-(η / 2)) := by rw [← Real.rpow_add hLp]; congr 1; ring
    _ ≤ L ^ (-(η / 20)) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bb_closureOne (M : Molecule V D) (b b' : V) (x₁ x₂ : D) {p q : V} (hp : p ∉ ({b, b'} : Finset V))
    (hq : q ∉ ({b, b'} : Finset V)) :
    (closureOne M b b' x₁ x₂).bondsBetween p q = M.bondsBetween p q +
      (if s(M.atom (M.mate x₁), M.atom (M.mate x₂)) = s(p, q) then 1 else 0) := by
  change (Mole.addBond (Degen.eraseAtoms M {b, b'}) _ _).bondsBetween p q = _
  rw [addBond_bondsBetween, Degen.bondsBetween_erase_eq M {b, b'} hp hq]

end

theorem ne_of_gapAt_ne {d : ℕ} {D : Type*} {L : ℝ} {κ : D → (Fin d → ℤ)} {x y : D}
    (h : Molecule.gapAt L (0 : Mom d) κ x y ≠ 0) : κ x ≠ κ y := by
  intro h0
  apply h
  unfold Molecule.gapAt
  simp [Molecule.kvec, h0]

/-- **Case (4): `V_α = 0`, `V_β = 2`** (DH23 L1883-L1886), conditional on the named non-exceptional input. -/
theorem case_four_of_nonexc (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) (hNE : Case4NonExc.{u, v} d γ η) :
    EvenCaseAt.{u, v} d γ η (fun a b => a = 0 ∧ b = 2) := by
  classical
  have hγ0 : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  rw [hγ0] at hsm
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  obtain ⟨h1, h2, h3, h4⟩ := small_facts hd hγ.1 hγ.2 hη hsm
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hηγ : η ≤ min γ (1 - γ) := by rw [hγ0]; linarith
  have hηmax : η ≤ min γ (1 - γ) / 2 := by rw [hγ0]; linarith
  have hκ : η / 10 ≤ CountLemmas.kappaHalf γ := by
    refine le_min ?_ ?_
    · nlinarith
    · linarith
  obtain ⟨C₀, hC₀, hrough⟩ := rough96.{u, v} d hd γ η hγ01 hη hηγ hηs
  obtain ⟨CA, hCA, hthA⟩ := theorem_A.{u, v} d hd γ hγ η hη hηmax (opCInput.{u, v} d γ η hγ01) (opDInput.{u, v} d γ η hη)
  obtain ⟨CA1, hCA1, hthA1⟩ := theorem_A_one.{u, v} d hd γ hγ η hη hηmax (opCInput.{u, v} d γ η hγ01)
  obtain ⟨Cs, hCs, hchain⟩ := chain_A_bound.{u, v} d hd γ hγ η hη hηmax
  obtain ⟨CN2, hCN2, hN2⟩ := hNE.two
  obtain ⟨CN1, hCN1, hN1⟩ := hNE.one
  refine ⟨max (max (max C₀ CA) (max CA1 Cs)) (max CN2 CN1), le_trans hC₀ ((le_max_left _ _).trans
    ((le_max_left _ _).trans (le_max_left _ _))), fun m C1 hC1 δ hδ => ?_⟩
  have c0 : C1 ≥ C₀ := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hC1))
  have cA : C1 ≥ CA := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hC1))
  have cA1 : C1 ≥ CA1 := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hC1))
  have cs : C1 ≥ Cs := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hC1))
  have cN2 : C1 ≥ CN2 := (le_max_left _ _).trans ((le_max_right _ _).trans hC1)
  have cN1 : C1 ≥ CN1 := (le_max_right _ _).trans ((le_max_right _ _).trans hC1)
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 c0
  obtain ⟨RA, hRA⟩ := hthA C1 cA δ hδ
  obtain ⟨RA1, hRA1⟩ := hthA1 C1 cA1 δ hδ
  obtain ⟨Rc, hRc1, hRc⟩ := hchain C1 cs δ hδ
  obtain ⟨RN2, hRN21, hRN2⟩ := hN2 m C1 cN2 δ hδ
  obtain ⟨RN1, hRN11, hRN1⟩ := hN1 m C1 cN1 δ hδ
  obtain ⟨R3, hR31, hR3⟩ := const_log_le_rpow (C := 3 ^ d * ((d : ℝ) * δ⁻¹ + 1)) (ε := η / 2) 8 (by positivity)
  refine ⟨max (max (max L₀ RA) (max RA1 Rc)) (max (max RN2 RN1) (max R3 (Real.exp 1))), ?_, ?_⟩
  · exact le_trans hL₀1 ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  intro L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLRA : RA ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLRA1 : RA1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLRc : Rc ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLRN2 : RN2 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLRN1 : RN1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLR3 : R3 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hδ0 := hδ.1
  by_cases hAex : ∃ κ, Adm κ
  swap
  · push Not at hAex
    rw [countA_zero_of_noAdm M L γ δ C1 Adm P hAex]; exact bot_le
  obtain ⟨κ0, hκ0⟩ := hAex
  have hηL : L ^ (-(η / 128)) ≥ L ^ (-(CountLemmas.kappaHalf γ / 2)) := by
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hB : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128))) := by
    rcases c4_data hS hnodd hnc hcase.1 hcase.2 with ⟨b, b', y₁, y₂, y₃, y₄, D4⟩ | ⟨b, b', x₁, x₂, y, y', D1⟩
    · -- two chains
      have hy12 : y₁ ≠ y₂ := fun h => D4.hfar1 (by rw [h])
      have hy34 : y₃ ≠ y₄ := fun h => D4.hfar2 (by rw [h])
      have hyd : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ≠ b ∧ M.atom (M.mate y) ≠ b' := fun y hy =>
        ⟨fun h => D4.hnb (h ▸ D4.hendsE y hy), fun h => D4.hnb' (h ▸ D4.hendsE y hy)⟩
      have hat : ∀ {K : Finset V} {p q : D}, crossDarts M K = {p, q} → M.atom p ∈ K ∧ M.atom q ∈ K := by
        intro K p q h
        exact ⟨(mem_crossDarts.mp (by rw [h]; simp)).1, (mem_crossDarts.mp (by rw [h]; simp)).1⟩
      have hat1 : M.atom y₁ = b := mem_singleton.mp (hat D4.hc1).1
      have hat2 : M.atom y₂ = b := mem_singleton.mp (hat D4.hc1).2
      have hat3 : M.atom y₃ = b' := mem_singleton.mp (hat D4.hc2).1
      have hat4 : M.atom y₄ = b' := mem_singleton.mp (hat D4.hc2).2
      have hall1 : ∀ x, M.atom x = b → x = y₁ ∨ x = y₂ := by
        intro x hx
        have : x ∈ crossDarts M {b} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
          fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
        rw [D4.hc1] at this; simpa using this
      have hall2 : ∀ x, M.atom x = b' → x = y₃ ∨ x = y₄ := by
        intro x hx
        have : x ∈ crossDarts M {b'} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
          fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
        rw [D4.hc2] at this; simpa using this
      have hends : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ∈ M.atoms ∧ M.atom (M.mate y) ≠ b ∧
          M.atom (M.mate y) ≠ b' := fun y hy => ⟨M.atom_mem _, (hyd y hy).1, (hyd y hy).2⟩
      have hreg := regcore_closureTwo M hS.caps hS.noLoop hS.conn (nocut_M0 hS hF hLp hnodd hκ0 hfr) D4.hdeg4 D4.hbb'
        hat1 hat2 hat3 hat4 hy12 hy34 hall1 hall2 D4.ho1 D4.ho2 D4.ho3 D4.ho4 hends D4.hfar1 D4.hfar2
      have hm : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ∈ (M.atoms \ {b}) \ {b'} := fun y hy =>
        mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨M.atom_mem _, by simpa using (hyd y hy).1⟩, by simpa using (hyd y hy).2⟩
      have hAt := atoms_closureTwo M b b' y₁ y₂ y₃ y₄ (hm y₁ (by simp)) (hm y₂ (by simp)) (hm y₃ (by simp)) (hm y₄ (by simp))
      have htrip := trip_closureTwo M b b' y₁ y₂ y₃ y₄ hS.noTriple hAt
      by_cases hex : YReachesQT (closureTwo M b b' y₁ y₂ y₃ y₄)
      · rcases reach_cases hex 2 hreg htrip with ⟨k, hk, hroute⟩ | hQ
        · -- T-type: Theorem A
          have hcard1 : (crossDarts M {b}).card = 2 := by rw [D4.hc1, card_pair hy12]
          have heven := shape_even hS hnodd
          have hconnb := connected_erase_of_two_cross M hS.conn heven {b} hcard1
          have hM : M.IsMolecule := hS.isMolecule
          have hKA : ({b} : Finset V) ⊆ M.atoms := by simpa using D4.hb
          let Ta : TwoExit M := ⟨{b}, hKA, y₂, y₁, by rw [D4.hc1]; exact pair_comm _ _, hy12.symm, D4.hfar1.symm,
            D4.ho2, D4.ho1⟩
          have p₃ : M.atom y₃ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₃) ∉ ({b} : Finset V) :=
            ⟨by rw [hat3]; simpa using D4.hbb'.symm, by simpa using (hyd y₃ (by simp)).1⟩
          have p₄ : M.atom y₄ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₄) ∉ ({b} : Finset V) :=
            ⟨by rw [hat4]; simpa using D4.hbb'.symm, by simpa using (hyd y₄ (by simp)).1⟩
          obtain ⟨hcK, hdir⟩ := chain_after_erase hS.noLoop D4.hc2 p₃ p₄
          have hbN : b' ∈ (Degen.eraseAtoms M {b}).atoms := mem_sdiff.mpr ⟨D4.hb', by simpa using D4.hbb'.symm⟩
          have hneN : (⟨y₄, p₄⟩ : Degen.RetainedDart M {b}) ≠ ⟨y₃, p₃⟩ := fun h => hy34 (congrArg Subtype.val h).symm
          have hKb : ({b'} : Finset V) ⊆ (Degen.eraseAtoms M {b}).atoms := by simpa using hbN
          let Tb : TwoExit (Degen.eraseAtoms M {b}) :=
            ⟨{b'}, hKb, ⟨y₄, p₄⟩, ⟨y₃, p₃⟩, by rw [hcK]; exact pair_comm _ _, hneN, D4.hfar2.symm, D4.ho4, D4.ho3⟩
          have hdb := hS.dir2 b D4.hb D4.hdeg2
          have hdb' := hS.dir2 b' D4.hb' D4.hdeg2'
          have hdbN : (Degen.eraseAtoms M {b}).outdeg b' = 1 ∧ (Degen.eraseAtoms M {b}).indeg b' = 1 := by
            unfold Molecule.outdeg Molecule.indeg; rw [hdir true, hdir false]; exact hdb'
          have hcapN := caps_eraseAtoms {b} hS.caps
          have hconnP : ∀ u ∈ Tb.post.atoms, ∀ w ∈ Tb.post.atoms, Tb.post.SameComponent u w := Tb.post_connected hconnb
          have hcapP := Tb.post_caps hcapN
          have hdegN : ∀ v ∈ Tb.Y, (Degen.eraseAtoms M {b}).deg v = 2 := by
            intro v hv
            have hv' : v = b' := mem_singleton.mp hv
            rw [hv']
            have := Mole.outdeg_add_indeg (Degen.eraseAtoms M {b}) b'; omega
          have hbA : (Degen.eraseAtoms M {b}).bonds.card + ({b} : Finset V).card + 1 = M.bonds.card :=
            erase_chain_bonds M Ta (fun v hv => by rw [mem_singleton.mp hv]; exact D4.hdeg2)
          have hbB : (Degen.eraseAtoms (Degen.eraseAtoms M {b}) {b'}).bonds.card + ({b'} : Finset V).card + 1 =
              (Degen.eraseAtoms M {b}).bonds.card := erase_chain_bonds (Degen.eraseAtoms M {b}) Tb hdegN
          have hpb : Tb.post.bonds.card = (Degen.eraseAtoms (Degen.eraseAtoms M {b}) {b'}).bonds.card + 1 :=
            Tb.post_bonds_eq
          have hMb := c5_two_bonds D4.hb D4.hb' D4.hbb' D4.hdeg2 D4.hdeg2' D4.hdeg4
          have hpatoms : Tb.post.atoms.card + 2 = M.atoms.card := by
            rw [Tb.post_atoms, card_sdiff_of_subset Tb.sub]
            have h1 : (Degen.eraseAtoms M {b}).atoms.card + 1 = M.atoms.card := by
              change (M.atoms \ {b}).card + 1 = _
              rw [card_sdiff_of_subset hKA]; have := card_pos.mpr ⟨b, D4.hb⟩; simp; omega
            have h2 : ({b'} : Finset V).card = 1 := card_singleton _
            show (Degen.eraseAtoms M {b}).atoms.card - ({b'} : Finset V).card + 2 = _
            omega
          have hEp : (Tb.post.bonds.card : ℤ) = 2 * Tb.post.atoms.card - 1 := by
            rw [card_singleton] at hbA hbB; omega
          obtain ⟨z, hz, hz4, hz3⟩ := exists_deg_ne_four Tb.post hcapP hEp
          have hgood : ∀ S ∈ MoleProp.ladderCells Tb.post, GoodCell Tb.post S :=
            fun S hS' => goodCell_of_connected_low hconnP hz hz3 hS'
          set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
          refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
          have hmain := hRA L hLRA M hS.caps hS.noLoop b b' y₁ y₂ y₃ y₄ D4.hb D4.hb' D4.hbb' hdb hdb' D4.hc1 D4.ho1
            D4.ho2 D4.hc2 D4.ho3 D4.ho4 D4.hfar1 D4.hfar2 (hyd y₁ (by simp)).2 (hyd y₂ (by simp)).2
            (hyd y₃ (by simp)).1 (hyd y₄ (by simp)).1 hS.conn hconnb hconnP hgood k hk hroute hreg.cap hreg.loop hreg.reg
            hreg.conn P' (fun S _ => hP _) (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ)
            (fun κ hκ => ⟨⟨fun p q hpq hpB hpo => ?_, hκ.2⟩, ne_of_gapAt_ne (hF.betaGap κ hκ.1 b D4.hb D4.hbeta y₁ y₂ hat1 hat2 hy12)⟩)
          · exact hmain.trans (ENNReal.ofReal_le_ofReal hηL)
          · have hpA : M.atom p ∈ M.atoms := M.atom_mem p
            have hε : (cls (M.atom p)).IsEps := D4.heps _ hpA (fun h => hpB (by simp [h])) (fun h => hpB (by simp [h]))
            exact (hF.epsLG κ hκ.1 _ hpA hε p q rfl hpq.symm hpo).le
        · -- Q-type: `M` is a vine (II), hence LG, and operation (c) applies
          obtain ⟨m', φ, hφ⟩ := yrouteQ_zq hQ hreg htrip
          have hV := c4_two_vine hS D4 ⟨m', φ, hφ⟩
          have hlg : ∀ κ, Adm κ → L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ y₁ - Molecule.kvec L (0 : Mom d) κ y₂‖ :=
            fun κ hκ => hF.vineLG (Or.inl ⟨_, _, _, hV⟩) κ hκ y₁ y₂ (hat1.trans hat2.symm)
              (by rw [D4.ho1, D4.ho2]; simp)
          have hAdm : ∀ κ, Adm κ → ∃ p q, M.atom p ∈ ({b} : Finset V) ∧ M.atom q = M.atom p ∧ p ≠ q ∧
              L ^ (-γ + η) ≤ ‖Molecule.kvec L (0 : Mom d) κ p - Molecule.kvec L (0 : Mom d) κ q‖ := fun κ hκ =>
            ⟨y₁, y₂, by rw [hat1]; simp, by rw [hat1, hat2], hy12, (hlg κ hκ).le⟩
          have hA2 := hRc L hLRc (L ^ (-γ + η)) (Real.rpow_pos_of_pos hLp _) M cls odd Adm P hS hF hnodd hnc hP hMA {b}
            D4.hKb hAdm
          exact hA2.trans ((ENNReal.ofReal_le_ofReal (chain_num hL1 hδ0 hη (by linarith) (hR3 L hLR3))).trans
            (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))))
      · exact hRN2 L hLRN2 M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' y₁ y₂ y₃ y₄ D4 hex
    · -- one chain
      have hcard : (crossDarts M {b, b'}).card = 2 := by rw [D1.hc, card_pair D1.hne]
      have heven := shape_even hS hnodd
      have hconnE := connected_erase_of_two_cross M hS.conn heven {b, b'} hcard
      have hM : M.IsMolecule := hS.isMolecule
      have hnocut := nocut_M0 hS hF hLp hnodd hκ0 hfr
      have hreg := regcore_closureOne hS.caps hS.noLoop hS.conn hnocut D1.hb D1.hb' D1.hdeg4 D1.hc D1.hne D1.ho1 D1.ho2
        D1.hfar
      have hend : ∀ w, (cls w).IsEps → w ∉ ({b, b'} : Finset V) := by
        intro w hw hwB
        rcases mem_insert.mp hwB with h | h
        · exact D1.hnb (h ▸ hw)
        · exact D1.hnb' ((mem_singleton.mp h) ▸ hw)
      have hx1 : M.atom (M.mate x₁) ∉ ({b, b'} : Finset V) := hend _ D1.hendsE.1
      have hx2 : M.atom (M.mate x₂) ∉ ({b, b'} : Finset V) := hend _ D1.hendsE.2
      have hAt : (closureOne M b b' x₁ x₂).atoms = M.atoms \ {b, b'} := by
        change insert (M.atom (M.mate x₁)) (insert (M.atom (M.mate x₂)) (M.atoms \ {b, b'})) = _
        rw [insert_eq_of_mem (mem_sdiff.mpr ⟨M.atom_mem _, hx2⟩), insert_eq_of_mem (mem_sdiff.mpr ⟨M.atom_mem _, hx1⟩)]
      have htrip := trip_closureOne M b b' x₁ x₂ hS.noTriple hAt
      by_cases hex : YReachesQT (closureOne M b b' x₁ x₂)
      · rcases reach_cases hex 2 hreg htrip with ⟨k, hk, hroute⟩ | hQ
        · -- T-type: Theorem A, one chain
          set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
          refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
          have hdb := hS.dir2 b D1.hb D1.hdeg2
          have hdb' := hS.dir2 b' D1.hb' D1.hdeg2'
          have hmain := hRA1 L hLRA1 M hS.caps hS.noLoop b b' x₁ x₂ y y' D1.hb D1.hb' hdb hdb' D1.hc D1.hfar D1.hyb
            D1.hyb' D1.hyy' hS.conn (chain_piece_connected D1.hK) hconnE k hk hroute hreg.cap hreg.loop hreg.reg hreg.conn
            P' (fun S _ => hP _) (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ)
            (fun κ hκ => ⟨⟨fun p q hpq hpB hpo => ?_, hκ.2⟩,
              ne_of_gapAt_ne (hF.betaGap κ hκ.1 b D1.hb D1.hbeta y y' D1.hyb D1.hyb' D1.hyy')⟩)
          · exact hmain.trans (ENNReal.ofReal_le_ofReal hηL)
          · have hpA : M.atom p ∈ M.atoms := M.atom_mem p
            have hε : (cls (M.atom p)).IsEps := D1.heps _ hpA (fun h => hpB (by simp [h])) (fun h => hpB (by simp [h]))
            exact (hF.epsLG κ hκ.1 _ hpA hε p q rfl hpq.symm hpo).le
        · -- Q-type is impossible for one chain
          exfalso
          obtain ⟨m', φ, hφ⟩ := yrouteQ_zq hQ hreg htrip
          refine zq_no_single (c := M.atom (M.mate x₁)) (d := M.atom (M.mate x₂)) hφ (fun p q => ?_)
          by_cases hpq : p ∈ (closureOne M b b' x₁ x₂).atoms ∧ q ∈ (closureOne M b b' x₁ x₂).atoms
          · rw [hAt] at hpq
            rw [bb_closureOne M b b' x₁ x₂ (mem_sdiff.mp hpq.1).2 (mem_sdiff.mp hpq.2).2]
            have := hS.noTriple p q
            split_ifs <;> omega
          · have : (closureOne M b b' x₁ x₂).bondsBetween p q = 0 := by
              by_cases hp : p ∈ (closureOne M b b' x₁ x₂).atoms
              · rw [Degen.bondsBetween_comm]; exact bb_zero_of_not_mem _ (fun hq => hpq ⟨hp, hq⟩) p
              · exact bb_zero_of_not_mem _ hp q
            rw [this]; omega
      · exact hRN1 L hLRN1 M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' x₁ x₂ y y' D1 hex
  have hA1 := hL₀ L hLL₀ M cls odd Adm P hS hF hsz hP hMA
  have hcard2 : (M.atoms.filter fun a => M.deg a ≠ 4).card = 2 := by
    rw [card_deg_ne_four_even hS hnodd, card_nonEps, hcase.1, hcase.2]
  rw [hcard2] at hA1
  have hρ : (0 : ℝ) ≤ (M.rho : ℝ) := Nat.cast_nonneg _
  have hfin := finalRHS_ge M cls odd hL1 hη.le hF.labRange
  have hexp : ((alphaAtoms M.atoms cls).card : ℝ) * ((γ - 5 * η) / 2) +
      ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
        (2 * min γ (1 - γ) + 5 * η ^ 2) * (open Classical in if odd then (0 : ℝ) else 1)) +
      (-(η ^ 5) * (M.rho : ℝ)) = -η ^ 2 - η ^ 5 * (M.rho : ℝ) := by
    rw [hcase.1, hcase.2, if_neg hnodd, hγ0]; push_cast; ring
  rw [hexp] at hfin
  exact (case4_finish hd hγ.1 hγ.2 hη hsm hL1 hρ (by push_cast at hA1 ⊢; exact hA1) hB).trans
    (ENNReal.ofReal_le_ofReal hfin)

end WaveTurbulence.FinalCountG8
