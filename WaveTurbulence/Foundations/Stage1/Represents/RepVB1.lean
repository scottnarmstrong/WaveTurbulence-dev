/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepCount2
public import WaveTurbulence.Foundations.Stage1.Represents.RepNode1
public import WaveTurbulence.Foundations.Vine.B.Fiber1
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: uniform decoration count of the outer mode amplitudes

For a mode `ξ` of a `SlotFam` of `G_sb`, `ampBound` (the outer amplitudes at a decoration) is supported on the decorations
whose pair momenta lie in the unit balls of the mode centres (`a_supp`), a finite set of cardinality at most
`((⌊2L⌋₊ + 2)^d)^{#pairs}`, uniformly in `ξ`.  This gives `hsum` of VINE-B♯'s per-mode identity and the uniform bound
needed to sum over the modes.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine

variable {w d : ℕ} {S : Garden w}

open scoped Classical in
/-- `decoration_count` with the unit-ball condition imposed on the pair slots only. -/
theorem decoration_count_pairs (hS : S.IsPlain) (L : ℝ) (hL : 0 < L) (base : Mom d) (roots : Fin w → Fin d → ℤ)
    (c : SourcePair S → Mom d) :
    {κ : GenDecoration S d roots 0 |
        ∀ p, hasBond hS (Sum.inl p) → ‖base + latticePoint L (κ.1 (slotNode hS (Sum.inl p))) - c p‖ ≤ 1}.Finite ∧
      {κ : GenDecoration S d roots 0 |
        ∀ p, hasBond hS (Sum.inl p) → ‖base + latticePoint L (κ.1 (slotNode hS (Sum.inl p))) - c p‖ ≤ 1}.ncard ≤
      ((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair S) := by
  choose F hFcard hFmem using fun p : SourcePair S => ball_finset L hL (base - c p)
  let Bnd : SourcePair S → Finset (Fin d → ℤ) := fun p =>
    if hasBond hS (Sum.inl p) then F p else {kconstInt hS roots (Sum.inl p)}
  let Φ : GenDecoration S d roots 0 → (SourcePair S → Fin d → ℤ) :=
    fun κ p => κ.1 (slotNode hS (Sum.inl p))
  have hmaps : Set.MapsTo Φ {κ : GenDecoration S d roots 0 |
        ∀ p, hasBond hS (Sum.inl p) → ‖base + latticePoint L (κ.1 (slotNode hS (Sum.inl p))) - c p‖ ≤ 1}
      (↑(Fintype.piFinset Bnd) : Set (SourcePair S → Fin d → ℤ)) := by
    intro κ hκ
    simp only [Finset.mem_coe, Fintype.mem_piFinset]
    intro p
    by_cases hb : hasBond hS (Sum.inl p)
    · simp only [Bnd, hb, ite_true]
      apply hFmem
      have := hκ _ hb
      have e : (base - c p) + latticePoint L (κ.1 (slotNode hS (Sum.inl p))) =
          base + latticePoint L (κ.1 (slotNode hS (Sum.inl p))) - c p := by abel
      rw [e]; exact this
    · simp only [Bnd, hb, ite_false, Finset.mem_singleton]
      exact kconstInt_spec hS roots _ hb κ.1 κ.2.1.2 κ.2.2.1
  have hinj : Set.InjOn Φ {κ : GenDecoration S d roots 0 |
        ∀ p, hasBond hS (Sum.inl p) → ‖base + latticePoint L (κ.1 (slotNode hS (Sum.inl p))) - c p‖ ≤ 1} := by
    intro κ _ κ' _ h
    apply Subtype.ext
    refine Comb.decoration_ext κ.2.1 κ'.2.1 fun ℓ => ?_
    rw [dec_leaf_eq_first hS κ.1 κ.2.1.2 ℓ, dec_leaf_eq_first hS κ'.1 κ'.2.1.2 ℓ]
    exact congrFun h (pairOfLeaf S hS ℓ)
  have hfin : (↑(Fintype.piFinset Bnd) : Set (SourcePair S → Fin d → ℤ)).Finite := Finset.finite_toSet _
  refine ⟨Set.Finite.of_injOn hmaps hinj hfin, (Set.ncard_le_ncard_of_injOn Φ hmaps hinj hfin).trans ?_⟩
  rw [Set.ncard_coe_finset, Fintype.card_piFinset]
  calc ∏ p, (Bnd p).card ≤ ∏ _p : SourcePair S, (⌊2 * L⌋₊ + 2) ^ d := by
        refine Finset.prod_le_prod fun p _ => ?_
        by_cases hb : hasBond hS (Sum.inl p)
        · simp only [Bnd, hb, ite_true]; exact hFcard p
        · simp only [Bnd, hb, ite_false, Finset.card_singleton]
          exact Nat.one_le_pow _ _ (by omega)
    _ = _ := by simp

open scoped Classical in
/-- The outer amplitudes of a mode are supported on at most `((⌊2L⌋₊+2)^d)^{#pairs}` decorations and bounded by `1`. -/
theorem tsum_ampBound_mode_le (fam : SlotFam S d) (hS : S.IsPlain) (L : ℝ) (hL : 0 < L) (base : Mom d)
    (roots : Fin w → Fin d → ℤ) (ξ : ∀ s, fam.Λ s) :
    Summable (fun z : GenDecoration S d roots 0 =>
        VineB.ampBound hS L base (fun s k => fam.a s (ξ s) k) z) ∧
      ∑' z : GenDecoration S d roots 0, VineB.ampBound hS L base (fun s k => fam.a s (ξ s) k) z ≤
        (((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair S) : ℕ) := by
  obtain ⟨hF, hC⟩ := decoration_count_pairs hS L hL base roots (fun p => latPt d (fam.n (Sum.inl p) (ξ (Sum.inl p))))
  set K := {κ : GenDecoration S d roots 0 |
    ∀ p, hasBond hS (Sum.inl p) →
      ‖base + latticePoint L (κ.1 (slotNode hS (Sum.inl p))) - latPt d (fam.n (Sum.inl p) (ξ (Sum.inl p)))‖ ≤ 1}
    with hK
  have hle : ∀ z : GenDecoration S d roots 0,
      VineB.ampBound hS L base (fun s k => fam.a s (ξ s) k) z ≤ if z ∈ hF.toFinset then 1 else 0 := by
    intro z
    by_cases hz : z ∈ hF.toFinset
    · simp only [hz, ite_true]
      unfold VineB.ampBound
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ => fam.a_one s (ξ s) _
    · simp only [hz, ite_false]
      have hz' : z ∉ K := by simpa [Set.Finite.mem_toFinset] using hz
      simp only [hK, Set.mem_ofPred_eq, not_forall] at hz'
      obtain ⟨p, hb, hp⟩ := hz'
      have h0 : fam.a (Sum.inl p) (ξ (Sum.inl p))
          (base + latticePoint L (z.1 (slotNode hS (Sum.inl p)))) = 0 := by
        by_contra hne
        exact hp (fam.a_supp p _ _ hne)
      unfold VineB.ampBound
      rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl p)) (by simp [h0])]
  have hnn : ∀ z : GenDecoration S d roots 0, 0 ≤ VineB.ampBound hS L base (fun s k => fam.a s (ξ s) k) z :=
    fun z => VineB.ampBound_nonneg _ _ _ _ _
  have hs : Summable (fun z : GenDecoration S d roots 0 => if z ∈ hF.toFinset then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := hF.toFinset) (fun x hx => by simp [hx])
  refine ⟨Summable.of_nonneg_of_le hnn hle hs, ?_⟩
  calc ∑' z : GenDecoration S d roots 0, VineB.ampBound hS L base (fun s k => fam.a s (ξ s) k) z
      ≤ ∑' z : GenDecoration S d roots 0, (if z ∈ hF.toFinset then (1 : ℝ) else 0) :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnn hle hs) hs
    _ = (hF.toFinset.card : ℝ) := by
        rw [tsum_eq_sum (s := hF.toFinset) (fun x hx => by simp [hx]), Finset.sum_ite_of_true (fun x hx => hx),
          Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
        have : hF.toFinset.card ≤ ((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair S) := by
          rw [← Set.ncard_eq_toFinset_card _ hF]; exact hC
        exact_mod_cast this

end WaveTurbulence.Represents
