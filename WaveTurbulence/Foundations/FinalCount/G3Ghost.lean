/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RemovalDev
public import WaveTurbulence.Foundations.FinalCount.CoverProj
public import WaveTurbulence.Foundations.FinalCount.G3Adm
/-! **FINALCOUNT-G3: deleting dartless (ghost) atoms does not change `𝔄`** (the ghost deletion of Step 2, reading R-T1).

If every dart of `M` sits at an atom satisfying `P`, then `restrictP M P` only forgets atoms without darts:
`𝔄(M) ≤ 𝔄(restrictP M P)` for the inherited admissible classes. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) (P : V → Prop) [DecidablePred P] (h : PClosed M P)

theorem sum_dartsAt_restrict {β : Type*} [AddCommMonoid β] {v : V} (hv : P v) (g : D → β) :
    ∑ x ∈ (restrictP M P h).dartsAt v, g x.1 = ∑ x ∈ M.dartsAt v, g x := by
  rw [restrictP_dartsAt M P h hv, Finset.sum_subtype_eq_sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_true_of_mem fun x hx => ?_
  have : M.atom x = v := by simpa [Molecule.dartsAt] using hx
  rw [this]; exact hv

include h in
theorem countE_restrict_dartless (hno : ∀ x : D, P (M.atom x)) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart M P → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) :
    M.countE L γ δ w Adm ≤ ((1 : ℕ) : ℕ∞) * (restrictP M P h).countE L γ δ w Adm' := by
  refine countE_le_mul_of_cover_proj M (restrictP M P h) L γ δ w Adm Adm' (fun κ x => κ x.1) 1 ?_
  intro c β k0 hp
  refine ⟨Unit, {()}, fun _ => Set.univ, fun _ => (c, β, fun x => k0 x.1), by simp, ?_, ?_, ?_⟩
  · intro i _
    refine ⟨fun v hv hv4 => hp.1 v (Finset.mem_filter.1 hv).1 ?_, fun x => ?_⟩
    · rw [← restrictP_deg M P h (Finset.mem_filter.1 hv).2]; exact hv4
    · exact hp.2 x.1
  · intro κ _; simp
  · intro i _
    refine ⟨fun κ _ κ' _ e => ?_, ?_⟩
    · funext x
      exact congrFun e ⟨x, hno x⟩
    · rintro _ ⟨κ, ⟨-, hκ⟩, rfl⟩
      obtain ⟨⟨hmate, hsum⟩, ⟨hG, hk⟩, hA⟩ := hκ
      refine ⟨⟨fun x => hmate x.1, fun v hv => ?_⟩, ⟨fun v hv => ?_, fun x => hk x.1⟩, hAdm κ hA⟩
      · have hv' := Finset.mem_filter.1 hv
        have := hsum v hv'.1
        show ∑ x ∈ (restrictP M P h).dartsAt v, M.dartSign x.1 • Molecule.kvec L w κ x.1 = c v
        rw [sum_dartsAt_restrict M P h hv'.2 (fun x => M.dartSign x • Molecule.kvec L w κ x)]
        exact this
      · have hv' := Finset.mem_filter.1 hv
        have := hG v hv'.1
        unfold Molecule.Gamma at this
        show |(restrictP M P h).Gamma L w (fun x => κ x.1) v - β v| ≤ _
        unfold Molecule.Gamma
        rw [show ∑ x ∈ (restrictP M P h).dartsAt v, (restrictP M P h).dartSign x *
            ‖Molecule.kvec L w (fun x : PDart M P => κ x.1) x‖ ^ 2 =
            ∑ x ∈ (restrictP M P h).dartsAt v, M.dartSign x.1 * ‖Molecule.kvec L w κ x.1‖ ^ 2 from rfl,
          sum_dartsAt_restrict M P h hv'.2 (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2)]
        exact this


section dartless
variable {V' D' : Type*} [DecidableEq V'] [Fintype D'] [DecidableEq D'] (N : Molecule V' D') [IsEmpty D']

theorem dartless_bonds : N.bonds.card = 0 := by
  unfold Molecule.bonds; simp

theorem dartless_numComponents : N.numComponents = N.atoms.card := by
  unfold Molecule.numComponents
  have hadj : ∀ u v : V', ¬ N.Adj u v := fun u v ⟨x, _⟩ => isEmptyElim x
  have hb : Function.Bijective (Quot.mk (fun u v : N.atoms => N.Adj u.1 v.1)) := by
    refine ⟨fun a b hab => ?_, Quot.mk_surjective⟩
    have h1 := Quot.eqvGen_exact hab
    have h2 : ∀ x y : N.atoms, Relation.EqvGen (fun u v : N.atoms => N.Adj u.1 v.1) x y → x = y := by
      intro x y hxy
      induction hxy with
      | rel x y hxy => exact absurd hxy (hadj _ _)
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact h2 a b h1
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem dartless_rank : N.circuitRank = 0 := by
  unfold Molecule.circuitRank
  rw [dartless_bonds N, dartless_numComponents N]; simp

theorem dartless_ladders : N.maximalLadders = ∅ := by
  ext S
  simp only [Finset.notMem_empty, iff_false]
  intro hS
  obtain ⟨m, u, v, hl, -⟩ := (Finset.mem_filter.1 hS).2.1
  have := hl.2.2.2.1 0
  unfold Molecule.bondsBetween Molecule.bonds at this
  simp at this

end dartless

include h in
theorem countA_restrict_dartless (hno : ∀ x : D, P (M.atom x)) (L γ δ C₁ : ℝ) (w : Mom d)
    (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C₁)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart M P → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (Pl : Finset V → ℝ)
    (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (Pl S)) :
    IsDeviation (M.countA L γ δ C₁ w Adm Pl) ((restrictP M P h).countA L γ δ C₁ w Adm' Pl) 1 := by
  have : IsEmpty (PDart M (fun a => ¬ P a)) := ⟨fun x => x.2 (hno x.1)⟩
  have key := removal_isDeviation M P h L γ δ C₁ w hL hδ hC Adm Adm' Pl hX ((1 : ℕ) : ℕ∞)
    (countE_restrict_dartless M P h hno L γ δ w Adm Adm' hAdm)
  rw [dartless_rank (restrictP M (fun a => ¬ P a) h.neg), dartless_ladders (restrictP M (fun a => ¬ P a) h.neg)] at key
  simpa [rankFactor] using key

end WaveTurbulence.FinalCountG3
