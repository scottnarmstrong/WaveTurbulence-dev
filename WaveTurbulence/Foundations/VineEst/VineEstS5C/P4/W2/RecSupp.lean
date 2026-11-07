/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecClause
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStepBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecVanish
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecInd

/-! # P4-W2 (session 17, step 3c): what a nonzero exceptional factor forces

`SuppConcl r zc addr`: at a clock function `u` where the exceptional factor `r.X x u` does not vanish, (i) (if `¬ zc`) every order pair of `addr` holds for the clocks of its two atoms (strictly, or at least
weakly with distinct variables), and (ii) the exceptional branch `r.bj` has a clock below the top clock `u a` or below the clock of an interior branch.  `supp_core` is the combinatorial core.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

section
variable {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β}

open Classical in
theorem nonstrict_kd0 (caseA : Prop) (c : Ch S bs₁ bs₂ rA rB) {r : Fin 3 × Fin 3 × Bool} (hr : r ∈ ordRels caseA c)
    (hs : r.2.2 = false) : recKind c = 0 ∧ r.2.1 = 0 ∧ r.1 ≠ 0 := by
  rcases c with (c | c | c | c | c | c) | (c | c)
  all_goals
    by_cases hc : caseA <;> simp [ordRels, hc] at hr <;> simp [recKind, kindOf]
  all_goals
    first
    | (rcases hr with rfl | rfl <;> simp_all)
    | skip

open Classical in
theorem strict_atom_exists (caseA : Prop) (c : Ch S bs₁ bs₂ rA rB) :
    ∃ r ∈ ordRels caseA c, r.1 = 0 ∧ r.2.2 = true ∧ r.2.1 ≠ 0 := by
  rcases c with (c | c | c | c | c | c) | (c | c)
  all_goals
    by_cases hc : caseA <;> simp [ordRels, hc]

end

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssembly G R n)

open VineParamContract in
theorem brSlot_inl_eq (hM9 : VINEPARAM) {v : GBranch G.tree} {c : (assemblyShape hM9 B).TVar}
    (h : brSlot hM9 B v = Sum.inl c) : (assemblyClockAtomEquiv hM9 B c).1 = v := by
  classical
  unfold brSlot at h
  by_cases hv : v ∈ clInteriorBranches R
  · rw [dif_pos hv, branchSlot_eq] at h
    have h2 : (assemblyClockAtomEquiv hM9 B).symm ⟨v, hv⟩ = c := Sum.inl.inj h
    have h3 := congrArg Subtype.val ((assemblyClockAtomEquiv hM9 B).apply_symm_apply ⟨v, hv⟩)
    rw [h2] at h3
    exact h3
  · rw [dif_neg hv] at h
    exact absurd h (by simp)

open Classical VineParamContract in
/-- **The combinatorial core**: if the order conditions of the summand `c` hold at the values `(u lo, dictS1, dictT1)`, then each order pair holds for the clocks of its atoms, and the lower joint is
below `qb` or `qr`. -/
theorem supp_core (hM9 : VINEPARAM) (caseA : Prop) {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β}
    (c : Ch S bs₁ bs₂ rA rB) (lo qb qr : GBranch G.tree) (ν : ℤˣ) (u : GBranch G.tree → ℝ)
    (hOrd : ExcOrd caseA (u lo) (dictS1 ν (u qb) (u qr)) (dictT1 ν (u qb) (u qr)) c) :
    (∀ p ∈ ordPairs (ordRels caseA c) (recSlots hM9 B lo qb qr ν), ∃ r ∈ ordRels caseA c,
        recSlots hM9 B lo qb qr ν r.1 = Sum.inl p.1 ∧ recSlots hM9 B lo qb qr ν r.2.1 = Sum.inl p.2 ∧
        (if r.2.2 then u (assemblyClockAtomEquiv hM9 B p.1).1 < u (assemblyClockAtomEquiv hM9 B p.2).1
          else u (assemblyClockAtomEquiv hM9 B p.1).1 ≤ u (assemblyClockAtomEquiv hM9 B p.2).1)) ∧
      (u lo < u qb ∨ u lo < u qr) := by
  have hv : (![u lo, dictS1 ν (u qb) (u qr), dictT1 ν (u qb) (u qr)] : Fin 3 → ℝ) =
      fun i => u (![lo, if ν = 1 then qr else qb, if ν = 1 then qb else qr] i) := by
    funext i; fin_cases i <;> simp [dictS1, dictT1] <;> split_ifs <;> rfl
  have hrel := (excOrd_iff caseA _ _ _ c).mp hOrd
  rw [hv] at hrel
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [ordPairs, Finset.mem_biUnion, List.mem_toFinset] at hp
    obtain ⟨r, hr', hp'⟩ := hp
    have hrr := hrel r hr'
    unfold pairOfRel at hp'
    rcases h1 : recSlots hM9 B lo qb qr ν r.1 with a1 | e1 <;> rcases h2 : recSlots hM9 B lo qb qr ν r.2.1 with a2 | e2
    · rw [h1, h2] at hp'
      simp at hp'
      have hpe : p = (a1, a2) := hp'
      subst hpe
      refine ⟨r, hr', h1, h2, ?_⟩
      have e1' : (assemblyClockAtomEquiv hM9 B a1).1 = ![lo, if ν = 1 then qr else qb, if ν = 1 then qb else qr] r.1 := by
        have := h1
        unfold recSlots at this
        revert this
        generalize r.1 = i
        fin_cases i <;> simp <;> intro hh <;> exact brSlot_inl_eq B hM9 hh
      have e2' : (assemblyClockAtomEquiv hM9 B a2).1 = ![lo, if ν = 1 then qr else qb, if ν = 1 then qb else qr] r.2.1 := by
        have := h2
        unfold recSlots at this
        revert this
        generalize r.2.1 = i
        fin_cases i <;> simp <;> intro hh <;> exact brSlot_inl_eq B hM9 hh
      unfold relHolds at hrr
      rw [e1', e2']
      exact hrr
    all_goals (rw [h1, h2] at hp'; simp at hp')
  · obtain ⟨r, hr, h0, hs, hne⟩ := strict_atom_exists caseA c
    have hrr := hrel r hr
    unfold relHolds at hrr
    rw [hs] at hrr
    simp only [ite_true] at hrr
    rw [h0] at hrr
    have : r.2.1 = 1 ∨ r.2.1 = 2 := by omega
    rcases this with h | h <;> rw [h] at hrr <;> simp at hrr
    · by_cases hν : ν = 1 <;> simp [hν] at hrr
      · exact Or.inr hrr
      · exact Or.inl hrr
    · by_cases hν : ν = 1 <;> simp [hν] at hrr
      · exact Or.inl hrr
      · exact Or.inr hrr

variable {RD : ReconstructionData G} {hG : G.IsPlain} {layer : GNode (RD.forest hG) → ℕ} {hLayer : IsLayering (RD.garden hG) layer}

open VineParamContract in
/-- **What a nonzero exceptional factor forces** (see the module docstring). -/
def SuppConcl (hM9 : VINEPARAM) {d : ℕ} (X : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) (bj : GBranch G.tree)
    (zc : Prop) (addr : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) : Prop :=
  ∀ x u, X x u ≠ 0 →
    (¬ zc → ∀ c ∈ addr, u (assemblyClockAtomEquiv hM9 B c.1).1 ≤ u (assemblyClockAtomEquiv hM9 B c.2).1 ∧
      (c.1 ≠ c.2 ∨ u (assemblyClockAtomEquiv hM9 B c.1).1 < u (assemblyClockAtomEquiv hM9 B c.2).1)) ∧
    (u bj < u a ∨ ∃ y ∈ U, y ≠ a ∧ u bj < u y)

open Classical VineParamContract in
/-- The consequences from `supp_core`, for a summand `c` with slots at `lo`, `qb`, `qr` and the exceptional branch `bj = lo`. -/
theorem suppConcl_of_core (hM9 : VINEPARAM) (hG : G.IsPlain) {β : Type*} {dd : ℕ} {S : SepTerms β dd} {bs₁ bs₂ rA rB : Finset β}
    (caseA : Prop) (c : Ch S bs₁ bs₂ rA rB) (lv : Lvl B) (pstar : lv.ι) (lo : GBranch G.tree)
    (hlo : lo = (assemblyPieceAt B (lv.e pstar).1).lower)
    (hqbU : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∈ U)
    (hqrU : qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∈ U)
    {d : ℕ} (X : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
    (hX : ∀ x u, X x u ≠ 0 → ExcOrd caseA (u lo)
      (dictS1 (nuOf (lv.state B RD hG layer hLayer) pstar) (u (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar)))
        (u (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))))
      (dictT1 (nuOf (lv.state B RD hG layer hLayer) pstar) (u (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar)))
        (u (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)))) c) :
    SuppConcl B hM9 X lo
      (ordBad (ordRels caseA c) (recSlots hM9 B lo (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar)) ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ recKind c = 0))
      (ordPairs (ordRels caseA c) (recSlots hM9 B lo (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) (nuOf (lv.state B RD hG layer hLayer) pstar))) := by
  intro x u hne
  obtain ⟨hpairs, hlt⟩ := supp_core B hM9 caseA c lo _ _ _ u (hX x u hne)
  refine ⟨fun hz p hp => ?_, ?_⟩
  · obtain ⟨r, hr, h1, h2, hrel⟩ := hpairs p hp
    by_cases hs : r.2.2 = true
    · rw [hs] at hrel
      simp only [ite_true] at hrel
      exact ⟨hrel.le, Or.inr hrel⟩
    · have hs' : r.2.2 = false := by simpa using hs
      rw [hs'] at hrel
      simp only [Bool.false_eq_true, ite_false] at hrel
      refine ⟨hrel, Or.inl ?_⟩
      obtain ⟨hk0, hr2, hr1⟩ := nonstrict_kd0 caseA c hr hs'
      have hqne : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) ≠
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) := fun h => hz (Or.inr ⟨h, hk0⟩)
      subst hlo
      obtain ⟨hm, h0, h12⟩ := rec_slots_typeII B RD hG layer hLayer hM9 lv pstar (nuOf (lv.state B RD hG layer hLayer) pstar) hqne
      rw [hr2, h0] at h2
      have hp2 : p.2 = .inl ⟨(lv.e pstar).1, 0⟩ := (Sum.inl.inj h2).symm
      have hr1' : r.1 = 1 ∨ r.1 = 2 := by omega
      intro hpp
      rw [hp2] at hpp
      rcases hr1' with h | h <;> rw [h] at h1 <;> rcases h12 with ⟨ha, hb⟩ | ⟨ha, hb⟩
      all_goals
        first
        | (rw [ha] at h1; have h3 := Sum.inl.inj h1; rw [hpp] at h3; first | (simp at h3; done) | exact absurd (eq_of_heq (Sigma.mk.inj (Sum.inl.inj h3)).2) (by simp [Fin.ext_iff]))
        | (rw [hb] at h1; have h3 := Sum.inl.inj h1; rw [hpp] at h3; first | (simp at h3; done) | exact absurd (eq_of_heq (Sigma.mk.inj (Sum.inl.inj h3)).2) (by simp [Fin.ext_iff]))
  · rcases hlt with h | h
    · by_cases hqa : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = a
      · left; rw [← hqa]; exact h
      · right; exact ⟨_, hqbU, hqa, h⟩
    · by_cases hqa : qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) = a
      · left; rw [← hqa]; exact h
      · right; exact ⟨_, hqrU, hqa, h⟩

end WaveTurbulence.VineEstS5C.P4.W2
