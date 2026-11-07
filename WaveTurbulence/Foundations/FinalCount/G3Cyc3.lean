/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Bal
public import WaveTurbulence.Foundations.FinalCount.G3TriPull
/-! **FINALCOUNT-G3: a three-atom balanced cycle is a triangle** (`TriData`).  Used for the `cycles` conclusion of
Prop 9.5 (L1807): a triangle component with two `α`-atoms would be a triangle with two SG triples, which `NoSGTriangle`
excludes. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

/-- The dart of a given direction at a balanced atom is unique. -/
theorem bal_uniq {M : Molecule V D} {c : V} (hb : M.outdeg c = 1 ∧ M.indeg c = 1) {z z' : D}
    (hz : M.atom z = c) (hz' : M.atom z' = c) (h : M.out z = M.out z') : z = z' := by
  cases ho : M.out z
  · have h1 := hb.2
    unfold Molecule.indeg at h1
    obtain ⟨o, ho'⟩ := Finset.card_eq_one.1 h1
    have e1 : z ∈ (M.dartsAt c).filter fun x => M.out x = false := by
      simp [Molecule.dartsAt, hz, ho]
    have e2 : z' ∈ (M.dartsAt c).filter fun x => M.out x = false := by
      simp [Molecule.dartsAt, hz', ← h, ho]
    rw [ho'] at e1 e2
    rw [Finset.mem_singleton.1 e1, Finset.mem_singleton.1 e2]
  · have h1 := hb.1
    unfold Molecule.outdeg at h1
    obtain ⟨o, ho'⟩ := Finset.card_eq_one.1 h1
    have e1 : z ∈ (M.dartsAt c).filter fun x => M.out x = true := by
      simp [Molecule.dartsAt, hz, ho]
    have e2 : z' ∈ (M.dartsAt c).filter fun x => M.out x = true := by
      simp [Molecule.dartsAt, hz', ← h, ho]
    rw [ho'] at e1 e2
    rw [Finset.mem_singleton.1 e1, Finset.mem_singleton.1 e2]

theorem bal_exists_out {M : Molecule V D} {c : V} (hb : M.outdeg c = 1 ∧ M.indeg c = 1) :
    ∃ o, M.atom o = c ∧ M.out o = true := by
  have h1 := hb.1
  unfold Molecule.outdeg at h1
  obtain ⟨o, ho'⟩ := Finset.card_eq_one.1 h1
  have : o ∈ (M.dartsAt c).filter fun x => M.out x = true := by rw [ho']; exact Finset.mem_singleton_self _
  simp [Molecule.dartsAt] at this
  exact ⟨o, this.1, this.2⟩

theorem exists_three_fresh [Infinite V] (S : Finset V) :
    ∃ f : Fin 3 → V, Function.Injective f ∧ ∀ j, f j ∉ S := by
  obtain ⟨f0, h0⟩ := Infinite.exists_notMem_finset S
  obtain ⟨f1, h1⟩ := Infinite.exists_notMem_finset (insert f0 S)
  obtain ⟨f2, h2⟩ := Infinite.exists_notMem_finset (insert f1 (insert f0 S))
  have n10 : f1 ≠ f0 := fun e => h1 (e ▸ Finset.mem_insert_self _ _)
  have n20 : f2 ≠ f0 := fun e => h2 (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have n21 : f2 ≠ f1 := fun e => h2 (e ▸ Finset.mem_insert_self _ _)
  refine ⟨![f0, f1, f2], ?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro j
    fin_cases j
    · exact h0
    · exact fun h => h1 (Finset.mem_insert_of_mem h)
    · exact fun h => h2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))

/-- **A balanced cycle of three atoms is a triangle.** `A` is a set of three degree-`2` atoms, closed under adjacency
and connected. For any outgoing dart `b₀` at an atom `u ∈ A` there is a `TriData` starting at `(u, b₀)` whose atoms are
those of `A`. -/
theorem cycle3_tri [Infinite V] {M : Molecule V D} (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x))
    {A : Finset V} (hAm : ∀ c ∈ A, c ∈ M.atoms) (hdeg : ∀ c ∈ A, M.deg c = 2)
    (hbal : ∀ c ∈ A, M.outdeg c = 1 ∧ M.indeg c = 1)
    (hcl : ∀ z, M.atom z ∈ A → M.atom (M.mate z) ∈ A)
    (hconn : ∀ c ∈ A, ∀ c' ∈ A, M.SameComponent c c') (hcard : A.card = 3)
    {u : V} (hu : u ∈ A) {b₀ : D} (hb₀ : M.atom b₀ = u) (hob₀ : M.out b₀ = true) :
    ∃ T : TriData M, T.t 0 = u ∧ T.b 0 = b₀ ∧ ∀ c ∈ A, c = T.t 0 ∨ c = T.t 1 ∨ c = T.t 2 := by
  have hmo : ∀ z, M.out z = true → M.out (M.mate z) = false := fun z h => by rw [M.out_mate, h]; rfl
  have hmi : ∀ z, M.out z = false → M.out (M.mate z) = true := fun z h => by rw [M.out_mate, h]; rfl
  set t₁ := M.atom (M.mate b₀) with ht₁
  have ht₁A : t₁ ∈ A := hcl b₀ (hb₀ ▸ hu)
  obtain ⟨b₁, hb₁, hob₁⟩ := bal_exists_out (hbal t₁ ht₁A)
  set t₂ := M.atom (M.mate b₁) with ht₂
  have ht₂A : t₂ ∈ A := hcl b₁ (hb₁ ▸ ht₁A)
  obtain ⟨b₂, hb₂, hob₂⟩ := bal_exists_out (hbal t₂ ht₂A)
  set t₃ := M.atom (M.mate b₂) with ht₃
  have ht₃A : t₃ ∈ A := hcl b₂ (hb₂ ▸ ht₂A)
  have n10 : t₁ ≠ u := fun e => hnl b₀ (by rw [hb₀]; exact e.symm)
  have n21 : t₂ ≠ t₁ := fun e => hnl b₁ (by rw [hb₁]; exact e.symm)
  have n32 : t₃ ≠ t₂ := fun e => hnl b₂ (by rw [hb₂]; exact e.symm)
  have n20 : t₂ ≠ u := by
    intro e20
    -- {u, t₁} is closed
    have hP : PClosed M (fun a => a = u ∨ a = t₁) := by
      intro z hz
      rcases hz with hz | hz
      · cases hoz : M.out z
        · have : z = M.mate b₁ := bal_uniq (hbal u hu) hz e20
              (by rw [hoz, hmo b₁ hob₁])
          rw [this, M.mate_mate, hb₁]; exact Or.inr rfl
        · have : z = b₀ := bal_uniq (hbal u hu) hz hb₀ (by rw [hoz, hob₀])
          rw [this]; exact Or.inr rfl
      · cases hoz : M.out z
        · have : z = M.mate b₀ := bal_uniq (hbal t₁ ht₁A) hz rfl (by rw [hoz, hmo b₀ hob₀])
          rw [this, M.mate_mate, hb₀]; exact Or.inl rfl
        · have : z = b₁ := bal_uniq (hbal t₁ ht₁A) hz hb₁ (by rw [hoz, hob₁])
          rw [this]; left; rw [← e20]
    have hsub : A ⊆ {u, t₁} := by
      intro c hc
      have := (PClosed.sc_iff M (fun a => a = u ∨ a = t₁) hP (hconn c hc u hu)).2 (Or.inl rfl)
      simpa using this
    have := Finset.card_le_card hsub
    have h2 : ({u, t₁} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  have hAeq : A = {u, t₁, t₂} := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ (by
      rw [hcard, Finset.card_insert_of_notMem, Finset.card_pair n21.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨n10.symm, n20.symm⟩)
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;> assumption
  have e3 : t₃ = u := by
    have h3 : t₃ ∈ ({u, t₁, t₂} : Finset V) := hAeq ▸ ht₃A
    simp only [Finset.mem_insert, Finset.mem_singleton] at h3
    rcases h3 with h | h | h
    · exact h
    · exfalso
      have : M.mate b₂ = M.mate b₀ :=
        bal_uniq (hbal t₁ ht₁A) h rfl (by rw [hmo b₂ hob₂, hmo b₀ hob₀])
      have := congrArg M.mate this
      rw [M.mate_mate, M.mate_mate] at this
      apply n20
      rw [← hb₂, this, hb₀]
    · exact absurd h n32
  obtain ⟨f, hfi, hfn⟩ := exists_three_fresh (V := V) M.atoms
  refine ⟨⟨![u, t₁, t₂], f, ![M.mate b₂, M.mate b₀, M.mate b₁], ![b₀, b₁, b₂], ?_, ?_, hfn, hfi, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, ?_⟩
  · intro j; fin_cases j
    · exact hAm u hu
    · exact hAm _ ht₁A
    · exact hAm _ ht₂A
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · intro j; fin_cases j
    · exact e3
    · rfl
    · rfl
  · intro j; fin_cases j
    · exact hb₀
    · exact hb₁
    · exact hb₂
  · intro j; fin_cases j
    · exact hmo b₂ hob₂
    · exact hmo b₀ hob₀
    · exact hmo b₁ hob₁
  · intro j; fin_cases j
    · exact hob₀
    · exact hob₁
    · exact hob₂
  · intro j; fin_cases j <;> rfl
  · intro c hc
    rw [hAeq] at hc
    simpa using hc

end WaveTurbulence.FinalCountG3
