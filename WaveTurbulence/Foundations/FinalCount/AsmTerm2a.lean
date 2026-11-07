/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm1
public import WaveTurbulence.Foundations.FinalCount.G3Op5b
public import WaveTurbulence.Foundations.FinalCount.G3InvDel
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 2a: Operation 5 with the isolated-atom refinement.**
G3's `Good.erase_set` proves `2R' + 4|E| + B = 2R + tch` with `B = Σ_iso base` and then drops `B ≥ 0`.  The refinement keeps `B ≥ 2 · #iso`
(the dropped atoms are non-ghost, base `≥ 2`), derived here from the two `phi` invariants (no edit of G3). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

/-- The atoms other than `E` that lose all their bonds when `E` is erased (they are dropped by Operation 5). -/
noncomputable def isoAtoms (s : St.{u} V D₀) (E : Finset V) : Finset V :=
  (s.M.atoms \ E).filter (fun a => ¬ keepS s E a)

theorem Good.erase_set_iso {s : St.{u} V D₀} {R : ℕ} {E : Finset V} (hg : Good R s)
    (hE : ∀ v ∈ E, v ∈ s.M.atoms ∧ s.cls v = .eps) :
    ∃ R' : ℕ, 2 * (R' : ℤ) + 4 * (E.card : ℤ) + 2 * ((isoAtoms s E).card : ℤ) ≤ 2 * (R : ℤ) + (tch s.M E : ℤ) ∧
      Good R' (s.eraseSetSt E) := by
  obtain ⟨R', -, hg'⟩ := hg.erase_set hE
  refine ⟨R', ?_, hg'⟩
  have hEsub : E ⊆ s.M.atoms := fun v hv => (hE v hv).1
  have hF1 : ∑ a ∈ s.M.atoms \ E, (s.cls a).base = Fintype.card s.D + 2 * (R : ℤ) - 4 * (E.card : ℤ) := by
    have h1 := Finset.sum_sdiff hEsub (f := fun a => (s.cls a).base)
    have h3 := hg.1.phi
    have h6 : ∑ a ∈ E, (s.cls a).base = 4 * (E.card : ℤ) := by
      rw [Finset.sum_congr rfl (fun a ha => by rw [(hE a ha).2]; rfl : ∀ a ∈ E, (s.cls a).base = 4)]
      simp [mul_comm]
    linarith
  have hF2 : (Fintype.card (EDartS s.M E) : ℤ) + (tch s.M E : ℤ) = Fintype.card s.D := by
    exact_mod_cast card_edartS s.M E
  have hF3 : (Fintype.card (s.eraseSetSt E).D : ℤ) = Fintype.card (EDartS s.M E) := by
    have h := card_pdart (eraseSet s.M E) (keepS s E)
    have h0 : ∑ a ∈ (eraseSet s.M E).atoms.filter (fun a => ¬ keepS s E a), (eraseSet s.M E).deg a = 0 := by
      refine Finset.sum_eq_zero fun a ha => ?_
      have := (Finset.mem_filter.1 ha).2
      unfold keepS at this; omega
    rw [h0] at h
    show (Fintype.card (PDart (eraseSet s.M E) (keepS s E)) : ℤ) = _
    exact_mod_cast (by omega : Fintype.card (PDart (eraseSet s.M E) (keepS s E)) = Fintype.card (EDartS s.M E))
  have hphi := hg'.1.phi
  have hat : (s.eraseSetSt E).M.atoms = (s.M.atoms \ E).filter (keepS s E) := rfl
  have hsplit := Finset.sum_filter_add_sum_filter_not (s.M.atoms \ E) (keepS s E) (fun a => (s.cls a).base)
  have hcls : ∀ a, ((s.eraseSetSt E).cls a) = s.cls a := fun a => rfl
  have hk : ∑ a ∈ (s.eraseSetSt E).M.atoms, ((s.eraseSetSt E).cls a).base =
      ∑ a ∈ (s.M.atoms \ E).filter (keepS s E), (s.cls a).base := by
    rw [hat]; simp only [hcls]
  have hiso : 2 * ((isoAtoms s E).card : ℤ) ≤ ∑ a ∈ (s.M.atoms \ E).filter (fun a => ¬ keepS s E a), (s.cls a).base := by
    have : ∀ a ∈ (s.M.atoms \ E).filter (fun a => ¬ keepS s E a), (2 : ℤ) ≤ (s.cls a).base := by
      intro a ha
      have haM := (Finset.mem_sdiff.1 (Finset.mem_filter.1 ha).1).1
      have hne := hg.2 a haM
      rcases hc : s.cls a with _ | _ | _ | _
      · simp [Cls.base]
      · simp [Cls.base]
      · simp [Cls.base]
      · exact absurd hc hne
    calc 2 * ((isoAtoms s E).card : ℤ) = ∑ a ∈ isoAtoms s E, (2 : ℤ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum this
  unfold isoAtoms at hiso ⊢
  linarith

end WaveTurbulence.FinalCountAsm
