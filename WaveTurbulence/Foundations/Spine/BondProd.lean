/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.FibreBij
/-! # The product over group bonds splits into chain codes and outer bonds (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {n : ℕ}
  {u v : Fin (n + 1 + 1) → V}

namespace LadderDarts.Ctx
variable (C : LadderDarts.Ctx M u v)

/-- The outgoing dart of the bond of a chain code. -/
def outDart (c : LadderDarts.Ctx.Code n) : D :=
  if M.out (C.dartOf c) = true then C.dartOf c else M.mate (C.dartOf c)

lemma out_outDart (c : LadderDarts.Ctx.Code n) : M.out (C.outDart c) = true := by
  unfold outDart
  by_cases h : M.out (C.dartOf c) = true
  · simp [h]
  · have : M.out (M.mate (C.dartOf c)) = true := by
      rw [M.out_mate]; simpa using h
    simp [h, this]

lemma isT_outDart (c : LadderDarts.Ctx.Code n) : C.IsT (C.outDart c) := by
  unfold outDart
  by_cases h : M.out (C.dartOf c) = true
  · simp only [h, if_true]; exact ⟨c, Or.inl rfl⟩
  · simp only [h, if_false]; exact ⟨c, Or.inr rfl⟩

lemma outDart_injective : Function.Injective (C.outDart (M := M)) := by
  intro c c' h
  unfold outDart at h
  by_cases h1 : M.out (C.dartOf c) = true <;> by_cases h2 : M.out (C.dartOf c') = true
  · simp only [h1, h2, if_true] at h; exact C.dartOf_injective h
  · simp only [h1, h2, if_true, if_false] at h; exact absurd h (C.dartOf_ne_mate _ _)
  · simp only [h1, h2, if_true, if_false] at h; exact absurd h.symm (C.dartOf_ne_mate _ _)
  · simp only [h1, h2, if_false] at h
    exact C.dartOf_injective (by simpa [M.mate_mate] using congrArg M.mate h)

lemma exists_outDart (x : D) (hx : M.out x = true) (hT : C.IsT x) : ∃ c, C.outDart c = x := by
  obtain ⟨c, hc | hc⟩ := hT
  · exact ⟨c, by unfold outDart; simp [hc, hx]⟩
  · refine ⟨c, ?_⟩
    unfold outDart
    have : ¬ M.out (C.dartOf c) = true := by
      intro h
      have h2 : M.out (M.mate (C.dartOf c)) = true := by rw [hc]; exact hx
      rw [M.out_mate] at h2; simp [h] at h2
    simp [this, hc]

open scoped Classical in
/-- The product over the chain bonds. -/
lemma prod_bonds_T (f : D → ℂ) :
    ∏ x ∈ M.bonds.filter (fun x => M.InGroup (Molecule.ladderAtoms u v) x ∧ C.IsT x), f x =
      ∏ c : LadderDarts.Ctx.Code n, f (C.outDart c) := by
  symm
  refine Finset.prod_bij (fun c _ => C.outDart c) ?_ ?_ ?_ ?_
  · intro c _
    simp only [Finset.mem_filter, Molecule.bonds, Finset.mem_univ, true_and]
    exact ⟨C.out_outDart c, C.isT_inGroup _ (C.isT_outDart c), C.isT_outDart c⟩
  · intro c _ c' _ h; exact C.outDart_injective h
  · intro x hx
    simp only [Finset.mem_filter, Molecule.bonds, Finset.mem_univ, true_and] at hx
    obtain ⟨c, hc⟩ := C.exists_outDart x hx.1 hx.2.2
    exact ⟨c, Finset.mem_univ _, hc⟩
  · intro c _; rfl

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay
