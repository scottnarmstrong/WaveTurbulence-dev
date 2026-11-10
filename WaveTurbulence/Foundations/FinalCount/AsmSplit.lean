/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmCountAlg
public import WaveTurbulence.Foundations.FinalCount.G3Ghost
public import WaveTurbulence.Foundations.FinalCount.RestrictRank
/-! **FINALCOUNT-ASSEMBLY, A3: splitting off a union of components.**

For a closed predicate `P` of a molecule `N`: `𝔈(N) ≤ 𝔈(N|P) · 𝔈(N|¬P)` for the classes `projAdm` (projections of `Adm` to the
darts of `P`, `¬P`), and the same for `𝔄` (rank and ladder products are additive). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The projection of a class of labellings to the darts at the atoms satisfying `P`. -/
def projAdm (N : Molecule V D) (P : V → Prop) (Adm : (D → (Fin d → ℤ)) → Prop) :
    (PDart N P → (Fin d → ℤ)) → Prop :=
  fun κ' => ∃ κ, Adm κ ∧ κ' = fun x => κ x.1

variable (N : Molecule V D) (P : V → Prop) [DecidablePred P] (h : PClosed N P)

theorem projAdm_mem {Adm : (D → (Fin d → ℤ)) → Prop} {κ : D → (Fin d → ℤ)} (hκ : Adm κ) :
    projAdm N P Adm (fun x => κ x.1) := ⟨κ, hκ, rfl⟩

include h in
theorem decSet_restrict (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) {κ : D → (Fin d → ℤ)} (hκ : κ ∈ decSet N L γ δ w Adm c β k0) :
    (fun x : PDart N P => κ x.1) ∈ decSet (restrictP N P h) L γ δ w (projAdm N P Adm) c β (fun x => k0 x.1) := by
  obtain ⟨⟨hmate, hsum⟩, ⟨hG, hk⟩, hA⟩ := hκ
  refine ⟨⟨fun x => hmate x.1, fun v hv => ?_⟩, ⟨fun v hv => ?_, fun x => hk x.1⟩, projAdm_mem N P hA⟩
  · have hv' := Finset.mem_filter.1 hv
    have := hsum v hv'.1
    show ∑ x ∈ (restrictP N P h).dartsAt v, N.dartSign x.1 • Molecule.kvec L w κ x.1 = c v
    rw [sum_dartsAt_restrict N P h hv'.2 (fun x => N.dartSign x • Molecule.kvec L w κ x)]
    exact this
  · have hv' := Finset.mem_filter.1 hv
    have := hG v hv'.1
    unfold Molecule.Gamma at this
    show |(restrictP N P h).Gamma L w (fun x => κ x.1) v - β v| ≤ _
    unfold Molecule.Gamma
    rw [show ∑ x ∈ (restrictP N P h).dartsAt v, (restrictP N P h).dartSign x *
        ‖Molecule.kvec L w (fun x : PDart N P => κ x.1) x‖ ^ 2 =
        ∑ x ∈ (restrictP N P h).dartsAt v, N.dartSign x.1 * ‖Molecule.kvec L w κ x.1‖ ^ 2 from rfl,
      sum_dartsAt_restrict N P h hv'.2 (fun x => N.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2)]
    exact this

include h in
theorem paramOK_restrict (c : V → Mom d) (k0 : D → Mom d) (hp : ParamOK N c k0) :
    ParamOK (restrictP N P h) c (fun x => k0 x.1) :=
  ⟨fun v hv hv4 => hp.1 v (Finset.mem_filter.1 hv).1 (by rw [← restrictP_deg N P h (Finset.mem_filter.1 hv).2]; exact hv4),
    fun x => hp.2 x.1⟩

end WaveTurbulence.FinalCountAsm
