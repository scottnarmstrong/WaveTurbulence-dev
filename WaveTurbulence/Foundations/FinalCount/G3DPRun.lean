/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3DPInv3
/-! **FINALCOUNT-G3: `HRun.dp`**, the dart-set invariant along a run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀}

theorem rtg_dp {step : HSt V D₀ → HSt V D₀ → Prop}
    (hstep : ∀ h h', step h h' → DPInv h → AncRel M₀ h.s h.anc → DPInv h' ∧ AncRel M₀ h'.s h'.anc)
    {x y : HSt V D₀} (h : Relation.ReflTransGen step x y) :
    DPInv x → AncRel M₀ x.s x.anc → DPInv y ∧ AncRel M₀ y.s y.anc := by
  induction h with
  | refl => exact fun a b => ⟨a, b⟩
  | tail _ hs ih => exact fun a b => (fun ⟨i, r⟩ => hstep _ _ hs i r) (ih a b)

theorem HRun.dp {hf : HSt V D₀} (hr : HRun L γ η w κ (HSt.init M₀) hf) : DPInv hf := by
  obtain ⟨h₁, h₂, h₃, a1, _, a2, _, a3, _, a4, _⟩ := hr
  have r0 := AncRel.init M₀
  have i0 : DPInv (HSt.init M₀) := DPInv.init M₀
  have s1 := rtg_dp (fun h h' hs i r => ⟨hs.dp i r.inj, hs.anc r⟩) a1 i0 r0
  have s2 := rtg_dp (fun h h' hs i r => ⟨hs.dp i r.inj, hs.anc r⟩) a2 s1.1 s1.2
  have s3 := rtg_dp (fun h h' hs i r => ⟨hs.dp i r.inj, hs.anc r⟩) a3 s2.1 s2.2
  exact (rtg_dp (fun h h' hs i r => ⟨hs.dp i r.inj, hs.anc r⟩) a4 s3.1 s3.2).1

end WaveTurbulence.FinalCountG3
