/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue4
import Mathlib.Tactic
/-! The centers `hX` of the paired atoms and their measurability / `Y`-dependence. -/
@[expose] public section
open WaveTurbulence.Induct
open Finset MeasureTheory
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}
variable {D : SplicedKernelData G d} {L γ δ : ℝ} {base : Mom d} {roots : Fin w → (Fin d → ℤ)}
  {hp : G.IsPlain} {π0 : PF G} {εS : LQ G → ℝ}

/-- The center of a paired `X` atom as a function of the frequencies. -/
noncomputable def CD.hXf (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (θ : Jr (cd.Kn isSmall) → Bool) (x : GBranch G.tree) (α : GBranch G.tree → ℝ) : ℝ :=
  if h : ∃ s, xθ (cd.ua isSmall) (cd.va isSmall) θ s = x then
    (∑ l, cd.cc h.choose.1 (cd.enum isSmall h.choose.1 h.choose.2) l *
        (α (atomAt π0 h.choose.1 true (cd.r' h.choose.1 l)) + α (atomAt π0 h.choose.1 false (cd.r' h.choose.1 l))) +
      cd.dd h.choose.1 (cd.enum isSmall h.choose.1 h.choose.2)) - α (yθ (cd.ua isSmall) (cd.va isSmall) θ h.choose)
  else 0

theorem CD.hXf_measurable (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (θ : Jr (cd.Kn isSmall) → Bool) (x : GBranch G.tree) : Measurable (cd.hXf isSmall θ x) := by
  by_cases h : ∃ s, xθ (cd.ua isSmall) (cd.va isSmall) θ s = x
  · have : cd.hXf isSmall θ x = fun α =>
        (∑ l, cd.cc h.choose.1 (cd.enum isSmall h.choose.1 h.choose.2) l *
          (α (atomAt π0 h.choose.1 true (cd.r' h.choose.1 l)) +
            α (atomAt π0 h.choose.1 false (cd.r' h.choose.1 l))) +
          cd.dd h.choose.1 (cd.enum isSmall h.choose.1 h.choose.2)) -
        α (yθ (cd.ua isSmall) (cd.va isSmall) θ h.choose) := by
      funext α; unfold CD.hXf; rw [dif_pos h]
    rw [this]
    refine Measurable.sub (Measurable.add (Finset.measurable_sum _ (fun l _ => ?_)) measurable_const)
      (measurable_pi_apply _)
    exact measurable_const.mul ((measurable_pi_apply _).add (measurable_pi_apply _))
  · have : cd.hXf isSmall θ x = fun _ => 0 := by
      funext α; unfold CD.hXf; rw [dif_neg h]
    rw [this]; exact measurable_const

theorem CD.sel_not_X (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (θ : Jr (cd.Kn isSmall) → Bool) (S : LQ G) (l : Fin (cd.q S)) (b : Bool) :
    atomAt π0 S b (cd.r' S l) ∉ Finset.univ.image (xθ (cd.ua isSmall) (cd.va isSmall) θ) := by
  intro hmem
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hmem
  have hrI := cd.hrI S l
  rw [Finset.mem_Icc] at hrI
  have hxs : xθ (cd.ua isSmall) (cd.va isSmall) θ s = atomAt π0 s.1 (θ s) (cd.enum isSmall s.1 s.2) := by
    unfold xθ CD.ua CD.va
    cases θ s <;> simp
  rw [hxs] at hs
  obtain ⟨h1, _, h3⟩ := atomAt_inj π0 s.1 S (θ s) b (cd.enum_le isSmall s.1 s.2) (by omega) hs
  subst h1
  have := (cd.JS_sub isSmall s.1 (cd.enum_mem isSmall s.1 s.2)).2.1
  apply this
  rw [h3]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ l)

theorem CD.hXf_dep (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (hinj : Function.Injective (Sum.elim (cd.ua isSmall) (cd.va isSmall)))
    (θ : Jr (cd.Kn isSmall) → Bool) (x : GBranch G.tree) (β β' : GBranch G.tree → ℝ)
    (h : ∀ b, b ∉ Finset.univ.image (xθ (cd.ua isSmall) (cd.va isSmall) θ) → β b = β' b) :
    cd.hXf isSmall θ x β = cd.hXf isSmall θ x β' := by
  unfold CD.hXf
  by_cases hx : ∃ s, xθ (cd.ua isSmall) (cd.va isSmall) θ s = x
  · rw [dif_pos hx, dif_pos hx]
    have h1 : ∀ l b, β (atomAt π0 hx.choose.1 b (cd.r' hx.choose.1 l)) = β' (atomAt π0 hx.choose.1 b (cd.r' hx.choose.1 l)) :=
      fun l b => h _ (cd.sel_not_X isSmall θ _ l b)
    have h2 : β (yθ (cd.ua isSmall) (cd.va isSmall) θ hx.choose) = β' (yθ (cd.ua isSmall) (cd.va isSmall) θ hx.choose) := by
      refine h _ (fun hmem => ?_)
      obtain ⟨s', _, hs'⟩ := Finset.mem_image.mp hmem
      exact yθ_ne_xθ (cd.ua isSmall) (cd.va isSmall) hinj θ _ _ hs'.symm
    simp only [h1, h2]
  · rw [dif_neg hx, dif_neg hx]

end WaveTurbulence.Ladder
