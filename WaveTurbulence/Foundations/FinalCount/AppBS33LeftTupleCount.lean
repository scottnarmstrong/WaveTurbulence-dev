/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33LeftCopiedLabel
import Mathlib.Tactic

/-! # Internal pair count after fixing the left component in 3S3-3G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_left_fixed_tuple_bound (d : ℕ) (hd : 2 ≤ d) (δ γ : ℝ)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.s33.pattern)
      (hg : AppbS33SplitGeometry M r) (p : AppbCountParameters M d) (w : Mom d)
      (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbS33LabelConditions M r L γ (min γ (1-γ)) w κ) →
      ∀ T : Finset (D → (Fin d → ℤ)), (∀ κ ∈ T,κ ∈ p.decorations L γ δ w Adm) →
      ∀ ζ : AppbSideDart (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r) → (Fin d → ℤ),
      (((T.filter (fun κ => appbS33LeftLabels r κ = ζ)).image r.localLabels).card : ℝ) ≤
        L^((d : ℝ)-γ-31*min γ (1-γ)/48) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_triple_fixed_tuples_good_bound (V := V) (D := D) d hd δ γ hδ hγ
  refine ⟨L₀,?_⟩
  intro L hL hLp M r hg p w Adm htest T hT ζ
  let Q := (T.filter (fun κ => appbS33LeftLabels r κ = ζ)).image r.localLabels
  let t := appbS33ReinsertFrame r
  have ht := appb_s33_reinsert_frame_indices r
  have hi := (appbS33Frame r).reindex_project_injOn (Equiv.swap 1 2) _
    (appb_s33_topology_projection_injective r (appb_s33_splitTopology_of_geometry hg) p hLp γ δ w Adm)
  apply hL₀ L hL hLp M _ r (r.vertex 1)
    (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.s33.pattern.removed by decide)) t p w Adm
    (ζ (appbS33LeftNewDart r hg)) Q
  · intro q hq
    obtain ⟨κ,hκ,rfl⟩ := Finset.mem_image.mp hq
    exact (r.mem_localChoices p hLp γ δ w Adm _).mpr ⟨κ,hT κ (mem_filter.mp hκ).1,rfl⟩
  · intro q hq
    obtain ⟨κ,hκ,rfl⟩ := Finset.mem_image.mp hq
    have he := congrFun (mem_filter.mp hκ).2 (appbS33LeftNewDart r hg)
    rw [appb_s33_left_copied_label] at he
    change r.localLabels κ ((appbS33ReinsertFrame r).index 2) = _
    rw [ht.2.2]
    exact he
  · exact hi
  · intro hsign κ hκ
    have hs : AppbOppositeFrom M (r.vertex 1) (r.vertex 1)
        (r.edge ⟨0,by decide⟩).val (r.edge ⟨2,by decide⟩).val := by
      apply (appb_incidence_sign_opposite_from M (r.vertex 1) (r.vertex 1) _ _).mp
      simpa only [t,ht.1,ht.2.1] using hsign
    have hh := (htest κ hκ.2.2).2 hs
    simpa only [t,ht.1,ht.2.1] using hh

end WaveTurbulence.Mole
