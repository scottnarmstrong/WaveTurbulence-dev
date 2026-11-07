/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.AdmissibilityPartition
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD33GlobalNormalValid
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD33GlobalBadLabels
import Mathlib.Tactic

/-! # Actual count partition for a normal-or-good double-pair decision

Constants precede both finite carrier types. Both post predicates retain
the inherited label test, its preceding admissibility constraints, and the
actual conditioned local labels chosen by the operation estimates.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

theorem d33_label_branches_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ (M : Molecule V D)
      (r : AppbRealization M AppbPatternKind.d33.pattern),
    M.IsMolecule → (∀ e : D,¬Degen.IsBridge M e) → AppbD33BoundaryOpposite M r →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (scales : Finset V → ℝ),
    AppbValidLinkScales M L w Adm c scales → (∀ S,0 ≤ scales S) →
    (∀ κ,Adm κ → ∀ x,κ (M.mate x) = κ x) →
    let A := fun κ => Adm κ ∧ AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ
    let B := fun κ => Adm κ ∧ ¬AppbD33LabelConditions M r L γ (min γ (1-γ)) w κ
    ∃ qN qG : Fin AppbPatternKind.d33.pattern.edges.length → (Fin d → ℤ),
      appbLinkCountA M L γ δ C1 w Adm scales ≤
        appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility A qN) scales+
        ENNReal.ofReal (L^(-5*min γ (1-γ)/8))*
          appbLinkCountA r.post L γ δ C1 w (r.conditionedPostAdmissibility B qG) scales := by
  obtain ⟨C₀,hC₀,hNormal⟩ := uniform_d33_global_normal_of_valid_scales_bound d hd γ hγ c hc
  refine ⟨C₀,hC₀,?_⟩
  intro δ hδ
  obtain ⟨LN,hLN⟩ := hNormal δ hδ
  obtain ⟨LG,hLG⟩ := uniform_d33_global_bad_labels_good_bound d hd γ hγ δ hδ
  refine ⟨max LN LG,?_⟩
  intro V D instV instF instD C1 hC1 L hL M r hM hb ho w Adm scales hv hs hm
  let Test := AppbD33LabelConditions M r L γ (min γ (1-γ)) w
  let A := fun κ => Adm κ ∧ Test κ
  let B := fun κ => Adm κ ∧ ¬Test κ
  obtain ⟨qN,hN⟩ := hLN V D C1 hC1 L ((le_max_left LN LG).trans hL)
    M r hM hb ho w A scales (hv.mono (fun _ h => h.1)) (fun κ h => hm κ h.1)
  obtain ⟨qG,hG⟩ := hLG V D C1 (hC₀.trans hC1) L ((le_max_right LN LG).trans hL)
    M r hM hb ho w B scales hs (fun _ h => h.2)
  refine ⟨qN,qG,?_⟩
  have hp := linkCountA_le_test_partition M L γ δ C1 w Adm Test scales
  change appbLinkCountA M L γ δ C1 w A scales ≤ _ at hN
  change appbLinkCountA M L γ δ C1 w B scales ≤ _ at hG
  rw [one_mul] at hN
  exact hp.trans (add_le_add hN hG)

end WaveTurbulence.Mole.AppbAlgorithm
