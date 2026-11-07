/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestStepExists
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33ReinsertReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33ReinsertReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ReinsertCleanupReductions
public import WaveTurbulence.Foundations.FinalCount.Algorithm.RuleThreePrimaryReduction
import Mathlib.Tactic

/-! # The scheduled step supply (carrier-uniform thresholds) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Set
universe u v

theorem exists_forest_step (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1-γ)) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∀ C1 ≥ C₀,∃ L₀ : ℝ,
    ∀ (V : Type v) [DecidableEq V] (w : Mom d) (B : ℕ),∀ L ≥ L₀,
    (B : ℝ) ≤ 2*(1+Real.log L)^m →
    ∀ F : CountingForest.{u,v} V d L γ η w c B,ForestOk m F → F.problems ≠ [] →
    Nonempty (ForestStep m F
      (ENNReal.ofReal (Real.log L^8)) (ENNReal.ofReal (L^(-η/2)))
      (ENNReal.ofReal (L^(-5*min γ (1-γ)/8))) δ C1) := by
  obtain ⟨C₁,hC₁,h₁⟩ := exists_dispatch.{u,v} d hd γ η hγ hη hηγ c hc
  obtain ⟨C₂,hC₂,h₂⟩ := exists_rule_three_primary_reduction.{u,v} d hd γ η hγ hη hηγ c hc
  obtain ⟨C₃,L₃,hC₃,h₃⟩ := exists_s33_cleanup_reduction.{u,v} d hd γ hγ
  obtain ⟨C₄,L₄,hC₄,h₄⟩ := exists_d33_cleanup_reduction.{u,v} d hd γ hγ
  refine ⟨max C₁ (max C₂ (max C₃ C₄)),hC₁.trans (le_max_left _ _),?_⟩
  intro m δ hδ C1 hC1
  obtain ⟨Lg,hLgexp,hLg⟩ := forest_half_gap_uniform.{u,v} γ η hη m
  obtain ⟨hC1₁,hC1'⟩ := max_le_iff.mp hC1
  obtain ⟨hC1₂,hC1''⟩ := max_le_iff.mp hC1'
  obtain ⟨hC1₃,hC1₄⟩ := max_le_iff.mp hC1''
  obtain ⟨L₁,hL₁⟩ := h₁ m δ hδ C1 hC1₁
  obtain ⟨L₂,hL₂⟩ := h₂ m δ hδ
  obtain ⟨L₅,hL₅⟩ := exists_s33_reinsert_reduction.{u,v} d (by omega) γ hγ m δ hδ
  obtain ⟨L₆,hL₆⟩ := exists_d33_reinsert_reduction.{u,v} d (by omega) γ hγ δ hδ
  refine ⟨max Lg (max L₁ (max L₂ (max L₃ (max L₄ (max L₅ L₆))))),?_⟩
  intro V _ w B L hL hB F hF hne
  obtain ⟨hLg',hL'⟩ := max_le_iff.mp hL
  obtain ⟨hL₁',hL''⟩ := max_le_iff.mp hL'
  obtain ⟨hL₂',hL'''⟩ := max_le_iff.mp hL''
  obtain ⟨hL₃',hL4⟩ := max_le_iff.mp hL'''
  obtain ⟨hL₄',hL56⟩ := max_le_iff.mp hL4
  obtain ⟨hL₅',hL₆'⟩ := max_le_iff.mp hL56
  have hexp : Real.exp 1 ≤ L := hLgexp.trans hLg'
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hexp
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hexp
  have hgap : L^(-γ+η)/2 ≤ F.gap := hLg L hLg' V d w c B hB F
  have hN : 1 ≤ ENNReal.ofReal (Real.log L^8) := ENNReal.one_le_ofReal.mpr (one_le_pow₀ hlog)
  have hHalf : ∀ p ∈ F.problems,∀ κ,p.admissible κ →
      AppbLargeGap p.state.graph L w κ (L^(-γ+η)/2) :=
    fun p _ κ hκ => (p.largeGap κ hκ).mono hgap
  have supply : ∀ p ∈ F.problems,
      (∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b) →
      (∀ r : AppbRealization p.state.graph AppbPatternKind.s33.pattern,
        AppbS33SplitGeometry p.state.graph r →
        ¬(p.state.graph.deg (r.vertex 3) = 4 ∧ p.state.graph.deg (r.vertex 5) = 4) →
        Nonempty (S33ReinsertReduction p.state.graph r L γ δ C1 F.gap w
          (fun κ => p.admissible κ ∧ AppbS33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ)
          p.scales)) ∧
      (∀ r : AppbRealization p.state.graph AppbPatternKind.s33.pattern,
        AppbS33SplitGeometry p.state.graph r →
        ¬(p.state.graph.deg (r.vertex 3) = 4 ∧ p.state.graph.deg (r.vertex 5) = 4) →
        ∀ A : (Degen.RetainedDart p.state.graph r.removedAtoms ⊕ Bool → (Fin d → ℤ)) → Prop,
        (∀ ζ,A ζ → AppbLargeGap (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L w ζ (F.gap-L^(-γ))) →
        AppbNoTripleBonds (r.directedPostWithBond 3 5 ⟨1,by decide⟩) ∨
        Nonempty (TBCleanupReduction (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L γ δ C1
          (F.gap-L^(-γ)) w A
          (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 5) p.scales))) ∧
      (∀ r : AppbRealization p.state.graph AppbPatternKind.d33.pattern,
        (∀ e : p.state.Dart,¬Degen.IsBridge p.state.graph e) → AppbD33BoundaryOpposite p.state.graph r →
        AppbD33ResidualDefect p.state.graph r →
        Nonempty (D33ReinsertReduction p.state.graph r L γ δ C1 F.gap w
          (fun κ => p.admissible κ ∧ AppbD33LabelConditions p.state.graph r L γ (min γ (1-γ)) w κ)
          p.scales)) ∧
      (∀ r : AppbRealization p.state.graph AppbPatternKind.d33.pattern,
        (∀ e : p.state.Dart,¬Degen.IsBridge p.state.graph e) → AppbD33BoundaryOpposite p.state.graph r →
        ¬D33Continues r → ¬HasD33ResidualCommon r → AppbD33ResidualDefect p.state.graph r →
        ∀ A : (Degen.RetainedDart p.state.graph r.removedAtoms ⊕ Bool → (Fin d → ℤ)) → Prop,
        (∀ ζ,A ζ → AppbLargeGap (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L w ζ (F.gap-L^(-γ))) →
        AppbNoTripleBonds (r.directedPostWithBond 3 4 ⟨2,by decide⟩) ∨
        Nonempty (TBCleanupReduction (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L γ δ C1
          (F.gap-L^(-γ)) w A
          (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 4) p.scales))) := by
    intro p hp hconnp
    have hpOk := hF.1 p hp
    refine ⟨?_,?_,?_,?_⟩
    · intro r hg hdd
      exact hL₅ V p.state.Dart C1 (by linarith only [hC1₁,hC₁]) L hL₅' p.state.graph r hpOk.2 p.molecule
        p.noLoops hconnp hg hdd F.gap w _ p.scales p.scales_nonneg (fun κ hκ => p.largeGap κ hκ.1)
        (fun κ hκ => hκ.2)
    · intro r hg hdd A hA
      exact h₃ V p.state.Dart C1 hC1₃ L hL₃' δ hδ p.state.graph p.molecule p.noLoops hpOk.1 r hg hdd
        _ w A (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 5) p.scales) hA
    · intro r hb ho hdef
      exact hL₆ V p.state.Dart C1 (by linarith only [hC1₁,hC₁]) L hL₆' p.state.graph r p.molecule p.noLoops
        hconnp ho hb hdef F.gap w _ p.scales p.scales_nonneg (fun κ hκ => p.largeGap κ hκ.1)
        (fun κ hκ => hκ.2)
    · intro r hb ho hc' ht hdef A hA
      exact h₄ V p.state.Dart C1 hC1₄ L hL₄' δ hδ p.state.graph p.molecule p.noLoops hpOk.1 r ho hconnp hb
        hc' ht hdef _ w A (appbReinsertScales p.state.graph r.removedAtoms (r.vertex 3) (r.vertex 4) p.scales) hA
  have hC1pos : 0 < C1 := by linarith only [hC1₁,hC₁]
  by_cases hlad : ∃ (p : Problem.{u,v} V d L w c F.gap) (hp : p ∈ F.problems)
      (head : LadderHead p.state),F.mode = .ladder p hp head
  · obtain ⟨p,hp,head,hmode⟩ := hlad
    obtain ⟨pre,tail,hlist⟩ := List.append_of_mem hp
    have hconnall : ∀ q ∈ F.problems,∀ a ∈ q.state.graph.atoms,∀ b ∈ q.state.graph.atoms,
        q.state.graph.SameComponent a b := by
      have h := hF.2
      rw [hmode] at h
      exact h
    have hconnF : ∀ s ∈ F.graphs,∀ a ∈ s.graph.atoms,∀ b ∈ s.graph.atoms,s.graph.SameComponent a b := by
      intro s hs
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
      exact hconnall q hq
    obtain ⟨hRI2,hCL2,hRI3,hCL3⟩ := supply p hp head.connected
    have rt := hL₂ V p.state.Dart C1 hC1₂ L hL₂' p.state.graph head.figure p.molecule p.noLoops
      (hF.1 p hp).1 head.connected head.noBridges (hF.1 p hp).2 w p.admissible p.scales
      p.validLinkScales p.scales_nonneg p.mateLabels (hHalf p hp)
    exact exists_rule_three_step m hF hLp pre tail p hlist hp δ C1 head.figure head.connected
      head.noBridges hconnF (fun h3 h4 => forestSlack_ladder F p hp head hmode h3 h4) rt
      (hRI3 head.figure) (hCL3 head.figure) _ _ _ hN le_rfl
  · have hnl : ∀ p hp head,F.mode ≠ ForestScanMode.ladder p hp head :=
      fun p hp head h => hlad ⟨p,hp,head,h⟩
    have hSl := forestSlack_nonladder F hnl
    by_cases hdisc : ∃ p ∈ F.problems,¬(∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,
        p.state.graph.SameComponent a b)
    · obtain ⟨p,hp,hnc⟩ := hdisc
      obtain ⟨pre,tail,hlist⟩ := List.append_of_mem hp
      obtain ⟨S,hS,hSn,hSc,-,-,-⟩ := p.exists_component_split hnc γ δ C1 hLp hδ.1 hC1pos
      exact ⟨forestSplitStep m hF hSl hLp pre tail p hlist S hS hSn hSc _ _ _ δ C1 hδ.1 hC1pos⟩
    · push_neg at hdisc
      by_cases hterm : ∃ p ∈ F.problems,Terminal p.state
      · obtain ⟨p,hp,ht⟩ := hterm
        obtain ⟨pre,tail,hlist⟩ := List.append_of_mem hp
        exact ⟨forestDiscardStep m hF hSl pre tail p hlist ht _ _ _ δ C1⟩
      · push_neg at hterm
        obtain ⟨p,tail,hlist⟩ : ∃ (p : Problem.{u,v} V d L w c F.gap) (tail : List (Problem.{u,v} V d L w c F.gap)),F.problems = p :: tail := by
          cases h : F.problems with
          | nil => exact absurd h hne
          | cons p t => exact ⟨p,t,rfl⟩
        have hp : p ∈ F.problems := by rw [hlist]; exact List.mem_cons_self
        have hconnp := hdisc p hp
        have hconnF : ∀ s ∈ F.graphs,∀ a ∈ s.graph.atoms,∀ b ∈ s.graph.atoms,
            s.graph.SameComponent a b := by
          intro s hs
          obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
          exact hdisc q hq
        have hbne : p.state.graph.bonds.Nonempty := Finset.nonempty_iff_ne_empty.mpr (hterm p hp)
        obtain ⟨hRI2,hCL2,hRI3,hCL3⟩ := supply p hp hconnp
        have dsp := hL₁ V p.state.Dart L hL₁' p.state.graph p.molecule p.noLoops (hF.1 p hp).1 hconnp hbne
          (hF.1 p hp).2 w p.admissible p.scales p.validLinkScales p.scales_nonneg p.mateLabels (hHalf p hp)
        exact exists_dispatch_step m hF hLp hSl [] tail p (by simpa using hlist) hp δ C1 hconnp hconnF dsp
          hRI2 hCL2 hRI3 hCL3 _ _ _ hN le_rfl le_rfl le_rfl

end WaveTurbulence.Mole.AppbAlgorithm
