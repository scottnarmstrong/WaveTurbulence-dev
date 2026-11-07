/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SplitQuadNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.GoodOperationScalar
public import WaveTurbulence.Foundations.FinalCount.MoleProp.InducedErasureCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.CutSideClosure
import Mathlib.Tactic

/-! # Neutral preliminary beta-removal and actual side selection

The logarithmic-size condition is internal to the final proof's size
split. This branch helper takes the actual circuit change as graph data.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem countAFree_le_beta_side_of_rank_change (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) → (M.atoms.card : ℝ) ≤ Real.log L →
    ∀ v ∈ M.atoms, ∀ x y r s : D, x ≠ y → x ≠ r → y ≠ r → s ∉ ({x,y,r} : Finset D) →
      M.dartsAt v = {x,y,r,s} →
      M.out x = false → M.out y = true → M.out r = false → M.out s = true →
    ∀ U : Finset V, U ⊆ M.atoms → Degen.boundaryDarts M U = {M.mate x,M.mate y} →
      (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank-2 →
    ∀ S : Finset V, S ⊆ M.atoms \ {v} →
      (∀ z ∈ Degen.boundaryDarts M S, M.atom (M.mate z) ∈ ({v} : Finset V)) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Mole.induced M S) L γ δ C1 (0 : Mom d)
          (inducedFreeAdmissibility M S Adm) P := by
  obtain ⟨C,hC,hDiscard⟩ := countAFree_le_induced_closed d hd γ hγ η hη hηmax
  obtain ⟨Rs,hRs⟩ := eventually_log_size_power_gain (show (0 : ℝ) ≤ 1 by norm_num) hη 2
  refine ⟨C,hC,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨Rq,hRq⟩ := split_quad_normalized_bound d hd γ hγ η hη hηmax δ hδ
  obtain ⟨Rd,hRd⟩ := hDiscard C1 hC1 δ hδ
  refine ⟨max (max (max Rq Rd) Rs) 1,?_⟩
  intro L hL hlog V D _ _ _ M hM hsimp hn v hv x y r s hxy hxr hyr hs hstar hxo hyo hro hso U hU hcut hχ S hS hboundary Adm P hAdm
  have hLbase : max (max Rq Rd) Rs ≤ L := (le_max_left _ _).trans hL
  have hLq : Rq ≤ L := (le_max_left Rq Rd).trans ((le_max_left _ _).trans hLbase)
  have hLd : Rd ≤ L := (le_max_right Rq Rd).trans ((le_max_left _ _).trans hLbase)
  have hLs : Rs ≤ L := (le_max_right _ _).trans hLbase
  have hLpos : 0 < L := zero_lt_one.trans_le ((le_max_right _ _).trans hL)
  have hC1' : 1 ≤ C1 := hC.trans hC1
  have hq := hRq L hLq hlog C1 hC1' M hsimp v hv x y r s hxy hxr hyr hs hstar hxo hyo hro hso U hU hcut hχ Adm P hAdm
  have hscale : ((U.card : ℝ)+1)^2*L^(-η) ≤ 1 := by
    have hsize : (U.card : ℝ) ≤ M.atoms.card := by exact_mod_cast card_le_card hU
    have hpoly := hRs L hLs M.atoms.card hn
    have hadd : (U.card : ℝ)+1 ≤ (M.atoms.card : ℝ)+1 := by linarith only [hsize]
    have hpow : ((U.card : ℝ)+1)^2 ≤ ((M.atoms.card : ℝ)+1)^2 :=
      pow_le_pow_left₀ (by positivity) hadd 2
    have hh' := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hLpos.le (-η))
    simp only [one_mul,neg_zero,Real.rpow_zero] at hpoly
    exact hh'.trans hpoly
  have hneutral : countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P := by
    apply hq.trans
    have he : ENNReal.ofReal (((U.card : ℝ)+1)^2*L^(-η)) ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hscale
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (show 0 ≤ countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P from bot_le)
  have hpost := hRd L hLd hlog (Degen.eraseAtoms M {v})
    (Degen.isMolecule_eraseAtoms M hM {v}) (simple_eraseAtoms M {v} hsimp)
    S hS (cut_side_closed_after_erasure M {v} S hboundary) _ P
    (projected_largeGap M L γ η (0 : Mom d) {v} Adm hAdm)
  exact hneutral.trans (hpost.trans (countAFree_induced_erasure_le_original M {v} S hS L γ δ C1 (0 : Mom d) Adm P))

end WaveTurbulence.MoleProp
