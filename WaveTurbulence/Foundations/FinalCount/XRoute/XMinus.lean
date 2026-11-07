/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.XRoute.RouteBound
public import WaveTurbulence.Foundations.FinalCount.Prop102Bridge
import Mathlib.Tactic

/-! # G8-XROUTE (e): `xMinus_afree`

`𝔄(M ∖ ℓ*)` for `M = X` (or the quadrilateral) and every bond `ℓ*`, for every LG parameter `η' ≥ η₀`: the pair of
adjacent atoms of degree `(3,3)` (`ℓ*` a copy) or `(3,4)` (`ℓ*` single) is removed by G8's `pairGainAt`
(DH23 Lemma A.3(4)), and the leftover double bond `c = d` gains `L^{-η₀/3}` from Prop 10.2's second statement
(`E = 2V − 2`; LG).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem xMinus_afree (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η₀ : ℝ) (hη₀ : 0 < η₀)
    (hηγ : η₀ ≤ min γ (1 - γ)) (hηs : 4 * 1440061 * η₀ ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsXFinal M →
        (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
        (∀ a ∈ M.atoms, M.deg a = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
        ∀ (e : D) (η' : ℝ), η₀ ≤ η' → ∀ P : Finset V → ℝ,
          (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
          AFree (MoleProp.eraseBond M e) d L γ δ η' C1 P ≤
            ENNReal.ofReal (K * Real.log L ^ B * L ^ (-min γ (1 - γ)) * L ^ (-(η₀ / 3))) := by
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  obtain ⟨C102, hC102, h102⟩ := prop102SecondInputSz.{u, v} d hd γ η₀ hγ01 hη₀ hηγ hηs
  refine ⟨C102, hC102, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R102, hR102⟩ := h102 2 C1 hC1 δ hδ
  obtain ⟨K, B, Rp, hRp⟩ := pairGainAt.{u, v} hd hγ hδ (by linarith) η₀
  refine ⟨K, B, max (max R102 Rp) (Real.exp 1), fun L hL V D _ _ _ M hX hcap hloop hreg hconn e η' hη' P hP => ?_⟩
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hR1 : R102 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hR2 : Rp ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  obtain ⟨hc4, _, _⟩ := hX.facts hloop
  refine (afree_mono_eta _ hL1 hη' P).trans ?_
  refine afree_case_pair hLp (hRp L hR2) (hR102 L hR1) ?_ (hX.isCore hcap hloop hreg hconn) e
    (hX.noTwoCross hloop hreg) (hX.double hloop e) P hP
  rw [hc4]
  push_cast
  nlinarith

end WaveTurbulence.FinalCountG8
