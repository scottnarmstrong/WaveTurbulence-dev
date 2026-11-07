/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.ChainStruct
public import WaveTurbulence.Foundations.FinalCount.OpCRho
public import WaveTurbulence.Foundations.FinalCount.Rough96
public import WaveTurbulence.Foundations.FinalCount.Cycle96
import Mathlib.Tactic

/-! # Prop 9.6: operation (c) followed by Prop 10.1' (DH23 L1861, cases (2), (3))

For an even non-cycle component, a chain `K` of `α`/`β`-atoms (two distinct `ε`-ends) is removed with the deviation
(operc), and the remaining molecule (which has a degree-lowered `ε`-atom in every component) has `𝔄 ≲ 1` by Prop 10.1'.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8.P101

theorem chain_A_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀, ∀ ρ : ℝ, 0 < ρ →
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → ¬ odd → (¬ ∀ a ∈ M.atoms, M.deg a = 2) →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm →
        ∀ K, IsChainSet M cls K →
          (∀ κ, Adm κ → ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
            ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖) →
          M.countA L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ρ⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)) := by
  classical
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  obtain ⟨Cs, hCs, hP1⟩ := proposition_one_off_bound.{u, v} d hd γ hγ01 η hη hηmax
  refine ⟨Cs, hCs, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨Rp, hRp⟩ := hP1 C1 hC1 δ hδ
  refine ⟨max Rp (Real.exp 1), le_trans (Real.one_le_exp (by norm_num)) (le_max_right _ _), ?_⟩
  intro L hL ρ hρ V D _ _ _ M cls odd Adm P hS hF hnodd hnc hP hMA K hK hAdm
  have hLRp : Rp ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hM : M.IsMolecule := hS.isMolecule
  have hC1' : 1 ≤ C1 := le_trans hCs hC1
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
  -- the chain data
  obtain ⟨y₁, y₂, hcross, hy12, hε1, hε2, hne⟩ := hS.chains hnodd hnc K hK
  have hKA : K ⊆ M.atoms := hK.2.1
  have hch : ∀ b ∈ K, M.outdeg b = 1 ∧ M.indeg b = 1 := by
    intro b hb
    have hnE : ¬ (cls b).IsEps := hK.2.2.1 b hb
    have h2 : M.deg b ≤ 2 := (hS.classes b (hKA hb)).mpr hnE
    have h4 : M.deg b = 2 ∨ M.deg b = 4 := hS.evenDeg hnodd b (hKA hb)
    exact hS.dir2 b (hKA hb) (by omega)
  have hcard : (crossDarts M K).card = 2 := by rw [hcross, card_pair hy12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun a ha => by
    rcases hS.evenDeg hnodd a ha with h | h <;> omega) K hcard
  have hAdm'' : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
      ∃ y y', M.atom y ∈ K ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
        ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := fun κ hκ => hAdm κ hκ.1
  have hstep := opC_rho (L := L) (γ := γ) (δ := δ) (C1 := C1) (ρ := ρ) hγ01 hL1 hlog hδ hC1' hρ M hS.caps hS.noLoop
    hS.conn K y₁ y₂ hKA hch hcross hne (chain_piece_connected hK) hpost P' (fun S _ => hP _)
    (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) hAdm''
  -- Prop 10.1' on the remainder
  have hKne : K.Nonempty := hK.1
  have hPM : PMol (nonEps M.atoms cls) (Degen.eraseAtoms M K) :=
    pmol_erase_of_connected hS.caps (fun v hv hvB => (hS.classes v hv).mpr (mem_filter.mp hvB).2) hS.conn K hKA hKne
  have hLG : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) →
      LargeGapOff (nonEps M.atoms cls) M L γ η (0 : Mom d) κ := by
    intro κ hκ v hvB x y hx hy hxy
    have hv : v ∈ M.atoms := hx ▸ M.atom_mem x
    have hε : (cls v).IsEps := by
      by_contra hne'; exact hvB (mem_filter.mpr ⟨hv, hne'⟩)
    exact (hF.epsLG κ hκ.1 v hv hε x y hx hy hxy).le
  have hrest : MoleProp.countAFree (Degen.eraseAtoms M K) L γ δ C1 (0 : Mom d)
      (erasedFreeAdmissibility M K (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ)) P' ≤ 1 :=
    hRp L hLRp hlog (nonEps M.atoms cls) (Degen.eraseAtoms M K) hPM (fun x _ => hS.noLoop x.val) _ _
      (projected_largeGapOff M L γ η (0 : Mom d) (nonEps M.atoms cls) K _ hLG)
      (projected_cellGap M L (0 : Mom d) K _ P' (fun κ hκ => hκ.2))
      (fun S _ => hP _)
  calc _ ≤ _ := hstep
    _ ≤ ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ρ⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)) * 1 :=
        mul_le_mul' le_rfl hrest
    _ = _ := mul_one _

end WaveTurbulence.FinalCountG8
