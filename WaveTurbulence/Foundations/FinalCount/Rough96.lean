/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Prop102Bridge
public import WaveTurbulence.Foundations.FinalCount.Prop96Statement
public import WaveTurbulence.Foundations.FinalCount.AdmBridge
public import WaveTurbulence.Foundations.FinalCount.CountABridge
import Mathlib.Tactic

/-! # Prop 9.6: the rough bound (roughbd, L1855/L1857), from DH23 Prop 10.2 third sentence

`𝔄₀ ≲ L^{-η²ρ₀ + C(V_α+V_β+1)}` for a final component with `ε`-atoms: the decoration is LG off the `α`/`β`-atoms
(`ProblemSG` of APPB with `ws = #{atoms of degree ≠ 4}`), and `dh23_prop_10_2` applies.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.Mole.AppbAlgorithm

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem rho_eq_sourceRho (M : Molecule V D) : M.rho = sourceRho M := by
  classical
  unfold Molecule.rho Molecule.numLadders Molecule.numFree sourceRho sourceFreeAtoms
  rw [maximalLadders_eq_source M]
  congr 1
  congr 1
  ext a
  simp only [mem_filter, mem_sdiff, mem_biUnion, id]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun ⟨S, hS, ha⟩ => h2 S hS ha⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun S hS ha => h2 ⟨S, hS, ha⟩⟩


/-- The admissibility of the SG problem: `Adm`, the cell restriction (scale `P ∘ parent`), mate labels. -/
def sgAdm (M : Molecule V D) {d : ℕ} (L : ℝ) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (κ : D → (Fin d → ℤ)) : Prop :=
  (Adm κ ∧ CellGapRestriction M L (0 : Mom d) (fun S => P (Mole.appbLinkParent M S)) (GapScale L) κ) ∧
    ∀ x, κ (M.mate x) = κ x

theorem sgAdm_valid (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (Adm : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) {κ0 : D → (Fin d → ℤ)} (h0 : sgAdm M L Adm P κ0) :
    Mole.AppbValidLinkScales M L (0 : Mom d) (sgAdm M L Adm P) 2
      (cellScale M (fun S => P (Mole.appbLinkParent M S))) := by
  refine ⟨fun S hS => ?_, fun u v h κ hκ g hg hpos => ?_⟩
  · obtain ⟨u, v, h, rfl⟩ := hS
    obtain ⟨r, hr⟩ := exists_cell_gap M L 0 κ0 u v h
    have := (gapScale_cases hL (h0.1.2 u v h r hr)).1
    rw [cellScale_ladder M _ u v h]
    exact this
  · have := gapScale_cases hL (hκ.1.2 u v h g hg)
    rw [cellScale_ladder M _ u v h] at hpos ⊢
    have h2 := this.2 hpos
    linarith [h2]

theorem FinalShape.isMolecule {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) :
    M.IsMolecule := by
  have hex : ∃ u ∈ M.atoms, M.deg u ≠ 4 := by
    by_cases hodd : odd
    · obtain ⟨u, hu, w, hw, _, h1, _⟩ := hS.oddDeg hodd
      exact ⟨u, hu, by omega⟩
    · obtain ⟨b, hb, hbβ⟩ := hS.evenBeta hodd
      refine ⟨b, hb, ?_⟩
      have := (hS.classes b hb).mpr (by cases hc : cls b <;> simp_all [Cls.IsBeta, Cls.IsEps])
      omega
  obtain ⟨u, hu, hu4⟩ := hex
  exact ⟨hS.caps, fun v hv => ⟨u, hu, hS.conn v hv u hu, hu4⟩⟩

/-- **roughbd** (DH23 L1855/L1857): from Prop 10.2, third sentence. -/
theorem rough96 (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1 - γ)) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ m : ℕ, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ C1 ≥ C₀, ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal
          (L ^ (-η ^ 2 * (M.rho : ℝ) + (16 * (d : ℝ) + 28) * (((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) + 1))) := by
  classical
  obtain ⟨C₀, hC₀, h⟩ := dh23_prop_10_2.{v, u} d hd γ η hγ hη hηγ hηs 2 (by norm_num)
  refine ⟨C₀, hC₀, fun m δ hδ C1 hC1 => ?_⟩
  obtain ⟨L₀, hL₀⟩ := h m δ hδ C1 hC1
  refine ⟨max L₀ 1, le_max_right _ _, fun L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLL : L ≥ L₀ := le_trans (le_max_left _ _) hL
  have hLp : 0 < L := by linarith
  have hM : M.IsMolecule := hS.isMolecule
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
  have heq : MoleProp.countAFree M L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧
      CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) P' =
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) (sgAdm M L Adm P) (cellScale M P') := by
    unfold MoleProp.countAFree
    rw [cellProduct_cellScale]
    congr 2
    refine countEFree_congr M L γ δ 0 _ _ fun κ hκ => ?_
    exact ⟨fun h => ⟨h, hκ⟩, fun h => h.1⟩
  rw [heq]
  by_cases hex : ∃ κ0, sgAdm M L Adm P κ0
  swap
  · push Not at hex
    have : MoleProp.countAFree M L γ δ C1 (0 : Mom d) (sgAdm M L Adm P) (cellScale M P') = 0 := by
      unfold MoleProp.countAFree
      rw [countEFree_eq_zero M L γ δ 0 _ fun κ _ => hex κ]
      simp
    rw [this]; exact bot_le
  obtain ⟨κ0, hκ0⟩ := hex
  have hsub : (nonEps M.atoms cls) ⊆ M.atoms.filter (fun a => M.deg a ≠ 4) := by
    intro a ha
    obtain ⟨h1, h2⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨h1, ?_⟩
    have := (hS.classes a h1).mpr h2
    omega
  let wn : ℕ := (M.atoms.filter fun a => M.deg a ≠ 4).card
  let pSG : ProblemSG.{v, u} V d L 0 2 (L ^ (-γ + η)) wn :=
    { state := ofMolecule M
      admissible := sgAdm M L Adm P
      scales := cellScale M P'
      molecule := hM
      noLoops := hS.noLoop
      scales_nonneg := pf_nonneg M P' (fun S _ => hP _)
      validLinkScales := sgAdm_valid M hL1 Adm P hκ0
      mateLabels := fun κ h x => h.2 x
      largeGap := fun κ hκ => ⟨nonEps M.atoms cls, by intro a ha; exact (mem_filter.mp ha).1,
        (card_le_card hsub), by
          intro v hv hvS x hx y hy hxy _
          have hε : (cls v).IsEps := by
            by_contra hne
            exact hvS (mem_filter.mpr ⟨hv, hne⟩)
          exact (hF.epsLG κ hκ.1.1 v hv hε x y ((Mole.mem_dartsAt M v x).mp hx) ((Mole.mem_dartsAt M v y).mp hy) hxy).le⟩ }
  have hb := ((hL₀ V 0 L hLL).2 wn pSG ⟨fun a _ b _ _ => hS.noTriple a b, hsz⟩ hS.conn hS.nonempty le_rfl)
  have hrho : sourceRho (pSG.state.graph) = M.rho := (rho_eq_sourceRho M).symm
  rw [hrho] at hb
  exact hb

end
end WaveTurbulence.FinalCountG8
