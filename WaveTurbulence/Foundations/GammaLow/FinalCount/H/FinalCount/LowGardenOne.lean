/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenOne
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL27
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLoops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenOne`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GARDEN): the one-atom gardens** (Examples A and B of R48, loops allowed).

A garden with a single atom has only loop darts (or none), so `countA_allLoops_le` (GL28) gives `𝔄 ≤ g^k`, `g = L^{-(d-γ)} C₁⁻¹ δ^{1/2}`,
`k = #loops = 2 - R`, `R ∈ {1, 2}`; the target bound follows from `ρ + #critical ≤ 2` (one free atom, no ladder, at most one critical atom). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp

variable {R d : ℕ} {G : Garden (2 * R)}

theorem lowGarden_single_atom {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ} (hγ1 : γ < 1) (hη : 0 < η) (hη40 : η ≤ 1 / 40)
    {R : ℕ} (G : Garden (2 * R)) (hp : G.IsPlain) (hR : 1 ≤ R) (D : SplicedKernelData G d) (C : Src.CountingChoices Src.γL G d)
    (hD : D.hinges = C.subpro.hinges) (hg : Src.CountingGeometry G C) (hone : G.molecule.atoms.card = 1)
    {L : ℝ} (hL : 1 ≤ L) {C1 δ : ℝ} (hC1 : 1 ≤ C1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (Adm : (GardenDart G → (Fin d → ℤ)) → Prop)
    (hA : ∀ κ, Adm κ → Src.splicedCountingAdmissible G D C L γ η base roots κ) :
    G.molecule.countA L γ δ C1 base Adm C.ladderScale ≤
      ENNReal.ofReal (L ^ (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
        L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40))) := by
  have hL0 : 0 < L := by linarith
  have hC0 : 0 < C1 := by linarith
  obtain ⟨a0, ha0⟩ := Finset.card_eq_one.1 hone
  have hall : ∀ x, G.molecule.atom x = G.molecule.atom (G.molecule.mate x) := by
    intro x
    have h1 : G.molecule.atom x ∈ G.molecule.atoms := G.molecule.atom_mem x
    have h2 : G.molecule.atom (G.molecule.mate x) ∈ G.molecule.atoms := G.molecule.atom_mem _
    rw [ha0] at h1 h2
    rw [Finset.mem_singleton] at h1 h2
    rw [h1, h2]
  have hb : ∀ a ∈ G.molecule.atoms, G.molecule.deg a ≤ 4 := fun a ha => deg_le_four (M := G.molecule) (hg.molecule.1 a ha)
  have hdet : ∀ κ₁ κ₂, Adm κ₁ → Adm κ₂ →
      (∀ x : GardenDart G, G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x) → κ₁ x = κ₂ x) → κ₁ = κ₂ :=
    fun κ₁ κ₂ h1 h2 h => garden_loop_det hp hg hD (hA κ₁ h1) (hA κ₂ h2) h
  refine (countA_allLoops_le hb hall L γ δ C1 hL0 hC0 hδ base Adm hdet C.ladderScale).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the count of loops
  have hbonds : G.molecule.bonds.card + R = 2 := by have := hg.bond_count; rw [← hg.atom_count, hone] at this; omega
  have hk : G.molecule.loopBonds.card = G.molecule.bonds.card := by
    unfold Molecule.loopBonds
    rw [Finset.filter_true_of_mem]
    intro x _; exact hall x
  have hρ : G.molecule.rho ≤ 1 := rho_le_one_of_one_atom G.molecule hall hone
  have hcrit : C.numCriticalSG ≤ 1 := by
    unfold Src.CountingChoices.numCriticalSG
    refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
    have : (Finset.univ : Finset (GBranch G.tree)) = G.molecule.atoms := rfl
    rw [this, hone]
  have hT : ((G.molecule.rho : ℝ) + (C.numCriticalSG : ℝ)) ≤ 2 := by
    have : ((G.molecule.rho + C.numCriticalSG : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : G.molecule.rho + C.numCriticalSG ≤ 2)
    exact_mod_cast this
  -- numerics
  have hη6 : η ^ 6 ≤ (1 / 40) ^ 6 := pow_le_pow_left₀ hη.le hη40 6
  have hη6' : 8 * η ^ 6 ≤ 1 / 100 := by
    have : (1 / 40 : ℝ) ^ 6 ≤ 1 / 800 := by norm_num
    linarith
  have hdγ : (2 : ℝ) ≤ (d : ℝ) - γ := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hX : (1 : ℝ) ≤ (d : ℝ) - γ - 1 / 4 - 1 / 40 := by linarith
  have hE1 : -(8 * η ^ 6) ≤ -4 * η ^ 6 * ((G.molecule.rho : ℝ) + (C.numCriticalSG : ℝ)) := by
    have h6 : 0 ≤ η ^ 6 := by positivity
    nlinarith
  have hLE1 : L ^ (-(8 * η ^ 6)) ≤ L ^ (-4 * η ^ 6 * ((G.molecule.rho : ℝ) + (C.numCriticalSG : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hL hE1
  have hgle : L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ≤ L ^ (-((d : ℝ) - γ)) := by
    have hδ' : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
    have hc : C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
      have : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
      calc C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 * 1 := mul_le_mul this hδ' (by positivity) zero_le_one
        _ = 1 := one_mul 1
    calc L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ≤ L ^ (-((d : ℝ) - γ)) * 1 :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := mul_one _
  rw [hk]
  rcases (by omega : R = 1 ∨ R = 2) with hR1 | hR2
  · -- R = 1: one loop
    have hb1 : G.molecule.bonds.card = 1 := by omega
    have hRr : (R : ℝ) = 1 := by exact_mod_cast hR1
    rw [hb1, pow_one, hRr]
    refine hgle.trans ?_
    calc L ^ (-((d : ℝ) - γ)) ≤ L ^ (-(8 * η ^ 6)) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
      _ ≤ L ^ (-4 * η ^ 6 * ((G.molecule.rho : ℝ) + (C.numCriticalSG : ℝ))) := hLE1
      _ = _ := by simp
  · -- R = 2: no bond
    have hb0 : G.molecule.bonds.card = 0 := by omega
    have hRr : (R : ℝ) = 2 := by exact_mod_cast hR2
    rw [hb0, pow_zero, hRr]
    have h1 : (1 : ℝ) ≤ L ^ (((2 - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)) + (-(8 * η ^ 6))) :=
      Real.one_le_rpow hL (by linarith)
    calc (1 : ℝ) ≤ L ^ (((2 - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)) + (-(8 * η ^ 6))) := h1
      _ = L ^ (-(8 * η ^ 6)) * L ^ ((2 - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)) := by
          rw [add_comm, Real.rpow_add hL0]
      _ ≤ _ := by gcongr

end WaveTurbulence.GammaLow.FinalCount.H
