/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain4
/-! **FINALCOUNT LOW-CHAIN, LC-2 (1): atom count along the LOW run** (`UCtx.card_atoms_le` with an index `R' ≤ Rn` and `SubHypL`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {M₀ : Molecule V D₀} {Rn R' : ℕ}

theorem card_atoms_leL_of_uctx (hS : SubHypL Rn M₀) (hR : R' ≤ Rn) {h : HSt V D₀} (hc : UCtx M₀ R' Adm0 L w h) :
    h.s.M.atoms.card ≤ 2 * M₀.atoms.card := by
  have hphi := hc.good.1.phi
  have hD : Fintype.card h.s.D ≤ Fintype.card D₀ := Fintype.card_le_of_injective _ hc.anc.inj
  have hD0 := card_darts_eq_two_bonds M₀
  have hcount := hS.count
  have hbase : ∀ a ∈ h.s.M.atoms, (2 : ℤ) ≤ (h.s.cls a).base := by
    intro a ha
    have hg := hc.good.2 a ha
    rcases hcls : h.s.cls a with _ | _ | _ | _
    · simp [Cls.base]
    · simp [Cls.base]
    · simp [Cls.base]
    · exact absurd hcls hg
  have hsum : (2 : ℤ) * h.s.M.atoms.card ≤ ∑ a ∈ h.s.M.atoms, (h.s.cls a).base := by
    have := Finset.card_nsmul_le_sum h.s.M.atoms (fun a => (h.s.cls a).base) 2 hbase
    simpa [mul_comm] using this
  have : ((h.s.M.atoms.card : ℕ) : ℤ) ≤ 2 * M₀.atoms.card := by
    have h1 : (Fintype.card h.s.D : ℤ) ≤ Fintype.card D₀ := by exact_mod_cast hD
    have h2 : (Fintype.card D₀ : ℤ) = 2 * M₀.bonds.card := by exact_mod_cast hD0
    have h3 : (M₀.bonds.card : ℤ) + Rn = 2 * M₀.atoms.card := by exact_mod_cast hcount
    have h4 : (R' : ℤ) ≤ Rn := by exact_mod_cast hR
    omega
  exact_mod_cast this

/-- `Inv3L` gives the atom bound. -/
theorem Inv3L.card_atoms_le {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {A0 A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀}
    (hS : SubHypL Rn M₀) (hA : Inv3L M₀ Rn Rch L w A0 A h) (hne : A ≠ ∅) : h.s.M.atoms.card ≤ 2 * M₀.atoms.card := by
  rcases hA.2 with he | ⟨⟨R', hR', hc⟩, -, -⟩
  · exact absurd he hne
  · exact card_atoms_leL_of_uctx hS hR' hc

end WaveTurbulence.FinalCountAsm
