/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Prop96Statement
import Mathlib.Tactic

/-! # The damaged-component bound DCB (ruling R29 item 5), statement

A component of the final molecule `M_fin'` (after the end-of-run erasure of tame clusters, Op 5) that is *imperfect*
(has an `ε`-atom of degree `≠ 4` or an `α`/`β`-atom of degree `≠ 2`) is bounded by
`𝔄 ≲ ∏_α L^{-(γ+3η)/2+κ_vη} R_v⁻¹ · L^{(γ₀+2η²)V_β} · L^{-η⁵ρ + ηZ}`,
`Z = #{ε-atoms of degree ≠ 4}`, counted for every `R` (no `-(2γ₀+5η²)G` gain).

It uses only the shape fields `isMolecule`, `abLow`, `degPos`, `noLoop`, `noTriple`, `conn`, `nonempty` of `FinalShape`, the
imperfection, and `epsLG` of `FinalDec`; NOT `N1`, `N2`, `noBetaCut`, chains, cycles, `vineLG`, `oddDeg`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

open Classical in
/-- `Z`: the number of `ε`-atoms of degree `≠ 4`. -/
noncomputable def epsDefect {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) : ℕ :=
  (M.atoms.filter fun a => (cls a).IsEps ∧ M.deg a ≠ 4).card

/-- The right-hand side of the damaged-component bound. -/
noncomputable def damagedRHS {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]
    (M : Molecule V D) (cls : V → Cls) (L γ η : ℝ) : ℝ :=
  let γ0 := min γ (1 - γ)
  (∏ v ∈ alphaAtoms M.atoms cls, (L ^ (-(γ + 3 * η) / 2 + ((cls v).kap : ℝ) * η) * ((cls v).lab)⁻¹)) *
    L ^ ((γ0 + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ)) *
    L ^ (-(η ^ 5) * (M.rho : ℝ) + η * (epsDefect M cls : ℝ))

/-- The shape of an imperfect component (only the fields DCB uses). -/
structure DamagedShape {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) : Prop where
  nonempty : M.atoms.Nonempty
  /-- the molecule axioms (caps and an atom of degree `≠ 4` in every component) -/
  isMolecule : M.IsMolecule
  noLoop : ∀ x, M.atom x ≠ M.atom (M.mate x)
  conn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b
  /-- every atom has a bond -/
  degPos : ∀ a ∈ M.atoms, 1 ≤ M.deg a
  /-- `α`/`β`-atoms have degree `≤ 2` (an `ε`-atom may also have low degree after Op 5) -/
  abLow : ∀ a ∈ M.atoms, ¬ (cls a).IsEps → M.deg a ≤ 2
  noTriple : ∀ a b, M.bondsBetween a b ≤ 2
  /-- imperfect: an `ε`-atom of degree `≠ 4` or an `α`/`β`-atom of degree `≠ 2` -/
  imperf : ∃ a ∈ M.atoms, ((cls a).IsEps ∧ M.deg a ≠ 4) ∨ (¬ (cls a).IsEps ∧ M.deg a ≠ 2)

/-- The decoration hypothesis of DCB: strict LG at the `ε`-atoms, and the label range of the `α`-atoms. -/
structure DamagedDec {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) {d : ℕ} (L γ η : ℝ) (Adm : (D → (Fin d → ℤ)) → Prop) : Prop where
  /-- the labels of `α`-atoms lie in `[L⁻¹, L^{-γ+η}]` (needed to evaluate `∏_α R_v⁻¹` from below) -/
  labRange : ∀ a ∈ M.atoms, (cls a).IsAlpha → L⁻¹ ≤ (cls a).lab ∧ (cls a).lab ≤ L ^ (-γ + η)
  epsLG : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsEps →
    ∀ x y, M.atom x = a → M.atom y = a → M.out x ≠ M.out y →
      L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖

theorem FinalDec.toDamaged {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {cls : V → Cls} {d : ℕ} {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop} (h : FinalDec M cls L γ η Adm) :
    DamagedDec M cls L γ η Adm := ⟨h.labRange, h.epsLG⟩

/-- **DCB** (R29 item 5), for `d ≥ 3`, `0 < γ < 1`, with `Cstar` depending only on `(d, γ, η)` (ruling R34): the size
exponent `m` is quantified after `Cstar` and enters only through `R₀`. -/
def Prop96DamagedAt.{u, v} (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, ∀ L ≥ R₀,
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (cls : V → Cls) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      DamagedShape M cls → DamagedDec M cls L γ η Adm →
      (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      (∀ S, 0 ≤ P S) →
      MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm →
      M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (damagedRHS M cls L γ η)

end WaveTurbulence.FinalCountG8
