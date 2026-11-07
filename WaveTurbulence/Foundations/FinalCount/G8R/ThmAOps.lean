/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.ThmARoute
import Mathlib.Tactic

/-! # Theorem A, Steps 1–2: operations (c) and (d), as named inputs

Orchestrator decision: the deviation bounds of DH23's operations (c) and (d) are named inputs. They are stated in
G6's relaxed count `MoleProp.countAFree`, which is APPB's `Mole.appbLinkCountA` verbatim: the same count
(`countEFree` = `appbCountE`: supremum over all conservation parameters), the same length-one ladder set
(`ladderCells` = `appbLinks`) and the same weights.

The β-atoms are exempt from the large-gap condition (`lgAdmOff`; case-4 note 4.4: "LG at b, b′ are irrelevant").

* `OpCInput` (DH23 L1861, (operc)): remove a chain `Y` of β-atoms (in = out = 1) attached by two bonds to distinct
  atoms; one gap of the chain is nonzero. Deviation `(log L)^C L^{1−γ}`: by Lemma A.3(1), `D ≲ 1 + δ⁻¹ R⁻¹ L^{−γ}` with
  `R ≥ 1/L` (case-4 note Step 1; referee check 1).
* `OpDInput` (DH23 L1865–L1867): remove the chain and add a bond `u → v` in its direction; LG weakened (`η/2`), deviation
  `(log L)^C`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **LG outside `B`** (the β-atoms) and the cell restriction. -/
def lgAdmOff (M : Molecule V D) (B : Finset V) {d : ℕ} (L γ η : ℝ) (P : Finset V → ℝ) (κ : D → (Fin d → ℤ)) : Prop :=
  (∀ x y, M.atom x = M.atom y → M.atom x ∉ B → M.out x ≠ M.out y →
    L ^ (-γ + η) ≤ ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖) ∧
  MoleProp.CellGapRestriction M L 0 P (MoleProp.GapScale L) κ

omit [DecidableEq D] in
theorem lgAdmOff_empty {M : Molecule V D} {d : ℕ} {L γ η : ℝ} {P : Finset V → ℝ} {κ : D → (Fin d → ℤ)}
    (h : lgAdmOff M ∅ L γ η P κ) : lgAdm M L γ η P κ :=
  ⟨fun x y hxy hdir => h.1 x y hxy (notMem_empty _) hdir, h.2⟩

/-- The darts of `𝕄 ∖ (inserted bond) ` are the darts of `𝕄`. -/
def addBondEraseEquiv (M : Molecule V D) (a b : V) :
    D ≃ MoleProp.WithoutBondDart (Mole.addBond M a b) (Sum.inr true) where
  toFun z := ⟨Sum.inl z, Sum.inl_ne_inr, Sum.inl_ne_inr⟩
  invFun y := match y with
    | ⟨Sum.inl z, _⟩ => z
    | ⟨Sum.inr bo, h⟩ => False.elim (by
        cases bo with
        | false => exact h.2 rfl
        | true => exact h.1 rfl)
  left_inv _ := rfl
  right_inv y := by
    obtain ⟨y | bo, h⟩ := y
    · rfl
    · exact False.elim (by
        cases bo with
        | false => exact h.2 rfl
        | true => exact h.1 rfl)

/-- **`𝔄(𝕄) ≤ 𝔄((𝕄 + ℓ) ∖ ℓ)`**: re-adding and removing a bond changes nothing. -/
theorem afree_le_addBond_erase (M : Molecule V D) {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {d : ℕ}
    (L γ δ η C1 : ℝ) (P : Finset V → ℝ) :
    AFree M d L γ δ η C1 P ≤ AFree (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)) d L γ δ η C1 P := by
  have hA : M.atoms = (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)).atoms := by
    change M.atoms = insert a (insert b M.atoms)
    rw [insert_eq_of_mem hb, insert_eq_of_mem ha]
  have ha : ∀ x, (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)).atom (addBondEraseEquiv M a b x) =
      M.atom x := fun _ => rfl
  have hm : ∀ x, (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)).mate (addBondEraseEquiv M a b x) =
      addBondEraseEquiv M a b (M.mate x) := fun _ => rfl
  have ho : ∀ x, (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)).out (addBondEraseEquiv M a b x) =
      M.out x := fun _ => rfl
  exact MoleProp.countAFree_le_of_dart_equiv M _ (addBondEraseEquiv M a b) hA ha hm ho L γ δ C1 0 _ _
    (fun κ h => lgAdm_relabel M _ _ hA ha hm ho h) P

theorem ladderCells_addBond_erase (M : Molecule V D) {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) :
    MoleProp.ladderCells (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)) = MoleProp.ladderCells M := by
  classical
  have hA : M.atoms = (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)).atoms := by
    change M.atoms = insert a (insert b M.atoms)
    rw [insert_eq_of_mem hb, insert_eq_of_mem ha]
  have ha : ∀ x, (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)).atom (addBondEraseEquiv M a b x) =
      M.atom x := fun _ => rfl
  have hm : ∀ x, (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)).mate (addBondEraseEquiv M a b x) =
      addBondEraseEquiv M a b (M.mate x) := fun _ => rfl
  have ho : ∀ x, (MoleProp.eraseBond (Mole.addBond M a b) (Sum.inr true)).out (addBondEraseEquiv M a b x) =
      M.out x := fun _ => rfl
  exact (ladderCells_eq_of_dart_equiv' M _ (addBondEraseEquiv M a b) hA ha hm ho).symm

end

/-- **Operation (c)** at a fixed `L` (DH23 L1861).

**Deviation (finalcount-g8, session 3).** MOLEPROP4-T's draft statement had no connectivity hypotheses and is false
without them (if `M ∖ Y` is disconnected, `Δχ = 0` and the count gains `L^{d-γ+γ₀}` with no normalization to absorb it).
Added: `M` connected, the chain `Y` connected (`piece M Y`), `M ∖ Y` connected. -/
def OpCAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
    (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
    (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
    ∀ (Y Bs : Finset V) (x₁ x₂ : D), Y ⊆ M.atoms → Y ⊆ Bs → (∀ b ∈ Y, M.outdeg b = 1 ∧ M.indeg b = 1) →
    crossDarts M Y = {x₁, x₂} → M.atom (M.mate x₁) ≠ M.atom (M.mate x₂) →
    (∀ a ∈ Y, ∀ b ∈ Y, (piece M Y).SameComponent a b) →
    (∀ a ∈ (Degen.eraseAtoms M Y).atoms, ∀ b ∈ (Degen.eraseAtoms M Y).atoms,
      (Degen.eraseAtoms M Y).SameComponent a b) →
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdmOff M Bs L γ η P κ ∧
      ∃ y y', M.atom y ∈ Y ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧ κ y ≠ κ y') →
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (K * Real.log L ^ B * L ^ (1 - γ)) *
          AFreeSupAdm (Degen.eraseAtoms M Y) d L γ δ C1 (fun P' κ' => lgAdmOff (Degen.eraseAtoms M Y) (Bs \ Y) L γ η P' κ')

/-- The input: `OpCAt` for every `L ≥ R`. -/
def OpCInput (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    OpCAt.{u, v} d L γ δ η C1 K B

/-- **Operation (d)** at a fixed `L` (DH23 L1865–L1867): the chain `u → Y → v` becomes a bond `u → v`. LG is weakened
(`η/2`), deviation `K (log L)^B`.

**Deviation (finalcount-g8, session 3).** MOLEPROP4-T's draft statement was false as stated (no `|Y|` bound although the
energy windows number `~ |Y|`; no connectivity; no good-cell hypothesis for the cells of the post molecule, as for
`BiBridgeEqualAt`). Added: `|Y| ≤ 3`, `M` connected, `Y` connected, the post connected, `hopen` (every cell of the post is
`GoodCell`), and the far ends `u, v ∉ Bs` (LG is used at `u` and `v`). -/
def OpDAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
    (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
    (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
    ∀ (Y Bs : Finset V) (x₁ x₂ : D), Y ⊆ M.atoms → Y ⊆ Bs → Y.card ≤ 3 → (∀ b ∈ Y, M.outdeg b = 1 ∧ M.indeg b = 1) →
    crossDarts M Y = {x₁, x₂} → M.out x₁ = false → M.out x₂ = true →
    M.atom (M.mate x₁) ≠ M.atom (M.mate x₂) → M.atom (M.mate x₁) ∉ Bs → M.atom (M.mate x₂) ∉ Bs →
    (∀ a ∈ Y, ∀ b ∈ Y, (piece M Y).SameComponent a b) →
    (∀ a ∈ (Mole.addBond (Degen.eraseAtoms M Y) (M.atom (M.mate x₁)) (M.atom (M.mate x₂))).atoms,
      ∀ b ∈ (Mole.addBond (Degen.eraseAtoms M Y) (M.atom (M.mate x₁)) (M.atom (M.mate x₂))).atoms,
      (Mole.addBond (Degen.eraseAtoms M Y) (M.atom (M.mate x₁)) (M.atom (M.mate x₂))).SameComponent a b) →
    (∀ S ∈ MoleProp.ladderCells (Mole.addBond (Degen.eraseAtoms M Y) (M.atom (M.mate x₁)) (M.atom (M.mate x₂))),
      GoodCell (Mole.addBond (Degen.eraseAtoms M Y) (M.atom (M.mate x₁)) (M.atom (M.mate x₂))) S) →
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdmOff M Bs L γ η P κ) →
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (K * Real.log L ^ B) *
          AFreeSupAdm (Mole.addBond (Degen.eraseAtoms M Y) (M.atom (M.mate x₁)) (M.atom (M.mate x₂))) d L γ δ C1
            (fun P' κ' => lgAdmOff (Mole.addBond (Degen.eraseAtoms M Y) (M.atom (M.mate x₁)) (M.atom (M.mate x₂)))
              (Bs \ Y) L γ (η / 2) P' κ')

/-- The input: `OpDAt` for every `L ≥ R`. -/
def OpDInput (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    OpDAt.{u, v} d L γ δ η C1 K B

end WaveTurbulence.MoleProp4
