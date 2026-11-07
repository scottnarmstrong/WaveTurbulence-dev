/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.Spine.SourceGapTableObjects
import Mathlib.Tactic

/-!
R83 successor copy of pinned/r83-RepSel.lean (original SHA in COPIED-SHA256SUMS).

# S2 REPRESENTS, W1: the gap kind of a group and the `σ`-restriction `sel`

TARGET L1950: the sum over a congruence class is split by specifying for every vine-like object of `𝒞` whether it
is SG, LG or ZG; this is "an extra restriction on the decoration" (the factor `Z`).  Here:
* `designatedObject G S` (redsplice, R25(a)): the designated vine-like object of the group `S`;
* `groupGapKind`: the gap kind of that object under a decoration (unique, `Object.hasGapKind_unique`);
* `GroupPrescription G`: SG/LG/ZG on the groups only (RULINGS R24 D2);
* `selOf σ`: the decorations whose group gap kinds are `σ`; `selOf_unique`, `exists_unique_prescription`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.RedSplice

variable {w : ℕ}

/-- SG/LG/ZG prescriptions on the groups of `𝒞` only (R24 D2). -/
abbrev GroupPrescription (G : Garden w) := {S : Finset (GBranch G.tree) // S ∈ maximalGroups G.molecule} → Molecule.GapKind

/-- The restriction of a total prescription to the groups. -/
@[expose] def GroupPrescription.ofPrescription {G : Garden w} (σ : Prescription G) : GroupPrescription G := fun S => σ S.1

theorem object_hasGapKind_unique {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (O : SourceVine.Object M) {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (κ : D → (Fin d → ℤ)) {k k' : Molecule.GapKind} (h : O.HasGapKind L γ η v κ k)
    (h' : O.HasGapKind L γ η v κ k') : k = k' := by
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨r', hr', rfl⟩ := h'
  unfold SourceVine.VineLikeObject.IsGap at hr hr'
  cases hs : O.shape with
  | vc hvc =>
    rw [hs] at hr hr'
    have := Vine.blockGap_unique M hvc.1 hr hr'
    rw [this]
  | hyper R =>
    rw [hs] at hr hr'
    have := Vine.blockGap_unique (Mole.eraseBond M R.added) R.adjoint.1 hr hr'
    rw [this]


/-- The gap kind of the group `S` under the decoration `κ` (momentum offset `v`): that of its designated
object; `ZG` if the group has no designated object or no gap (irrelevant for groups of `𝒞`). -/
@[expose] noncomputable def groupGapKind (G : Garden w) {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (S : Finset (GBranch G.tree)) : Molecule.GapKind := by
  classical
  exact if h : ∃ O, designatedObject G S = some O ∧ ∃ k, O.HasGapKind L γ η v κ k then h.choose_spec.2.choose
  else .ZG

theorem groupGapKind_eq {G : Garden w} {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) {S : Finset (GBranch G.tree)} {O : SourceVine.Object G.molecule}
    (hO : designatedObject G S = some O) {k : Molecule.GapKind} (hk : O.HasGapKind L γ η v κ k) :
    groupGapKind G L γ η v κ S = k := by
  classical
  have h : ∃ O, designatedObject G S = some O ∧ ∃ k, O.HasGapKind L γ η v κ k := ⟨O, hO, k, hk⟩
  unfold groupGapKind
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hO', hk'⟩ := h.choose_spec
  have hOO : h.choose = O := (Option.some.inj (hO'.symm.trans hO))
  have key : ∀ (O' : SourceVine.Object G.molecule) (k' : Molecule.GapKind), O' = O →
      O'.HasGapKind L γ η v κ k' → k' = k := by
    rintro O' k' rfl hk'
    exact object_hasGapKind_unique O' L γ η v κ hk' hk
  exact key _ _ hOO h.choose_spec.2.choose_spec

/-- **The `σ`-restriction on decorations** (TARGET L1950, factor `Z`): the group gap kinds of the
decoration `z` of the garden `G` are `σ`. -/
@[expose] def selOf {G : Garden w} {d : ℕ} (σ : GroupPrescription G) (L γ η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : Prop :=
  ∀ S : {S : Finset (GBranch G.tree) // S ∈ maximalGroups G.molecule},
    groupGapKind G L γ η v (bondIndex G z) S.1 = σ S

/-- The prescription of a decoration. -/
@[expose] noncomputable def prescriptionOf (G : Garden w) {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : GroupPrescription G :=
  fun S => groupGapKind G L γ η v (bondIndex G z) S.1

theorem selOf_prescriptionOf {G : Garden w} {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : selOf (prescriptionOf G L γ η v z) L γ η v z := fun _ => rfl

/-- **Uniqueness**: a decoration satisfies the restriction of exactly one group prescription. -/
theorem selOf_unique {G : Garden w} {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) {σ τ : GroupPrescription G}
    (hσ : selOf σ L γ η v z) (hτ : selOf τ L γ η v z) : σ = τ :=
  funext fun S => (hσ S).symm.trans (hτ S)

theorem exists_unique_prescription {G : Garden w} {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : ∃! σ : GroupPrescription G, selOf σ L γ η v z :=
  ⟨prescriptionOf G L γ η v z, selOf_prescriptionOf L γ η v z, fun _ h => selOf_unique L γ η v z h
    (selOf_prescriptionOf L γ η v z)⟩

end WaveTurbulence.VineA.NormalizedSplice
