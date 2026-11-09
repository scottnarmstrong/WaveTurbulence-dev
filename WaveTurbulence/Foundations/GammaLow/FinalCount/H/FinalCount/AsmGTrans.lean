/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGTrans
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGCn
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmUnsel
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproShapeC1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Transport
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmGTrans`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (garden level): the instantiation data and the class-level inputs of `hmemAt_of_shape`.**

For a garden `G` with counting choices `C`, the class theorem runs on `M₀ = inlMol G.molecule` (atoms `GBranch ⊕ ℕ`) at base `0` with
* `C0 C = collMap Sum.inl (collDataOf C.subpro)` (G3's collection data),
* `Un0 C L γ η κ = objMap '' unselOf (collDataOf C.subpro) L γ η 0 κ C.omittedDVConstituents` (the omitted vines),
* `Fst0 C = objMap '' fstG C.subpro` (the ordinary members of `C₁`: CN / root-CL vines, removed first).

Garden-level facts at base `0` (`*_G`) come from `Admissible` at the real base (S4-DISJ, S4-SHAPE, the shape lemma `c2_shape`) through
the base independence of `AsmGBase`; they are transported to `M₀` (`*_0`).  Discharged here: `hsh` (`hsh0`), `hcrit` (`hcrit0`),
`hsgC`/`hdesC` (`hsg_hinge0`), `hFst` (`hFst0`), `hdisj` (`hdisj0`), and the `C₂` facts used by S4-SHAPE (`hd22_0`, `vcShape0`,
`unselOK0`). 

**Low-range change (L6-HDS).** The ordinary members of `C₂` are one or two double bonds or T-vines (`vcShape_G`,
`vcShape0`; main: a vine (V)); `ObjVine` (= `IsVineEnl`) and T-vines are transported along `mapAtoms` by
`DS.mapAtoms_isVineEnl`, `DS.mapAtoms_isTVine` (L6-HTV's `isTVine_map_of_groupBonds`).
-/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp

section transport
variable {V W : Type*} [DecidableEq V] [DecidableEq W] {D : Type*} [Fintype D] [DecidableEq D]

theorem objVine_objMap_iff (M : Molecule V D) (ι : V ↪ W) (U : Src.Object Src.γL M) :
    ObjVine (mapAtoms M ι) (objMap (ι := ι) U) ↔ ObjVine M U := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc h => exact DS.mapAtoms_isVineEnl M ι S a b
  | hyper R => exact DS.mapAtoms_isVineEnl (M.eraseBond R.added) ι S a b

end transport

section garden
variable {R d : ℕ} {G : Garden (2 * R)}

/-- G3's collection data of the choices (S4-DISJ's `collDataOf`). -/
abbrev gCol (C : Src.CountingChoices Src.γL G d) : CollData G.molecule := collDataOf C.subpro

/-- The omitted vines (pool members whose atom set is omitted), at base `0`. -/
abbrev unG (C : Src.CountingChoices Src.γL G d) (L γ η : ℝ) (κ : GardenDart G → (Fin d → ℤ)) : Set (Src.Object Src.γL G.molecule) :=
  unselOf (gCol C) L γ η 0 κ C.omittedDVConstituents

/-- The collection data on `inlMol G.molecule`. -/
noncomputable abbrev C0 (C : Src.CountingChoices Src.γL G d) : CollData (inlMol G.molecule) := collMap (inlEmb _) (gCol C)

/-- The omitted vines on `inlMol G.molecule`. -/
abbrev Un0 (C : Src.CountingChoices Src.γL G d) (L γ η : ℝ) (κ : GardenDart G → (Fin d → ℤ)) : Set (Src.Object Src.γL (inlMol G.molecule)) :=
  objMap (ι := inlEmb _) '' unG C L γ η κ

/-- The first-stage objects on `inlMol G.molecule`. -/
abbrev Fst0 (C : Src.CountingChoices Src.γL G d) : Set (Src.Object Src.γL (inlMol G.molecule)) := objMap (ι := inlEmb _) '' fstG C.subpro

variable (C : Src.CountingChoices Src.γL G d) {L γ η : ℝ}

theorem c2Of0_iff (κ : GardenDart G → (Fin d → ℤ)) (U : Src.Object Src.γL G.molecule) :
    objMap (ι := inlEmb _) U ∈ (C0 C).C2Of L γ η 0 κ (Un0 C L γ η κ) ↔ U ∈ (gCol C).C2Of L γ η 0 κ (unG C L γ η κ) :=
  mem_collMap_c2Of (inlEmb _) (gCol C) _ U

theorem c2Of0_mem {κ : GardenDart G → (Fin d → ℤ)} {U' : Src.Object Src.γL (inlMol G.molecule)}
    (h : U' ∈ (C0 C).C2Of L γ η 0 κ (Un0 C L γ η κ)) :
    ∃ U, U' = objMap (ι := inlEmb _) U ∧ U ∈ (gCol C).C2Of L γ η 0 κ (unG C L γ η κ) := by
  obtain ⟨U, rfl⟩ := objMap_surjective (M := G.molecule) (ι := inlEmb _) U'
  exact ⟨U, rfl, (c2Of0_iff C κ U).1 h⟩

theorem collected0 {κ : GardenDart G → (Fin d → ℤ)} {U' : Src.Object Src.γL (inlMol G.molecule)}
    (h : Collected (C0 C) (Un0 C L γ η κ) L γ η 0 κ U') :
    ∃ U, U' = objMap (ι := inlEmb _) U ∧ Collected (gCol C) (unG C L γ η κ) L γ η 0 κ U := by
  rcases h with ⟨i, rfl⟩ | h
  · exact ⟨_, rfl, Or.inl ⟨i, rfl⟩⟩
  · obtain ⟨U, rfl⟩ := objMap_surjective (M := G.molecule) (ι := inlEmb _) U'
    exact ⟨U, rfl, Or.inr ((mem_collMap_c2Can (inlEmb _) (gCol C) _ U).1 h)⟩

/-! ### Garden-level facts at base `0` -/

variable {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)}

theorem unselOK_G (hadm : C.Admissible L γ η base κ) : (gCol C).UnselOK L γ η 0 κ (unG C L γ η κ) := by
  obtain ⟨rk, -, K, hK, -⟩ := hadm.2.1
  have h := unselOK_of_second8 (Mole.garden_isMolecule G) (gCol C) (L := L) (γ := γ) (η := η) (base := base)
    (omitted := C.omittedDVConstituents) hK
  rw [unselOf_base_eq (gCol C) L γ η base 0 κ, unselOK_base_iff (gCol C) L γ η base 0 κ] at h
  exact h

theorem c2Of_G_base {U : Src.Object Src.γL G.molecule} (hU : U ∈ (gCol C).C2Of L γ η 0 κ (unG C L γ η κ)) :
    U ∈ (gCol C).C2Of L γ η base κ (unselOf (gCol C) L γ η base κ C.omittedDVConstituents) := by
  rw [c2Of_base_eq (gCol C) L γ η base 0 κ, unselOf_base_eq (gCol C) L γ η base 0 κ]
  exact hU

theorem hd22_G {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hadm : C.Admissible L γ η base κ)
    {U U' : Src.Object Src.γL G.molecule} (hU : U ∈ (gCol C).C2Of L γ η 0 κ (unG C L γ η κ))
    (hU' : U' ∈ (gCol C).C2Of L γ η 0 κ (unG C L γ η κ)) : U.atoms = U'.atoms ∨ Disjoint U.atoms U'.atoms := by
  obtain ⟨rk, -, K, hK, -⟩ := hadm.2.1
  exact c2Of_atoms_eq_or_disjoint (Mole.garden_isMolecule G) hκ hc (gCol C) hK (c2Of_G_base C hU) (c2Of_G_base C hU')

theorem vcShape_G {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hadm : C.Admissible L γ η base κ)
    {U : Src.Object Src.γL G.molecule} (hU : U ∈ (gCol C).C2Of L γ η 0 κ (unG C L γ η κ)) (hvc : ∃ h, U.shape = .vc h) :
    Vine.DoubleChain G.molecule U.atoms U.upper U.lower 1 ∨ Vine.DoubleChain G.molecule U.atoms U.upper U.lower 2 ∨
      G.molecule.IsTVine U.atoms U.upper U.lower := by
  obtain ⟨⟨⟨hsg, hout, hdis, -⟩, -⟩, -⟩ := c2Of_G_base C (base := base) hU
  exact step1_vc_shape' G C.subpro L γ η base C.fixedRoots κ (supportA_of_support hadm.1) c hκ hc U hsg hout hdis hvc

theorem shape_G {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hadm : C.Admissible L γ η base κ)
    {U : Src.Object Src.γL G.molecule} (hU : U ∈ (gCol C).C2Of L γ η 0 κ (unG C L γ η κ)) :
    U.atoms.card = 3 ∨ ObjVine G.molecule U :=
  c2_shape C.subpro hκ hc hadm.1 (c2Of_G_base C hU)

theorem crit_G (hadm : C.Admissible L γ η base κ) {U : Src.Object Src.γL G.molecule}
    (hU : Collected (gCol C) (unG C L γ η κ) L γ η 0 κ U) {v : GBranch G.tree} (hv : U.IsInterior v) :
    ¬ C.CriticalSG v := by
  rcases hU with ⟨i, rfl⟩ | hU
  · exact not_critical_of_interior_c1 C hv
  · exact not_critical_of_interior_c2' C hadm.2.1 (c2Of_G_base C hU.1) hv

/-! ### The class-level inputs on `M₀ = inlMol G.molecule` -/

theorem hsh0 (hgeo : Src.CountingGeometry G C) {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hadm : C.Admissible L γ η base κ)
    {U' : Src.Object Src.γL (inlMol G.molecule)} (hU' : Collected (C0 C) (Un0 C L γ η κ) L γ η 0 κ U') :
    U'.atoms.card = 3 ∨ ObjVine (inlMol G.molecule) U' := by
  obtain ⟨U, rfl, hU⟩ := collected0 C hU'
  rw [objMap_atoms, Finset.card_map, objVine_objMap_iff]
  rcases hU with ⟨i, rfl⟩ | hU
  · exact Or.inr (objVine_of_allowed (hgeo.subpro.1 i))
  · exact shape_G C hκ hc hadm hU.1

theorem hcrit0 (hadm : C.Admissible L γ η base κ) {U' : Src.Object Src.γL (inlMol G.molecule)}
    (hU' : Collected (C0 C) (Un0 C L γ η κ) L γ η 0 κ U') :
    ∀ a ∈ U'.atoms, a ≠ U'.upper → a ≠ U'.lower → ¬ critMap (inlEmb _) C a := by
  obtain ⟨U, rfl, hU⟩ := collected0 C hU'
  intro a ha h1 h2
  rw [objMap_atoms] at ha
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.1 ha
  rw [critMap_iff]
  exact crit_G C hadm hU ⟨ha0, fun e => h1 (by rw [e]; rfl), fun e => h2 (by rw [e]; rfl)⟩

theorem obl0 (hadm : C.Admissible L γ η base κ) : SubproOblG (C0 C) L γ η 0 κ := by
  rw [collMap_subproOblG, subproOblG_base_indep (gCol C) L γ η 0 base κ]
  exact subproOblG_of_support hadm.1

theorem hsg_hinge0 (hadm : C.Admissible L γ η base κ) {U' : Src.Object Src.γL (inlMol G.molecule)}
    (hU' : Collected (C0 C) (Un0 C L γ η κ) L γ η 0 κ U') :
    U'.HasGapKind L γ η 0 κ .SG ∧ HingeData (C0 C) U' := by
  refine collected_sg_hinge (obl0 C hadm) (fun i => ?_) hU'
  show (objMap (ι := inlEmb _) (C.subpro.collection i)).HasGapKind L γ η 0 κ .SG
  rw [objMap_hasGapKind_iff, object_hasGapKind_base_indep _ L γ η 0 base κ]
  exact hadm.1.selectedSG i

theorem hFst0 {U' : Src.Object Src.γL (inlMol G.molecule)} (hU' : U' ∈ Fst0 C) : Collected (C0 C) (Un0 C L γ η κ) L γ η 0 κ U' := by
  obtain ⟨U, ⟨⟨i, rfl⟩, -⟩, rfl⟩ := hU'
  exact Or.inl ⟨i, rfl⟩

theorem hd22_0 {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hadm : C.Admissible L γ η base κ) :
    ∀ O ∈ (C0 C).C2Of L γ η 0 κ (Un0 C L γ η κ), ∀ O' ∈ (C0 C).C2Of L γ η 0 κ (Un0 C L γ η κ),
      O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms := by
  intro O hO O' hO'
  obtain ⟨U, rfl, hU⟩ := c2Of0_mem C hO
  obtain ⟨U', rfl, hU'⟩ := c2Of0_mem C hO'
  rw [objMap_atoms, objMap_atoms, Finset.map_inj, Finset.disjoint_map]
  exact hd22_G C hκ hc hadm hU hU'

theorem vcShape0 {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hadm : C.Admissible L γ η base κ) :
    ∀ O ∈ (C0 C).C2Of L γ η 0 κ (Un0 C L γ η κ), (∃ h, O.shape = .vc h) →
      Vine.DoubleChain (inlMol G.molecule) O.atoms O.upper O.lower 1 ∨
        Vine.DoubleChain (inlMol G.molecule) O.atoms O.upper O.lower 2 ∨
        (inlMol G.molecule).IsTVine O.atoms O.upper O.lower := by
  intro O hO hvc
  obtain ⟨U, rfl, hU⟩ := c2Of0_mem C hO
  rcases vcShape_G C hκ hc hadm hU ((objMap_shape_vc_iff (inlEmb _) U).1 hvc) with h | h | h
  · exact Or.inl (doubleChain_map G.molecule (inlEmb _) h)
  · exact Or.inr (Or.inl (doubleChain_map G.molecule (inlEmb _) h))
  · exact Or.inr (Or.inr ((DS.mapAtoms_isTVine G.molecule (inlEmb _) _ _ _).2 h))

theorem unselOK0 (hadm : C.Admissible L γ η base κ) : (C0 C).UnselOK L γ η 0 κ (Un0 C L γ η κ) :=
  (collMap_unselOK (inlEmb _) (gCol C) _).2 (unselOK_G C hadm)

theorem hdisj0 (hgeo : Src.CountingGeometry G C) {c : GBranch G.tree → Mom d} (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hadm : C.Admissible L γ η base κ)
    (U U' : Src.Object Src.γL (inlMol G.molecule)) (hU : Collected (C0 C) (Un0 C L γ η κ) L γ η 0 κ U)
    (hU' : Collected (C0 C) (Un0 C L γ η κ) L γ η 0 κ U') : SameDes U U' ∨ Disjoint U.atoms U'.atoms := by
  refine desDisj_of_parts (fun i j hij => ?_) (fun O hO i => (c2Of_disjoint_c1_hinges (C0 C) hO).1 i)
    (hd22_0 C hκ hc hadm) U U' hU hU'
  show Disjoint ((C.subpro.collection i).atoms.map (inlEmb _)) ((C.subpro.collection j).atoms.map (inlEmb _))
  rw [Finset.disjoint_map]
  exact hgeo.subpro.2.1 i j hij

end garden

end WaveTurbulence.GammaLow.FinalCount.H
