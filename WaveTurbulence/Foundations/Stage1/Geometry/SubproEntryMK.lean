/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproEntry2R83
public import WaveTurbulence.Foundations.Vine.A.VineHingePairMK
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: the gap entry of an unmarked group lies in its `𝒞₁` object (Mk twins of SubproEntry2R83)

`entry_objMk` (main's `entry_obj`, with `gapSpecificationMk`): the entry of the group of an object of `𝒞₁`
(`objects G σ Mk`, unmarked groups only) lies inside the object at one of its joints; `obj_skip_dataMk` (main's
`obj_skip_data`).  Main's proofs, with the Mk twins of the unit/splice lemmas for unmarked groups.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)}

/-- The HV case: the designated object and the object of `C_1` share the canonical triple. -/
theorem entry_obj_hvMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) {Mk : Set (Stage1.CLVine G)} (hmkS : ¬ markedGroup G Mk S) {O : Object (stSt G σ Mk).G.molecule} {A : Finset (GBranch G.tree)}
    (hOa : O.atoms = A.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls))
    (hnm : ∀ z ∈ S, (stSt G σ Mk).cls z = none → z ∈ A)
    (hhv : ∃ a b, IsHV G.molecule S a b) (hnhvc : ¬ ∃ a b, IsHVC G.molecule S a b)
    (hnone : (groupUnitsOf G S).skip = none)
    {a0 b0 : GBranch G.tree} {e0 : GardenDart G} (hpk : hvGroupPick G S = some (a0, b0, e0))
    (hup : O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a0)
    {R0 : HyperLikeRealization (stSt G σ Mk).G.molecule O.atoms O.upper O.lower}
    (hR : O.shape = VineLikeObject.hyper R0) (hRe : (stSt G σ Mk).M.od R0.added = e0)
    {a : GBranch G.tree} (ha : groupJoint G S = some a)
    {e : LocalGapSpecification (stSt G σ Mk).G ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt G σ Mk).M.od e.first = p.1) (h2 : (stSt G σ Mk).M.od e.second = p.2)
    (hnh : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∉ (stSt G σ Mk).hinges → intPairOrig G S = some p ∧ IntSpec G S p) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = O.upper ∨ (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = O.lower) := by
  have hunits : (groupUnitsOf G S).units = [] := (groupUnitsOf G S).hv_empty hhv hnhvc
  have hnotH : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∉ (stSt G σ Mk).hinges := by
    intro hh
    obtain ⟨-, u, hu, -⟩ := hinge_unitMk hM σ hSm hmkS ha hh
    rw [hunits] at hu; cases hu
  obtain ⟨-, a1, Q, ha1, hQ, -, hT, hQ1, hQ2⟩ := hnh hnotH
  obtain ⟨a', ha', hdes⟩ := designatedObject_isDesig hQ
  rw [ha] at ha1 ha'
  cases ha1; cases ha'
  obtain ⟨b, e', hpk', hQa, -, R1, hR1, hR1e⟩ := hdes.2.2.2.2.2.1 hnone hunits hhv hnhvc
  rw [hpk] at hpk'
  obtain ⟨h_a, h_b, h_e⟩ : a = a0 ∧ b = b0 ∧ e' = e0 := by
    have := Option.some.inj hpk'
    simp only [Prod.mk.injEq] at this
    exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩
  subst h_a h_b h_e
  have hall : ∀ z ∈ S, (stSt G σ Mk).cls z = none := fun z hz =>
    stSt_cls_noneMk (Mk := Mk) hM σ (no_unit_hvMk hM σ hSm hhv hnhvc hmkS hz)
  have hcd : ∀ (f : GardenDart (stSt G σ Mk).G) (q : GardenDart G), (stSt G σ Mk).M.od f = q → Q.ContainsDart q →
      O.ContainsDart f := by
    intro f q hf hq
    unfold Object.ContainsDart at hq
    rw [hR1] at hq
    obtain ⟨n1, n2, hg⟩ := hq
    rw [hQa] at hg
    refine containsDart_of_origMk (Mk := Mk) σ hOa (A := A) (by rw [hf]; exact ⟨hnm _ hg.1 (hall _ hg.1), hnm _ hg.2 (hall _ hg.2)⟩) ?_
    intro R' hR'
    rw [hR] at hR'
    have hRR : R' = R0 := (VineLikeObject.hyper.inj hR').symm
    subst hRR
    rw [hRe, hf, ← hR1e]
    exact ⟨n1, n2⟩
  exact ⟨hcd _ _ h1 hQ1, hcd _ _ h2 hQ2, Or.inl hup.symm⟩

theorem left_trivialMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) {Mk : Set (Stage1.CLVine G)}
    (hmkS : ¬ markedGroup G Mk S)
    (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    (hnh : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.a ∉ (stSt G σ Mk).hinges) : sk.x = sk.a := by
  rcases sk.left with ⟨-, hx⟩ | ⟨-, haL, -, -⟩
  · exact hx
  · exfalso
    apply hnh
    rcases ((groupUnitsOf G S).skip_units sk hsk).2.1 with h0 | ⟨u, hu, hL⟩
    · rw [h0] at haL; cases haL
    · have hau : sk.a ∈ u.atoms := hL ▸ haL
      have huB : u ∈ unitBlocks G σ Mk :=
        mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (groupUnitsMk_of_not_marked hmkS).symm ▸ hu⟩
      rw [(stSt G σ Mk).mem_hinges, (stSt G σ Mk).M.ob_pi, stSt_repC_memMk (Mk := Mk) hM σ huB hau,
        stSt_cls_memMk (Mk := Mk) hM σ huB u.isBlock.2.1]
      simp

theorem entry_obj_nonhingeMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) {Mk : Set (Stage1.CLVine G)}
    (hmkS : ¬ markedGroup G Mk S)
    (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {O : Object (stSt G σ Mk).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls))
    (hup : O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.x)
    (hsh1 : sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ Mk).G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ (stSt G σ Mk).M.od R.added = e)
    {a : GBranch G.tree} (ha : groupJoint G S = some a)
    {e : LocalGapSpecification (stSt G σ Mk).G ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt G σ Mk).M.od e.first = p.1) (h2 : (stSt G σ Mk).M.od e.second = p.2)
    (hnh : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∉ (stSt G σ Mk).hinges → intPairOrig G S = some p ∧ IntSpec G S p)
    (hnotH : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∉ (stSt G σ Mk).hinges) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = O.upper ∨ (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = O.lower) := by
  have haa : a = sk.a := (groupJoint_spec ha).1 sk hsk
  subst haa
  have hxa := left_trivialMk hM σ hSm hσ hmkS sk hsk hnotH
  obtain ⟨-, a1, Q, ha1, hQ, -, hT, hQ1, hQ2⟩ := hnh hnotH
  obtain ⟨a', ha', hdes⟩ := designatedObject_isDesig hQ
  rw [ha] at ha1 ha'
  cases ha1; cases ha'
  -- the darts of `p` at `a` that are in `S` are in `A`
  have key : ∀ q : GardenDart G, G.molecule.atom q = sk.a → Q.ContainsDart q →
      (∀ e', sk.bond = some e' → q ≠ e' ∧ q ≠ G.molecule.mate e') ∧ G.molecule.InGroup sk.A q := by
    intro q hq hQq
    rcases hb : sk.bond with _ | e'
    · obtain ⟨hQS, hv, hsh⟩ := hdes.2.2.1 sk hsk hb
      unfold Object.ContainsDart at hQq
      rw [hsh] at hQq
      dsimp only at hQq
      refine ⟨(fun e' he' => by cases he'), ?_⟩
      have := skel_darts_in_A (sk.skelM hb) hxa (d := q) hq (by rw [hQS] at hQq; exact hQq)
      exact this
    · obtain ⟨hQS, R1, hR1, hR1e⟩ := hdes.2.2.2.1 sk e' hsk hb
      unfold Object.ContainsDart at hQq
      rw [hR1] at hQq
      obtain ⟨n1, n2, hg⟩ := hQq
      rw [hR1e] at n1 n2
      refine ⟨fun e'' he'' => ?_, ?_⟩
      · cases he''; exact ⟨n1, n2⟩
      · have := skel_darts_in_A (sk.skelN e' hb) hxa (d := ⟨q, n1, n2⟩) hq (by rw [hQS] at hg; exact hg)
        exact this
  obtain ⟨b1, g1⟩ := key p.1 hT.1 hQ1
  obtain ⟨b2, g2⟩ := key p.2 hT.2.1 hQ2
  refine ⟨containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h1]; exact g1)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h1]; exact b1 e' he')),
    containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h2]; exact g2)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h2]; exact b2 e' he')), ?_⟩
  rw [hxa] at hup
  exact Or.inl hup.symm

/-- **The entry of the gap specification of a group with an object `O` of `C_1` lies inside `O`**, at a joint of `O`. -/
theorem entry_objMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) {Mk : Set (Stage1.CLVine G)}
    {O : Object (stSt G σ Mk).G.molecule} (hO : objOf G σ S Mk = some O) :
    ∃ a, groupJoint G S = some a ∧
      ∃ e : LocalGapSpecification (stSt G σ Mk).G ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a),
        gapSpecificationMk G σ Mk ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a) = some e ∧ e.kind = σ S ∧
        O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
        ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = O.upper ∨ (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = O.lower) := by
  have hmkS : ¬ markedGroup G Mk S := objOf_not_marked (Option.mem_def.mpr hO)
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := gapSpecificationMk_group hM σ hSm hmkS
  obtain ⟨-, -, -, hSpec⟩ := objOf_specMk (Option.mem_def.mpr hO)
  obtain ⟨A, hAS, hOa, hnm, hsrc⟩ := hSpec.src
  refine ⟨a, ha, e, he, hk, ?_⟩
  rcases hsrc with ⟨⟨hhv, hnhvc⟩, hnone, a0, b0, e0, hpk, hup, hlo, R0, hR, hRe⟩ |
      ⟨sk, hsk, hAeq, hup, hlo, hsh1, hsh2⟩
  · exact entry_obj_hvMk hM σ hSm hmkS hOa hnm hhv hnhvc hnone hpk hup hR hRe ha h1 h2 hnh.2
  · subst hAeq
    by_cases hh : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∈ (stSt G σ Mk).hinges
    · exact entry_obj_hingeMk (Mk := Mk) hM σ sk hsk hOa hup hlo hsh1 hsh2 h1 h2 (hnh.1 hh).2
    · exact entry_obj_nonhingeMk hM σ hSm hσ hmkS sk hsk hOa hup hsh1 hsh2 ha h1 h2 hnh.2 hh

/-- If a hinge is a joint of an object of `C_1`, the group of its unit has a skipped vine and the object is its image. -/
theorem obj_skip_dataMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Stage1.CLVine G)}
    {O : Object (stSt G σ Mk).G.molecule} (hOm : O ∈ objects G σ Mk) {v : GBranch (stSt G σ Mk).G.tree} (hvO : v ∈ O.atoms)
    {S : Finset (GBranch G.tree)} (hSm : S ∈ maximalGroups G.molecule) {u : CLBlock G}
    (hu : u ∈ (groupUnitsOf G S).units) (hob : (stSt G σ Mk).M.ob v = u.upper) :
    ∃ sk : SkipData G S, (groupUnitsOf G S).skip = some sk ∧
      O.atoms = sk.A.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
      O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.x ∧ O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.y ∧
      (sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h) ∧
      (∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ Mk).G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ (stSt G σ Mk).M.od R.added = e) := by
  obtain ⟨S', -, hS'm, hO'⟩ := mem_objects'Mk hOm
  obtain ⟨-, -, -, hSpec⟩ := objOf_specMk (Option.mem_def.mpr hO')
  obtain ⟨z, hz, hvz⟩ := hSpec.atoms_sub v hvO
  have h1 : repC (stSt G σ Mk).cls z ∈ S' := repC_mem_groupMk hM σ hS'm hz
  have h2 : (stSt G σ Mk).M.ob v = repC (stSt G σ Mk).cls z := by rw [hvz, (stSt G σ Mk).M.ob_pi]
  have h3 : u.upper ∈ S := (groupUnitsOf G S).sub u hu u.isBlock.2.1
  have hSS : S' = S := by
    by_contra hne
    rw [h2] at hob
    exact Finset.disjoint_left.mp (groups_disjoint hM hS'm hSm hne) h1 (hob ▸ h3)
  subst hSS
  obtain ⟨A, -, hOa, -, hsrc⟩ := hSpec.src
  rcases hsrc with ⟨⟨hhv, hnh⟩, -⟩ | ⟨sk, hsk, hAeq, hup, hlo, hsh1, hsh2⟩
  · have := (groupUnitsOf G S').hv_empty hhv hnh
    rw [this] at hu; cases hu
  · subst hAeq
    exact ⟨sk, hsk, hOa, hup, hlo, hsh1, hsh2⟩

end WaveTurbulence.VineA.NormalizedSplice.Subpro
