/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
-- R83 port of sp-src/SubproEntry2.lean (FLOWER-P6 R83): successor designations, see HANDOFF

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproEntryR83
import Mathlib.Tactic

/-!
# SUBPRO (S4): `entry_obj`, the entry of the gap specification of a group with a `C_1` object lies inside the object
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
theorem entry_obj_hv (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) {O : Object (stSt G σ).G.molecule} {A : Finset (GBranch G.tree)}
    (hOa : O.atoms = A.image ((stSt G σ).M.pi (stSt G σ).hcls))
    (hnm : ∀ z ∈ S, (stSt G σ).cls z = none → z ∈ A)
    (hhv : ∃ a b, IsHV G.molecule S a b) (hnhvc : ¬ ∃ a b, IsHVC G.molecule S a b)
    (hnone : (groupUnitsOf G S).skip = none)
    {a0 b0 : GBranch G.tree} {e0 : GardenDart G} (hpk : hvGroupPick G S = some (a0, b0, e0))
    (hup : O.upper = (stSt G σ).M.pi (stSt G σ).hcls a0)
    {R0 : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower}
    (hR : O.shape = VineLikeObject.hyper R0) (hRe : (stSt G σ).M.od R0.added = e0)
    {a : GBranch G.tree} (ha : groupJoint G S = some a)
    {e : LocalGapSpecification (stSt G σ).G ((stSt G σ).M.pi (stSt G σ).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt G σ).M.od e.first = p.1) (h2 : (stSt G σ).M.od e.second = p.2)
    (hnh : (stSt G σ).M.pi (stSt G σ).hcls a ∉ (stSt G σ).hinges → intPairOrig G S = some p ∧ IntSpec G S p) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt G σ).M.pi (stSt G σ).hcls a = O.upper ∨ (stSt G σ).M.pi (stSt G σ).hcls a = O.lower) := by
  have hunits : (groupUnitsOf G S).units = [] := (groupUnitsOf G S).hv_empty hhv hnhvc
  have hnotH : (stSt G σ).M.pi (stSt G σ).hcls a ∉ (stSt G σ).hinges := by
    intro hh
    obtain ⟨-, u, hu, -⟩ := hinge_unit hM σ hSm ha hh
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
  have hall : ∀ z ∈ S, (stSt G σ).cls z = none := fun z hz =>
    stSt_cls_none hM σ (no_unit_hv hM σ hSm hhv hnhvc hz)
  have hcd : ∀ (f : GardenDart (stSt G σ).G) (q : GardenDart G), (stSt G σ).M.od f = q → Q.ContainsDart q →
      O.ContainsDart f := by
    intro f q hf hq
    unfold Object.ContainsDart at hq
    rw [hR1] at hq
    obtain ⟨n1, n2, hg⟩ := hq
    rw [hQa] at hg
    refine containsDart_of_orig σ hOa (A := A) (by rw [hf]; exact ⟨hnm _ hg.1 (hall _ hg.1), hnm _ hg.2 (hall _ hg.2)⟩) ?_
    intro R' hR'
    rw [hR] at hR'
    have hRR : R' = R0 := (VineLikeObject.hyper.inj hR').symm
    subst hRR
    rw [hRe, hf, ← hR1e]
    exact ⟨n1, n2⟩
  exact ⟨hcd _ _ h1 hQ1, hcd _ _ h2 hQ2, Or.inl hup.symm⟩

/-- B1b (Mk-general form of `hsh_skip`). -/
theorem hsh_skipMk (σ : Prescription G) {S : Finset (GBranch G.tree)} (sk : SkipData G S)
    {Mk : Set (Stage1.CLVine _)} {O : Object (stSt (Mk := Mk) G σ).G.molecule}
    (hsh1 : sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt (Mk := Mk) G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ (stSt (Mk := Mk) G σ).M.od R.added = e)
    {f : GardenDart (stSt (Mk := Mk) G σ).G}
    (hbond : ∀ e, sk.bond = some e → (stSt (Mk := Mk) G σ).M.od f ≠ e ∧ (stSt (Mk := Mk) G σ).M.od f ≠ G.molecule.mate e) :
    ∀ R', O.shape = VineLikeObject.hyper R' →
      (stSt (Mk := Mk) G σ).M.od f ≠ (stSt (Mk := Mk) G σ).M.od R'.added ∧
        (stSt (Mk := Mk) G σ).M.od f ≠ G.molecule.mate ((stSt (Mk := Mk) G σ).M.od R'.added) := by
  intro R' hR'
  rcases hb : sk.bond with _ | e
  · obtain ⟨h, hh⟩ := hsh1 hb
    rw [hh] at hR'; cases hR'
  · obtain ⟨R'', hR'', hRe⟩ := hsh2 e hb
    rw [hR''] at hR'
    have : R'' = R' := VineLikeObject.hyper.inj hR'
    subst this
    rw [hRe]
    exact hbond e hb

theorem hsh_skip (σ : Prescription G) {S : Finset (GBranch G.tree)} (sk : SkipData G S)
    {O : Object (stSt G σ).G.molecule}
    (hsh1 : sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e)
    {f : GardenDart (stSt G σ).G}
    (hbond : ∀ e, sk.bond = some e → (stSt G σ).M.od f ≠ e ∧ (stSt G σ).M.od f ≠ G.molecule.mate e) :
    ∀ R', O.shape = VineLikeObject.hyper R' →
      (stSt G σ).M.od f ≠ (stSt G σ).M.od R'.added ∧
        (stSt G σ).M.od f ≠ G.molecule.mate ((stSt G σ).M.od R'.added) := hsh_skipMk (Mk := ∅) σ sk hsh1 hsh2 hbond

theorem x_mem_A {S : Finset (GBranch G.tree)} (sk : SkipData G S) : sk.x ∈ sk.A ∧ sk.y ∈ sk.A := by
  obtain ⟨X, hX⟩ := sk.vine
  exact ⟨hX.1.2.1, hX.1.2.2.1⟩

/-- B1b (Mk-general form of `entry_obj_hinge`). -/
theorem entry_obj_hingeMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {Mk : Set (Stage1.CLVine _)} {O : Object (stSt (Mk := Mk) G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls))
    (hup : O.upper = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls sk.x) (hlo : O.lower = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls sk.y)
    (hsh1 : sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt (Mk := Mk) G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ (stSt (Mk := Mk) G σ).M.od R.added = e)
    {a : GBranch G.tree}
    {e : LocalGapSpecification (stSt (Mk := Mk) G σ).G ((stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt (Mk := Mk) G σ).M.od e.first = p.1) (h2 : (stSt (Mk := Mk) G σ).M.od e.second = p.2)
    (hsp : HingeSpec G S a p) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls a = O.upper ∨ (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls a = O.lower) := by
  obtain ⟨u, hu, hau, j, hj, hT, hn1, hn2, hrel⟩ := hsp
  obtain ⟨hjxy, hm1, hm2, hbond⟩ := hrel.1 sk hsk
  obtain ⟨hxA, hyA⟩ := x_mem_A sk
  have hjA : j ∈ sk.A := by rcases hjxy with rfl | rfl; exact hxA; exact hyA
  have hg1 : G.molecule.InGroup sk.A p.1 := ⟨hT.1 ▸ hjA, hm1⟩
  have hg2 : G.molecule.InGroup sk.A p.2 := ⟨hT.2.1 ▸ hjA, hm2⟩
  refine ⟨containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h1]; exact hg1)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h1]; exact ⟨(hbond e' he').1, (hbond e' he').2.1⟩)),
    containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h2]; exact hg2)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h2]; exact ⟨(hbond e' he').2.2.1, (hbond e' he').2.2.2⟩)), ?_⟩
  have hat : (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls a = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls j := by
    rw [← e.at_first, (atom_eq_piMk (Mk := Mk) σ e.first).1, h1, hT.1]
  rw [hat]
  rcases hjxy with rfl | rfl
  · exact Or.inl hup.symm
  · exact Or.inr hlo.symm

/-- The merged-first-joint case: a pair of the skipped vine at a hinge. -/
theorem entry_obj_hinge (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {O : Object (stSt G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt G σ).M.pi (stSt G σ).hcls))
    (hup : O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk.x) (hlo : O.lower = (stSt G σ).M.pi (stSt G σ).hcls sk.y)
    (hsh1 : sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e)
    {a : GBranch G.tree}
    {e : LocalGapSpecification (stSt G σ).G ((stSt G σ).M.pi (stSt G σ).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt G σ).M.od e.first = p.1) (h2 : (stSt G σ).M.od e.second = p.2)
    (hsp : HingeSpec G S a p) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt G σ).M.pi (stSt G σ).hcls a = O.upper ∨ (stSt G σ).M.pi (stSt G σ).hcls a = O.lower) := entry_obj_hingeMk (Mk := ∅) hM σ sk hsk hOa hup hlo hsh1 hsh2 h1 h2 hsp

/-- A non-hinge group joint of a group with a skipped vine has `L0 = ∅` and `x = a`. -/
theorem left_trivial (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    (hnh : (stSt G σ).M.pi (stSt G σ).hcls sk.a ∉ (stSt G σ).hinges) : sk.x = sk.a := by
  rcases sk.left with ⟨-, hx⟩ | ⟨-, haL, -, -⟩
  · exact hx
  · exfalso
    apply hnh
    rcases ((groupUnitsOf G S).skip_units sk hsk).2.1 with h0 | ⟨u, hu, hL⟩
    · rw [h0] at haL; cases haL
    · have hau : sk.a ∈ u.atoms := hL ▸ haL
      have huB : u ∈ unitBlocks G σ := mem_unitBlocks.mpr ⟨S, hSm, hσ, hu⟩
      rw [(stSt G σ).mem_hinges, (stSt G σ).M.ob_pi, stSt_repC_mem hM σ huB hau,
        stSt_cls_mem hM σ huB u.isBlock.2.1]
      simp

theorem entry_obj_nonhinge (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {O : Object (stSt G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt G σ).M.pi (stSt G σ).hcls))
    (hup : O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk.x)
    (hsh1 : sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e)
    {a : GBranch G.tree} (ha : groupJoint G S = some a)
    {e : LocalGapSpecification (stSt G σ).G ((stSt G σ).M.pi (stSt G σ).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (stSt G σ).M.od e.first = p.1) (h2 : (stSt G σ).M.od e.second = p.2)
    (hnh : (stSt G σ).M.pi (stSt G σ).hcls a ∉ (stSt G σ).hinges → intPairOrig G S = some p ∧ IntSpec G S p)
    (hnotH : (stSt G σ).M.pi (stSt G σ).hcls a ∉ (stSt G σ).hinges) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((stSt G σ).M.pi (stSt G σ).hcls a = O.upper ∨ (stSt G σ).M.pi (stSt G σ).hcls a = O.lower) := by
  have haa : a = sk.a := (groupJoint_spec ha).1 sk hsk
  subst haa
  have hxa := left_trivial hM σ hSm hσ sk hsk hnotH
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
  refine ⟨containsDart_of_orig σ hOa (by rw [h1]; exact g1)
      (hsh_skip σ sk hsh1 hsh2 (by intro e' he'; rw [h1]; exact b1 e' he')),
    containsDart_of_orig σ hOa (by rw [h2]; exact g2)
      (hsh_skip σ sk hsh1 hsh2 (by intro e' he'; rw [h2]; exact b2 e' he')), ?_⟩
  rw [hxa] at hup
  exact Or.inl hup.symm

/-- **The entry of the gap specification of a group with an object `O` of `C_1` lies inside `O`**, at a joint of `O`. -/
theorem entry_obj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) {O : Object (stSt G σ).G.molecule}
    (hO : objOf G σ S = some O) :
    ∃ a, groupJoint G S = some a ∧
      ∃ e : LocalGapSpecification (stSt G σ).G ((stSt G σ).M.pi (stSt G σ).hcls a),
        gapSpecification G σ ((stSt G σ).M.pi (stSt G σ).hcls a) = some e ∧ e.kind = σ S ∧
        O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
        ((stSt G σ).M.pi (stSt G σ).hcls a = O.upper ∨ (stSt G σ).M.pi (stSt G σ).hcls a = O.lower) := by
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := gapSpecification_group hM σ hSm
  obtain ⟨-, -, -, hSpec⟩ := objOf_spec (Option.mem_def.mpr hO)
  obtain ⟨A, hAS, hOa, hnm, hsrc⟩ := hSpec.src
  refine ⟨a, ha, e, he, hk, ?_⟩
  rcases hsrc with ⟨⟨hhv, hnhvc⟩, hnone, a0, b0, e0, hpk, hup, hlo, R0, hR, hRe⟩ |
      ⟨sk, hsk, hAeq, hup, hlo, hsh1, hsh2⟩
  · exact entry_obj_hv hM σ hSm hOa hnm hhv hnhvc hnone hpk hup hR hRe ha h1 h2 hnh.2
  · subst hAeq
    by_cases hh : (stSt G σ).M.pi (stSt G σ).hcls a ∈ (stSt G σ).hinges
    · exact entry_obj_hinge hM σ sk hsk hOa hup hlo hsh1 hsh2 h1 h2 (hnh.1 hh).2
    · exact entry_obj_nonhinge hM σ hSm hσ sk hsk hOa hup hsh1 hsh2 ha h1 h2 hnh.2 hh

/-- B1b (Mk-general form of `hinge_dart_obj`). -/
theorem hinge_dart_objMk (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {Mk : Set (Stage1.CLVine _)} {O : Object (stSt (Mk := Mk) G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls))
    (hup : O.upper = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls sk.x) (hlo : O.lower = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls sk.y)
    (hsh1 : sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt (Mk := Mk) G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ (stSt (Mk := Mk) G σ).M.od R.added = e)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hsp : HingeSpec G S a p)
    {f1 f2 : GardenDart (stSt (Mk := Mk) G σ).G} (h1 : (stSt (Mk := Mk) G σ).M.od f1 = p.1) (h2 : (stSt (Mk := Mk) G σ).M.od f2 = p.2) :
    O.ContainsDart f1 ∧ O.ContainsDart f2 ∧
      ((stSt (Mk := Mk) G σ).G.molecule.atom f1 = O.upper ∨ (stSt (Mk := Mk) G σ).G.molecule.atom f1 = O.lower) := by
  obtain ⟨u, hu, hau, j, hj, hT, hn1, hn2, hrel⟩ := hsp
  obtain ⟨hjxy, hm1, hm2, hbond⟩ := hrel.1 sk hsk
  obtain ⟨hxA, hyA⟩ := x_mem_A sk
  have hjA : j ∈ sk.A := by rcases hjxy with rfl | rfl; exact hxA; exact hyA
  have hg1 : G.molecule.InGroup sk.A p.1 := ⟨hT.1 ▸ hjA, hm1⟩
  have hg2 : G.molecule.InGroup sk.A p.2 := ⟨hT.2.1 ▸ hjA, hm2⟩
  refine ⟨containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h1]; exact hg1)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h1]; exact ⟨(hbond e' he').1, (hbond e' he').2.1⟩)),
    containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h2]; exact hg2)
      (hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h2]; exact ⟨(hbond e' he').2.2.1, (hbond e' he').2.2.2⟩)), ?_⟩
  rw [(atom_eq_piMk (Mk := Mk) σ f1).1, h1, hT.1]
  rcases hjxy with rfl | rfl
  · exact Or.inl hup.symm
  · exact Or.inr hlo.symm

/-- The darts of a `HingeSpec` pair of a unit of a skipped-vine group lie inside the residual object, at a joint. -/
theorem hinge_dart_obj (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {O : Object (stSt G σ).G.molecule}
    (hOa : O.atoms = sk.A.image ((stSt G σ).M.pi (stSt G σ).hcls))
    (hup : O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk.x) (hlo : O.lower = (stSt G σ).M.pi (stSt G σ).hcls sk.y)
    (hsh1 : sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hsp : HingeSpec G S a p)
    {f1 f2 : GardenDart (stSt G σ).G} (h1 : (stSt G σ).M.od f1 = p.1) (h2 : (stSt G σ).M.od f2 = p.2) :
    O.ContainsDart f1 ∧ O.ContainsDart f2 ∧
      ((stSt G σ).G.molecule.atom f1 = O.upper ∨ (stSt G σ).G.molecule.atom f1 = O.lower) := hinge_dart_objMk (Mk := ∅) σ sk hsk hOa hup hlo hsh1 hsh2 hsp h1 h2

/-- If a hinge is a joint of an object of `C_1`, the group of its unit has a skipped vine and the object is its image. -/
theorem obj_skip_data (hM : G.molecule.IsMolecule) (σ : Prescription G) {O : Object (stSt G σ).G.molecule}
    (hOm : O ∈ objects G σ) {v : GBranch (stSt G σ).G.tree} (hvO : v ∈ O.atoms)
    {S : Finset (GBranch G.tree)} (hSm : S ∈ maximalGroups G.molecule) {u : CLBlock G}
    (hu : u ∈ (groupUnitsOf G S).units) (hob : (stSt G σ).M.ob v = u.upper) :
    ∃ sk : SkipData G S, (groupUnitsOf G S).skip = some sk ∧
      O.atoms = sk.A.image ((stSt G σ).M.pi (stSt G σ).hcls) ∧
      O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk.x ∧ O.lower = (stSt G σ).M.pi (stSt G σ).hcls sk.y ∧
      (sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h) ∧
      (∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e) := by
  obtain ⟨S', -, hS'm, hO'⟩ := mem_objects' hOm
  obtain ⟨-, -, -, hSpec⟩ := objOf_spec (Option.mem_def.mpr hO')
  obtain ⟨z, hz, hvz⟩ := hSpec.atoms_sub v hvO
  have h1 : repC (stSt G σ).cls z ∈ S' := repC_mem_group hM σ hS'm hz
  have h2 : (stSt G σ).M.ob v = repC (stSt G σ).cls z := by rw [hvz, (stSt G σ).M.ob_pi]
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
