/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceGapKind
public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnitBlocks
import Mathlib.Tactic

/-!
# S2 REPRESENTS, UnitGap (1): every unit of a group has an external pair of the gap kind of the designated object

`HingeSpec G S a p` gives the external pair only for the unit containing the designated joint `a`.  `UnitSpec G S u p` is its
inner clause for an arbitrary unit `u`; `exists_unitSpec` produces it for every unit (units are disjoint, so the unit of
`HingeSpec` for `a := u.upper` is `u`), and `unitSpec_gapKind` is the proof of `hingeOrig_gapKind` with `u` general (the
designated joint `a` enters only through `IsDesig`): the gap of the pair `p` has the kind of the designated object.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w}

/-- The external pair of a given unit `u` (the inner clause of `HingeSpec`). -/
def UnitSpec (G : Garden w) (S : Finset (GBranch G.tree)) (u : CLBlock G) (p : GardenDart G × GardenDart G) : Prop :=
  ∃ j ∈ u.atoms,
    TripleAt G j p.1 p.2 ∧ ¬ G.molecule.InGroup u.atoms p.1 ∧ ¬ G.molecule.InGroup u.atoms p.2 ∧
    (∀ sk, (groupUnitsOf G S).skip = some sk → (j = sk.x ∨ j = sk.y) ∧
      G.molecule.atom (G.molecule.mate p.1) ∈ sk.A ∧ G.molecule.atom (G.molecule.mate p.2) ∈ sk.A ∧
      ∀ e, sk.bond = some e → p.1 ≠ e ∧ p.1 ≠ G.molecule.mate e ∧ p.2 ≠ e ∧ p.2 ≠ G.molecule.mate e) ∧
    ((groupUnitsOf G S).skip = none → u.atoms = S ∧ (j = u.upper ∨ j = u.lower))

theorem unit_eq_of_mem {S : Finset (GBranch G.tree)} {u u' : CLBlock G} (hu : u ∈ (groupUnitsOf G S).units)
    (hu' : u' ∈ (groupUnitsOf G S).units) {a : GBranch G.tree} (ha : a ∈ u.atoms) (ha' : a ∈ u'.atoms) : u = u' := by
  by_contra hne
  have : Std.Symm (fun u u' : CLBlock G => Disjoint u.atoms u'.atoms) := ⟨fun _ _ h => h.symm⟩
  have := List.Pairwise.forall (groupUnitsOf G S).disj hu hu' hne
  exact Finset.disjoint_left.mp this ha ha'

theorem exists_unitSpec {S : Finset (GBranch G.tree)} {u : CLBlock G} (hu : u ∈ (groupUnitsOf G S).units) :
    ∃ p, UnitSpec G S u p := by
  obtain ⟨p, hp⟩ := exists_hingeSpec (S := S) (a := u.upper) ⟨u, hu, u.isBlock.2.1⟩
  obtain ⟨u', hu', hau, j, hj, rest⟩ := hp
  have he := unit_eq_of_mem hu hu' u.isBlock.2.1 hau
  subst he
  exact ⟨p, j, hj, rest⟩

/-- **The gap of the external pair of any unit has the kind of the designated object**
(`hingeOrig_gapKind` for a general unit). -/
theorem unitSpec_gapKind (hM : G.molecule.IsMolecule) {S : Finset (GBranch G.tree)} {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    {a : GBranch G.tree} {u : CLBlock G} (hu : u ∈ (groupUnitsOf G S).units) {p : GardenDart G × GardenDart G}
    (hsp : UnitSpec G S u p)
    {O : Object G.molecule} (hdes : IsDesig G S a O) {k : Molecule.GapKind} (hk : O.HasGapKind L γ η w κ k) :
    Molecule.gapKind L γ η (Molecule.gapAt L w κ p.1 p.2) = k := by
  obtain ⟨hk1, hc1⟩ := kvec_cons L w c κ hκ hc0
  unfold UnitSpec at hsp
  obtain ⟨j, hj, hT, hn1, hn2, hrel⟩ := hsp
  obtain ⟨r, hr, rfl⟩ := hk
  unfold VineLikeObject.IsGap at hr
  unfold Molecule.gapAt
  rcases hsk : (groupUnitsOf G S).skip with _ | sk
  · -- the whole-group unit
    obtain ⟨hUS, hjw⟩ := hrel.2 hsk
    obtain ⟨hOS, hv, hshape⟩ := hdes.2.2.2.2.1 hsk (List.ne_nil_of_mem hu)
    have hB : G.molecule.IsBlock S u.upper u.lower := hUS ▸ u.isBlock
    have hn := ext_pair_norm' G.molecule hM hB hjw (Molecule.kvec L w κ) hk1 hc1 hT.1 hT.2.1
      (hUS ▸ hn1) (hUS ▸ hn2) hT.2.2.2
    have hB2 : G.molecule.IsBlock S O.upper O.lower := by rw [← hOS]; exact hv.1
    have hfn := flow_norm_joint G.molecule hM hB hB2 (Molecule.kvec L w κ) hk1 hc1
    rw [hshape] at hr
    have hOb : G.molecule.IsBlock O.atoms O.upper O.lower := hv.1
    refine kind_of_flow_norm G.molecule hOb L γ η w κ hr ?_
    rw [hOS]
    exact hn.trans hfn.symm
  · obtain ⟨hjxy, hm1, hm2, he⟩ := hrel.1 sk hsk
    have hjA : j ∈ sk.A := by
      obtain ⟨X, hX⟩ := sk.vine
      rcases hjxy with rfl | rfl
      · exact hX.1.2.1
      · exact hX.1.2.2.1
    have hg1 : G.molecule.InGroup sk.A p.1 := ⟨by rw [hT.1]; exact hjA, hm1⟩
    have hg2 : G.molecule.InGroup sk.A p.2 := ⟨by rw [hT.2.1]; exact hjA, hm2⟩
    rcases hb : sk.bond with _ | e
    · obtain ⟨n, hI⟩ := sk.chainM hb
      have hU := sk.blockM hb
      have hn := pair_norm_ingredient G.molecule hM hI hU hjxy (Molecule.kvec L w κ) hk1 hc1 hT.1 hT.2.1 hg1 hg2
        hT.2.2.2
      obtain ⟨hOS, hv, hshape⟩ := hdes.2.2.1 sk hsk hb
      have hB2 : G.molecule.IsBlock S O.upper O.lower := by rw [← hOS]; exact hv.1
      have hfn := flow_norm_joint G.molecule hM hU hB2 (Molecule.kvec L w κ) hk1 hc1
      rw [hshape] at hr
      refine kind_of_flow_norm G.molecule hv.1 L γ η w κ hr ?_
      rw [hOS]
      exact hn.trans hfn.symm
    · obtain ⟨n, hn2', hI⟩ := sk.chainN e hb
      obtain ⟨hends, hUN⟩ := sk.blockN e hb
      have hne' := Vine.ends_distinct_of_pair G.molecule e hends hUN.2.2.2.1
      have hN := Vine.eraseBond_isMolecule G.molecule hM e hne'
      obtain ⟨cN, hκN, hcN⟩ := Vine.eraseBond_decoration_exists G.molecule hM e hne' L w c κ hκ hc0
      obtain ⟨hk2, hc2⟩ := kvec_cons L w cN (fun z => κ z.1) hκN hcN
      obtain ⟨he1, he2, he3, he4⟩ := he e hb
      have hn := pair_norm_ingredient (eraseBond G.molecule e) hN hI hUN hjxy (Molecule.kvec L w (fun z => κ z.1))
        hk2 hc2 (x := ⟨p.1, he1, he2⟩) (y := ⟨p.2, he3, he4⟩) hT.1 hT.2.1 hg1 hg2 hT.2.2.2
      obtain ⟨hOS, R, hshape, hRe⟩ := hdes.2.2.2.1 sk e hsk hb
      rw [hshape] at hr
      have hOb : (eraseBond G.molecule e).IsBlock O.atoms O.upper O.lower := by
        have := R.adjoint.1
        rw [hRe] at this
        exact this
      change (eraseBond G.molecule R.added).IsBlockGap L w (fun z => κ z.1) O.atoms O.upper r at hr
      rw [hRe] at hr
      have hB2 : (eraseBond G.molecule e).IsBlock S O.upper O.lower := by rw [← hOS]; exact hOb
      have hfn := flow_norm_joint (eraseBond G.molecule e) hN hUN hB2 (Molecule.kvec L w (fun z => κ z.1)) hk2 hc2
      refine kind_of_flow_norm (eraseBond G.molecule e) hOb L γ η w (fun z => κ z.1) hr ?_
      rw [hOS]
      exact hn.trans hfn.symm

end WaveTurbulence.Represents
