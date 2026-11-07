/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceGap
public import WaveTurbulence.Foundations.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.Molecule.VineHyperMissingJoint
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), R25: the gap kind of the specified pair equals that of the designated object

`gapSpecification_gapKind_eq`: for each group `S` of `𝒞`, on a decoration `κ` of the ORIGINAL garden with the source
conservation (a `(c_v)`-decoration with `c_v = 0` at the atoms of degree four), the gap kind of the specified pair of
`gapSpecification` (computed from the labels `κ ∘ od` of `G_sb`) is the gap kind of the designated object
`designatedObject G S`.  Cases (R25(b)):
1. non-hinge joint: the pair is inside the designated object (`obj_pair_gapKind`);
2. hinge with a skipped vine `A`: the pair is a pair of `A` at a joint, the flow of the ingredient equals the flow of
   the chain (`pair_norm_ingredient`);
3. whole-group unit: the external out/in pair at the degree-four joint has gap `-(internal gap)`
   (`ext_pair_norm'`, charge `0` at degree-four atoms).
The gap kind depends only on the norm (`gapKind_eq_of_norm_eq`).  Hence, together with `object_hasGapKind_unique`
(one object, one kind), the indicator factor of the group in `splicedGapIndicator` is `[kind of the object = σ S]`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem kvec_cons {M : Molecule V D} (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) :
    (∀ x, Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x) ∧
    (∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x = 0) :=
  ⟨fun x => by simp only [Molecule.kvec, hκ.1 x], fun v hv hd => (hκ.2 v hv).trans (hc0 v hv hd)⟩

/-- **Case 1.** An out/in pair of darts inside an object, at one of its joints, has the gap kind of the object. -/
theorem obj_pair_gapKind (M : Molecule V D) (hM : M.IsMolecule) (L γ η : ℝ) (w : Mom d) (c : V → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    (O : Object M) {k : Molecule.GapKind} (hk : O.HasGapKind L γ η w κ k) {j : V}
    (hj : j = O.upper ∨ j = O.lower) {x y : D} (hx : M.atom x = j) (hy : M.atom y = j)
    (hcx : O.ContainsDart x) (hcy : O.ContainsDart y) (hne : M.out x ≠ M.out y) :
    Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = k := by
  obtain ⟨r, hr, rfl⟩ := hk
  obtain ⟨hk1, hc1⟩ := kvec_cons L w c κ hκ hc0
  unfold VineLikeObject.IsGap at hr
  unfold Object.ContainsDart at hcx hcy
  cases hs : O.shape with
  | vc hv =>
    rw [hs] at hr hcx hcy
    have hn := pair_norm_block' M hM hv.1 hj (Molecule.kvec L w κ) hk1 hc1 hx hy hcx hcy hne
    exact kind_of_flow_norm M hv.1 L γ η w κ hr hn
  | hyper R =>
    rw [hs] at hr hcx hcy
    obtain ⟨e, he, hadj⟩ := R
    have hne' := Vine.ends_distinct_of_pair M e he hadj.1.2.2.2.1
    have hN := Vine.eraseBond_isMolecule M hM e hne'
    obtain ⟨cN, hκN, hcN⟩ := Vine.eraseBond_decoration_exists M hM e hne' L w c κ hκ hc0
    obtain ⟨hk2, hc2⟩ := kvec_cons L w cN (fun z => κ z.1) hκN hcN
    have hn := pair_norm_block' (Mole.eraseBond M e) hN hadj.1 hj (Molecule.kvec L w (fun z => κ z.1)) hk2 hc2
      (x := ⟨x, hcx.1, hcx.2.1⟩) (y := ⟨y, hcy.1, hcy.2.1⟩) hx hy hcx.2.2 hcy.2.2 hne
    exact kind_of_flow_norm (Mole.eraseBond M e) hadj.1 L γ η w (fun z => κ z.1) hr hn

end generic

/-- **Cases 2 and 3.** The gap kind of the hinge pair equals that of the designated object. -/
theorem hingeOrig_gapKind (hM : G.molecule.IsMolecule) {S : Finset (GBranch G.tree)} {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hsp : HingeSpec G S a p)
    {O : Object G.molecule} (hdes : IsDesig G S a O) {k : Molecule.GapKind} (hk : O.HasGapKind L γ η w κ k) :
    Molecule.gapKind L γ η (Molecule.gapAt L w κ p.1 p.2) = k := by
  obtain ⟨hk1, hc1⟩ := kvec_cons L w c κ hκ hc0
  unfold HingeSpec at hsp
  obtain ⟨u, hu, hau, j, hj, hT, hn1, hn2, hrel⟩ := hsp
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

/-- **The bridge of R25 (W1b).**  For each group `S` of `𝒞` the entry of `gapSpecification` at the designated atom has
kind `σ S`, and its pair (computed from any labels `κsb = κ ∘ od` on the darts of `G_sb`, `κ` a conserving decoration
of the original garden) has the gap kind of the designated object `O`:
`gapKind (base + k(first) - (base + k(second))) = k` whenever `O.HasGapKind … k`.  Together with
`object_hasGapKind_unique`, the factor of the group in `splicedGapIndicator` is `[gap kind of O = σ S]`. -/
theorem gapSpecification_gapKind_eq (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (κsb : GardenDart (stSt G σ).G → (Fin d → ℤ)) (hlab : ∀ y, κsb y = κ ((stSt G σ).M.od y)) :
    ∃ a O, groupJoint G S = some a ∧ designatedObject G S = some O ∧
      ∃ e : LocalGapSpecification (stSt G σ).G ((stSt G σ).M.pi (stSt G σ).hcls a),
        gapSpecification G σ ((stSt G σ).M.pi (stSt G σ).hcls a) = some e ∧ e.kind = σ S ∧
        ∀ k, O.HasGapKind L γ η w κ k →
          Molecule.gapKind L γ η ((w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second))) = k := by
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := gapSpecification_group hM σ hS
  obtain ⟨a', O, ha', hO, hd⟩ := designatedObject_spec hS
  rw [ha] at ha'
  cases ha'
  refine ⟨a, O, ha, hO, e, he, hk, fun k hOk => ?_⟩
  have hgap : (w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second)) =
      Molecule.gapAt L w κ p.1 p.2 := by
    simp only [Molecule.gapAt, Molecule.kvec, hlab, h1, h2]
  rw [hgap]
  by_cases hh : (stSt G σ).M.pi (stSt G σ).hcls a ∈ (stSt G σ).hinges
  · obtain ⟨_, hsp⟩ := hnh.1 hh
    exact hingeOrig_gapKind hM L γ η w c κ hκ hc0 hsp hd hOk
  · obtain ⟨hp, hsp⟩ := hnh.2 hh
    unfold IntSpec at hsp
    obtain ⟨a1, O1, ha1, hO1, hOj, hT, hx, hy⟩ := hsp
    rw [hO] at hO1; cases hO1
    rw [ha] at ha1; cases ha1
    exact obj_pair_gapKind G.molecule hM L γ η w c κ hκ hc0 O hOk hOj hT.1 hT.2.1 hx hy hT.2.2.2

/-- **The indicator factor of a group.**  The gap kind of the specified pair equals the kind of the entry exactly when
the designated object has the prescribed kind `σ S`. -/
theorem gapSpecification_indicator_iff (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (κsb : GardenDart (stSt G σ).G → (Fin d → ℤ)) (hlab : ∀ y, κsb y = κ ((stSt G σ).M.od y)) :
    ∃ a O, groupJoint G S = some a ∧ designatedObject G S = some O ∧
      ∃ e : LocalGapSpecification (stSt G σ).G ((stSt G σ).M.pi (stSt G σ).hcls a),
        gapSpecification G σ ((stSt G σ).M.pi (stSt G σ).hcls a) = some e ∧
        ∀ k, O.HasGapKind L γ η w κ k →
          (Molecule.gapKind L γ η ((w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second))) = e.kind
            ↔ k = σ S) := by
  obtain ⟨a, O, ha, hO, e, he, hk, hgap⟩ := gapSpecification_gapKind_eq hM σ hS L γ η w c κ hκ hc0 κsb hlab
  exact ⟨a, O, ha, hO, e, he, fun k hOk => by rw [hgap k hOk, hk]⟩

end WaveTurbulence.RedSplice
