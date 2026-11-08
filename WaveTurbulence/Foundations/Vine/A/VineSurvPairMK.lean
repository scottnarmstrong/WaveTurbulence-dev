/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineSurvSGMK
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: the designated pair at a survivor joint (o75 Theorem 7.5′(5), 75-F1; `SubproSupportMK.jointPair`)

At every joint `v` of a survivor (hinge or not), the chosen pair `(collectionChoices G σ Mk).first/second v` is the
lift of a pair of the first survivor (in `survObjs` order) having `v` as a joint, so both darts are bonds of that
survivor (`jointPair_survObjs`).  This is branch 0 of `hingePair` (`survPairAt`, ruling R171).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- A vine has an out/in pair of darts inside it at each of its joints. -/
theorem exists_survPairSpec_joint {T : Finset (GBranch G.tree)} {j l k : GBranch G.tree}
    (hT : Vine.IsSomeVine G.molecule T j l) (hk : k = j ∨ k = l) : ∃ p, SurvPairSpec G T k p := by
  obtain ⟨X, hX⟩ := hT
  let O : Object G.molecule := ⟨T, j, l, .vc ⟨hX.1, 1, Chain.single ⟨X, hX⟩⟩⟩
  obtain ⟨x, y, hxy, hx, hy⟩ := objectJoint_pair O (v := k) hk
  exact ⟨(x, y), hxy, hx, hy⟩

/-- `survJointAt` finds the first survivor with a joint image at `v`. -/
theorem survJointAt_first {σ : Prescription G} {Mk : Set (CLVine G)} {i : ℕ} (hi : i < (survivorsMk G σ Mk).length)
    {v : GBranch (stSt G σ Mk).G.tree}
    (hv : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.1 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.2 = v)
    (hfirst : ∀ j (hj : j < i), ¬ ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.1 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.2 = v)) :
    ∃ j, survJointAt G σ v = some ((survivorsMk G σ Mk)[i].1, j) ∧
      (j = (survivorsMk G σ Mk)[i].2.1 ∨ j = (survivorsMk G σ Mk)[i].2.2) ∧
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls j = v := by
  classical
  have key : ∀ p : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree → Bool,
      (∀ t, p t = true ↔ ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.2 = v ∨
        (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 = v)) →
      (survivorsMk G σ Mk).find? p = some (survivorsMk G σ Mk)[i] := by
    intro p hp
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨(hp _).mpr hv.symm, i, hi, rfl, fun j hj => ?_⟩
    have := hfirst j (by omega)
    rw [Bool.not_eq_true']
    by_contra hc
    exact this ((hp _).mp (Bool.not_eq_false _ ▸ hc)).symm
  unfold survJointAt
  rw [key _ (fun t => by simp)]
  by_cases h2 : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.2 = v
  · exact ⟨_, by simp [h2], Or.inr rfl, h2⟩
  · exact ⟨_, by simp [h2], Or.inl rfl, hv.resolve_right h2⟩

theorem hingePair_of_survPairAt {σ : Prescription G} {Mk : Set (CLVine G)} {v : GBranch (stSt G σ Mk).G.tree}
    {q : GardenDart (stSt G σ Mk).G × GardenDart (stSt G σ Mk).G} (h : survPairAt G σ v = some q) :
    hingePair G σ v = some q := by
  classical
  have h0 : ∃ q, survPairAt G σ v = some q := ⟨q, h⟩
  unfold hingePair
  rw [dite_eq_left h0]
  exact congrArg some (Option.some.inj (h0.choose_spec.symm.trans h))

section main
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
include hM

/-- **75-F1 at a survivor joint**: the hinge pair at a joint `v` of the `i`-th survivor, the first one with a joint at
`v`, is the lift of a pair of bonds of that survivor. -/
theorem hingePair_survFirst {i : ℕ} (hi : i < (survivorsMk G σ Mk).length) {v : GBranch (stSt G σ Mk).G.tree}
    (hv : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.1 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.2 = v)
    (hfirst : ∀ j (hj : j < i), ¬ ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.1 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.2 = v)) :
    ∃ q, hingePair G σ v = some q ∧ TripleAt (stSt G σ Mk).G v q.1 q.2 ∧
      G.molecule.InGroup (survivorsMk G σ Mk)[i].1 ((stSt G σ Mk).M.od q.1) ∧
      G.molecule.InGroup (survivorsMk G σ Mk)[i].1 ((stSt G σ Mk).M.od q.2) := by
  classical
  have ht : (survivorsMk G σ Mk)[i] ∈ survivorsMk G σ Mk := List.getElem_mem hi
  obtain ⟨S, hS, -, hmk, htm, -⟩ := survivorsMk_group ht
  obtain ⟨hvine, -, -⟩ := (markedUnitsOfMK hmk).surv_spec _ htm
  obtain ⟨j, hJ, hjt, hjv⟩ := survJointAt_first hi hv hfirst
  obtain ⟨p, hp, hsp⟩ := survOrigPair_isSome (exists_survPairSpec_joint hvine hjt)
  obtain ⟨⟨hpx, hpy, hpne, hpout⟩, hgx, hgy⟩ := hsp
  have hrep : ∀ z : GardenDart G, G.molecule.atom z = j →
      repC (stSt G σ Mk).cls (G.molecule.atom z) = (stSt G σ Mk).M.ob v := by
    intro z hz
    rw [hz, ← hjv]
    exact ((stSt G σ Mk).M.ob_pi (stSt G σ Mk).hcls _).symm
  obtain ⟨y1, y2, hy1, hy2, hT'⟩ := (stSt G σ Mk).M.tripleAt_of_lift (c := v) (d1 := p.1) (d2 := p.2)
    (hrep p.1 hpx) (hrep p.2 hpy) (survDart_not_internal hM σ hS hmk htm hgx (by rw [hpx]; exact hjt))
    (survDart_not_internal hM σ hS hmk htm hgy (by rw [hpy]; exact hjt)) hpout hpne
  obtain ⟨q, hq, hq1, hq2, hqT⟩ := liftPair_of_existsMk (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hT'⟩
  have hsq : survPairAt G σ v = some q := by
    unfold survPairAt
    rw [hJ, Option.bind_some]
    simp only
    rw [hp, Option.bind_some]
    exact hq
  exact ⟨q, hingePair_of_survPairAt hsq, hqT, hq1 ▸ hgx, hq2 ▸ hgy⟩

/-- **`SubproSupportMK.jointPair`** (o75 Theorem 7.5′(5), 75-F1) for `S.surv := (survObjs G σ Mk).get` and
`C := collectionChoices G σ Mk`: at a joint `v` of the survivor `i`, the first one with joint `v`, the chosen pair
consists of bonds of that survivor. -/
theorem jointPair_survObjs (i : Fin (survObjs G σ Mk).length) (v : GBranch (stSt G σ Mk).G.tree)
    (hv : v = ((survObjs G σ Mk).get i).upper ∨ v = ((survObjs G σ Mk).get i).lower)
    (hfirst : ∀ j : Fin (survObjs G σ Mk).length, j < i →
      ¬ (v = ((survObjs G σ Mk).get j).upper ∨ v = ((survObjs G σ Mk).get j).lower)) :
    HasChosenPair ((collectionChoices G σ Mk).first v) ((collectionChoices G σ Mk).second v)
      (fun x y => ((survObjs G σ Mk).get i).ContainsDart x ∧ ((survObjs G σ Mk).get i).ContainsDart y) := by
  obtain ⟨i', hi', hii, hgi⟩ := survObjs_get i
  have hlen := survObjs_length G σ Mk
  have hget : ∀ (k : Fin (survivorsMk G σ Mk).length), (survivorsMk G σ Mk).get k = (survivorsMk G σ Mk)[k.val] :=
    fun k => List.get_eq_getElem
  have hv' : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i'.val].2.1 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i'.val].2.2 = v := by
    rw [hgi, (survObj_spec hi').2.1, (survObj_spec hi').2.2.1, hget] at hv
    exact hv.symm.imp Eq.symm Eq.symm |>.symm
  have hfirst' : ∀ j (hj : j < i'.val), ¬ ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.1 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.2 = v) := by
    intro j hj hc
    have hjl : j < (survObjs G σ Mk).length := by rw [hlen]; exact lt_trans hj i'.2
    obtain ⟨j', hj', hjj, hgj⟩ := survObjs_get ⟨j, hjl⟩
    apply hfirst ⟨j, hjl⟩ (Fin.lt_def.mpr (by simp only; omega))
    rw [hgj, (survObj_spec hj').2.1, (survObj_spec hj').2.2.1, hget]
    have e : j'.val = j := hjj
    simp only [e]
    exact hc.imp Eq.symm Eq.symm
  obtain ⟨q, hq, -, h1, h2⟩ := hingePair_survFirst hM σ i'.2 hv' hfirst'
  rw [← hget] at h1 h2
  refine ⟨q.1, q.2, by simp [collectionChoices, hq], by simp [collectionChoices, hq], ?_, ?_⟩
  · rw [hgi]; exact survObj_containsDart hM σ hi' h1
  · rw [hgi]; exact survObj_containsDart hM σ hi' h2

end main

end WaveTurbulence.VineA.NormalizedSplice
