/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.End2

/-! # C1b1 MK-PHASE1 (12): transporting an object of `M₀` to the state along a renaming (coverage, part 1)

Main transports an **intact** object `U` to the state by the identity on atoms (`stateIso`, AsmTransport;
`stateObj_spec` AsmVN3; `singleVineVC_of_objVine` AsmVN13; `vineDataL_of_intact` LowChain22). A survivor with a
pending re-cut joint is present only through a renaming `π`: its shared joint `v` is represented by the remnant `r`
(`anc r = v`). `MatchA h U π` records what is needed: `π` is injective on `U.atoms`, lands in the present atoms, is a
section of `anc`, and every group dart of `U` is present. Then:

* `stateIsoA` : the induced isomorphism of `M₀` on `U.atoms` with the state on `U.atoms.image π`;
* `stateObjA_spec`: the transported object (atoms `image π`, joints `π U.upper`, `π U.lower`, darts through `down`);
* `singleVineVCA`: a vine object stays a single vine (main's proof with `π`);
* `vineDataA`: a vine cut of the state along the transported object, with fresh names, node darts in `U`, the joint
  pairs, the `SG` gap and the twin relation (main's `vineDataL_of_intact` with `π`).

For an intact object `π = id` (`matchA_of_intact`). Copied by source (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section transport
variable {M₀ : Molecule V D₀}

/-- An object `U` of `M₀` present in the state through the renaming `π`. -/
structure MatchA (h : HSt V D₀) (U : Object M₀) (π : V → V) : Prop where
  inj : Set.InjOn π U.atoms
  mem : ∀ a ∈ U.atoms, π a ∈ h.s.M.atoms
  anc : ∀ a ∈ U.atoms, h.anc (π a) = a
  lift : ∀ z : D₀, M₀.InGroup U.atoms z → ∃ y : h.s.D, h.s.down y = z

variable {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
  (hinj : ∀ c ∈ h.s.M.atoms, ∀ e ∈ h.s.M.atoms, h.anc c = h.anc e → c = e) {U : Object M₀} {π : V → V}
  (hm : MatchA h U π)
include hA hD hinj hm

/-- A present dart whose `M₀` atom lies in `U` sits at the renamed atom. -/
theorem MatchA.atom_eq {y : h.s.D} (hy : M₀.atom (h.s.down y) ∈ U.atoms) :
    h.s.M.atom y = π (M₀.atom (h.s.down y)) := by
  refine hinj _ (h.s.M.atom_mem y) _ (hm.mem _ hy) ?_
  rw [hm.anc _ hy, hA.atom]

theorem MatchA.group_lift {z : D₀} (hz : M₀.InGroup U.atoms z) :
    ∃ y : h.s.D, h.s.down y = z ∧ h.s.M.InGroup (U.atoms.image π) y := by
  obtain ⟨y, hy⟩ := hm.lift z hz
  have h1 : h.s.M.atom y = π (M₀.atom z) := by rw [MatchA.atom_eq hA hD hinj hm (hy ▸ hz.1), hy]
  have h2 : h.s.M.atom (h.s.M.mate y) = π (M₀.atom (M₀.mate z)) := by
    have hz2 : M₀.atom (h.s.down (h.s.M.mate y)) ∈ U.atoms := by rw [← hD.mate, hy]; exact hz.2
    rw [MatchA.atom_eq hA hD hinj hm hz2, ← hD.mate, hy]
  exact ⟨y, hy, by rw [h1]; exact Finset.mem_image_of_mem _ hz.1, by rw [h2]; exact Finset.mem_image_of_mem _ hz.2⟩

theorem MatchA.group_down {y : h.s.D} (hy : h.s.M.InGroup (U.atoms.image π) y) : M₀.InGroup U.atoms (h.s.down y) := by
  have key : ∀ c : V, c ∈ U.atoms.image π → h.anc c ∈ U.atoms := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    rw [hm.anc a ha]; exact ha
  refine ⟨?_, ?_⟩
  · rw [hA.atom]; exact key _ hy.1
  · rw [hD.mate, hA.atom]; exact key _ hy.2

/-- **The induced isomorphism along the renaming** (main's `stateIso` with `π`). -/
noncomputable def stateIsoA : RedSplice.InducedIso M₀ h.s.M U.atoms (U.atoms.image π) where
  π := π
  inj := hm.inj
  img := rfl
  sub := fun c hc => by obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc; exact hm.mem a ha
  e :=
    { toFun := fun x => ⟨Classical.choose (MatchA.group_lift hA hD hinj hm x.2),
        (Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)).2⟩
      invFun := fun y => ⟨h.s.down y.1, MatchA.group_down hA hD hinj hm y.2⟩
      left_inv := fun x => Subtype.ext (Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)).1
      right_inv := fun y => Subtype.ext (hA.inj
        (Classical.choose_spec (MatchA.group_lift hA hD hinj hm (MatchA.group_down hA hD hinj hm y.2))).1) }
  atom_comm := fun x => by
    have hx := Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)
    show h.s.M.atom (Classical.choose (MatchA.group_lift hA hD hinj hm x.2)) = π (M₀.atom x.1)
    rw [MatchA.atom_eq hA hD hinj hm (by rw [hx.1]; exact x.2.1), hx.1]
  mate_comm := fun x => by
    have hx := Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)
    have hmx := Classical.choose_spec (MatchA.group_lift hA hD hinj hm
      (show M₀.InGroup U.atoms (M₀.mate x.1) from ⟨x.2.2, by simpa [M₀.mate_mate] using x.2.1⟩))
    have e2 : h.s.down (h.s.M.mate (Classical.choose (MatchA.group_lift hA hD hinj hm x.2))) = M₀.mate x.1 := by
      rw [← hD.mate, hx.1]
    exact hA.inj (hmx.1.trans e2.symm)
  out_comm := fun x => by
    have hx := Classical.choose_spec (MatchA.group_lift hA hD hinj hm x.2)
    show h.s.M.out (Classical.choose (MatchA.group_lift hA hD hinj hm x.2)) = M₀.out x.1
    rw [← hD.out, hx.1]

theorem stateIsoA_e {x : D₀} (hx : M₀.InGroup U.atoms x) :
    h.s.down ((stateIsoA hA hD hinj hm).e ⟨x, hx⟩).1 = x :=
  (Classical.choose_spec (MatchA.group_lift hA hD hinj hm hx)).1

/-- **The transported object** (main's `stateObj_spec` with `π`). -/
theorem stateObjA_spec :
    ∃ Ũ : Object h.s.M, Ũ.atoms = U.atoms.image π ∧ Ũ.upper = π U.upper ∧ Ũ.lower = π U.lower ∧
      (∀ z : h.s.D, Ũ.ContainsDart z ↔ U.ContainsDart (h.s.down z)) ∧
      ∀ K' : VineCut h.s.M, K'.C.atoms = U.atoms.image π → ObjVine M₀ U → SingleVineVC K' := by
  let I := stateIsoA hA hD hinj hm
  refine ⟨I.mapObj U subset_rfl, rfl, rfl, rfl, fun z => ?_, ?_⟩
  · constructor
    · intro hz
      have hg := containsDart_inGroup _ hz
      have hg' : h.s.M.InGroup (U.atoms.image π) z := hg
      have hx := MatchA.group_down hA hD hinj hm hg'
      have e : (I.e ⟨h.s.down z, hx⟩).1 = z := by
        apply hA.inj
        exact stateIsoA_e hA hD hinj hm hx
      have := (I.containsDart_map U subset_rfl hx).mp (by rw [e]; exact hz)
      exact this
    · intro hz
      have hx := containsDart_inGroup U hz
      have e : (I.e ⟨h.s.down z, hx⟩).1 = z := by
        apply hA.inj
        exact stateIsoA_e hA hD hinj hm hx
      have := (I.containsDart_map U subset_rfl hx).mpr hz
      rwa [e] at this
  · intro K' hat hov
    obtain ⟨A, u, l, sh⟩ := U
    simp only at hat hov
    have hat' : K'.C.atoms = (I.mapObj ⟨A, u, l, sh⟩ subset_rfl).atoms := hat
    have hjoint : ({K'.C.upper, K'.C.lower} : Finset V) = {π u, π l} :=
      object_joints_eq K'.C (I.mapObj ⟨A, u, l, sh⟩ subset_rfl) hat'
    cases sh with
    | vc h0 =>
      rcases LGSpine.object_shape_cases K'.C with ⟨h', hsh'⟩ | ⟨R', hsh'⟩
      · obtain ⟨X, hX⟩ := hov
        have hv : h.s.M.IsVine X (A.image π) (π u) (π l) := I.isVine hX
        unfold SingleVineVC
        rw [hsh']
        exact ⟨X, isVine_atoms_congr hat.symm (isVine_orient K'.ab_ne hjoint hv)⟩
      · exact (not_vc_hyper_atoms (U := I.mapObj ⟨A, u, l, .vc h0⟩ subset_rfl) (U' := K'.C) ⟨_, rfl⟩ ⟨R', hsh'⟩
          hat'.symm).elim
    | hyper R =>
      rcases LGSpine.object_shape_cases K'.C with ⟨h', hsh'⟩ | ⟨R', hsh'⟩
      · exact (not_vc_hyper_atoms (U := K'.C) (U' := I.mapObj ⟨A, u, l, .hyper R⟩ subset_rfl) ⟨h', hsh'⟩ ⟨_, rfl⟩
          hat').elim
      · have he : M₀.InGroup A R.added := RedSplice.inGroup_of_ends R.ends_eq R.adjoint.1.2.1 R.adjoint.1.2.2.1
        obtain ⟨Rt, hRt, hRta⟩ : ∃ Rt, (I.mapObj ⟨A, u, l, .hyper R⟩ subset_rfl).shape = .hyper Rt ∧
            Rt.added = (I.e ⟨R.added, he⟩).1 := ⟨_, rfl, rfl⟩
        obtain ⟨X, hX⟩ := hov
        have hv : (h.s.M.eraseBond (I.e ⟨R.added, he⟩).1).IsVine X (A.image π) (π u) (π l) :=
          (I.eraseE R.added he).isVine hX
        unfold SingleVineVC
        rw [hsh']
        by_cases h1 : R'.added = (I.e ⟨R.added, he⟩).1
        · exact ⟨X, isVine_atoms_congr hat.symm (isVine_orient K'.ab_ne hjoint (isVine_eraseBond_congr h1.symm hv))⟩
        · by_cases h2 : R'.added = h.s.M.mate (I.e ⟨R.added, he⟩).1
          · have hB : A.image π ⊆ h.s.M.atoms := I.sub
            have hv2 := (eraseMateIso h.s.M (I.e ⟨R.added, he⟩).1 (A.image π) hB).isVine hv
            exact ⟨X, isVine_atoms_congr hat.symm (isVine_orient K'.ab_ne hjoint (isVine_eraseBond_congr h2.symm hv2))⟩
          · refine hyper_other_isSomeVine (I.mapObj ⟨A, u, l, .hyper R⟩ subset_rfl) K'.C hat'.symm hRt hsh' ?_
            rw [hRta]
            exact fun h => h.elim h1 h2

end transport

end WaveTurbulence.Flower.FinalMKPhase1
