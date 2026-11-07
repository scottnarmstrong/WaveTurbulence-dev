/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
-- R83 port of sp-src/SubproCross2.lean (FLOWER-P6 R83): successor designations, see HANDOFF

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossR83
import Mathlib.Tactic

/-!
# SUBPRO (S4): `crossing`, the far darts of a hinge (R28 session 2)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1 WaveTurbulence.Mole

variable {R : ℕ} {G : Garden (2 * R)}

/-- The data of the substitution at the hinges of `P`: `jf` sends a hinge of `P` to the common joint of its unit that carries
the inside darts of `P`. -/
@[expose] def KData (σ : Prescription G) (P : Object (stSt G σ).G.molecule)
    (jf : GBranch (stSt G σ).G.tree → GBranch G.tree) : Prop :=
  ∀ w ∈ P.atoms, w ∈ (stSt G σ).hinges → (w = P.upper ∨ w = P.lower) ∧
    ∃ u ∈ unitBlocks G σ, (stSt G σ).M.ob w = u.upper ∧ (jf w = u.upper ∨ jf w = u.lower) ∧
      ∀ x, (stSt G σ).G.molecule.atom x = w → P.ContainsDart x → G.molecule.atom ((stSt G σ).M.od x) = jf w

/-- A dart at a hinge of `P` that is not inside `P` has its image at the other joint of the unit, hence outside the image. -/
theorem far_dart (hM : G.molecule.IsMolecule) (σ : Prescription G) (P : Object (stSt G σ).G.molecule)
    (jf : GBranch (stSt G σ).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P.atoms, c ∉ (stSt G σ).hinges → jf c = (stSt G σ).M.ob c)
    (hK : KData σ P jf) {w : GBranch (stSt G σ).G.tree} (hw : w ∈ P.atoms) (hwh : w ∈ (stSt G σ).hinges)
    {d : GardenDart (stSt G σ).G} (hd : (stSt G σ).G.molecule.atom d = w) (hnc : ¬ P.ContainsDart d) :
    G.molecule.atom ((stSt G σ).M.od d) ∉ P.atoms.image jf := by
  classical
  intro hmem
  obtain ⟨hwj, u, hu, hob, hjw, hKw⟩ := hK w hw hwh
  obtain ⟨ao, hao, hao_c, hao_o, -⟩ := contained_unique (stSt G σ).G P hwj true
  obtain ⟨ai, hai, hai_c, hai_o, -⟩ := contained_unique (stSt G σ).G P hwj false
  obtain ⟨hdm, hde, hdj⟩ := crown_dart hM σ hu hob hd
  -- the image atom of `d` is `jf w`
  have hatom : G.molecule.atom ((stSt G σ).M.od d) = jf w := by
    obtain ⟨c, hc, hcj⟩ := Finset.mem_image.mp hmem
    by_cases hch : c ∈ (stSt G σ).hinges
    · obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hK c hc hch
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      have hucu : uc = u := unit_eq_of_mem hM σ huc hu hjcm (hcj ▸ hdm)
      subst hucu
      have : c = w := (stSt G σ).M.ob_inj (hobc.trans hob.symm)
      rw [← hcj, this]
    · exfalso
      have h1 : (stSt G σ).cls (G.molecule.atom ((stSt G σ).M.od d)) = some u.upper := by
        have := stSt_cls_mem hM σ hu hdm
        exact this
      have h2 : (stSt G σ).cls (jf c) = none := by
        rw [hjnon c hc hch]
        by_contra hne
        exact hch (((stSt G σ).mem_hinges c).mpr hne)
      rw [← hcj, h2] at h1
      cases h1
  -- the external darts at `jf w` are exactly the lifts of the two inside darts
  have hblock : ∃ j', G.molecule.IsBlock u.atoms (jf w) j' := by
    rcases hjw with h | h
    · exact ⟨u.lower, h ▸ u.isBlock⟩
    · exact ⟨u.upper, h ▸ block_swap_joints _ u.isBlock⟩
  have hcard := joint_ext_card hM hblock.choose_spec
  set E := (G.molecule.dartsAt (jf w)).filter (fun e => ¬ G.molecule.InGroup u.atoms e) with hE
  have hao_a := hKw ao hao hao_c
  have hai_a := hKw ai hai hai_c
  have hoE : (stSt G σ).M.od ao ∈ E := by
    obtain ⟨-, hext, -⟩ := crown_dart hM σ hu hob hao
    simp [hE, Molecule.dartsAt, hao_a, hext]
  have hiE : (stSt G σ).M.od ai ∈ E := by
    obtain ⟨-, hext, -⟩ := crown_dart hM σ hu hob hai
    simp [hE, Molecule.dartsAt, hai_a, hext]
  have hne : (stSt G σ).M.od ao ≠ (stSt G σ).M.od ai := by
    intro h
    have := congrArg G.molecule.out h
    rw [(stSt G σ).M.od_out, (stSt G σ).M.od_out, hao_o, hai_o] at this
    cases this
  have hE2 : E = {(stSt G σ).M.od ao, (stSt G σ).M.od ai} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hoE
      · rw [Finset.mem_singleton.mp he]; exact hiE
    · have : ({(stSt G σ).M.od ao, (stSt G σ).M.od ai} : Finset (GardenDart G)).card = 2 := Finset.card_pair hne
      omega
  have hdE : (stSt G σ).M.od d ∈ E := by simp [hE, Molecule.dartsAt, hatom, hde]
  rw [hE2] at hdE
  rcases Finset.mem_insert.mp hdE with h | h
  · exact hnc (by rw [(stSt G σ).M.od_inj h]; exact hao_c)
  · exact hnc (by rw [(stSt G σ).M.od_inj (Finset.mem_singleton.mp h)]; exact hai_c)

/-- **The substituted object is a VC of the original molecule.** -/
theorem cross_isvc (hM : G.molecule.IsMolecule) (σ : Prescription G) (P : Object (stSt G σ).G.molecule)
    (jf : GBranch (stSt G σ).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P.atoms, c ∉ (stSt G σ).hinges → jf c = (stSt G σ).M.ob c)
    (hK : KData σ P jf) (hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (stSt G σ).hinges) :
    IsVC G.molecule (P.atoms.image jf) (jf P.upper) (jf P.lower) := by
  classical
  have J1 : ∀ v ∈ P.atoms, v ∈ (stSt G σ).hinges → ∃ u ∈ unitBlocks G σ, (stSt G σ).M.ob v = u.upper ∧
      (jf v = u.upper ∨ jf v = u.lower) := by
    intro v hv hvh
    obtain ⟨-, u, hu, hob, hj, -⟩ := hK v hv hvh
    exact ⟨u, hu, hob, hj⟩
  cases hs : P.shape with
  | vc h =>
    obtain ⟨I, hI⟩ := crossing_iso hM σ (stSt G σ).G.molecule id Function.injective_id (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) P.atoms jf hjnon J1
      (by
        intro v hv hvh x hx hxv
        obtain ⟨-, u, hu, hob, hj, hKw⟩ := hK v hv hvh
        refine hKw x hxv ?_
        unfold Object.ContainsDart
        rw [hs]; exact hx)
      (fun x0 _ => ⟨x0, rfl⟩)
    have := I.isVC_map h (subset_refl _)
    rw [hI] at this
    exact this
  | hyper R =>
    obtain ⟨I, hI⟩ := crossing_iso hM σ (Mole.eraseBond (stSt G σ).G.molecule R.added)
      (fun x => x.1) Subtype.val_injective (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) P.atoms jf hjnon J1
      (by
        intro v hv hvh x hx hxv
        obtain ⟨-, u, hu, hob, hj, hKw⟩ := hK v hv hvh
        refine hKw x.1 hxv ?_
        unfold Object.ContainsDart
        rw [hs]; exact ⟨x.2.1, x.2.2, hx⟩)
      (by
        intro x0 hx0
        by_contra hnot
        have hbad : x0 = R.added ∨ x0 = (stSt G σ).G.molecule.mate R.added := by
          by_contra hh
          push Not at hh
          exact hnot ⟨⟨x0, hh.1, hh.2⟩, rfl⟩
        obtain ⟨w, hwj, hwh⟩ := hend
        have hends := R.ends_eq
        unfold Molecule.ends at hends
        have hwP : w ∈ P.atoms := by rcases hwj with rfl | rfl; exact Object.upper_mem P; exact Object.lower_mem P
        have hwd : ∃ d, (d = R.added ∨ d = (stSt G σ).G.molecule.mate R.added) ∧
            (stSt G σ).G.molecule.atom d = w := by
          rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rcases hwj with rfl | rfl
            · exact ⟨R.added, Or.inl rfl, h1⟩
            · exact ⟨(stSt G σ).G.molecule.mate R.added, Or.inr rfl, h2⟩
          · rcases hwj with rfl | rfl
            · exact ⟨(stSt G σ).G.molecule.mate R.added, Or.inr rfl, h2⟩
            · exact ⟨R.added, Or.inl rfl, h1⟩
        obtain ⟨d, hdd, hdw⟩ := hwd
        have hnc : ¬ P.ContainsDart d := by
          unfold Object.ContainsDart
          rw [hs]
          rintro ⟨h1, h2, -⟩
          rcases hdd with rfl | rfl
          · exact h1 rfl
          · exact h2 rfl
        have hfar := far_dart hM σ P jf hjnon hK hwP hwh hdw hnc
        apply hfar
        obtain ⟨hin1, hin2⟩ := hx0
        have hmate : ∀ y : GardenDart (stSt G σ).G, (stSt G σ).M.od ((stSt G σ).G.molecule.mate y) =
            G.molecule.mate ((stSt G σ).M.od y) := (stSt G σ).M.od_mate
        have hdx : d = x0 ∨ d = (stSt G σ).G.molecule.mate x0 := by
          rcases hbad with h0 | h0 <;> rcases hdd with hd | hd
          · exact Or.inl (hd.trans h0.symm)
          · exact Or.inr (by rw [hd, h0])
          · exact Or.inr (by rw [hd, h0, (stSt G σ).G.molecule.mate_mate])
          · exact Or.inl (hd.trans h0.symm)
        rcases hdx with h | h
        · rw [h]; exact hin1
        · rw [h, hmate]; exact hin2)
    have := I.isVC_map R.adjoint (subset_refl _)
    rw [hI] at this
    exact this

theorem Object.upper_ne_lower' {w : ℕ} {G' : Garden w} (P : Object G'.molecule) : P.upper ≠ P.lower := by
  obtain ⟨A, a, b, sh⟩ := P
  cases sh with
  | vc h => exact h.1.2.2.2.1
  | hyper R => exact R.adjoint.1.2.2.2.1

/-- B1b (Mk-general form of `hinge_mem_obj`). -/
theorem hinge_mem_objMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {Mk : Set (Stage1.CLVine _)} {O : Object (stSt (Mk := Mk) G σ).G.molecule} (hOa : O.atoms = sk.A.image ((stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls))
    (hup : O.upper = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls sk.x) (hlo : O.lower = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls sk.y)
    {u : CLBlock G} (hu : u ∈ unitBlocks (Mk := Mk) G σ) (hu' : u ∈ (groupUnitsOf G S).units)
    {c : GBranch (stSt (Mk := Mk) G σ).G.tree} (hob : (stSt (Mk := Mk) G σ).M.ob c = u.upper) : c ∈ O.atoms := by
  have hsu := (groupUnitsOf G S).skip_units sk hsk
  rcases hsu.1 u hu' with ⟨hL, hl⟩ | ⟨hR, hr⟩
  · have hxu : sk.x ∈ u.atoms := by
      rcases hl with ⟨_, h2⟩ | ⟨h2, _⟩
      · rw [← h2]; exact u.isBlock.2.2.1
      · rw [← h2]; exact u.isBlock.2.1
    have : (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls sk.x = c := by
      apply (stSt (Mk := Mk) G σ).M.ob_inj
      rw [(stSt (Mk := Mk) G σ).M.ob_pi, hob]
      exact stSt_repC_memMk (Mk := Mk) hM σ hu hxu
    rw [← this, ← hup]; exact Object.upper_mem O
  · have hyu : sk.y ∈ u.atoms := by
      rcases hr with ⟨h2, _⟩ | ⟨_, h2⟩
      · rw [← h2]; exact u.isBlock.2.1
      · rw [← h2]; exact u.isBlock.2.2.1
    have : (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls sk.y = c := by
      apply (stSt (Mk := Mk) G σ).M.ob_inj
      rw [(stSt (Mk := Mk) G σ).M.ob_pi, hob]
      exact stSt_repC_memMk (Mk := Mk) hM σ hu hyu
    rw [← this, ← hlo]; exact Object.lower_mem O

/-- A hinge that is the crown of a unit of a group with a skipped vine is an atom (a joint) of the residual object. -/
theorem hinge_mem_obj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk)
    {O : Object (stSt G σ).G.molecule} (hOa : O.atoms = sk.A.image ((stSt G σ).M.pi (stSt G σ).hcls))
    (hup : O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk.x) (hlo : O.lower = (stSt G σ).M.pi (stSt G σ).hcls sk.y)
    {u : CLBlock G} (hu : u ∈ unitBlocks G σ) (hu' : u ∈ (groupUnitsOf G S).units)
    {c : GBranch (stSt G σ).G.tree} (hob : (stSt G σ).M.ob c = u.upper) : c ∈ O.atoms := hinge_mem_objMk (Mk := ∅) hM σ hSm sk hsk hOa hup hlo hu hu' hob

end WaveTurbulence.VineA.NormalizedSplice.Subpro
