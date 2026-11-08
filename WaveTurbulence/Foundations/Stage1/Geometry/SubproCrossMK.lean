/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCross3R83
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: the substitution at aligned hinges for the marked splice; o75 Theorem 7.5′(6)

* `hingePair_properMk`: every hinge pair is a proper pair (an external out/in pair of the hinge's unit at one of its
  joints): main's `hingePair_spec` at an unmarked hinge; at a run hinge of a marked group, the 75-F1 pair of the
  first survivor with a joint there (both bonds at that survivor's joint).
* `KDataMk`, `hinge_common_jointMk`, `far_dartMk`, `cross_isvcMk`: main's substitution (SubproCrossR83,
  SubproCross2R83) at every marking: replacing aligned hinges of an object of `G_sb` by joints of their units gives a
  VC of the original molecule.
* `crossing_atomsMk` (o75 (6)): an object of `G_sb` avoiding the survivor joints and meeting the hinges, not inside an
  object of `𝒞₁`, has a hinge in configuration (6).  A hinge of a marked group is a survivor joint
  (`hingePair_markedHinge`), so all its hinges are unmarked and main's argument applies.
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

/-- `hingePair_survFirst`, also recording that both bonds sit at one atom of `G` (the survivor's joint). -/
theorem hingePair_survFirstP (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    {i : ℕ} (hi : i < (survivorsMk G σ Mk).length) {v : GBranch (stSt G σ Mk).G.tree}
    (hv : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.1 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.2 = v)
    (hfirst : ∀ j (hj : j < i), ¬ ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.1 = v ∨
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.2 = v)) :
    ∃ q, hingePair G σ v = some q ∧ TripleAt (stSt G σ Mk).G v q.1 q.2 ∧
      G.molecule.atom ((stSt G σ Mk).M.od q.1) = G.molecule.atom ((stSt G σ Mk).M.od q.2) := by
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
  refine ⟨q, hingePair_of_survPairAt hsq, hqT, ?_⟩
  rw [hq1, hq2, hpx, hpy]

/-- `hingePair_markedHinge` with both bonds at one atom of `G`. -/
theorem hingePair_markedHingeP (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    {S : Finset (GBranch G.tree)} (hSm : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmk : markedGroup G Mk S) {u : CLBlock G} (hu : u ∈ groupUnitsMk G Mk S)
    {v : GBranch (stSt G σ Mk).G.tree} (hcr : (stSt G σ Mk).M.ob v = u.upper) :
    ∃ q, hingePair G σ v = some q ∧ TripleAt (stSt G σ Mk).G v q.1 q.2 ∧
      G.molecule.atom ((stSt G σ Mk).M.od q.1) = G.molecule.atom ((stSt G σ Mk).M.od q.2) := by
  classical
  have huB : u ∈ unitBlocks G σ Mk := mem_unitBlocksMk.mpr ⟨S, hSm, hσ, hu⟩
  have hu' : u ∈ (markedUnitsOfMK hmk).runs := groupUnitsMk_of_markedMK hmk ▸ hu
  obtain ⟨t, ht, hj⟩ := run_survivor_joint hmk hu'
  have htm : t ∈ survivorsMk G σ Mk := mem_survivorsMk_iffMK.mpr ⟨S, hSm, hσ, hmk, ht⟩
  have hex : ∃ i, ∃ hi : i < (survivorsMk G σ Mk).length,
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.1 = v ∨
        (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[i].2.2 = v := by
    obtain ⟨i, hi, hti⟩ := List.getElem_of_mem htm
    refine ⟨i, hi, ?_⟩
    rw [hti]
    rcases hj with h | h
    · exact Or.inl (pi_of_crown hM σ huB hcr h)
    · exact Or.inr (pi_of_crown hM σ huB hcr h)
  obtain ⟨hi0, hv0⟩ := Nat.find_spec hex
  have hfirst : ∀ j (hj : j < Nat.find hex),
      ¬ ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.1 = v ∨
        (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (survivorsMk G σ Mk)[j].2.2 = v) :=
    fun j hj hc => Nat.find_min hex hj ⟨by omega, hc⟩
  exact hingePair_survFirstP hM σ hi0 hv0 hfirst

/-- **Every hinge pair is proper** (o75 Theorem 7.5′(5)): main's pair at a hinge of an unmarked group, the 75-F1
survivor pair at a run hinge of a marked group. -/
theorem hingePair_properMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    {v : GBranch (stSt G σ Mk).G.tree} (hv : v ∈ (stSt G σ Mk).hinges) :
    ∃ x y, hingePair G σ v = some (x, y) ∧ ProperPair G σ v x y := by
  obtain ⟨S, hS, hσ, u, hu, hcr⟩ := hinge_groupMk hM σ hv
  have huB : u ∈ unitBlocks G σ Mk := mem_unitBlocksMk.mpr ⟨S, hS, hσ, hu⟩
  by_cases hmk : markedGroup G Mk S
  · obtain ⟨q, hq, hqT, hat⟩ := hingePair_markedHingeP hM σ hS hσ hmk hu hcr
    obtain ⟨-, hxe, hj⟩ := crown_dartMk hM σ huB hcr hqT.1
    obtain ⟨-, hye, -⟩ := crown_dartMk hM σ huB hcr hqT.2.1
    exact ⟨q.1, q.2, hq, hqT, u, huB, hcr, _, hj, rfl, hat.symm, hxe, hye⟩
  · have hu' : u ∈ (groupUnitsOf G S).units := groupUnitsMk_of_not_marked hmk ▸ hu
    obtain ⟨x, y, hp, hPP, -⟩ := hingePair_specMk hM σ hS hσ hmk hu' hcr
    exact ⟨x, y, hp, hPP⟩

/-- Main's `hinge_common_joint` at every marking: the two inside darts of `P` at an aligned hinge sit at one common
joint of the unit. -/
theorem hinge_common_jointMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    (P : Object (stSt G σ Mk).G.molecule) {v : GBranch (stSt G σ Mk).G.tree} (hvh : v ∈ (stSt G σ Mk).hinges)
    (hvj : v = P.upper ∨ v = P.lower)
    (hnx : ∀ x y, hingePair G σ v = some (x, y) → (P.ContainsDart x ↔ P.ContainsDart y)) :
    ∃ u ∈ unitBlocks G σ Mk, (stSt G σ Mk).M.ob v = u.upper ∧ ∃ j, (j = u.upper ∨ j = u.lower) ∧
      ∀ x, (stSt G σ Mk).G.molecule.atom x = v → P.ContainsDart x →
        G.molecule.atom ((stSt G σ Mk).M.od x) = j := by
  classical
  obtain ⟨x, y, hp, hPP⟩ := hingePair_properMk hM σ hvh
  have hnx' := hnx x y hp
  obtain ⟨hT, u, hu, hob, jc, hjc, hxj, hyj, hxe, hye⟩ := hPP
  obtain ⟨ao, hao, hao_c, hao_o, hao_u⟩ := contained_unique (stSt G σ Mk).G P hvj true
  obtain ⟨ai, hai, hai_c, hai_o, hai_u⟩ := contained_unique (stSt G σ Mk).G P hvj false
  have main : ∀ oc ic : GardenDart (stSt G σ Mk).G, G.molecule.atom ((stSt G σ Mk).M.od oc) = jc →
      G.molecule.atom ((stSt G σ Mk).M.od ic) = jc → ¬ G.molecule.InGroup u.atoms ((stSt G σ Mk).M.od oc) →
      ¬ G.molecule.InGroup u.atoms ((stSt G σ Mk).M.od ic) → (stSt G σ Mk).G.molecule.out oc = true →
      (stSt G σ Mk).G.molecule.out ic = false → (P.ContainsDart oc ↔ P.ContainsDart ic) →
      (stSt G σ Mk).G.molecule.atom oc = v → (stSt G σ Mk).G.molecule.atom ic = v →
      ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt G σ Mk).M.od ao) = j ∧
        G.molecule.atom ((stSt G σ Mk).M.od ai) = j := by
    intro oc ic hoc hic hoe hie hoo hio hiff hoa hia
    refine common_jointMk hM σ hu hob hjc hoc hic hoe hie hoo hio hao hai hao_o hai_o ?_
    by_cases hc : P.ContainsDart oc
    · exact Or.inl ⟨(hao_u oc hoa hc hoo).symm, (hai_u ic hia (hiff.mp hc) hio).symm⟩
    · refine Or.inr ⟨fun h => hc (h ▸ hao_c), fun h => (fun hc' => hc (hiff.mpr hc')) (h ▸ hai_c)⟩
  have hout : (stSt G σ Mk).G.molecule.out x ≠ (stSt G σ Mk).G.molecule.out y := hT.2.2.2
  obtain ⟨j, hj, hjao, hjai⟩ : ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt G σ Mk).M.od ao) = j ∧
      G.molecule.atom ((stSt G σ Mk).M.od ai) = j := by
    cases hox : (stSt G σ Mk).G.molecule.out x
    · have hoy : (stSt G σ Mk).G.molecule.out y = true := by
        cases hoy' : (stSt G σ Mk).G.molecule.out y
        · exact absurd (hox.trans hoy'.symm) hout
        · rfl
      exact main y x hyj hxj hye hxe hoy hox hnx'.symm hT.2.1 hT.1
    · have hoy : (stSt G σ Mk).G.molecule.out y = false := by
        cases hoy' : (stSt G σ Mk).G.molecule.out y
        · rfl
        · exact absurd (hox.trans hoy'.symm) hout
      exact main x y hxj hyj hxe hye hox hoy hnx' hT.1 hT.2.1
  refine ⟨u, hu, hob, j, hj, ?_⟩
  intro x' hx' hc'
  cases hox : (stSt G σ Mk).G.molecule.out x'
  · rw [hai_u x' hx' hc' hox]; exact hjai
  · rw [hao_u x' hx' hc' hox]; exact hjao

/-- Main's `KData` at every marking. -/
def KDataMk (σ : Prescription G) {Mk : Set (CLVine G)} (P : Object (stSt G σ Mk).G.molecule)
    (jf : GBranch (stSt G σ Mk).G.tree → GBranch G.tree) : Prop :=
  ∀ w ∈ P.atoms, w ∈ (stSt G σ Mk).hinges → (w = P.upper ∨ w = P.lower) ∧
    ∃ u ∈ unitBlocks G σ Mk, (stSt G σ Mk).M.ob w = u.upper ∧ (jf w = u.upper ∨ jf w = u.lower) ∧
      ∀ x, (stSt G σ Mk).G.molecule.atom x = w → P.ContainsDart x → G.molecule.atom ((stSt G σ Mk).M.od x) = jf w

/-- Main's `far_dart` at every marking. -/
theorem far_dartMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    (P : Object (stSt G σ Mk).G.molecule) (jf : GBranch (stSt G σ Mk).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P.atoms, c ∉ (stSt G σ Mk).hinges → jf c = (stSt G σ Mk).M.ob c)
    (hK : KDataMk σ P jf) {w : GBranch (stSt G σ Mk).G.tree} (hw : w ∈ P.atoms) (hwh : w ∈ (stSt G σ Mk).hinges)
    {d : GardenDart (stSt G σ Mk).G} (hd : (stSt G σ Mk).G.molecule.atom d = w) (hnc : ¬ P.ContainsDart d) :
    G.molecule.atom ((stSt G σ Mk).M.od d) ∉ P.atoms.image jf := by
  classical
  intro hmem
  obtain ⟨hwj, u, hu, hob, hjw, hKw⟩ := hK w hw hwh
  obtain ⟨ao, hao, hao_c, hao_o, -⟩ := contained_unique (stSt G σ Mk).G P hwj true
  obtain ⟨ai, hai, hai_c, hai_o, -⟩ := contained_unique (stSt G σ Mk).G P hwj false
  obtain ⟨hdm, hde, hdj⟩ := crown_dartMk hM σ hu hob hd
  have hatom : G.molecule.atom ((stSt G σ Mk).M.od d) = jf w := by
    obtain ⟨c, hc, hcj⟩ := Finset.mem_image.mp hmem
    by_cases hch : c ∈ (stSt G σ Mk).hinges
    · obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hK c hc hch
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      have hucu : uc = u := unit_eq_of_memMk hM σ huc hu hjcm (hcj ▸ hdm)
      subst hucu
      have : c = w := (stSt G σ Mk).M.ob_inj (hobc.trans hob.symm)
      rw [← hcj, this]
    · exfalso
      have h1 : (stSt G σ Mk).cls (G.molecule.atom ((stSt G σ Mk).M.od d)) = some u.upper :=
        stSt_cls_memMk (Mk := Mk) hM σ hu hdm
      have h2 : (stSt G σ Mk).cls (jf c) = none := by
        rw [hjnon c hc hch]
        by_contra hne
        exact hch (((stSt G σ Mk).mem_hinges c).mpr hne)
      rw [← hcj, h2] at h1
      cases h1
  have hblock : ∃ j', G.molecule.IsBlock u.atoms (jf w) j' := by
    rcases hjw with h | h
    · exact ⟨u.lower, h ▸ u.isBlock⟩
    · exact ⟨u.upper, h ▸ block_swap_joints _ u.isBlock⟩
  have hcard := joint_ext_card hM hblock.choose_spec
  set E := (G.molecule.dartsAt (jf w)).filter (fun e => ¬ G.molecule.InGroup u.atoms e) with hE
  have hao_a := hKw ao hao hao_c
  have hai_a := hKw ai hai hai_c
  have hoE : (stSt G σ Mk).M.od ao ∈ E := by
    obtain ⟨-, hext, -⟩ := crown_dartMk hM σ hu hob hao
    simp [hE, Molecule.dartsAt, hao_a, hext]
  have hiE : (stSt G σ Mk).M.od ai ∈ E := by
    obtain ⟨-, hext, -⟩ := crown_dartMk hM σ hu hob hai
    simp [hE, Molecule.dartsAt, hai_a, hext]
  have hne : (stSt G σ Mk).M.od ao ≠ (stSt G σ Mk).M.od ai := by
    intro h
    have := congrArg G.molecule.out h
    rw [(stSt G σ Mk).M.od_out, (stSt G σ Mk).M.od_out, hao_o, hai_o] at this
    cases this
  have hE2 : E = {(stSt G σ Mk).M.od ao, (stSt G σ Mk).M.od ai} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hoE
      · rw [Finset.mem_singleton.mp he]; exact hiE
    · have : ({(stSt G σ Mk).M.od ao, (stSt G σ Mk).M.od ai} : Finset (GardenDart G)).card = 2 :=
        Finset.card_pair hne
      omega
  have hdE : (stSt G σ Mk).M.od d ∈ E := by simp [hE, Molecule.dartsAt, hatom, hde]
  rw [hE2] at hdE
  rcases Finset.mem_insert.mp hdE with h | h
  · exact hnc (by rw [(stSt G σ Mk).M.od_inj h]; exact hao_c)
  · exact hnc (by rw [(stSt G σ Mk).M.od_inj (Finset.mem_singleton.mp h)]; exact hai_c)

/-- Main's `cross_isvc` at every marking: **the substituted object is a VC of the original molecule.** -/
theorem cross_isvcMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    (P : Object (stSt G σ Mk).G.molecule) (jf : GBranch (stSt G σ Mk).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P.atoms, c ∉ (stSt G σ Mk).hinges → jf c = (stSt G σ Mk).M.ob c)
    (hK : KDataMk σ P jf) (hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (stSt G σ Mk).hinges) :
    IsVC G.molecule (P.atoms.image jf) (jf P.upper) (jf P.lower) := by
  classical
  have J1 : ∀ v ∈ P.atoms, v ∈ (stSt G σ Mk).hinges → ∃ u ∈ unitBlocks G σ Mk, (stSt G σ Mk).M.ob v = u.upper ∧
      (jf v = u.upper ∨ jf v = u.lower) := by
    intro v hv hvh
    obtain ⟨-, u, hu, hob, hj, -⟩ := hK v hv hvh
    exact ⟨u, hu, hob, hj⟩
  cases hs : P.shape with
  | vc h =>
    obtain ⟨I, hI⟩ := crossing_isoMk (Mk := Mk) hM σ (stSt G σ Mk).G.molecule id Function.injective_id
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) P.atoms jf hjnon J1
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
    obtain ⟨I, hI⟩ := crossing_isoMk (Mk := Mk) hM σ (Mole.eraseBond (stSt G σ Mk).G.molecule R.added)
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
        have hbad : x0 = R.added ∨ x0 = (stSt G σ Mk).G.molecule.mate R.added := by
          by_contra hh
          push Not at hh
          exact hnot ⟨⟨x0, hh.1, hh.2⟩, rfl⟩
        obtain ⟨w, hwj, hwh⟩ := hend
        have hends := R.ends_eq
        unfold Molecule.ends at hends
        have hwP : w ∈ P.atoms := by
          rcases hwj with rfl | rfl; exact Object.upper_mem P; exact Object.lower_mem P
        have hwd : ∃ d, (d = R.added ∨ d = (stSt G σ Mk).G.molecule.mate R.added) ∧
            (stSt G σ Mk).G.molecule.atom d = w := by
          rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rcases hwj with rfl | rfl
            · exact ⟨R.added, Or.inl rfl, h1⟩
            · exact ⟨(stSt G σ Mk).G.molecule.mate R.added, Or.inr rfl, h2⟩
          · rcases hwj with rfl | rfl
            · exact ⟨(stSt G σ Mk).G.molecule.mate R.added, Or.inr rfl, h2⟩
            · exact ⟨R.added, Or.inl rfl, h1⟩
        obtain ⟨d, hdd, hdw⟩ := hwd
        have hnc : ¬ P.ContainsDart d := by
          unfold Object.ContainsDart
          rw [hs]
          rintro ⟨h1, h2, -⟩
          rcases hdd with rfl | rfl
          · exact h1 rfl
          · exact h2 rfl
        have hfar := far_dartMk hM σ P jf hjnon hK hwP hwh hdw hnc
        apply hfar
        obtain ⟨hin1, hin2⟩ := hx0
        have hmate : ∀ y : GardenDart (stSt G σ Mk).G, (stSt G σ Mk).M.od ((stSt G σ Mk).G.molecule.mate y) =
            G.molecule.mate ((stSt G σ Mk).M.od y) := (stSt G σ Mk).M.od_mate
        have hdx : d = x0 ∨ d = (stSt G σ Mk).G.molecule.mate x0 := by
          rcases hbad with h0 | h0 <;> rcases hdd with hd | hd
          · exact Or.inl (hd.trans h0.symm)
          · exact Or.inr (by rw [hd, h0])
          · exact Or.inr (by rw [hd, h0, (stSt G σ Mk).G.molecule.mate_mate])
          · exact Or.inl (hd.trans h0.symm)
        rcases hdx with h | h
        · rw [h]; exact hin1
        · rw [h, hmate]; exact hin2)
    have := I.isVC_map R.adjoint (subset_refl _)
    rw [hI] at this
    exact this

/-- **o75 Theorem 7.5′(6) for the marked splice** (main's `crossing_atoms`): an object of `G_sb` that avoids the
survivor joints, meets the hinges and is not inside an object of `𝒞₁` contains a hinge that is interior to it, or a
joint of it splitting the hinge pair. -/
theorem crossing_atomsMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    (P : Object (stSt G σ Mk).G.molecule)
    (hout : ∀ O ∈ objects G σ Mk, ¬ P.atoms ⊆ O.atoms)
    (hJ : ∀ t (ht : t ∈ survivorsMk G σ Mk), (survObj ht).upper ∉ P.atoms ∧ (survObj ht).lower ∉ P.atoms)
    (hnd : ¬ Disjoint P.atoms (stSt G σ Mk).hinges) :
    ∃ v ∈ (collectionChoices G σ Mk).hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair ((collectionChoices G σ Mk).first v) ((collectionChoices G σ Mk).second v)
            (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y)))) := by
  classical
  by_contra hcon
  have hjoint : ∀ v ∈ (stSt G σ Mk).hinges, v ∈ P.atoms → v = P.upper ∨ v = P.lower := by
    intro v hv hvP
    by_contra h
    push Not at h
    exact hcon ⟨v, hv, hvP, Or.inl h⟩
  have hnx : ∀ v ∈ (stSt G σ Mk).hinges, v ∈ P.atoms → ∀ x y, hingePair G σ v = some (x, y) →
      (P.ContainsDart x ↔ P.ContainsDart y) := by
    intro v hv hvP x y hp
    by_contra hne
    apply hcon
    refine ⟨v, hv, hvP, Or.inr ⟨hjoint v hv hvP, x, y, by simp [collectionChoices, hp],
      by simp [collectionChoices, hp], ?_⟩⟩
    by_cases hx : P.ContainsDart x
    · exact Or.inl ⟨hx, fun hy => hne ⟨fun _ => hy, fun _ => hx⟩⟩
    · have hy : P.ContainsDart y := by
        by_contra hy
        exact hne ⟨fun h => absurd h hx, fun h => absurd h hy⟩
      exact Or.inr ⟨hy, hx⟩
  have hK : ∀ v, v ∈ P.atoms → v ∈ (stSt G σ Mk).hinges → ∃ j, (v = P.upper ∨ v = P.lower) ∧
      ∃ u ∈ unitBlocks G σ Mk, (stSt G σ Mk).M.ob v = u.upper ∧ (j = u.upper ∨ j = u.lower) ∧
        ∀ x, (stSt G σ Mk).G.molecule.atom x = v → P.ContainsDart x →
          G.molecule.atom ((stSt G σ Mk).M.od x) = j := by
    intro v hvP hvh
    obtain ⟨u, hu, hob, j, hj, hx⟩ := hinge_common_jointMk hM σ P hvh (hjoint v hvh hvP) (hnx v hvh hvP)
    exact ⟨j, hjoint v hvh hvP, u, hu, hob, hj, hx⟩
  let jf : GBranch (stSt G σ Mk).G.tree → GBranch G.tree := fun c =>
    if h : c ∈ P.atoms ∧ c ∈ (stSt G σ Mk).hinges then Classical.choose (hK c h.1 h.2) else (stSt G σ Mk).M.ob c
  have hjnon : ∀ c ∈ P.atoms, c ∉ (stSt G σ Mk).hinges → jf c = (stSt G σ Mk).M.ob c := by
    intro c hc hch
    simp only [jf]
    rw [dif_neg (fun h => hch h.2)]
  have hjsp : ∀ w ∈ P.atoms, w ∈ (stSt G σ Mk).hinges → (w = P.upper ∨ w = P.lower) ∧
      ∃ u ∈ unitBlocks G σ Mk, (stSt G σ Mk).M.ob w = u.upper ∧ (jf w = u.upper ∨ jf w = u.lower) ∧
        ∀ x, (stSt G σ Mk).G.molecule.atom x = w → P.ContainsDart x →
          G.molecule.atom ((stSt G σ Mk).M.od x) = jf w := by
    intro w hw hwh
    have := Classical.choose_spec (hK w hw hwh)
    simp only [jf]
    rw [dif_pos ⟨hw, hwh⟩]
    exact this
  have hKd : KDataMk σ P jf := hjsp
  obtain ⟨v0, hv0P, hv0h⟩ : ∃ v0, v0 ∈ P.atoms ∧ v0 ∈ (stSt G σ Mk).hinges := by
    by_contra h
    push Not at h
    exact hnd (Finset.disjoint_left.mpr fun v hv hvh => h v hv hvh)
  have hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (stSt G σ Mk).hinges :=
    ⟨v0, hjoint v0 hv0h hv0P, hv0h⟩
  have hvc := cross_isvcMk hM σ P jf hjnon hKd hend
  obtain ⟨g, hg, hBg⟩ := cover_group hM (T := P.atoms.image jf) ⟨_, _, Or.inr (Or.inl hvc)⟩
  have hjg : ∀ c ∈ P.atoms, jf c ∈ g := fun c hc => hBg (Finset.mem_image_of_mem _ hc)
  -- the group of the hinge `v0`
  obtain ⟨-, u0, hu0, hob0, hj0, -⟩ := hjsp v0 hv0P hv0h
  obtain ⟨S0, hS0m, hσ0, hmem0⟩ := mem_unitBlocksMk.mp hu0
  have hj0m : jf v0 ∈ u0.atoms := by rcases hj0 with h | h <;> rw [h]; exacts [u0.isBlock.2.1, u0.isBlock.2.2.1]
  have hgS : g = S0 := by
    by_contra hne
    exact Finset.disjoint_left.mp (groups_disjoint hM hg hS0m hne) (hjg v0 hv0P) (groupUnitsMk_sub hmem0 hj0m)
  subst hgS
  -- the group is unmarked: a hinge of a marked group is a survivor joint
  have hgm : ¬ markedGroup G Mk g := by
    intro hmk
    obtain ⟨q, -, -, t, ht, hvt, -, -⟩ := hingePair_markedHinge hM σ hg hσ0 hmk hmem0 hob0
    rcases hvt with h | h
    · exact (hJ t ht).1 (h ▸ hv0P)
    · exact (hJ t ht).2 (h ▸ hv0P)
  have hgU : groupUnitsMk G Mk g = (groupUnitsOf G g).units := groupUnitsMk_of_not_marked hgm
  have hmem0' : u0 ∈ (groupUnitsOf G g).units := hgU ▸ hmem0
  rcases hsk : (groupUnitsOf G g).skip with _ | sk
  · -- a whole-group unit: the image has at most one atom
    have hall : ∀ z ∈ g, z ∈ u0.atoms := fun z hz => ((groupUnitsOf G g).noskip_units hsk u0 hmem0') ▸ hz
    have hhinge : ∀ c ∈ P.atoms, c ∈ (stSt G σ Mk).hinges := by
      intro c hc
      by_contra hch
      have h1 := stSt_cls_memMk (Mk := Mk) hM σ hu0 (hall _ (hjg c hc))
      rw [hjnon c hc hch] at h1
      have h2 : (stSt G σ Mk).cls ((stSt G σ Mk).M.ob c) = none := by
        by_contra hne; exact hch (((stSt G σ Mk).mem_hinges c).mpr hne)
      rw [h2] at h1; cases h1
    have hone : ∀ c ∈ P.atoms, c = v0 := by
      intro c hc
      obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hjsp c hc (hhinge c hc)
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      have hucu : uc = u0 := unit_eq_of_memMk hM σ huc hu0 hjcm (hall _ (hjg c hc))
      subst hucu
      exact (stSt G σ Mk).M.ob_inj (hobc.trans hob0.symm)
    exact Object.upper_ne_lower' P ((hone _ (Object.upper_mem P)).trans (hone _ (Object.lower_mem P)).symm)
  · -- a skipped vine: `P` lies in the residual object
    obtain ⟨O, hO, hOm⟩ := objOf_isSomeMk hM σ hg hσ0 (Or.inr ⟨sk, hsk⟩) hgm
    obtain ⟨-, -, -, hSpec⟩ := objOf_specMk (Option.mem_def.mpr hO)
    obtain ⟨A, -, hOa, hnm, hsrc⟩ := hSpec.src
    obtain ⟨sk', hsk', hAeq, hup, hlo, -, -⟩ : ∃ sk', (groupUnitsOf G g).skip = some sk' ∧ A = sk'.A ∧
        O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk'.x ∧
        O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk'.y ∧ True ∧ True := by
      rcases hsrc with ⟨⟨hhv, hnh⟩, hnone, -⟩ | ⟨sk', hsk', hAeq, hup, hlo, -, -⟩
      · rw [hsk] at hnone; cases hnone
      · exact ⟨sk', hsk', hAeq, hup, hlo, trivial, trivial⟩
    rw [hsk] at hsk'
    cases hsk'
    subst hAeq
    apply hout O hOm
    intro c hc
    by_cases hch : c ∈ (stSt G σ Mk).hinges
    · obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hjsp c hc hch
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      obtain ⟨Sc, hScm, -, hmemc⟩ := mem_unitBlocksMk.mp huc
      have hScg : Sc = g := by
        by_contra hne
        exact Finset.disjoint_left.mp (groups_disjoint hM hScm hg hne) (groupUnitsMk_sub hmemc hjcm) (hjg c hc)
      subst hScg
      exact hinge_mem_objMk hM σ hg sk hsk hOa hup hlo huc (hgU ▸ hmemc) hobc
    · have hcn : (stSt G σ Mk).cls ((stSt G σ Mk).M.ob c) = none := by
        by_contra hne; exact hch (((stSt G σ Mk).mem_hinges c).mpr hne)
      have hobg : (stSt G σ Mk).M.ob c ∈ g := by rw [← hjnon c hc hch]; exact hjg c hc
      exact atoms_sub_objMk hM σ hO (P := {c}) (by
        intro c' hc'
        rw [Finset.mem_singleton] at hc'
        subst hc'
        exact ⟨hobg, hcn⟩) (Finset.mem_singleton_self c)

end WaveTurbulence.VineA.NormalizedSplice.Subpro
