/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCross2
import Mathlib.Tactic

/-!
# SUBPRO (S4): TARGET `subpro` (6), atom-set form (R28 session 2)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1 WaveTurbulence.Mole

variable {R : ℕ} {G : Garden (2 * R)}

theorem crossing_atoms (hM : G.molecule.IsMolecule) (σ : Prescription G) (P : Object (stSt G σ).G.molecule)
    (hout : ∀ O ∈ objects G σ, ¬ P.atoms ⊆ O.atoms) (hnd : ¬ Disjoint P.atoms (stSt G σ).hinges) :
    ∃ v ∈ (collectionChoices G σ).hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair ((collectionChoices G σ).first v) ((collectionChoices G σ).second v)
            (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y)))) := by
  classical
  by_contra hcon
  have hjoint : ∀ v ∈ (stSt G σ).hinges, v ∈ P.atoms → v = P.upper ∨ v = P.lower := by
    intro v hv hvP
    by_contra h
    push Not at h
    exact hcon ⟨v, hv, hvP, Or.inl h⟩
  have hnx : ∀ v ∈ (stSt G σ).hinges, v ∈ P.atoms → ∀ x y, hingePair G σ v = some (x, y) →
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
  have hK : ∀ v, v ∈ P.atoms → v ∈ (stSt G σ).hinges → ∃ j, (v = P.upper ∨ v = P.lower) ∧
      ∃ u ∈ unitBlocks G σ, (stSt G σ).M.ob v = u.upper ∧ (j = u.upper ∨ j = u.lower) ∧
        ∀ x, (stSt G σ).G.molecule.atom x = v → P.ContainsDart x → G.molecule.atom ((stSt G σ).M.od x) = j := by
    intro v hvP hvh
    obtain ⟨u, hu, hob, j, hj, hx⟩ := hinge_common_joint hM σ P hvh (hjoint v hvh hvP) (hnx v hvh hvP)
    exact ⟨j, hjoint v hvh hvP, u, hu, hob, hj, hx⟩
  let jf : GBranch (stSt G σ).G.tree → GBranch G.tree := fun c =>
    if h : c ∈ P.atoms ∧ c ∈ (stSt G σ).hinges then Classical.choose (hK c h.1 h.2) else (stSt G σ).M.ob c
  have hjnon : ∀ c ∈ P.atoms, c ∉ (stSt G σ).hinges → jf c = (stSt G σ).M.ob c := by
    intro c hc hch
    simp only [jf]
    rw [dif_neg (fun h => hch h.2)]
  have hjsp : ∀ w ∈ P.atoms, w ∈ (stSt G σ).hinges → (w = P.upper ∨ w = P.lower) ∧
      ∃ u ∈ unitBlocks G σ, (stSt G σ).M.ob w = u.upper ∧ (jf w = u.upper ∨ jf w = u.lower) ∧
        ∀ x, (stSt G σ).G.molecule.atom x = w → P.ContainsDart x →
          G.molecule.atom ((stSt G σ).M.od x) = jf w := by
    intro w hw hwh
    have := Classical.choose_spec (hK w hw hwh)
    simp only [jf]
    rw [dif_pos ⟨hw, hwh⟩]
    exact this
  have hKd : KData σ P jf := hjsp
  obtain ⟨v0, hv0P, hv0h⟩ : ∃ v0, v0 ∈ P.atoms ∧ v0 ∈ (stSt G σ).hinges := by
    by_contra h
    push Not at h
    exact hnd (Finset.disjoint_left.mpr fun v hv hvh => h v hv hvh)
  have hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (stSt G σ).hinges :=
    ⟨v0, hjoint v0 hv0h hv0P, hv0h⟩
  have hvc := cross_isvc hM σ P jf hjnon hKd hend
  obtain ⟨g, hg, hBg⟩ := cover_group hM (T := P.atoms.image jf) ⟨_, _, Or.inr (Or.inl hvc)⟩
  have hjg : ∀ c ∈ P.atoms, jf c ∈ g := fun c hc => hBg (Finset.mem_image_of_mem _ hc)
  -- the group of the hinge `v0`
  obtain ⟨-, u0, hu0, hob0, hj0, -⟩ := hjsp v0 hv0P hv0h
  obtain ⟨S0, hS0m, hσ0, hmem0⟩ := mem_unitBlocks.mp hu0
  have hj0m : jf v0 ∈ u0.atoms := by rcases hj0 with h | h <;> rw [h]; exacts [u0.isBlock.2.1, u0.isBlock.2.2.1]
  have hgS : g = S0 := by
    by_contra hne
    exact Finset.disjoint_left.mp (groups_disjoint hM hg hS0m hne) (hjg v0 hv0P)
      ((groupUnitsOf G S0).sub u0 hmem0 hj0m)
  subst hgS
  rcases hsk : (groupUnitsOf G g).skip with _ | sk
  · -- a whole-group unit: the image has at most one atom
    have hall : ∀ z ∈ g, z ∈ u0.atoms := fun z hz => ((groupUnitsOf G g).noskip_units hsk u0 hmem0) ▸ hz
    have hhinge : ∀ c ∈ P.atoms, c ∈ (stSt G σ).hinges := by
      intro c hc
      by_contra hch
      have h1 := stSt_cls_mem hM σ hu0 (hall _ (hjg c hc))
      rw [hjnon c hc hch] at h1
      have h2 : (stSt G σ).cls ((stSt G σ).M.ob c) = none := by
        by_contra hne; exact hch (((stSt G σ).mem_hinges c).mpr hne)
      rw [h2] at h1; cases h1
    have hone : ∀ c ∈ P.atoms, c = v0 := by
      intro c hc
      obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hjsp c hc (hhinge c hc)
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      have hucu : uc = u0 := unit_eq_of_mem hM σ huc hu0 hjcm (hall _ (hjg c hc))
      subst hucu
      exact (stSt G σ).M.ob_inj (hobc.trans hob0.symm)
    exact Object.upper_ne_lower' P ((hone _ (Object.upper_mem P)).trans (hone _ (Object.lower_mem P)).symm)
  · -- a skipped vine: `P` lies in the residual object
    have hσg : σ g = Molecule.GapKind.SG := hσ0
    obtain ⟨O, hO⟩ := objOf_some hM σ hg hσg (Or.inr ⟨sk, hsk⟩)
    obtain ⟨-, -, -, hSpec⟩ := objOf_spec (Option.mem_def.mpr hO)
    obtain ⟨A, -, hOa, hnm, hsrc⟩ := hSpec.src
    obtain ⟨sk', hsk', hAeq, hup, hlo, -, -⟩ : ∃ sk', (groupUnitsOf G g).skip = some sk' ∧ A = sk'.A ∧
        O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk'.x ∧ O.lower = (stSt G σ).M.pi (stSt G σ).hcls sk'.y ∧ True ∧ True := by
      rcases hsrc with ⟨⟨hhv, hnh⟩, hnone, -⟩ | ⟨sk', hsk', hAeq, hup, hlo, -, -⟩
      · rw [hsk] at hnone; cases hnone
      · exact ⟨sk', hsk', hAeq, hup, hlo, trivial, trivial⟩
    rw [hsk] at hsk'
    cases hsk'
    subst hAeq
    apply hout O (mem_objects_of σ hg hσg hO)
    intro c hc
    by_cases hch : c ∈ (stSt G σ).hinges
    · obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hjsp c hc hch
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      obtain ⟨Sc, hScm, hσc, hmemc⟩ := mem_unitBlocks.mp huc
      have hScg : Sc = g := by
        by_contra hne
        exact Finset.disjoint_left.mp (groups_disjoint hM hScm hg hne) ((groupUnitsOf G Sc).sub uc hmemc hjcm)
          (hjg c hc)
      subst hScg
      exact hinge_mem_obj hM σ hg sk hsk hOa hup hlo huc hmemc hobc
    · have hcn : (stSt G σ).cls ((stSt G σ).M.ob c) = none := by
        by_contra hne; exact hch (((stSt G σ).mem_hinges c).mpr hne)
      have hobg : (stSt G σ).M.ob c ∈ g := by rw [← hjnon c hc hch]; exact hjg c hc
      exact atoms_sub_obj hM σ hO (P := {c}) (by
        intro c' hc'
        rw [Finset.mem_singleton] at hc'
        subst hc'
        exact ⟨hobg, hcn⟩) (Finset.mem_singleton_self c)

end WaveTurbulence.Subpro
