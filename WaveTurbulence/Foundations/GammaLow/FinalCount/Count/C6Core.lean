/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Shape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.OpEGenBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.OpEConfig
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.PostGood
public import WaveTurbulence.Foundations.FinalCount.P101.Main
import Mathlib.Tactic

/-! # Case (6d), the core: operation (e) and Prop 10.1′ (packet L6-COUNT, Case6TopLow; M2 §4.10, Lemma 4.3)

`case6d_core`: in a connected molecule `N` with in/out caps two, let `S` be a generalized theta chain
(`ThetaGenData`, `|S| ≤ 5`, `|C| ≤ 3`) whose gap chain has charge `≥ ρ` on the admissible set, let `Bs` be the protected
atoms (degree `≤ 2`; LG off `Bs`), let some atom outside `S` be unsaturated when `S` has two exits, and assume no pinch at `S`. Then
`𝔄(N) ≤ K (log L)^{78} min(1, δ⁻¹L^{−2γ}/ρ)`.

Proof: `exit_cases` (at most two exits, balanced with two): no exit (`S = N`, `opE_gen_none`); one exit
(`opE_gen_one`, then Prop 10.1′ on `N ∖ S`, whose far exit atom lost a bond); two exits (`opE_gen_bound` with the
multiplier `exists_postGoodOff_any`, then Prop 10.1′ at `η/2` on each post molecule, which keeps the unsaturated atom).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.FinalCountG8 WaveTurbulence.FinalCountG8.P101

/-- `11 ≤ L^{η/2}` eventually. -/
theorem eventually_eleven_le {η : ℝ} (hη : 0 < η) : ∃ R : ℝ, 1 ≤ R ∧ ∀ L ≥ R, 11 ≤ L ^ (η / 2) := by
  refine ⟨11 ^ (2 / η), Real.one_le_rpow (by norm_num) (by positivity), fun L hL => ?_⟩
  have h0 : (0 : ℝ) ≤ 11 ^ (2 / η) := by positivity
  calc (11 : ℝ) = (11 ^ (2 / η)) ^ (η / 2) := by
        rw [← Real.rpow_mul (by norm_num), show 2 / η * (η / 2) = 1 by field_simp, Real.rpow_one]
    _ ≤ L ^ (η / 2) := Real.rpow_le_rpow h0 hL (by positivity)

/-- **Case (6d), the core** (see the module docstring). -/
theorem case6d_core (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar K : ℝ, 1 ≤ Cstar ∧ 0 ≤ K ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D)
        (S : Finset V) (p q : V) (a b z₁ z₂ : D) (C C' Bs : Finset V),
        (∀ w ∈ N.atoms, N.outdeg w ≤ 2 ∧ N.indeg w ≤ 2) →
        (∀ x ∈ N.atoms, ∀ y ∈ N.atoms, N.SameComponent x y) →
        ThetaGenData N S p q a b z₁ z₂ C C' → S.card ≤ 5 → C.card ≤ 3 →
        (∀ w ∈ N.atoms, w ∈ Bs → N.deg w ≤ 2) →
        ((crossDarts N S).card = 2 → ∃ e ∈ N.atoms, e ∉ S ∧ N.deg e ≠ cap Bs e) →
        (∀ T : Pinch N, T.Y = S → False) →
        ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ), (∀ T ∈ MoleProp.ladderCells N, 0 ≤ P T) →
        (∀ κ, Adm κ → LargeGapOff Bs N L γ η (0 : Mom d) κ) →
        (∀ κ, Adm κ → CellGapRestriction N L (0 : Mom d) P (GapScale L) κ) →
        (∀ κ, Adm κ → ρ ≤ ‖Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂‖) →
          MoleProp.countAFree N L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (K * Real.log L ^ (78 : ℕ) * min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ)) := by
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ.1, by linarith [hγ.2]⟩
  obtain ⟨C0, L0, hC0, hnone⟩ := opE_gen_none d hd γ hγ
  obtain ⟨Co, Lo, hCo, hone⟩ := opE_gen_one d hd γ hγ
  obtain ⟨Ct, Lt, hCt, htwo⟩ := opE_gen_bound d hd γ hγ
  obtain ⟨Ca, hCa, hPa⟩ := proposition_one_off_bound.{u, v} d hd γ hγ01 η hη hηmax
  obtain ⟨Cb, hCb, hPb⟩ := proposition_one_off_bound.{u, v} d hd γ hγ01 (η / 2) (by positivity) (by linarith)
  obtain ⟨R11, hR11, h11⟩ := eventually_eleven_le hη
  refine ⟨max Ca Cb, C0 + Co + Ct, le_trans hCa (le_max_left _ _), by positivity, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨Ra, hRa⟩ := hPa C1 ((le_max_left _ _).trans hC1) δ hδ
  obtain ⟨Rb, hRb⟩ := hPb C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max (max (max L0 Lo) (max Lt R11)) (max (max Ra Rb) (Real.exp 1)), ?_⟩
  intro L hL ρ hρ hρ1 V D _ _ _ N S p q a b z₁ z₂ C C' Bs hcap hconn hT hS5 hC3 hBdeg hunsat hnop Adm P hP hLG
    hCG hgap
  classical
  simp only [max_le_iff] at hL
  obtain ⟨⟨⟨l0, lo⟩, lt, l11⟩, ⟨la, lb⟩, le⟩ := hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le le
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans le
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr le
  have hC11 : 1 ≤ C1 := le_trans hCa ((le_max_left _ _).trans hC1)
  have hδ0 := hδ.1
  have hm : 0 ≤ min 1 (δ⁻¹ * L ^ (-2 * γ) / ρ) := le_min zero_le_one (by positivity)
  have hl64 : Real.log L ^ (64 : ℕ) ≤ Real.log L ^ (78 : ℕ) := pow_le_pow_right₀ hlog (by norm_num)
  have hlog0 : 0 ≤ Real.log L := by linarith
  have hdeg4 : ∀ w ∈ N.atoms, N.deg w ≤ 4 := fun w hw => by
    have := hcap w hw; have := Mole.outdeg_add_indeg N w; omega
  have hcapB : ∀ w ∈ N.atoms, N.deg w ≤ cap Bs w := by
    intro w hw; unfold cap; split_ifs with hwB
    · exact hBdeg w hw hwB
    · exact hdeg4 w hw
  rcases exit_cases N S hT.sub (hT.card_cross_le hcap) (fun h2 => hT.balanced hcap h2) with
    h0 | ⟨T, hTY⟩ | ⟨T, hTY⟩ | ⟨T, hTY⟩
  · -- no exit: `S` is the whole molecule
    have hcl : ∀ z, N.atom z ∈ S → N.atom (N.mate z) ∈ S := by
      intro z hz; by_contra hn
      have : z ∈ crossDarts N S := mem_crossDarts.mpr ⟨hz, hn⟩
      rw [h0] at this; simp at this
    have hSA : S = N.atoms := by
      refine Finset.Subset.antisymm hT.sub fun w hw => ?_
      exact (mem_iff_of_sameComponent_of_closed hcl (hconn p (hT.sub hT.p_mem) w hw)).mp hT.p_mem
    have h1 := hnone L l0 δ hδ C1 hC11 ρ hρ hρ1 N p q a b z₁ z₂ C C' (hT.isThetaGen_self hSA) hC3
      (by rw [← hSA]; exact hS5) hconn P hP Adm hgap
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) hl64 (by positivity) (by positivity)) hm
  · -- one exit
    subst hTY
    have hθ := hT.isThetaGen_piece
    have hconnP : ∀ x ∈ T.Y, ∀ y ∈ T.Y, (piece N T.Y).SameComponent x y := by
      have := hθ.connected; rw [piece_atoms hT.sub] at this; exact this
    have h1 := hone L lo δ hδ C1 hC11 ρ hρ hρ1 N T hS5 p q _ _ _ _ C C' hθ hC3 hconnP P hP Adm hgap
    set E := Degen.eraseAtoms N T.Y with hE
    have hcE : T.c ∈ E.atoms := mem_sdiff.mpr ⟨N.atom_mem _, T.c_notMem⟩
    have hPMol : PMol Bs E := by
      refine ⟨caps_eraseAtoms T.Y hcap, fun w hw hwB => ?_, fun w hw => ⟨T.c, hcE, ?_, ?_⟩⟩
      · have hwY : w ∉ T.Y := (mem_sdiff.mp hw).2
        have h1 := deg_eraseAtoms_add (N := N) T.Y hwY
        rw [← hE] at h1
        have := hBdeg w (mem_sdiff.mp hw).1 hwB
        omega
      · have hf := T.erase_sameComponent_fold (hconn w (mem_sdiff.mp hw).1 T.c (N.atom_mem _))
        simpa only [(mem_sdiff.mp hw).2, T.c_notMem, ite_false] using hf
      · have hadd := deg_eraseAtoms_add (N := N) T.Y T.c_notMem
        rw [← hE] at hadd
        have hrem : 1 ≤ (Degen.removedDartsAt N T.Y T.c).card := by
          refine card_pos.mpr ⟨N.mate T.x, ?_⟩
          simp only [Degen.removedDartsAt, mem_filter, Molecule.dartsAt, mem_univ, true_and]
          exact ⟨rfl, by rw [N.mate_mate]; exact T.atom_x⟩
        have := hcapB T.c (N.atom_mem _)
        omega
    have hPE : ∀ S' ∈ MoleProp.ladderCells E, 0 ≤ P S' := fun S' hS' => by
      have := (MoleProp.isLadderCell_erase_iff N T.Y S').mp (mem_filter.mp hS').2
      exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N this.1), this.1⟩)
    have h2 : MoleProp.countAFree E L γ δ C1 (0 : Mom d) (MoleProp.erasedFreeAdmissibility N T.Y Adm) P ≤ 1 :=
      hRa L la hlog Bs E hPMol (fun x _ => hT.noLoop x.val) _ P
        (projected_largeGapOff N L γ η (0 : Mom d) Bs T.Y Adm hLG)
        (projected_cellGap N L (0 : Mom d) T.Y Adm P hCG) hPE
    refine h1.trans ((mul_le_mul' le_rfl h2).trans ?_)
    rw [mul_one]
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) hl64 (by positivity) (by positivity)) hm
  · -- two exits
    subst hTY
    have hθ := hT.isThetaGen_piece
    have hconnP : ∀ x ∈ T.Y, ∀ y ∈ T.Y, (piece N T.Y).SameComponent x y := by
      have := hθ.connected; rw [piece_atoms hT.sub] at this; exact this
    obtain ⟨e, heN, heY, he⟩ := hunsat (by rw [T.cross, card_pair T.ne])
    have hePost : e ∈ T.post.atoms := by rw [T.post_atoms]; exact mem_sdiff.mpr ⟨heN, heY⟩
    have he3 : N.deg e ≤ 3 := by
      have := hcapB e heN
      unfold cap at he this
      split_ifs at he this with heB
      · have := hBdeg e heN heB; omega
      · omega
    have hconnPost := T.post_connected hconn
    have hopen : ∀ S' ∈ MoleProp.ladderCells T.post, T.c ∈ S' → GoodCell T.post S' := fun S' hS' _ =>
      goodCell_of_connected_low hconnPost hePost (by rw [T.post_deg heY]; exact he3) hS'
    have hAdmOff : ∀ κ, Adm κ → lgAdmOff N Bs L γ η P κ := fun κ hκ =>
      ⟨fun x y hxy hxB hdir => hLG κ hκ (N.atom x) hxB x y rfl hxy.symm hdir, hCG κ hκ⟩
    have hW : ∀ κ, Adm κ → (∀ x, κ (N.mate x) = κ x) →
        ∃ g ∈ Icc (0 : ℤ) 4, T.PostGoodOff Bs L γ (η / 2) κ g ∧ (fun (_ : ℤ) (_ : D → (Fin d → ℤ)) => True) g κ := by
      intro κ hκ hb
      obtain ⟨g, hg, hgood⟩ := exists_postGoodOff_any T hL1 (h11 L l11) hb hcap Bs (hAdmOff κ hκ).1
      exact ⟨g, hg, hgood, trivial⟩
    have h1 := htwo L lt δ hδ C1 hC11 ρ hρ hρ1 N T hT.noLoop hdeg4 hS5 p q _ _ _ _ C C' hθ hC3 hconnP Bs hopen η P hP
      Adm hAdmOff hgap _ hW
    have hPMol : PMol (Bs \ T.Y) T.post := by
      refine ⟨T.post_caps hcap, fun w hw hwB => ?_, fun w hw => ⟨e, hePost, hconnPost w hw e hePost, ?_⟩⟩
      · rw [T.post_atoms] at hw
        rw [T.post_deg (mem_sdiff.mp hw).2]
        exact hBdeg w (mem_sdiff.mp hw).1 (mem_sdiff.mp hwB).1
      · rw [T.post_deg heY]
        have hcap' : cap (Bs \ T.Y) e = cap Bs e := by
          unfold cap; simp only [mem_sdiff, heY, not_false_eq_true, and_true]
        rw [hcap']; exact he
    have h2 : (⨆ g ∈ Icc (0 : ℤ) 4, ⨆ P' ∈ T.scaleFamily L P,
        MoleProp.countAFree T.post L γ δ C1 (0 : Mom d)
          (T.postAdmOff Bs Adm (fun (_ : ℤ) (_ : D → (Fin d → ℤ)) => True) L γ (η / 2) P' g) P') ≤ 1 := by
      refine iSup₂_le fun g _ => iSup₂_le fun P' hP' => ?_
      have hP'nn := T.scaleFamily_nonneg hP' (fun S' hS' hc => hP S' (by
        have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS').2
        exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N hcell.1), hcell.1⟩))
      exact hRb L lb hlog (Bs \ T.Y) T.post hPMol (fun x _ => T.post_loop_free hT.noLoop x) _ P'
        (fun κ' hκ' w hw x y hx hy hdir => hκ'.1.1 x y (hx.trans hy.symm) (hx ▸ hw) hdir)
        (fun κ' hκ' => hκ'.1.2) hP'nn
    refine h1.trans ((mul_le_mul' le_rfl h2).trans ?_)
    rw [mul_one]
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) le_rfl (by positivity) (by positivity)) hm
  · exact (hnop T hTY).elim

end WaveTurbulence.GammaLow.FinalCount.Count
