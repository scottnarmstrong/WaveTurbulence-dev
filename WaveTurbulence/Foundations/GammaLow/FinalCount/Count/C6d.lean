/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Theta
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.C6Core
public import WaveTurbulence.Foundations.FinalCount.ChainRemoval96
public import WaveTurbulence.Foundations.FinalCount.BiBridgeEqual
import Mathlib.Tactic

/-! # Case (6d): operation (c), then operation (e) (packet L6-COUNT, Case6TopLow; M2 §4.10)

`c6d_key`: let `K₁` be the chain of an `α`-atom `v₁` of an even non-cycle component `𝕄₀`, and `S` a generalized theta
chain of `𝕄₀` disjoint from `K₁` (`ThetaGenData`), such that on genuine decorations (charge `0` at degree-four atoms)
the gap chain has charge `≥ L^{−γ−100η}/2` and `S` has nonzero total charge. Then
`𝔄(𝕄₀) ≤ [3^d (d δ⁻¹ (R₁/2)⁻¹ L^{−γ} + L^{γ−1}) (log L)^8] · K (log L)^{78} · 2 δ⁻¹ L^{−γ+100η}`.

Proof: strengthen the admissibility by the two charge facts (`countA_strengthen`: they hold for every counted
decoration), relax to the free count (`countA_le_countAFree_cell`), remove `K₁` (operation (c), main's `opC_rho`, gap of
`v₁` by `alphaGap`), and bound `𝕄₀ ∖ K₁` by `case6d_core` (operation (e) and Prop 10.1′). A pinch at `S` in `𝕄₀ ∖ K₁` is
excluded: at an `ε`-atom it lifts to `𝕄₀`, where `noBetaCut` forces zero total charge (`pinch_gap_eq_zero`,
REF-M2 R3); at a degree-two atom `S` plus that atom would be all of `𝕄₀ ∖ K₁`, which contains the degree-three end of
`K₁`. -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8 WaveTurbulence.FinalCountG8.P101

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Strengthening the admissibility** by a property of every counted decoration. -/
theorem countA_strengthen (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ) (Adm Q : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ)
    (hQ : ∀ c κ, (∀ a ∈ M.atoms, M.deg a = 4 → c a = 0) → M.IsDecoration L 0 c κ → Adm κ → Q κ) :
    M.countA L γ δ C1 (0 : Mom d) Adm P ≤ M.countA L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧ Q κ) P := by
  unfold Molecule.countA
  refine mul_le_mul' (ENat.toENNReal_mono ?_) le_rfl
  unfold Molecule.countE
  refine iSup_mono fun c => iSup_mono fun hc => iSup_mono fun β => iSup_mono fun k0 => iSup_mono fun hk0 =>
    Set.encard_mono ?_
  rintro κ ⟨hd, hr, ha⟩
  exact ⟨hd, hr, ha, hQ c κ hc hd ha⟩

theorem finalDec_and {M : Molecule V D} {cls : V → Cls} {d : ℕ} {L γ η : ℝ} {Adm Q : (D → (Fin d → ℤ)) → Prop}
    (hF : FinalDec M cls L γ η Adm) : FinalDec M cls L γ η (fun κ => Adm κ ∧ Q κ) where
  labRange := hF.labRange
  kapVals := hF.kapVals
  epsLG := fun κ h => hF.epsLG κ h.1
  alphaGap := fun κ h => hF.alphaGap κ h.1
  alphaSG := fun κ h => hF.alphaSG κ h.1
  betaGap := fun κ h => hF.betaGap κ h.1
  vineLG := fun hv κ h => hF.vineLG hv κ h.1
  noBetaCut := fun κ h => hF.noBetaCut κ h.1
  iota := fun κ h => hF.iota κ h.1

theorem erase_deg_end {M : Molecule V D} {K : Finset V} {y₁ y₂ : D} (hcross : crossDarts M K = {y₁, y₂})
    (hne : M.atom (M.mate y₁) ≠ M.atom (M.mate y₂)) :
    (Degen.eraseAtoms M K).deg (M.atom (M.mate y₁)) + 1 = M.deg (M.atom (M.mate y₁)) := by
  classical
  have hy1 : M.atom (M.mate y₁) ∉ K := (mem_crossDarts.mp (by rw [hcross]; simp : y₁ ∈ crossDarts M K)).2
  have hadd := deg_eraseAtoms_add (N := M) K hy1
  have h1 : Degen.removedDartsAt M K (M.atom (M.mate y₁)) = {M.mate y₁} := by
    ext z
    simp only [Degen.removedDartsAt, mem_filter, Molecule.dartsAt, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hz, hmz⟩
      rcases enter_chain hcross (by rw [hz]; exact hy1) hmz with e | e
      · exact e
      · exact absurd (by rw [← hz, e]) hne
    · rintro rfl
      exact ⟨rfl, by rw [M.mate_mate]; exact (mem_crossDarts.mp (by rw [hcross]; simp : y₁ ∈ crossDarts M K)).1⟩
  rw [h1, card_singleton] at hadd
  exact hadd

end

/-- **Case (6d): operation (c) on `K₁`, then operation (e)** (see the module docstring). -/
theorem c6d_key (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar K : ℝ, 1 ≤ Cstar ∧ 0 ≤ K ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, 1 ≤ R ∧ ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → ¬ odd → (¬ ∀ a ∈ M.atoms, M.deg a = 2) →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → (∃ w, w ∉ M.atoms) →
        ∀ (v₁ : V) (K₁ : Finset V), v₁ ∈ M.atoms → (cls v₁).IsAlpha → IsChainSet M cls K₁ → v₁ ∈ K₁ →
        ∀ (S : Finset V) (p q : V) (a b z₁ z₂ : D) (C C' : Finset V),
        ThetaGenData M S p q a b z₁ z₂ C C' → Disjoint S K₁ → S.card ≤ 5 → C.card ≤ 3 →
        (∀ c κ, (∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) → M.IsDecoration L 0 c κ → Adm κ →
          L ^ (-γ - 100 * η) / 2 ≤ ‖Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂‖ ∧
          ∑ w ∈ S, ∑ z ∈ M.dartsAt w, M.dartSign z • Molecule.kvec L 0 κ z ≠ 0) →
          M.countA L γ δ C1 (0 : Mom d) Adm P ≤
            ENNReal.ofReal (3 ^ d * (d * δ⁻¹ * ((cls v₁).lab / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) *
              Real.log L ^ (8 : ℝ)) *
              ENNReal.ofReal (K * Real.log L ^ (78 : ℕ) * (2 * δ⁻¹ * L ^ (-γ + 100 * η))) := by
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ.1, by linarith [hγ.2]⟩
  obtain ⟨Cc, Kc, hCc, hKc, hcore⟩ := case6d_core.{u, v} d hd γ hγ η hη hηmax
  refine ⟨Cc, Kc, hCc, hKc, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨Rc, hRc⟩ := hcore C1 hC1 δ hδ
  refine ⟨max Rc (Real.exp 1), le_trans (Real.one_le_exp (by norm_num)) (le_max_right _ _), ?_⟩
  intro L hL V D _ _ _ M cls odd Adm P hS hF hnodd hnc hP hMA hfr v₁ K₁ hv₁ hα₁ hK₁ hv₁K S p q a b z₁ z₂ C C'
    hT hSK hS5 hC3 hQ
  classical
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hC11 : 1 ≤ C1 := le_trans hCc hC1
  have hM : M.IsMolecule := hS.isMolecule
  set ρ : ℝ := L ^ (-γ - 100 * η) / 2 with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    have : L ^ (-γ - 100 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith [hγ.1])
    linarith
  -- the strengthened admissibility
  set Q : (D → (Fin d → ℤ)) → Prop := fun κ => ρ ≤ ‖Molecule.kvec L 0 κ z₁ - Molecule.kvec L 0 κ z₂‖ ∧
    ∑ w ∈ S, ∑ z ∈ M.dartsAt w, M.dartSign z • Molecule.kvec L 0 κ z ≠ 0 with hQdef
  set Adm₂ := fun κ => Adm κ ∧ Q κ with hAdm₂
  have hF₂ : FinalDec M cls L γ η Adm₂ := finalDec_and hF
  have hMA₂ : MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm₂ := fun κ h => hMA κ h.1
  refine (countA_strengthen M L γ δ C1 Adm Q P hQ).trans ?_
  set P' : Finset V → ℝ := fun S' => P (Mole.appbLinkParent M S') with hP'
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm₂ P (GapScale L) hMA₂).trans ?_
  set Adm₀ := fun κ => Adm₂ κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ with hAdm₀
  -- the chain `K₁`
  obtain ⟨y₁, y₂, hcross, hy12, hε1, hε2, hne⟩ := hS.chains hnodd hnc K₁ hK₁
  have hKA : K₁ ⊆ M.atoms := hK₁.2.1
  have hch : ∀ x ∈ K₁, M.outdeg x = 1 ∧ M.indeg x = 1 := by
    intro x hx
    have h2 : M.deg x ≤ 2 := (hS.classes x (hKA hx)).mpr (hK₁.2.2.1 x hx)
    have h4 := hS.evenDeg hnodd x (hKA hx)
    exact hS.dir2 x (hKA hx) (by omega)
  have hcard : (crossDarts M K₁).card = 2 := by rw [hcross, card_pair hy12]
  have hpost := connected_erase_of_two_cross M hS.conn (fun x hx => by
    rcases hS.evenDeg hnodd x hx with h | h <;> omega) K₁ hcard
  -- operation (c)
  have hlab := hF.labRange v₁ hv₁ hα₁
  have hR0 : 0 < (cls v₁).lab / 2 := by have := lt_of_lt_of_le (inv_pos.mpr hLp) hlab.1; positivity
  have hdv : M.deg v₁ = 2 := by
    have := (hS.classes v₁ hv₁).mpr (alpha_not_eps hα₁)
    rcases hS.evenDeg hnodd v₁ hv₁ with h | h <;> omega
  have hAdmc : ∀ κ, Adm₀ κ → ∃ y y', M.atom y ∈ K₁ ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      (cls v₁).lab / 2 ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := by
    intro κ hκ
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_darts M hdv
    exact ⟨x, y, hx ▸ hv₁K, hy.trans hx.symm, hxy, (hF.alphaGap κ hκ.1.1 v₁ hv₁ hα₁ x y hx hy hxy).1⟩
  have hstep := opC_rho (L := L) (γ := γ) (δ := δ) (C1 := C1) (ρ := (cls v₁).lab / 2) hγ01 hL1 hlog hδ hC11 hR0
    M hS.caps hS.noLoop hS.conn K₁ y₁ y₂ hKA hch hcross hne (chain_piece_connected hK₁) hpost P'
    (fun S' _ => hP _) Adm₀ hAdmc
  refine hstep.trans (mul_le_mul' le_rfl ?_)
  -- the molecule after operation (c)
  set N := Degen.eraseAtoms M K₁ with hN
  set Adm_N := MoleProp.erasedFreeAdmissibility M K₁ Adm₀ with hAdmN
  by_cases hne0 : ∃ κ', Adm_N κ'
  swap
  · push Not at hne0
    rw [MoleProp.countAFree_eq_normalization, countEFree_eq_zero_of_empty N L γ δ Adm_N hne0]
    simp
  obtain ⟨κ', κ, hκ, hκm, rfl⟩ := hne0
  have hTN := hT.erase K₁ hSK
  set e₁ := M.atom (M.mate y₁) with he₁
  have he₁K : e₁ ∉ K₁ := (mem_crossDarts.mp (by rw [hcross]; simp : y₁ ∈ crossDarts M K₁)).2
  have he₁A : e₁ ∈ M.atoms := M.atom_mem _
  have he₁N : e₁ ∈ N.atoms := mem_sdiff.mpr ⟨he₁A, he₁K⟩
  have hdeg4e : M.deg e₁ = 4 := by
    have h1 : ¬ M.deg e₁ ≤ 2 := fun h => ((hS.classes e₁ he₁A).mp h) hε1
    rcases hS.evenDeg hnodd e₁ he₁A with h | h <;> omega
  have hdegNe : N.deg e₁ = 3 := by
    have h' : N.deg e₁ + 1 = M.deg e₁ := erase_deg_end hcross hne
    omega
  have hcapN := caps_eraseAtoms K₁ hS.caps
  -- the atoms of `C ∪ C'` have degree two
  have hdegC : ∀ x ∈ C ∪ C', M.deg x = 2 := by
    intro x hx; have := hT.chain x hx; have := Mole.outdeg_add_indeg M x; omega
  -- `e₁` is not in `S` when `S` has two exits in `N`
  have he₁S : (crossDarts N S).card = 2 → e₁ ∉ S := by
    intro h2 he
    have h4 : N.deg p = 4 ∧ N.deg q = 4 := hTN.deg_four_of_two hcapN h2
    rw [hT.hS] at he
    simp only [mem_insert] at he
    rcases he with e | e | e
    · rw [← e] at h4; omega
    · rw [← e] at h4; omega
    · have := hdegC e₁ e; omega
  have hεS : ∀ x, x ∉ nonEps M.atoms cls → x ∈ M.atoms → (cls x).IsEps := by
    intro x hx hxA; by_contra hn; exact hx (mem_filter.mpr ⟨hxA, hn⟩)
  -- the bound by `case6d_core`
  have hbound := hRc L ((le_max_left _ _).trans hL) ρ hρ0 hρ1 N S p q _ _ _ _ C C' (nonEps M.atoms cls) hcapN hpost
    hTN hS5 hC3
    (fun w hw hwB => by
      have hwA := (mem_sdiff.mp hw).1
      have h2 : M.deg w ≤ 2 := (hS.classes w hwA).mpr (mem_filter.mp hwB).2
      have h' : N.deg w + (Degen.removedDartsAt M K₁ w).card = M.deg w :=
        deg_eraseAtoms_add (N := M) K₁ (mem_sdiff.mp hw).2
      omega)
    (fun h2 => ⟨e₁, he₁N, he₁S h2, by
      have hnB : e₁ ∉ nonEps M.atoms cls := fun h => (mem_filter.mp h).2 hε1
      rw [hdegNe]; unfold cap; simp [hnB]⟩)
    (by
      intro T hTY
      have h2 : (crossDarts N S).card = 2 := by rw [← hTY, T.cross, card_pair T.ne]
      have h4 : N.deg p = 4 ∧ N.deg q = 4 := hTN.deg_four_of_two hcapN h2
      set w := T.w with hw
      have hwN : w ∈ N.atoms := N.atom_mem _
      have hwA : w ∈ M.atoms := (mem_sdiff.mp hwN).1
      by_cases hwε : (cls w).IsEps
      · -- lift the pinch to `𝕄₀`
        have hnoK : ∀ z : D, M.atom z ∈ S → M.atom (M.mate z) ∉ K₁ := by
          intro z hz hmz
          rcases enter_chain hcross (disjoint_left.mp hSK hz) hmz with e | e
          · apply he₁S h2; rw [he₁, ← e]; exact hz
          · -- `z` at the other end `e₂`
            have hz2 : M.atom z = M.atom (M.mate y₂) := by rw [e]
            have hdeg4e2 : M.deg (M.atom (M.mate y₂)) = 4 := by
              have hA := M.atom_mem (M.mate y₂)
              have h1 : ¬ M.deg (M.atom (M.mate y₂)) ≤ 2 := fun h => ((hS.classes _ hA).mp h) hε2
              rcases hS.evenDeg hnodd _ hA with h | h <;> omega
            have hdegN2 : N.deg (M.atom (M.mate y₂)) = 3 := by
              have h' : N.deg (M.atom (M.mate y₂)) + 1 = M.deg (M.atom (M.mate y₂)) :=
                erase_deg_end (K := K₁) (y₁ := y₂) (y₂ := y₁) (by rw [hcross, pair_comm]) (Ne.symm hne)
              omega
            have hz' : M.atom (M.mate y₂) ∈ S := hz2 ▸ hz
            rw [hT.hS] at hz'
            simp only [mem_insert] at hz'
            rcases hz' with e3 | e3 | e3
            · rw [← e3] at h4; omega
            · rw [← e3] at h4; omega
            · have := hdegC _ e3; omega
        have hcrossM : crossDarts M S = {T.x.val, T.y.val} := by
          ext z
          rw [mem_crossDarts]
          simp only [mem_insert, mem_singleton]
          constructor
          · rintro ⟨hz, hmz⟩
            have hr : M.atom z ∉ K₁ ∧ M.atom (M.mate z) ∉ K₁ := ⟨disjoint_left.mp hSK hz, hnoK z hz⟩
            have hz' : (⟨z, hr⟩ : Degen.RetainedDart M K₁) ∈ crossDarts N S := mem_crossDarts.mpr ⟨hz, hmz⟩
            rw [← hTY, T.cross] at hz'
            rcases mem_insert.mp hz' with e | e
            · left; exact congrArg Subtype.val e
            · right; exact congrArg Subtype.val (mem_singleton.mp e)
          · rintro (rfl | rfl)
            · have h := T.x_mem; rw [hTY] at h; exact (mem_crossDarts (N := N)).mp h
            · have h := T.y_mem; rw [hTY] at h; exact (mem_crossDarts (N := N)).mp h
        let TM : Pinch M := ⟨S, hT.sub, T.x.val, T.y.val, hcrossM, fun e => T.ne (Subtype.ext e), T.same,
          T.out_x, T.out_y⟩
        have hdegw : 3 ≤ M.deg TM.w := by
          have h1 : ¬ M.deg w ≤ 2 := fun h => ((hS.classes w hwA).mp h) hwε
          change 3 ≤ M.deg w
          rcases hS.evenDeg hnodd w hwA with h | h <;> omega
        have hz := pinch_gap_eq_zero_of_finalDec TM hF₂ hκ.1 hfr hdegw
        rw [pinch_gap_eq_starSum TM L hκm] at hz
        exact hκ.1.2.2 hz
      · -- a pinch at a degree-two atom would close `S ∪ {w}`
        have hdegw : N.deg w ≤ 2 := by
          have h2' : M.deg w ≤ 2 := (hS.classes w hwA).mpr hwε
          have h' : N.deg w + (Degen.removedDartsAt M K₁ w).card = M.deg w :=
            deg_eraseAtoms_add (N := M) K₁ (mem_sdiff.mp hwN).2
          omega
        have hwS : w ∉ S := by rw [hTY.symm]; exact T.w_notMem
        have hmx : N.atom (N.mate T.x) = w := rfl
        have hmy : N.atom (N.mate T.y) = w := T.same.symm
        have hxy : N.mate T.x ≠ N.mate T.y := fun e => T.ne (by
          have := congrArg N.mate e; rwa [N.mate_mate, N.mate_mate] at this)
        have hstar : N.dartsAt w = {N.mate T.x, N.mate T.y} := by
          have hsub : ({N.mate T.x, N.mate T.y} : Finset _) ⊆ N.dartsAt w := by
            intro z hz
            rcases mem_insert.mp hz with rfl | e
            · exact (Mole.mem_dartsAt N w _).mpr hmx
            · rw [mem_singleton.mp e]; exact (Mole.mem_dartsAt N w _).mpr hmy
          refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
          rw [card_pair hxy]; exact hdegw
        have hcl : ∀ z, N.atom z ∈ insert w S → N.atom (N.mate z) ∈ insert w S := by
          intro z hz
          rcases mem_insert.mp hz with e | e
          · have hzw : z ∈ N.dartsAt w := (Mole.mem_dartsAt N w z).mpr e
            rw [hstar] at hzw
            rcases mem_insert.mp hzw with rfl | e2
            · rw [N.mate_mate]; exact mem_insert_of_mem (by rw [← hTY]; exact T.atom_x)
            · rw [mem_singleton.mp e2, N.mate_mate]; exact mem_insert_of_mem (by rw [← hTY]; exact T.atom_y)
          · by_cases hm : N.atom (N.mate z) ∈ S
            · exact mem_insert_of_mem hm
            · have : z ∈ crossDarts N S := mem_crossDarts.mpr ⟨e, hm⟩
              rw [← hTY, T.cross] at this
              rcases mem_insert.mp this with rfl | e2
              · rw [hmx]; exact mem_insert_self _ _
              · rw [mem_singleton.mp e2, hmy]; exact mem_insert_self _ _
        have hpS : p ∈ insert w S := mem_insert_of_mem hTN.p_mem
        have he₁in := (mem_iff_of_sameComponent_of_closed hcl (hpost p (hTN.sub hTN.p_mem) e₁ he₁N)).mp hpS
        rcases mem_insert.mp he₁in with e | e
        · rw [e] at hdegNe; omega
        · exact he₁S h2 e)
    Adm_N P' (fun S' _ => hP _)
    (projected_largeGapOff M L γ η (0 : Mom d) (nonEps M.atoms cls) K₁ Adm₀ (fun κ hκ v hvB x y hx hy hxy => by
      have hvA : v ∈ M.atoms := hx ▸ M.atom_mem x
      exact (hF.epsLG κ hκ.1.1 v hvA (hεS v hvB hvA) x y hx hy hxy).le))
    (projected_cellGap M L (0 : Mom d) K₁ Adm₀ P' (fun κ hκ => hκ.2))
    (by rintro κ'' ⟨κ₁, hκ₁, -, rfl⟩; exact hκ₁.1.2.1)
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hm := opE_min_le (η := η) hLp hδ.1 (le_of_eq hρdef.symm)
  have hK0 : 0 ≤ Kc * Real.log L ^ (78 : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_left hm hK0

end WaveTurbulence.GammaLow.FinalCount.Count
