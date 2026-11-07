/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Split2Thm
import Mathlib.Tactic

/-! # Case (4), one chain, not `Y`-exceptional: the decoration-level theorem (finalcount-g8, F6-1)

`case4_one_split`: a case-(4) component whose two `β`-atoms form one chain `u → b → b′ → v`, with `𝕄₁` not
`Y`-exceptional and without a small cell, has `𝔄₀ ≤ L^{-η/128}`.  One application of operation (d) (`opDW`) for the
class where a good multiplier transports `κ` to a decoration failing `Q`; one application of operation (c) (`opCFree`)
for the others.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

/-- **First class, one chain.** -/
def Cls1One {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M₀ : Molecule V D} (T : TwoExit M₀) {d : ℕ}
    (Q : (Degen.RetainedDart M₀ T.Y ⊕ Bool → (Fin d → ℤ)) → Prop) (Bs : Finset V) (L γ η : ℝ)
    (κ : D → (Fin d → ℤ)) : Prop :=
  ∃ g ∈ Icc (0 : ℤ) 4, T.PostGoodOff Bs L γ (η / 2) κ g ∧ ¬ Q (T.postLabels κ g)

theorem case4_one_split (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M₀ : Molecule V D),
        (∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) → (∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z)) →
        ∀ (b b' : V) (x₁ x₂ y y' : D), b ∈ M₀.atoms → b' ∈ M₀.atoms →
        (M₀.outdeg b = 1 ∧ M₀.indeg b = 1) → (M₀.outdeg b' = 1 ∧ M₀.indeg b' = 1) →
        crossDarts M₀ {b, b'} = {x₁, x₂} → M₀.out x₁ = false → M₀.out x₂ = true →
        M₀.atom (M₀.mate x₁) ≠ M₀.atom (M₀.mate x₂) →
        M₀.atom y = b → M₀.atom y' = b → y ≠ y' →
        (∀ a ∈ M₀.atoms, ∀ c ∈ M₀.atoms, M₀.SameComponent a c) →
        (∀ a ∈ ({b, b'} : Finset V), ∀ c ∈ ({b, b'} : Finset V), (piece M₀ {b, b'}).SameComponent a c) →
        (∀ a ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms, ∀ c ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms,
          (Degen.eraseAtoms M₀ {b, b'}).SameComponent a c) →
        RegCore (closureOne M₀ b b' x₁ x₂) →
        (tripSet (closureOne M₀ b b' x₁ x₂)).card ≤ 2 →
        ((closureOne M₀ b b' x₁ x₂).atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        5 ≤ (closureOne M₀ b b' x₁ x₂).atoms.card → ¬ YReachesQT (closureOne M₀ b b' x₁ x₂) →
        ¬ YReachesSmallCell (closureOne M₀ b b' x₁ x₂) →
        ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S) →
        ∀ Adm : (D → (Fin d → ℤ)) → Prop,
          (∀ κ, Adm κ → lgAdmOff M₀ {b, b'} L γ η P κ ∧ κ y ≠ κ y') →
          MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128))) := by
  have hγ0 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  have hmin : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  have hpos : 0 < min γ (1 - γ) := lt_min hγ0.1 (by linarith [hγ.2])
  have hηs0 : 0 < η / 2 := by positivity
  obtain ⟨Cs, hCs, hP104⟩ := prop104_two_proved.{u, v} d hd γ hγ (η / 2) hηs0 (by linarith) (by
      have : (d : ℝ) * (η / 2) ≤ d * η := by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        nlinarith
      linarith) (by linarith)
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R1, hR1⟩ := hP104 m C1 hC1 δ hδ
  obtain ⟨A0, hA0⟩ := exists_mul_log_rpow_le (splitK d m δ) (((56 + m : ℕ) : ℝ)) (θ := η / 2 / 32) (by positivity)
  refine ⟨max (max R1 A0) (max (Real.exp 1) ((11 : ℝ) ^ (1 / (η / 2)))), fun L hL => ?_⟩
  have hLR1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLA0 : A0 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL11' : (11 : ℝ) ^ (1 / (η / 2)) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hL11 : 11 ≤ L ^ (η / 2) := eleven_le_rpow hηs0 hL11'
  have hbig : splitK d m δ * Real.log L ^ (56 + m) ≤ L ^ (η / 2 / 32) := by
    have := hA0 L hLA0
    rwa [Real.rpow_natCast] at this
  have hδ0 := hδ.1
  intro V D _ _ _ M₀ hcap hloop b b' x₁ x₂ y y' hb hb' hdb hdb' hc ho1 ho2 huv hy hy' hyy' hconn0 hYconn hconnK hcl
    htrip hsz h5 hnq hnsc P hP Adm hAdm
  classical
  have hne : x₂ ≠ x₁ := fun h => huv (by rw [h])
  have hx1m : x₁ ∈ crossDarts M₀ {b, b'} := by rw [hc]; exact mem_insert_self _ _
  have hx2m : x₂ ∈ crossDarts M₀ {b, b'} := by rw [hc]; exact mem_insert_of_mem (mem_singleton_self _)
  have hY : ({b, b'} : Finset V) ⊆ M₀.atoms := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
  let T : TwoExit M₀ := ⟨{b, b'}, hY, x₂, x₁, by rw [hc]; exact pair_comm _ _, hne, huv.symm, ho2, ho1⟩
  have hSplit := hR1 L hLR1 (closureOne M₀ b b' x₁ x₂) hcl.cap hcl.loop hcl.reg hcl.conn hcl.nocut
    (triple_of_tripSet htrip) (bb_le_three_of_nonexc hcl hnq) hsz hnq hnsc (Sum.inr true)
  obtain ⟨Q, hQ1, hQ2⟩ := hSplit
  have hpost : ∀ a ∈ T.post.atoms, ∀ c ∈ T.post.atoms, T.post.SameComponent a c := hcl.conn
  have hopen : ∀ S ∈ MoleProp.ladderCells T.post, GoodCell T.post S := fun S hS => goodCell_of_connected hpost h5 hS
  have hch : ∀ x ∈ T.Y, M₀.outdeg x = 1 ∧ M₀.indeg x = 1 := fun x hx => by
    rcases mem_insert.mp hx with rfl | h
    · exact hdb
    · rw [mem_singleton.mp h]; exact hdb'
  have hBs : ({b, b'} : Finset V) \ T.Y = ∅ := by
    change ({b, b'} : Finset V) \ {b, b'} = ∅
    simp
  have hY3 : T.Y.card ≤ 3 := by
    change ({b, b'} : Finset V).card ≤ 3
    exact (card_insert_le _ _).trans (by simp)
  have hcB : T.c ∉ ({b, b'} : Finset V) := (mem_crossDarts.mp hx2m).2
  have hdB : T.d ∉ ({b, b'} : Finset V) := (mem_crossDarts.mp hx1m).2
  -- the first class: operation (d)
  have hcls1 : MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧ Cls1One T Q {b, b'} L γ η κ) P ≤
      ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) * ENNReal.ofReal
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
          (((closureOne M₀ b b' x₁ x₂).atoms.card + 1 : ℝ) * L ^ (-(η / 2 / 16)))) := by
    have hA1 := opDW hL1 hlog hδ (hCs.trans hC1) M₀ T hcap hloop hconn0 {b, b'} hY3 hch hYconn hpost hopen P hP
      (fun κ => Adm κ ∧ Cls1One T Q {b, b'} L γ η κ) (fun κ h => (hAdm κ h.1).1)
      (fun g κ => ¬ Q (T.postLabels κ g))
      (by
        rintro κ ⟨hκ, g, hg, hpg, hnq'⟩ _
        exact ⟨g, hg, hpg, hnq'⟩)
    refine hA1.trans (mul_le_mul' le_rfl ?_)
    refine iSup₂_le fun g hg => ?_
    unfold TwoExit.afreeSupPost
    refine iSup₂_le fun P' hP' => ?_
    refine (countAFree_mono_adm T.post (L := L) (γ := γ) (δ := δ) (C1 := C1) (P := P')
      (B := fun κ => lgAdm T.post L γ (η / 2) P' κ ∧ ¬ Q κ) ?_).trans (hQ1 P' hP')
    rintro κ''' ⟨hlg, κ, _, _, hnq', rfl⟩
    rw [hBs] at hlg
    exact ⟨lgAdmOff_empty hlg, hnq'⟩
  -- the second class: operation (c)
  have hcls2 : MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧ ¬ Cls1One T Q {b, b'} L γ η κ) P ≤
      ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ (1 - γ)) * ENNReal.ofReal
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
          (((closureOne M₀ b b' x₁ x₂).atoms.card + 1 : ℝ) * L ^ (-(min γ (1 - γ) + η / 2 / 16)))) := by
    have hC := opCFree hγ0 hL1 hlog hδ (hCs.trans hC1) M₀ hloop hcap hconn0 {b, b'} x₁ x₂ hY
      (fun z hz => by simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption)
      hc huv hYconn hconnK P hP (fun κ => Adm κ ∧ ¬ Cls1One T Q {b, b'} L γ η κ)
      (fun κ h => ⟨y, y', by rw [hy]; exact mem_insert_self _ _, by rw [hy, hy'], hyy', (hAdm κ h.1).2⟩)
    refine hC.trans (mul_le_mul' le_rfl ?_)
    have hu : M₀.atom (M₀.mate x₁) ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms :=
      mem_sdiff.mpr ⟨M₀.atom_mem _, (mem_crossDarts.mp hx1m).2⟩
    have hv : M₀.atom (M₀.mate x₂) ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms :=
      mem_sdiff.mpr ⟨M₀.atom_mem _, (mem_crossDarts.mp hx2m).2⟩
    set a := M₀.atom (M₀.mate x₁) with ha_def
    set c := M₀.atom (M₀.mate x₂) with hc_def
    let ι := addBondEraseEquiv (Degen.eraseAtoms M₀ {b, b'}) a c
    have hA : (Degen.eraseAtoms M₀ {b, b'}).atoms =
        (MoleProp.eraseBond (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) (Sum.inr true)).atoms := by
      change (Degen.eraseAtoms M₀ {b, b'}).atoms = insert a (insert c (Degen.eraseAtoms M₀ {b, b'}).atoms)
      rw [insert_eq_of_mem hv, insert_eq_of_mem hu]
    have hcells := ladderCells_addBond_erase (Degen.eraseAtoms M₀ {b, b'}) hu hv
    have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms M₀ {b, b'}), 0 ≤ P S' := fun S' hS' => by
      have := (MoleProp.isLadderCell_erase_iff M₀ {b, b'} S').mp (mem_filter.mp hS').2
      exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M₀ this.1), this.1⟩)
    have hself : ({b, b'} : Finset V) \ {b, b'} = ∅ := by simp
    refine (MoleProp.countAFree_le_of_dart_equiv (Degen.eraseAtoms M₀ {b, b'})
      (MoleProp.eraseBond (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) (Sum.inr true)) ι hA
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) L γ δ C1 0 _
      (fun κ => lgAdm (MoleProp.eraseBond (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) (Sum.inr true))
          L γ (η / 2) P κ ∧
        MoleProp.erasedBondAdmissibility (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) (Sum.inr true)
          (fun κ0 => MoleProp.LargeGap (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) L γ (η / 2) (0 : Mom d) κ0 ∧
            Q κ0) κ) ?_ P).trans
      (hQ2 P (fun S hS => hPerase S (by rw [← hcells]; exact hS)))
    rintro κ'' ⟨κ, ⟨hκ, hn⟩, hsym, rfl⟩
    have hlgE := lgAdmOff_erase M₀ {b, b'} {b, b'} (hAdm κ hκ).1
    rw [hself] at hlgE
    refine ⟨lgAdm_relabel _ _ ι hA (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (lgAdm_mono (Degen.eraseAtoms M₀ {b, b'}) hL1 (show η / 2 ≤ η by linarith) (lgAdmOff_empty hlgE)), ?_⟩
    obtain ⟨g, hg, hpg⟩ := T.exists_postGoodOff hL1 hL11 hsym hcap {b, b'} hcB hdB (hAdm κ hκ).1.1
    refine ⟨T.postLabels κ g, ⟨postGoodOff_largeGap T hBs hpg, ?_⟩, T.postLabels_mate hsym g, ?_⟩
    · by_contra hq
      exact hn ⟨g, hg, hpg, hq⟩
    · funext x
      obtain ⟨z, rfl⟩ := ι.surjective x
      change T.postLabels κ g (Sum.inl z) = MoleProp.relabelDartLabels ι _ (ι z)
      rw [relabel_apply]
      rfl
  have hA1 : 1 ≤ 21125 * Real.log L ^ (14 : ℝ) := by
    have := Real.one_le_rpow hlog (show (0 : ℝ) ≤ 14 by norm_num)
    linarith
  have hl0 : 0 ≤ Real.log L := by linarith
  have hA0 : 0 ≤ 21125 * Real.log L ^ (14 : ℝ) := by linarith
  have hC0 : 0 ≤ 2 * 3 ^ d * ((d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ (1 - γ) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hl0 _)) (Real.rpow_nonneg hLp.le _)
  have hε1 : 0 ≤ (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
      (((closureOne M₀ b b' x₁ x₂).atoms.card + 1 : ℝ) * L ^ (-(η / 2 / 16))) := by
    have := hLp; positivity
  have hε2 : 0 ≤ (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
      (((closureOne M₀ b b' x₁ x₂).atoms.card + 1 : ℝ) * L ^ (-(min γ (1 - γ) + η / 2 / 16))) := by
    have := hLp; positivity
  have hs := split_arith (d := d) (m := m) (L := L) (γ := γ) (δ := δ) (ηs := η / 2)
    (a := ((closureOne M₀ b b' x₁ x₂).atoms.card : ℝ)) hγ.1 hγ.2 hδ0 hLe (Nat.cast_nonneg _) hsz hbig
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hA1
  refine (countAFree_or_le M₀ L γ δ C1 P Adm (fun κ => Adm κ ∧ Cls1One T Q {b, b'} L γ η κ)
    (fun κ => Adm κ ∧ ¬ Cls1One T Q {b, b'} L γ η κ) (fun κ hκ => by
      by_cases h : Cls1One T Q {b, b'} L γ η κ
      · exact Or.inl ⟨hκ, h⟩
      · exact Or.inr ⟨hκ, h⟩)).trans ?_
  calc _ ≤ _ := add_le_add hcls1 hcls2
    _ ≤ _ := add_le_add (le_mul_of_one_le_left bot_le h1) (le_mul_of_one_le_left bot_le h1)
    _ ≤ ENNReal.ofReal (L ^ (-(η / 2 / 32))) := ofReal_sum_bound _ _ _ _ _ hA0 hC0 hε1 hε2 hs
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))

end WaveTurbulence.FinalCountG8
