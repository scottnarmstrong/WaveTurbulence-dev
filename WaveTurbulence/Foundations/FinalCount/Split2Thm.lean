/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Split2Main
import Mathlib.Tactic

/-! # Case (4), two chains, not `Y`-exceptional: the decoration-level theorem (finalcount-g8, F6-1)

`case4_two_split`: for a case-(4) component with two separate `β`-chains whose closure `𝕄₁` is not `Y`-exceptional and
has no small cell, `𝔄₀ ≤ L^{-η/128}`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem eleven_le_rpow {t L : ℝ} (ht : 0 < t) (h : (11 : ℝ) ^ (1 / t) ≤ L) : 11 ≤ L ^ t := by
  calc (11 : ℝ) = ((11 : ℝ) ^ (1 / t)) ^ t := by
        rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
    _ ≤ L ^ t := Real.rpow_le_rpow (by positivity) h ht.le

theorem case4_two_split (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M₀ : Molecule V D),
        (∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) → (∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z)) →
        (∀ a ∈ M₀.atoms, M₀.deg a % 2 = 0) → (∀ a ∈ M₀.atoms, ∀ c ∈ M₀.atoms, M₀.SameComponent a c) →
        ∀ (b b' : V) (y₁ y₂ y₃ y₄ : D), b ∈ M₀.atoms → b' ∈ M₀.atoms → b ≠ b' →
        (M₀.outdeg b = 1 ∧ M₀.indeg b = 1) → (M₀.outdeg b' = 1 ∧ M₀.indeg b' = 1) →
        crossDarts M₀ {b} = {y₁, y₂} → M₀.out y₁ = false → M₀.out y₂ = true →
        crossDarts M₀ {b'} = {y₃, y₄} → M₀.out y₃ = false → M₀.out y₄ = true →
        M₀.atom (M₀.mate y₁) ≠ M₀.atom (M₀.mate y₂) → M₀.atom (M₀.mate y₃) ≠ M₀.atom (M₀.mate y₄) →
        M₀.atom (M₀.mate y₁) ≠ b' → M₀.atom (M₀.mate y₂) ≠ b' →
        M₀.atom (M₀.mate y₃) ≠ b → M₀.atom (M₀.mate y₄) ≠ b →
        RegCore (closureTwo M₀ b b' y₁ y₂ y₃ y₄) → (tripSet (closureTwo M₀ b b' y₁ y₂ y₃ y₄)).card ≤ 2 →
        ((closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        5 ≤ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card → ¬ YReachesQT (closureTwo M₀ b b' y₁ y₂ y₃ y₄) →
        ¬ YReachesSmallCell (closureTwo M₀ b b' y₁ y₂ y₃ y₄) →
        ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S) →
        ∀ Adm : (D → (Fin d → ℤ)) → Prop,
          (∀ κ, Adm κ → lgAdmOff M₀ {b, b'} L γ η P κ ∧ κ y₁ ≠ κ y₂ ∧ κ y₃ ≠ κ y₄) →
          MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128))) := by
  have hγ0 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  have hmin : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  have hpos : 0 < min γ (1 - γ) := lt_min hγ0.1 (by linarith [hγ.2])
  have hηs0 : 0 < η / 2 / 2 := by positivity
  obtain ⟨Cs, hCs, hP104⟩ := prop104_two_proved.{u, v} d hd γ hγ (η / 2 / 2) hηs0 (by linarith) (by
      have : (d : ℝ) * (η / 2 / 2) ≤ d * η := by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        nlinarith
      linarith) (by linarith)
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R1, hR1⟩ := hP104 m C1 hC1 δ hδ
  obtain ⟨A0, hA0⟩ := exists_mul_log_rpow_le (splitK d m δ) (((56 + m : ℕ) : ℝ)) (θ := η / 2 / 2 / 32) (by positivity)
  refine ⟨max (max R1 A0) (max (Real.exp 1) ((11 : ℝ) ^ (1 / (η / 2 / 2)))), fun L hL => ?_⟩
  have hLR1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLA0 : A0 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL11' : (11 : ℝ) ^ (1 / (η / 2 / 2)) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hL11b : 11 ≤ L ^ (η / 2 / 2) := eleven_le_rpow hηs0 hL11'
  have hL11a : 11 ≤ L ^ (η / 2) := by
    refine hL11b.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hbig : splitK d m δ * Real.log L ^ (56 + m) ≤ L ^ (η / 2 / 2 / 32) := by
    have := hA0 L hLA0
    rwa [Real.rpow_natCast] at this
  have hδ0 := hδ.1
  intro V D _ _ _ M₀ hcap hloop heven hconn0 b b' y₁ y₂ y₃ y₄ hb hb' hbb' hdb hdb' hc1 ho1 ho2 hc2 ho3 ho4 huv huv'
    hs1 hs2 hs3 hs4 hcl htrip hsz h5 hnq hnsc P hP Adm hAdm
  classical
  have hy12 : y₁ ≠ y₂ := fun h => huv (by rw [h])
  have hy34 : y₃ ≠ y₄ := fun h => huv' (by rw [h])
  have hy1m : y₁ ∈ crossDarts M₀ {b} := by rw [hc1]; exact mem_insert_self _ _
  have hy2m : y₂ ∈ crossDarts M₀ {b} := by rw [hc1]; exact mem_insert_of_mem (mem_singleton_self _)
  have hy3m : y₃ ∈ crossDarts M₀ {b'} := by rw [hc2]; exact mem_insert_self _ _
  have hy4m : y₄ ∈ crossDarts M₀ {b'} := by rw [hc2]; exact mem_insert_of_mem (mem_singleton_self _)
  have hat3 : M₀.atom y₃ = b' := mem_singleton.mp (mem_crossDarts.mp hy3m).1
  have hat4 : M₀.atom y₄ = b' := mem_singleton.mp (mem_crossDarts.mp hy4m).1
  have hu1 : M₀.atom (M₀.mate y₁) ≠ b := fun h => (mem_crossDarts.mp hy1m).2 (by rw [h]; exact mem_singleton_self _)
  have hu2 : M₀.atom (M₀.mate y₂) ≠ b := fun h => (mem_crossDarts.mp hy2m).2 (by rw [h]; exact mem_singleton_self _)
  have hu3 : M₀.atom (M₀.mate y₃) ≠ b' := fun h => (mem_crossDarts.mp hy3m).2 (by rw [h]; exact mem_singleton_self _)
  have hu4 : M₀.atom (M₀.mate y₄) ≠ b' := fun h => (mem_crossDarts.mp hy4m).2 (by rw [h]; exact mem_singleton_self _)
  have hKA : ({b} : Finset V) ⊆ M₀.atoms := by simpa using hb
  -- the first chain
  let Ta : TwoExit M₀ := ⟨{b}, hKA, y₂, y₁, by rw [hc1]; exact pair_comm _ _, hy12.symm, huv.symm, ho2, ho1⟩
  have p₃ : M₀.atom y₃ ∉ ({b} : Finset V) ∧ M₀.atom (M₀.mate y₃) ∉ ({b} : Finset V) :=
    ⟨by rw [hat3]; simpa using hbb'.symm, by simpa using hs3⟩
  have p₄ : M₀.atom y₄ ∉ ({b} : Finset V) ∧ M₀.atom (M₀.mate y₄) ∉ ({b} : Finset V) :=
    ⟨by rw [hat4]; simpa using hbb'.symm, by simpa using hs4⟩
  obtain ⟨hcK, hdir⟩ := chain_after_erase hloop hc2 p₃ p₄
  have hc1' : M₀.atom (M₀.mate y₁) ∉ ({b'} : Finset V) := by simpa using hs1
  have hc2' : M₀.atom (M₀.mate y₂) ∉ ({b'} : Finset V) := by simpa using hs2
  have hcross2 : crossDarts Ta.post {b'} = {Sum.inl ⟨y₄, p₄⟩, Sum.inl ⟨y₃, p₃⟩} := by
    change crossDarts (Mole.addBond (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))) {b'} = _
    rw [crossDarts_addBond_inl _ hc1' hc2' hcK]
    exact pair_comm _ _
  have hbN : ({b'} : Finset V) ⊆ Ta.post.atoms := by
    rw [Ta.post_atoms]
    intro x hx
    rw [mem_singleton] at hx
    rw [hx]
    exact mem_sdiff.mpr ⟨hb', by show b' ∉ ({b} : Finset V); simpa using hbb'.symm⟩
  let Tb : TwoExit Ta.post := ⟨{b'}, hbN, Sum.inl ⟨y₄, p₄⟩, Sum.inl ⟨y₃, p₃⟩, hcross2,
    fun h => hy34 (congrArg Subtype.val (Sum.inl.inj h)).symm, huv'.symm, ho4, ho3⟩
  let Φ : Degen.RetainedDart Ta.post Tb.Y ⊕ Bool ≃
      (Degen.RetainedDart (Degen.eraseAtoms M₀ {b}) {b'} ⊕ Bool) ⊕ Bool :=
    bondPostEquiv (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂)) {b'} hc1' hc2'
  have hA : Tb.post.atoms = (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms :=
    bondPostEquiv_atoms (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))
      (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄)) {b'} hc1' hc2'
  have ha : ∀ x, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atom (Φ x) = Tb.post.atom x := fun x =>
    bondPostEquiv_atom (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))
      (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄)) {b'} hc1' hc2' x
  have hm : ∀ x, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).mate (Φ x) = Φ (Tb.post.mate x) := fun x =>
    bondPostEquiv_mate (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))
      (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄)) {b'} hc1' hc2' x
  have ho : ∀ x, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).out (Φ x) = Tb.post.out x := fun x =>
    bondPostEquiv_out (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))
      (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄)) {b'} hc1' hc2' x
  have hSplit := hR1 L hLR1 (closureTwo M₀ b b' y₁ y₂ y₃ y₄) hcl.cap hcl.loop hcl.reg hcl.conn hcl.nocut
    (triple_of_tripSet htrip) (bb_le_three_of_nonexc hcl hnq) hsz hnq hnsc (Φ (Sum.inr true))
  obtain ⟨Q, hQ1, hQ2⟩ := hSplit
  -- structure of the first post
  have hpostA : ∀ a ∈ Ta.post.atoms, ∀ c ∈ Ta.post.atoms, Ta.post.SameComponent a c := Ta.post_connected hconn0
  have h5A : 5 ≤ Ta.post.atoms.card := h5.trans (card_le_card (by
    rw [← hA, Tb.post_atoms]; exact sdiff_subset))
  have hopenA : ∀ S ∈ MoleProp.ladderCells Ta.post, GoodCell Ta.post S := fun S hS => goodCell_of_connected hpostA h5A hS
  have hcap1 := Ta.post_caps hcap
  have hloop1 := Ta.post_loop hloop
  have hdb2 : (Degen.eraseAtoms M₀ {b}).outdeg b' = 1 ∧ (Degen.eraseAtoms M₀ {b}).indeg b' = 1 := by
    unfold Molecule.outdeg Molecule.indeg; rw [hdir true, hdir false]; exact hdb'
  have hchb : ∀ x ∈ Tb.Y, Ta.post.outdeg x = 1 ∧ Ta.post.indeg x = 1 := by
    intro x hx
    have hx' : x = b' := mem_singleton.mp hx
    subst hx'
    have hdne : M₀.atom (M₀.mate y₁) ≠ x := fun h => hc1' (by rw [h]; exact mem_singleton_self _)
    have hcne : M₀.atom (M₀.mate y₂) ≠ x := fun h => hc2' (by rw [h]; exact mem_singleton_self _)
    constructor
    · change (Mole.addBond (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))).outdeg x = 1
      rw [addBond_outdeg, if_neg hdne, add_zero]; exact hdb2.1
    · change (Mole.addBond (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))).indeg x = 1
      rw [addBond_indeg', if_neg hcne, add_zero]; exact hdb2.2
  have hYconna : ∀ x ∈ Ta.Y, ∀ y ∈ Ta.Y, (piece M₀ Ta.Y).SameComponent x y := fun x hx y hy => by
    rw [mem_singleton.mp hx, mem_singleton.mp hy]; exact Relation.EqvGen.refl _
  have hYconnb : ∀ x ∈ Tb.Y, ∀ y ∈ Tb.Y, (piece Ta.post Tb.Y).SameComponent x y := fun x hx y hy => by
    rw [mem_singleton.mp hx, mem_singleton.mp hy]; exact Relation.EqvGen.refl _
  have hcBa : Ta.c ∉ ({b, b'} : Finset V) := by
    change M₀.atom (M₀.mate y₂) ∉ ({b, b'} : Finset V)
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hu2, hs2⟩
  have hdBa : Ta.d ∉ ({b, b'} : Finset V) := by
    change M₀.atom (M₀.mate y₁) ∉ ({b, b'} : Finset V)
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hu1, hs1⟩
  have hcBb : Tb.c ∉ (({b, b'} : Finset V) \ Ta.Y) := by
    change M₀.atom (M₀.mate y₄) ∉ (({b, b'} : Finset V) \ {b})
    simp only [mem_sdiff, mem_insert, mem_singleton, not_and, not_not]
    intro h; rcases h with h | h
    · exact h
    · exact absurd h hu4
  have hdBb : Tb.d ∉ (({b, b'} : Finset V) \ Ta.Y) := by
    change M₀.atom (M₀.mate y₃) ∉ (({b, b'} : Finset V) \ {b})
    simp only [mem_sdiff, mem_insert, mem_singleton, not_and, not_not]
    intro h; rcases h with h | h
    · exact h
    · exact absurd h hu3
  have hpostB : ∀ a ∈ Tb.post.atoms, ∀ c ∈ Tb.post.atoms, Tb.post.SameComponent a c := Tb.post_connected hpostA
  have h5B : 5 ≤ Tb.post.atoms.card := by rw [hA]; exact h5
  have hopenB : ∀ S ∈ MoleProp.ladderCells Tb.post, GoodCell Tb.post S := fun S hS => goodCell_of_connected hpostB h5B hS
  have hBs : ((({b, b'} : Finset V) \ Ta.Y) \ Tb.Y) = ∅ := by
    change ((({b, b'} : Finset V) \ {b}) \ {b'}) = ∅
    ext x; simp only [mem_sdiff, mem_insert, mem_singleton, notMem_empty, iff_false]; tauto
  have heven1 : ∀ a ∈ Ta.post.atoms, Ta.post.deg a % 2 = 0 := by
    intro a ha
    rw [Ta.post_atoms] at ha
    obtain ⟨ha1, ha2⟩ := mem_sdiff.mp ha
    rw [Ta.post_deg ha2]; exact heven a ha1
  have hpostE : ∀ a ∈ (Degen.eraseAtoms Ta.post Tb.Y).atoms, ∀ c ∈ (Degen.eraseAtoms Ta.post Tb.Y).atoms,
      (Degen.eraseAtoms Ta.post Tb.Y).SameComponent a c :=
    connected_erase_of_two_cross Ta.post hpostA heven1 {b'} (by
      rw [hcross2]; exact card_pair (fun h => hy34 (congrArg Subtype.val (Sum.inl.inj h)).symm))
  have hxy : Ta.post.atom Tb.y = Ta.post.atom Tb.x := by
    change M₀.atom y₃ = M₀.atom y₄
    rw [hat3, hat4]
  have hY3a : Ta.Y.card ≤ 3 := by change ({b} : Finset V).card ≤ 3; simp
  have hY3b : Tb.Y.card ≤ 3 := by change ({b'} : Finset V).card ≤ 3; simp
  have hcha : ∀ x ∈ Ta.Y, M₀.outdeg x = 1 ∧ M₀.indeg x = 1 := fun x hx => by
    rw [mem_singleton.mp hx]; exact hdb
  -- the two classes
  have hcls1 := class1_bound (η := η) hL1 hlog hδ (hCs.trans hC1) Ta Tb {b, b'} hcap hloop hconn0 hY3a hcha hYconna hpostA hopenA
    hcap1 hloop1 hY3b hchb hYconnb hpostB hopenB hBs (closureTwo M₀ b b' y₁ y₂ y₃ y₄) Φ hA ha hm ho Q hQ1 P hP Adm
    (fun κ h => (hAdm κ h).1)
  have hcls2 := class2_bound (η := η) hL1 hlog hη.le hγ0 hδ (hCs.trans hC1) hL11a hL11b Ta Tb {b, b'} hcap hloop hconn0 hY3a hcha
    hYconna hcBa hdBa hpostA hopenA hcap1 hloop1 hchb hYconnb hcBb hdBb hpostE hxy hBs
    (closureTwo M₀ b b' y₁ y₂ y₃ y₄) Φ hA ha hm ho Q hQ2 P hP Adm (fun κ h => (hAdm κ h).1)
    (fun κ hκ g h => (hAdm κ hκ).2.2 h.symm)
  have hl0 : 0 ≤ Real.log L := by linarith
  have hA0 : 0 ≤ 21125 * Real.log L ^ (14 : ℝ) := mul_nonneg (by norm_num) (Real.rpow_nonneg hl0 _)
  have hC0 : 0 ≤ 2 * 3 ^ d * ((d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ (1 - γ) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hl0 _)) (Real.rpow_nonneg hLp.le _)
  have hε1 : 0 ≤ (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
      ((((closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card : ℕ) + 1 : ℝ) * L ^ (-(η / 2 / 2 / 16))) := by
    have := hLp; positivity
  have hε2 : 0 ≤ (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
      (((((closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card : ℕ) : ℝ) + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 2 / 16))) := by
    have := hLp; positivity
  have hs := split_arith (d := d) (m := m) (L := L) (γ := γ) (δ := δ) (ηs := η / 2 / 2)
    (a := ((closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card : ℝ)) hγ.1 hγ.2 hδ0 hLe (Nat.cast_nonneg _) hsz hbig
  refine (countAFree_or_le M₀ L γ δ C1 P Adm (fun κ => Adm κ ∧ Cls1 Ta Tb Φ Q {b, b'} L γ η κ)
    (fun κ => Adm κ ∧ ¬ Cls1 Ta Tb Φ Q {b, b'} L γ η κ) (fun κ hκ => by
      by_cases h : Cls1 Ta Tb Φ Q {b, b'} L γ η κ
      · exact Or.inl ⟨hκ, h⟩
      · exact Or.inr ⟨hκ, h⟩)).trans ((add_le_add hcls1 hcls2).trans ?_)
  refine (ofReal_sum_bound _ _ _ _ _ hA0 hC0 hε1 hε2 hs).trans (le_of_eq ?_)
  congr 2
  ring

end WaveTurbulence.FinalCountG8
