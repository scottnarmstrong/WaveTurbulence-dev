/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.ThmABase
import Mathlib.Tactic

/-! # Theorem A, Steps 3–4: from `𝕄₁ ∖ ℓ` to `T ∖ ℓ*`

* `tMinus_afree`: `𝔄(T ∖ ℓ*) ≤ C δ⁻² (C₁⁻¹ δ^{1/2})³ L^{−γ₀−κ(γ)}` for every bond and every LG parameter
  (`χ(T ∖ ℓ*) = 3`, no ladder cell).
* `YRouteT k 𝕄`: a route of `k` complete (Y2) sequences from `𝕄` to `T` (case-4 note 3.1: on a 4-regular molecule every
  complete sequence of a route to `T` ends in (Y2)).
* `route_step`: one sequence carries a bound for every `𝕄′ ∖ ℓ′` back to every `𝕄 ∖ ℓ` (case-4 note Lemma 4.1: ylem2,
  second statement, or the "not removed" variant; `𝕄 ∖ ℓ` is connected since a 4-regular connected molecule has no
  bridge).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Bonded atoms are adjacent. -/
theorem sameComponent_of_bondsBetween_pos {M : Molecule V D} {a b : V} (h : 0 < M.bondsBetween a b) :
    M.SameComponent a b := by
  obtain ⟨x, hx⟩ := card_pos.mp h
  have he : M.ends x = s(a, b) := (mem_filter.mp hx).2
  unfold Molecule.ends at he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Relation.EqvGen.rel _ _ ⟨x, h1, h2⟩
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨x, h1, h2⟩)

/-- **`T` is 4-regular and connected.** -/
theorem IsT.reg_conn {M : Molecule V D} (hT : IsT M) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) :
    (∀ a ∈ M.atoms, M.deg a = 4) ∧ ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b := by
  classical
  obtain ⟨a, b, c, hab, hbc, hac, hs, h1, h2, h3, _⟩ := hT
  have hbb : ∀ u ∈ M.atoms, ∀ w ∈ M.atoms, u ≠ w → M.bondsBetween u w = 2 := by
    intro u hu w hw huw
    rw [hs] at hu hw
    simp only [mem_insert, mem_singleton] at hu hw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first | exact absurd rfl huw | assumption | (rw [bondsBetween_symm]; assumption)
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [deg_eq_sum_bb M hloop]
    rw [hs] at hx ⊢
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · rw [show ({x, b, c} : Finset V).erase x = {b, c} by
        ext z; simp only [mem_erase, mem_insert, mem_singleton]; aesop, sum_pair hbc, h1, h3]
    · rw [show ({a, x, c} : Finset V).erase x = {a, c} by
        ext z; simp only [mem_erase, mem_insert, mem_singleton]; aesop, sum_pair hac, bondsBetween_symm, h1, h2]
    · rw [show ({a, b, x} : Finset V).erase x = {a, b} by
        ext z; simp only [mem_erase, mem_insert, mem_singleton]; aesop, sum_pair hab, bondsBetween_symm,
        bondsBetween_symm M x b, h3, h2]
  · by_cases hxy : x = y
    · rw [hxy]; exact Relation.EqvGen.refl _
    · exact sameComponent_of_bondsBetween_pos (by rw [hbb x hx y hy hxy]; norm_num)

/-- `T ∖ ℓ*` has circuit rank 3. -/
theorem IsT.circuitRank_eraseBond {M : Molecule V D} (hT : IsT M) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (e : D) : (MoleProp.eraseBond M e).circuitRank = 3 := by
  classical
  obtain ⟨hreg, hconn⟩ := hT.reg_conn hloop
  obtain ⟨a, b, c, hab, hbc, hac, hs, _, _, _, hE⟩ := hT
  have hb := MoleProp.card_bonds_eraseBond_add_one M e
  have hconnN := eraseBond_connected_of_even M (fun x hx => by rw [hreg x hx]; exact ⟨2, rfl⟩) hconn e
  have hF := Mole.numComponents_eq_one (MoleProp.eraseBond M e) ⟨a, by
    change a ∈ M.atoms; rw [hs]; exact mem_insert_self _ _⟩ hconnN
  unfold Molecule.circuitRank
  rw [hF]
  change ((MoleProp.eraseBond M e).bonds.card : ℤ) - (M.atoms.card : ℤ) + ((1 : ℕ) : ℤ) = 3
  rw [hs, card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]), card_singleton]
  omega

omit [DecidableEq D] in
/-- A molecule with fewer than four atoms has no ladder cell. -/
theorem ladderCells_eq_empty_of_card {M : Molecule V D} (h : M.atoms.card < 4) : MoleProp.ladderCells M = ∅ := by
  classical
  rw [eq_empty_iff_forall_notMem]
  intro S hS
  obtain ⟨hsub, u, w, hL, rfl⟩ := mem_filter.mp hS
  have h4 := Degen.ladderAtoms_card_of_injective hL.2.1
  have := card_le_card (mem_powerset.mp hsub)
  omega

end

/-- **`𝔄(T ∖ ℓ*)`**, normalized (case-4 note Step 4). -/
theorem tMinus_afree (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀,
      ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsT M →
        (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
        ∀ (e : D) (η' C1 : ℝ) (P : Finset V → ℝ),
          AFree (MoleProp.eraseBond M e) d L γ δ η' C1 P ≤
            ENNReal.ofReal (C * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 *
              L ^ (-(1 - γ) - CountLemmas.kappaHalf γ)) := by
  obtain ⟨C, hC, hb⟩ := tMinus_countE d hd γ hγ
  refine ⟨C, hC, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hb δ hδ
  refine ⟨max L₀ 1, fun L hL V D _ _ _ M hT hcap hloop e η' C1 P => ?_⟩
  classical
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right _ _).trans hL)
  have hcount := hL₀ L ((le_max_left _ _).trans hL) M hT hcap hloop e (lgAdm (MoleProp.eraseBond M e) L γ η' P)
  have hχ := hT.circuitRank_eraseBond hloop e
  have hcells : MoleProp.ladderCells (MoleProp.eraseBond M e) = ∅ := by
    obtain ⟨a, b, c, hab, hbc, hac, hs, _⟩ := hT
    apply ladderCells_eq_empty_of_card
    change M.atoms.card < 4
    rw [hs, card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]), card_singleton]
    norm_num
  unfold AFree MoleProp.countAFree MoleProp.cellProduct
  rw [hcells, prod_empty, mul_one, hχ]
  have hX : 0 ≤ C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - CountLemmas.kappaHalf γ) := by positivity
  refine (mul_le_mul_of_nonneg_right hcount bot_le).trans ?_
  rw [← ENNReal.ofReal_mul hX]
  apply ENNReal.ofReal_le_ofReal (le_of_eq _)
  have hpow : L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - CountLemmas.kappaHalf γ) * L ^ (-((d : ℝ) - γ) * ((3 : ℤ) : ℝ)) =
      L ^ (-(1 - γ) - CountLemmas.kappaHalf γ) := by
    rw [← Real.rpow_add hLp]; congr 1; push_cast; ring
  rw [zpow_ofNat]
  calc C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - CountLemmas.kappaHalf γ) *
        (L ^ (-((d : ℝ) - γ) * ((3 : ℤ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3)
      = C * δ⁻¹ ^ 2 * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 *
        (L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - CountLemmas.kappaHalf γ) * L ^ (-((d : ℝ) - γ) * ((3 : ℤ) : ℝ))) := by
          ring
    _ = _ := by rw [hpow]

/-- **A route of `k` complete (Y2) sequences to `T`.** -/
inductive YRouteT : ℕ → {V : Type u} → {D : Type v} → [DecidableEq V] → [Fintype D] → [DecidableEq D] →
    Molecule V D → Prop where
  | done {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) :
      IsT M → YRouteT 0 M
  | y2 {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (k : ℕ) (M : Molecule V D)
      (hcap : ∀ w ∈ M.atoms, M.outdeg w ≤ 2 ∧ M.indeg w ≤ 2) (C : YChain M) (E : Y2End C) :
      M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2 →
      YRouteT k (E.toTwoExit hcap).post → YRouteT (k + 1) M

/-- ylem2, second statement (`ℓ` removed by the sequence), at a fixed `L`. -/
def Ylem2SecondAt (d : ℕ) (L γ δ η C1 : ℝ) : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (C : YChain M) (E : Y2End C) (e : D),
    (M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set) →
    (∀ u ∈ M.atoms, ∀ w ∈ M.atoms, (MoleProp.eraseBond M e).SameComponent u w) →
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
      AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
        ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
          AFreeSup (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)) d L γ δ (η / 2) C1

/-- The "not removed" variant (case-4 note Lemma 4.1) at a fixed `L`. -/
def Ylem2NotRemovedAt (d : ℕ) (L γ δ η C1 : ℝ) : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (C : YChain M) (E : Y2End C) (e : D)
    (heY : M.atom e ∉ (E.toTwoExit hcap).Y ∧ M.atom (M.mate e) ∉ (E.toTwoExit hcap).Y),
    (∀ u ∈ M.atoms, ∀ w ∈ M.atoms, (MoleProp.eraseBond M e).SameComponent u w) →
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
      AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
        ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
          AFreeSup (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)) d L γ δ (η / 2) C1

theorem ylem2At_of (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      Ylem2SecondAt.{u, v} d L γ δ η C1 ∧ Ylem2NotRemovedAt.{u, v} d L γ δ η C1 := by
  obtain ⟨C₁, h₁, hs⟩ := ylem2_second d hd γ hγ η hη hηmax
  obtain ⟨C₂, h₂, hn⟩ := ylem2_notRemoved d hd γ hγ η hη hηmax
  refine ⟨max C₁ C₂, h₁.trans (le_max_left _ _), fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hs C1 (by linarith [le_max_left C₁ C₂]) δ hδ
  obtain ⟨R₂, hR₂⟩ := hn C1 (by linarith [le_max_right C₁ C₂]) δ hδ
  exact ⟨max R₁ R₂, fun L hL => ⟨fun M => hR₁ L ((le_max_left _ _).trans hL) M,
    fun M => hR₂ L ((le_max_right _ _).trans hL) M⟩⟩

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **One (Y2) sequence** (case-4 note Lemma 4.1): a bound for every `𝕄′ ∖ ℓ′` at LG parameter `η/2` gives
`𝔄(𝕄 ∖ ℓ) ≤ K · bound` for every bond `ℓ` of the 4-regular connected `𝕄`. -/
theorem route_step {d : ℕ} {L γ δ η C1 X : ℝ} (hsec : Ylem2SecondAt.{u, v} d L γ δ η C1)
    (hnr : Ylem2NotRemovedAt.{u, v} d L γ δ η C1) (M : Molecule V D)
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (h4 : ∀ v ∈ M.atoms, M.deg v = 4)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) (C : YChain M) (E : Y2End C)
    (hpost : ∀ (e₁ : Degen.RetainedDart M (E.toTwoExit hcap).Y ⊕ Bool) (P' : Finset V → ℝ),
      (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond (E.toTwoExit hcap).post e₁), 0 ≤ P' S) →
      AFree (MoleProp.eraseBond (E.toTwoExit hcap).post e₁) d L γ δ (η / 2) C1 P' ≤ ENNReal.ofReal X)
    (e : D) (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) :
    AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
      ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) * ENNReal.ofReal X := by
  classical
  have hconnN := eraseBond_connected_of_even M (fun a ha => by rw [h4 a ha]; exact ⟨2, rfl⟩) hconn e
  have hY := E.toTwoExit_Y hcap
  by_cases hrem : M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set
  · exact (hsec M hcap C E e hrem hconnN P hP).trans (mul_le_mul' le_rfl (iSup₂_le fun P' hP' => hpost _ P' hP'))
  · push Not at hrem
    have heY : M.atom e ∉ (E.toTwoExit hcap).Y ∧ M.atom (M.mate e) ∉ (E.toTwoExit hcap).Y := by
      rw [hY]; exact hrem
    exact (hnr M hcap C E e heY hconnN P hP).trans (mul_le_mul' le_rfl (iSup₂_le fun P' hP' => hpost _ P' hP'))

/-- The post molecule of a 4-regular molecule is 4-regular, with caps, no loops, connected. -/
theorem Y2End.post_props {M : Molecule V D} {C : YChain M} (E : Y2End C)
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (h4 : ∀ v ∈ M.atoms, M.deg v = 4) (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    (∀ v ∈ (E.toTwoExit hcap).post.atoms, (E.toTwoExit hcap).post.outdeg v ≤ 2 ∧
      (E.toTwoExit hcap).post.indeg v ≤ 2) ∧
    (∀ z, (E.toTwoExit hcap).post.atom z ≠ (E.toTwoExit hcap).post.atom ((E.toTwoExit hcap).post.mate z)) ∧
    (∀ v ∈ (E.toTwoExit hcap).post.atoms, (E.toTwoExit hcap).post.deg v = 4) ∧
    (∀ u ∈ (E.toTwoExit hcap).post.atoms, ∀ v ∈ (E.toTwoExit hcap).post.atoms,
      (E.toTwoExit hcap).post.SameComponent u v) := by
  refine ⟨(E.toTwoExit hcap).post_caps hcap, (E.toTwoExit hcap).post_loop hloop, fun a ha => ?_,
    (E.toTwoExit hcap).post_connected hconn⟩
  rw [TwoExit.post_atoms] at ha
  rw [TwoExit.post_deg _ (mem_sdiff.mp ha).2]
  exact h4 a (mem_sdiff.mp ha).1

end WaveTurbulence.MoleProp4
