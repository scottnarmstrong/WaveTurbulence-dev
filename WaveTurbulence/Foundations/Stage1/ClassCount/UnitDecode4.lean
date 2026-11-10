/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode3
import Mathlib.Tactic

/-!
# CLASSCOUNT: a vine chain is a unit code

`chain_decode`: a vine chain `U` (`Chain M U a b n`) that is a block with joints `(a, b)` has a unit code `cs`
(`n` well-formed ingredient codes) and a labelling `lab` of its atoms by `0 … W` (`W = unitWeight cs`), injective on
`U` with `lab a = 0`, `lab b = W`, whose arcs are `unitArcs cs`.  The proof is by induction on the chain, using
`vine_decode` (one ingredient) and `group_split` (the bonds of a concatenation).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine

theorem ingPosOf_add (p : ℕ) {sz : ℕ} (hsz : 1 ≤ sz) (sw : Bool) (t : ℕ) :
    ingPosOf p sz sw t = p + ingPosOf 0 sz sw t := by
  unfold ingPosOf; split_ifs <;> first | omega | contradiction

theorem ingPosOf_lt {sz : ℕ} (hsz : 2 ≤ sz) {sw : Bool} {t : ℕ} (ht : t < sz) : ingPosOf 0 sz sw t < sz := by
  unfold ingPosOf; split_ifs <;> first | omega | contradiction

theorem ingPosOf_inj {sz : ℕ} {sw : Bool} {t t' : ℕ} (ht : t < sz) (ht' : t' < sz)
    (h : ingPosOf 0 sz sw t = ingPosOf 0 sz sw t') : t = t' := by
  unfold ingPosOf at h; split_ifs at h <;> first | omega | contradiction

theorem ingPosOf_surj {sz : ℕ} (hsz : 2 ≤ sz) (sw : Bool) {y : ℕ} (hy : y < sz) :
    ∃ t, t < sz ∧ ingPosOf 0 sz sw t = y := by
  by_cases h0 : y = 0
  · refine ⟨if sw then 1 else 0, by split_ifs <;> first | omega | contradiction, ?_⟩
    unfold ingPosOf; split_ifs <;> first | omega | contradiction
  · by_cases h1 : y = sz - 1
    · refine ⟨if sw then 0 else 1, by split_ifs <;> first | omega | contradiction, ?_⟩
      unfold ingPosOf; split_ifs <;> first | omega | contradiction
    · refine ⟨y + 1, by omega, ?_⟩
      unfold ingPosOf; split_ifs <;> first | omega | contradiction

theorem ingPosOf_first {sz : ℕ} (hsz : 2 ≤ sz) (sw : Bool) {t : ℕ} (ht : t = if sw then 1 else 0) (p : ℕ) :
    ingPosOf p sz sw t = p := by
  unfold ingPosOf; split_ifs at ht ⊢ <;> first | omega | contradiction

theorem ingPosOf_second {sz : ℕ} (hsz : 2 ≤ sz) (sw : Bool) {t : ℕ} (ht : t = if sw then 0 else 1) (p : ℕ) :
    ingPosOf p sz sw t = p + sz - 1 := by
  unfold ingPosOf; split_ifs at ht ⊢ <;> first | omega | contradiction

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `groupArcs` only depends on the labels of the atoms of the group. -/
theorem groupArcs_congr (M : Molecule V D) (S : Finset V) {l l' : V → ℕ} (h : ∀ v ∈ S, l v = l' v) :
    groupArcs M S l = groupArcs M S l' := by
  classical
  unfold groupArcs
  refine Multiset.map_congr rfl (fun x hx => ?_)
  have hx' := (Finset.mem_filter.mp (by simpa using hx : x ∈ (Finset.univ.filter fun x => M.out x = true ∧ M.InGroup S x))).2.2
  rw [h _ hx'.1, h _ hx'.2]

theorem unitArcsAux_append (c : IngCode) : ∀ (cs : List IngCode) (p : ℕ), (∀ d ∈ cs, 1 ≤ d.size) →
    unitArcsAux p (cs ++ [c]) = unitArcsAux p cs ++
      ingArcs c (ingPosOf (p + unitWeight cs) c.size c.swap)
  | [], p, _ => by simp [unitArcsAux, unitWeight]
  | d :: cs, p, h => by
    have hd := h d (by simp)
    have := unitArcsAux_append c cs (p + d.size - 1) (fun e he => h e (by simp [he]))
    have hw : p + unitWeight (d :: cs) = p + d.size - 1 + unitWeight cs := by
      simp only [unitWeight, List.map_cons, List.sum_cons]; omega
    simp only [List.cons_append, unitArcsAux, this, List.append_assoc]
    rw [hw]


theorem unitWeight_append_single (cs : List IngCode) (c : IngCode) :
    unitWeight (cs ++ [c]) = unitWeight cs + (c.size - 1) := by
  simp [unitWeight]

/-- Joints of a vine realization are `0, 1`. -/
theorem vine_joint_cases {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) :
    (R.f a = 0 ∧ R.f b = 1) ∨ (R.f a = 1 ∧ R.f b = 0) := by
  have h1 : R.f a ∈ ({0, 1} : Finset ℕ) := by rw [← R.joints_eq]; simp
  have h2 : R.f b ∈ ({0, 1} : Finset ℕ) := by rw [← R.joints_eq]; simp
  have h3 : R.f a ≠ R.f b := fun h => hab (R.injOn ha hb h)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  omega


/-- One vine ingredient as a code with a shifted labelling. -/
theorem vine_chain_code (M : Molecule V D) {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) (p : ℕ) :
    ∃ c : IngCode, c.Wf ∧ 2 ≤ c.size ∧
      Set.InjOn (fun v => ingPosOf p c.size c.swap (R.f v)) S ∧
      S.image (fun v => ingPosOf p c.size c.swap (R.f v)) = Finset.Ico p (p + c.size) ∧
      ingPosOf p c.size c.swap (R.f a) = p ∧ ingPosOf p c.size c.swap (R.f b) = p + c.size - 1 ∧
      groupArcs M S (fun v => ingPosOf p c.size c.swap (R.f v)) =
        ((ingArcs c (ingPosOf p c.size c.swap) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  classical
  obtain ⟨c, hwf, hcX, hck, hcsw, harcs⟩ := vine_decode M R p
  have hsz2 : 2 ≤ c.size := by
    have : c.size = (X.expand R.k).n := by unfold IngCode.size; rw [hcX, hck]
    rw [this]; exact expand_n_ge X R.k R.length_eq
  have hsz : c.size = (X.expand R.k).n := by unfold IngCode.size; rw [hcX, hck]
  have himg : ∀ v ∈ S, R.f v < c.size := by
    intro v hv
    have : R.f v ∈ S.image R.f := Finset.mem_image_of_mem _ hv
    rw [R.image_eq, Finset.mem_range] at this
    omega
  refine ⟨c, hwf, hsz2, ?_, ?_, ?_, ?_, harcs⟩
  · intro v1 hv1 v2 hv2 h
    have := ingPosOf_inj (himg v1 hv1) (himg v2 hv2)
      (by simpa [ingPosOf_add p (by omega : 1 ≤ c.size)] using h)
    exact R.injOn hv1 hv2 this
  · ext y
    simp only [Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := ingPosOf_lt hsz2 (sw := c.swap) (himg v hv)
      rw [ingPosOf_add p (by omega : 1 ≤ c.size)]
      omega
    · rintro ⟨h1, h2⟩
      obtain ⟨t, ht, ht'⟩ := ingPosOf_surj hsz2 c.swap (y := y - p) (by omega)
      have : t ∈ S.image R.f := by rw [R.image_eq, Finset.mem_range]; omega
      obtain ⟨v, hv, hvt⟩ := Finset.mem_image.mp this
      refine ⟨v, hv, ?_⟩
      rw [hvt, ingPosOf_add p (by omega : 1 ≤ c.size), ht']
      omega
  · rcases vine_joint_cases R hab ha hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : c.swap = false := by rw [hcsw]; simp [h1]
      exact ingPosOf_first hsz2 _ (by rw [this, h1]; rfl) p
    · have : c.swap = true := by rw [hcsw]; simp [h1]
      exact ingPosOf_first hsz2 _ (by rw [this, h1]; rfl) p
  · rcases vine_joint_cases R hab ha hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : c.swap = false := by rw [hcsw]; simp [h1]
      exact ingPosOf_second hsz2 _ (by rw [this, h2]; rfl) p
    · have : c.swap = true := by rw [hcsw]; simp [h1]
      exact ingPosOf_second hsz2 _ (by rw [this, h2]; rfl) p


/-- **A vine chain is a unit code.** -/
theorem chain_decode (M : Molecule V D) (hM : M.IsMolecule) {U : Finset V} {a b : V} {n : ℕ}
    (h : Chain M U a b n) : M.IsBlock U a b →
    ∃ cs : List IngCode, cs.length = n ∧ (∀ c ∈ cs, c.Wf) ∧ ∃ lab : V → ℕ,
      Set.InjOn lab U ∧ U.image lab = Finset.range (unitWeight cs + 1) ∧ lab a = 0 ∧
      lab b = unitWeight cs ∧ groupArcs M U lab = ((unitArcs cs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  classical
  induction h with
  | @single S a b hv =>
    intro hB
    obtain ⟨X, hX⟩ := hv
    obtain ⟨-, ⟨R⟩⟩ := isVine_iff_realization.mp hX
    obtain ⟨c, hwf, hsz, hinj, himg, hlaba, hlabb, harcs⟩ :=
      vine_chain_code M R hB.2.2.2.1 hB.2.1 hB.2.2.1 0
    refine ⟨[c], rfl, by simpa using hwf, fun v => ingPosOf 0 c.size c.swap (R.f v), hinj, ?_, hlaba, ?_, ?_⟩
    · rw [himg]; ext y; simp only [Finset.mem_Ico, Finset.mem_range, unitWeight]; simp; omega
    · simp [unitWeight]; omega
    · rw [harcs]; simp [unitArcs, unitArcsAux]
  | @append S T a b c n hS hT hi hne ih =>
    intro hU
    obtain ⟨Y, hY⟩ := hT
    have hBS : M.IsBlock S a b := chain_prefix_isBlock M hM hS hY hi hU
    obtain ⟨cs, hcsl, hwfs, labS, injS, imgS, hla, hlb, harcsS⟩ := ih hBS
    obtain ⟨-, ⟨R⟩⟩ := isVine_iff_realization.mp hY
    have hbT : b ∈ T := hY.1.2.1
    have hcT : c ∈ T := hY.1.2.2.1
    have hbc : b ≠ c := hY.1.2.2.2.1
    have hbS : b ∈ S := (chain_joints_mem hS).2
    have haS : a ∈ S := (chain_joints_mem hS).1
    have hcS : c ∉ S := by
      intro hc
      have : c ∈ S ∩ T := Finset.mem_inter.mpr ⟨hc, hcT⟩
      rw [hi, Finset.mem_singleton] at this
      exact hbc this.symm
    set W := unitWeight cs with hW
    obtain ⟨cT, hwfT, hszT, injT, imgT, hlabTb, hlabTc, harcsT⟩ :=
      vine_chain_code M R hbc hbT hcT W
    let labT : V → ℕ := fun v => ingPosOf W cT.size cT.swap (R.f v)
    let lab : V → ℕ := fun v => if v ∈ S then labS v else labT v
    have hlabS : ∀ v ∈ S, lab v = labS v := fun v hv => by simp [lab, hv]
    have hlabT : ∀ v ∈ T, lab v = labT v := by
      intro v hv
      by_cases hvS : v ∈ S
      · have : v ∈ S ∩ T := Finset.mem_inter.mpr ⟨hvS, hv⟩
        rw [hi, Finset.mem_singleton] at this
        subst this
        simp only [lab, hvS, if_true]
        rw [hlb]; exact hlabTb.symm
      · simp [lab, hvS]
    have hSr : ∀ v ∈ S, labS v ≤ W := by
      intro v hv
      have : labS v ∈ S.image labS := Finset.mem_image_of_mem _ hv
      rw [imgS, Finset.mem_range] at this; omega
    have hTr : ∀ v ∈ T, W ≤ labT v ∧ labT v < W + cT.size := by
      intro v hv
      have : labT v ∈ T.image labT := Finset.mem_image_of_mem _ hv
      rw [imgT, Finset.mem_Ico] at this; omega
    refine ⟨cs ++ [cT], by simp [hcsl], ?_, lab, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hwfs d hd
      · rw [List.mem_singleton.mp hd]; exact hwfT
    · intro v1 hv1 v2 hv2 hv
      rcases Finset.mem_union.mp hv1 with h1 | h1 <;> rcases Finset.mem_union.mp hv2 with h2 | h2
      · rw [hlabS v1 h1, hlabS v2 h2] at hv; exact injS h1 h2 hv
      · by_cases h2S : v2 ∈ S
        · rw [hlabS v1 h1, hlabS v2 h2S] at hv; exact injS h1 h2S hv
        · rw [hlabS v1 h1, hlabT v2 h2] at hv
          have := hSr v1 h1
          have h3 := hTr v2 h2
          have h4 : labT v2 ≠ labT b := by
            intro e
            have := injT h2 hbT e
            exact h2S (this ▸ hbS)
          have h5 : labT b = W := hlabTb
          omega
      · by_cases h1S : v1 ∈ S
        · rw [hlabS v1 h1S, hlabS v2 h2] at hv; exact injS h1S h2 hv
        · rw [hlabS v2 h2, hlabT v1 h1] at hv
          have := hSr v2 h2
          have h3 := hTr v1 h1
          have h4 : labT v1 ≠ labT b := by
            intro e
            have := injT h1 hbT e
            exact h1S (this ▸ hbS)
          have h5 : labT b = W := hlabTb
          omega
      · by_cases h1S : v1 ∈ S
        · by_cases h2S : v2 ∈ S
          · rw [hlabS v1 h1S, hlabS v2 h2S] at hv; exact injS h1S h2S hv
          · rw [hlabS v1 h1S, hlabT v2 h2] at hv
            have := hSr v1 h1S
            have h3 := hTr v2 h2
            have h4 : labT v2 ≠ labT b := by
              intro e
              exact h2S ((injT h2 hbT e) ▸ hbS)
            have h5 : labT b = W := hlabTb
            omega
        · by_cases h2S : v2 ∈ S
          · rw [hlabT v1 h1, hlabS v2 h2S] at hv
            have := hSr v2 h2S
            have h3 := hTr v1 h1
            have h4 : labT v1 ≠ labT b := by
              intro e
              exact h1S ((injT h1 hbT e) ▸ hbS)
            have h5 : labT b = W := hlabTb
            omega
          · rw [hlabT v1 h1, hlabT v2 h2] at hv; exact injT h1 h2 hv
    · rw [Finset.image_union]
      have e1 : S.image lab = S.image labS := Finset.image_congr (fun v hv => hlabS v hv)
      have e2 : T.image lab = T.image labT := Finset.image_congr (fun v hv => hlabT v hv)
      rw [e1, e2, imgS, imgT, unitWeight_append_single]
      ext y
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    · rw [hlabS a haS]; exact hla
    · rw [unitWeight_append_single]
      have : lab c = labT c := by simp [lab, hcS]
      rw [this]; show ingPosOf W cT.size cT.swap (R.f c) = W + (cT.size - 1)
      rw [hlabTc]; omega
    · have hiS := groupArcs_union M hM hBS hY.1 hU hi lab
      rw [hiS, groupArcs_congr M S hlabS, groupArcs_congr M T hlabT, harcsS, harcsT]
      have hsz : ∀ d ∈ cs, 1 ≤ d.size := by
        intro d hd
        have := hwfs d hd
        have := expand_n_ge d.X d.k this.1
        unfold IngCode.size; omega
      have := unitArcsAux_append cT cs 0 hsz
      unfold unitArcs
      rw [this, Multiset.coe_add, Nat.zero_add]

end WaveTurbulence.ClassCount
