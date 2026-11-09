/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode4` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode3
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily


/-!
# CLASSCOUNT: a vine Fama.chain is a unit code

`chain_decode`: a vine Fama.chain `U` (`Src.Chain γ M U a b n`) that is a block with joints `(a, b)` has a unit code `cs`
(`n` well-formed ingredient codes) and a labelling `lab` of its atoms by `0 … W` (`W = unitWeight cs`), injective on
`U` with `lab a = 0`, `lab b = W`, whose arcs are `unitArcs cs`.  The proof is by induction on the Fama.chain, using
`vine_decode` (one ingredient) and `Fama.group_split` (the bonds of a concatenation).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount







theorem ingPosOf_pos {sz : ℕ} (hsz : 2 ≤ sz) {sw : Bool} {t : ℕ} (ht : t < sz) (hne : t ≠ if sw then 1 else 0) (p : ℕ) :
    p + 1 ≤ ingPosOf p sz sw t := by
  unfold ingPosOf; split_ifs at hne ⊢ <;> first | omega | contradiction

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

/-- `groupArcs` only depends on the labels of the atoms of the group. -/

theorem unitArcsAux_append (c : IngCodeG) : ∀ (cs : List IngCodeG) (p : ℕ), (∀ d ∈ cs, 1 ≤ d.size) →
    unitArcsAux p (cs ++ [c]) = unitArcsAux p cs ++
      ingArcsG c (ingPosOf (p + unitWeight cs) c.size c.swap)
  | [], p, _ => by simp [unitArcsAux, unitWeight]
  | d :: cs, p, h => by
    have hd := h d (by simp)
    have := unitArcsAux_append c cs (p + d.size - 1) (fun e he => h e (by simp [he]))
    have hw : p + unitWeight (d :: cs) = p + d.size - 1 + unitWeight cs := by
      simp only [unitWeight, List.map_cons, List.sum_cons]; omega
    simp only [List.cons_append, unitArcsAux, this, List.append_assoc]
    rw [hw]


theorem unitWeight_cons (c : IngCodeG) (cs : List IngCodeG) :
    unitWeight (c :: cs) = (c.size - 1) + unitWeight cs := by
  simp [unitWeight]

theorem unitWeight_append_single (cs : List IngCodeG) (c : IngCodeG) :
    unitWeight (cs ++ [c]) = unitWeight cs + (c.size - 1) := by
  simp [unitWeight]

theorem chain_decode (M : Molecule V D) (hM : M.IsMolecule) {U : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ M U a b n) : M.IsBlock U a b →
    ∃ cs : List IngCodeG, cs.length = n ∧ (∀ c ∈ cs, c.Wf) ∧ ∃ lab : V → ℕ,
      Set.InjOn lab U ∧ U.image lab = Finset.range (unitWeight cs + 1) ∧ lab a = 0 ∧
      lab b = unitWeight cs ∧ groupArcs M U lab = ((unitArcs cs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  classical
  induction h with
  | @single S a b hv =>
    intro hB
    obtain ⟨c, hwf, hsz, lab0, hinj, himg, hlaba, hlabb, harcs⟩ :=
      vine_chain_codeG (Fact.out : TVineStructInputs) (Fact.out : γ ≤ 1 / 2) M hM hv 0
    refine ⟨[c], rfl, by simpa using hwf, lab0, hinj, ?_, hlaba, ?_, ?_⟩
    · rw [himg]; ext y; simp only [Finset.mem_Ico, Finset.mem_range, unitWeight]; simp; omega
    · simp [unitWeight]; omega
    · rw [harcs]; simp [unitArcs, unitArcsAux]
  | @append S T a b c n hS hT hi hne ih =>
    intro hU
    have hY := hT
    have hBS : M.IsBlock S a b := chain_prefix_isBlock M hM hS hY hi hU
    obtain ⟨cs, hcsl, hwfs, labS, injS, imgS, hla, hlb, harcsS⟩ := ih hBS
    have hbT : b ∈ T := (Src.isBlock_of_isSomeVine hY).2.1
    have hcT : c ∈ T := (Src.isBlock_of_isSomeVine hY).2.2.1
    have hbc : b ≠ c := (Src.isBlock_of_isSomeVine hY).2.2.2.1
    have hbS : b ∈ S := (chain_joints_mem hS).2
    have haS : a ∈ S := (chain_joints_mem hS).1
    have hcS : c ∉ S := by
      intro hc
      have : c ∈ S ∩ T := Finset.mem_inter.mpr ⟨hc, hcT⟩
      rw [hi, Finset.mem_singleton] at this
      exact hbc this.symm
    set W := unitWeight cs with hW
    obtain ⟨cT, hwfT, hszT, labT, injT, imgT, hlabTb, hlabTc, harcsT⟩ :=
      vine_chain_codeG (Fact.out : TVineStructInputs) (Fact.out : γ ≤ 1 / 2) M hM hY W
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
      rw [this]; show labT c = W + (cT.size - 1)
      rw [hlabTc]; omega
    · have hiS := groupArcs_union M hM hBS (Src.isBlock_of_isSomeVine hY) hU hi lab
      rw [hiS, groupArcs_congr M S hlabS, groupArcs_congr M T hlabT, harcsS, harcsT]
      have hsz : ∀ d ∈ cs, 1 ≤ d.size := by
        intro d hd
        have := (hwfs d hd).1
        unfold IngCodeG.size; omega
      have := unitArcsAux_append cT cs 0 hsz
      unfold unitArcs
      rw [this, Multiset.coe_add, Nat.zero_add]

end WaveTurbulence.GammaLow.Famc.ClassCount
