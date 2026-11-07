/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.WkeId

/-!
# Enhanced dominant trees and B2's tree leading terms

A dominant regular tree of sign `+` (TARGET Def `defentree`) is a dominant chain with its couples. B2 codes it by a
`RegChain`; its special subsets are its chosen chain nodes. As for couples (`EFinite`):

* `EDT b`: the well-formed enhanced dominant chains with `n(𝒯) = 2b`; `domTrees b`: B2's well-formed dominant tree
  codes of order `2b`;
* `sum_domTrees_specialSets`: `(𝒳, Z) ↦ enhC Z 𝒳 1 (0, [])` is a bijection onto `EDT b`;
* `tree_specialWeight_eq_sw`, **`tree_app_eq_sum`**: B2's `(K*_𝒯)_app` (sign `+`) as a sum over enhanced trees,
  `2^{-2b} δ^b ζ*(f) sw(f) 𝒥ℬ*_f(t,s) ∏_j ℳ*_{(j)}(k)`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set Finset

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel

variable {d : ℕ}

theorem finite_EDT (b : ℕ) : {f : EChain | f.wf = true ∧ f.hsize = b}.Finite :=
  (finite_bounded b).2.subset fun _ hf => ⟨hf.1, hf.2.le⟩

/-- **The well-formed enhanced dominant trees of order `2b`.** -/
noncomputable def EDT (b : ℕ) : Finset EChain := (finite_EDT b).toFinset

theorem mem_EDT {b : ℕ} {f : EChain} : f ∈ EDT b ↔ f.wf = true ∧ f.hsize = b := by
  simp [EDT]

theorem finite_domTrees (b : ℕ) :
    {X : RegChain | X.wf = true ∧ X.dominant = true ∧ X.size = 2 * b}.Finite := by
  refine ((finite_EDT b).image EChain.code).subset ?_
  rintro X ⟨hw, hd, hs⟩
  refine ⟨enhC ∅ X 1 ((0 : Fin 1), []), ⟨?_, ?_⟩, code_enhC ∅ X hd _ _⟩
  · rw [← EChain.wf_code, code_enhC ∅ X hd, hw]
  · have := EChain.size_code (enhC ∅ X 1 ((0 : Fin 1), []))
    rw [code_enhC ∅ X hd] at this
    omega

/-- **B2's well-formed dominant tree codes of order `2b`.** -/
noncomputable def domTrees (b : ℕ) : Finset RegChain := (finite_domTrees b).toFinset

theorem mem_domTrees {b : ℕ} {X : RegChain} :
    X ∈ domTrees b ↔ X.wf = true ∧ X.dominant = true ∧ X.size = 2 * b := by
  simp [domTrees]

/-- The root of a tree. -/
abbrev rtT : Fin 1 × Path := (0, [])

theorem enhC_inj {X : RegChain} (hX : X.dominant = true) {Z Z' : Finset (Fin 1 × Path)}
    (hZ : Z ∈ specialSets (X.treeLinks 1)) (hZ' : Z' ∈ specialSets (X.treeLinks 1))
    (h : enhC Z X 1 rtT = enhC Z' X 1 rtT) : Z = Z' := by
  have hb := congrArg EChain.bits h
  rw [bits_enhC Z X hX, bits_enhC Z' X hX, List.map_inj_left] at hb
  rw [tree_mem_specialSets_iff] at hZ hZ'
  ext z
  constructor
  · intro hz
    exact (decide_eq_decide.mp (hb z (hZ z hz))).mp hz
  · intro hz
    exact (decide_eq_decide.mp (hb z (hZ' z hz))).mpr hz

theorem exists_enhC_eq {X : RegChain} (hX : X.dominant = true) {f : EChain} (hf : f.code = X) :
    ∃ Z ∈ specialSets (X.treeLinks 1), enhC Z X 1 rtT = f := by
  set l := chainSpecial X 1 rtT with hl
  have hlen : f.bits.length = l.length := by
    have h1 := EChain.length_bits_eq f (enhC ∅ X 1 rtT) (by rw [hf, code_enhC ∅ X hX])
    rw [h1, bits_enhC ∅ X hX, List.length_map]
  refine ⟨zfrom l f.bits, ?_, ?_⟩
  · rw [tree_mem_specialSets_iff]
    exact fun z hz => zfrom_subset l f.bits hz
  · refine EChain.ext_code_bits _ _ (by rw [code_enhC _ X hX, hf]) ?_
    rw [bits_enhC _ X hX]
    exact map_mem_zfrom l (tree_specialList_nodup X 1) f.bits hlen

/-- **Summing over dominant tree codes and their special subsets is summing over enhanced trees.** -/
theorem sum_domTrees_specialSets {M : Type*} [AddCommMonoid M] (b : ℕ) (g : EChain → M) :
    ∑ X ∈ domTrees b, ∑ Z ∈ specialSets (X.treeLinks 1), g (enhC Z X 1 rtT) = ∑ f ∈ EDT b, g f := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => enhC p.2 p.1 1 rtT) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨X, Z⟩ hp
    rw [Finset.mem_sigma, mem_domTrees] at hp
    obtain ⟨⟨hw, hd, hs⟩, -⟩ := hp
    dsimp only at hw hd hs ⊢
    rw [mem_EDT]
    refine ⟨by rw [← EChain.wf_code, code_enhC Z X hd, hw], ?_⟩
    have := EChain.size_code (enhC Z X 1 rtT)
    rw [code_enhC Z X hd] at this
    omega
  · rintro ⟨X, Z⟩ hp ⟨X', Z'⟩ hp' h
    rw [Finset.mem_sigma, mem_domTrees] at hp hp'
    have hX : X = X' := by
      have := congrArg EChain.code h
      simp only at this
      rwa [code_enhC Z X hp.1.2.1, code_enhC Z' X' hp'.1.2.1] at this
    subst hX
    have := enhC_inj hp.1.2.1 hp.2 hp'.2 h
    subst this
    rfl
  · intro f hf
    rw [mem_EDT] at hf
    obtain ⟨Z, hZ, hZf⟩ := exists_enhC_eq f.dominant_code rfl
    refine ⟨⟨f.code, Z⟩, ?_, hZf⟩
    rw [Finset.mem_sigma, mem_domTrees]
    exact ⟨⟨by rw [EChain.wf_code, hf.1], f.dominant_code, by rw [EChain.size_code, hf.2]⟩, hZ⟩

/-- **B2's `specialWeight` for a tree of sign `+`** is the special weight of the enhanced tree. -/
theorem tree_specialWeight_eq_sw {X : RegChain} (hX : X.dominant = true) {Z : Finset (Fin 1 × Path)}
    (hZ : Z ∈ specialSets (X.treeLinks 1)) : specialWeight ![1] Z = (enhC Z X 1 rtT).sw 1 := by
  rw [sw_enhC ![1] Z X hX 1 rtT (by simp [nodeSign, pathSign])]
  rw [tree_mem_specialSets_iff] at hZ
  exact prod_eq_list_prod (tree_specialList_nodup X 1) hZ _

/-- `𝒥ℬ*_𝒯(t, s)` of an enhanced tree. -/
noncomputable def EChain.JBt (r : ℝ) (f : EChain) (t s : ℝ) : ℝ := f.code.JBtree r t s

/-- The summand of the tree leading terms: `2^{-2b} δ^b ζ*(f) sw(f) 𝒥ℬ*_f(t,s) ∏_j ℳ*_{(j)}(k)`. -/
noncomputable def gtree (δ r : ℝ) (F : Mom d → ℝ) (t s : ℝ) (k : Mom d) (f : EChain) : ℂ :=
  ((cn δ f.hsize : ℝ) : ℂ) * (f.tuples.netSign : ℂ) * f.sw 1 * (f.JBt r t s : ℂ) *
    (Mtuples F f.tuples k : ℂ)

/-- **B2's tree leading term (sign `+`)** as a sum over enhanced trees. -/
theorem tree_app_eq_sum (δ r : ℝ) (F : Mom d → ℝ) {b : ℕ} {X : RegChain} (hX : X ∈ domTrees b)
    (t s : ℝ) (k : Mom d) :
    X.app δ r F 1 t s k = ∑ Z ∈ specialSets (X.treeLinks 1), gtree δ r F t s k (enhC Z X 1 rtT) := by
  obtain ⟨-, hd, hs⟩ := mem_domTrees.1 hX
  simp only [RegChain.app, hd, ↓reduceIte, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z hZ => ?_
  have hh : (enhC Z X 1 rtT).hsize = b := by
    have := EChain.size_code (enhC Z X 1 rtT)
    rw [code_enhC Z X hd] at this
    omega
  have hns : ((chainTuples0 X).netSign : ℂ) = ((enhC Z X 1 rtT).tuples.netSign : ℂ) := by
    rw [EChain.netSign_tuples, code_enhC Z X hd]
  have hJB : X.JBtree r t s = (enhC Z X 1 rtT).JBt r t s := by rw [EChain.JBt, code_enhC Z X hd]
  rw [tree_specialWeight_eq_sw hd hZ, nstar_eq_mtuples F Z X hd, ← tuples_enhC,
    zetaOfTrees_tree_eq_netSign X hd 1, hns, hJB, gtree, hh, hs, cn,
    Nat.mul_div_cancel_left b (by norm_num : 0 < 2)]
  push_cast
  ring

end WaveTurbulence.Mexp
