/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4GtA

/-!
# Labelled codes are pairs (upper labelled chain, bottom object)

For sizes graded by halves:

* **`sum_couple_decomp`**: `∑_{Q ∈ domCodes a} ∑_{ls ∈ labC Q} g = ∑_{i + a₀ = a} ∑_{x ∈ UP i} ∑_{B ∈ domCodes a₀}
  g (composeC x B)`;
* **`sum_tree_decomp`**: `∑_{X ∈ domTrees b} ∑_{μ} h = ∑_{j + b₀ = b} ∑_{y ∈ UP j} ∑_{Z ∈ domTrees b₀} h (join y Z)`.

Here `UP i` is the set of dominant well-formed chains of size `2i` with labels in `[q'+1, q]`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset
open scoped Classical

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The upper labelled chains of size `2i`. -/
noncomputable def UP (q q' i : ℕ) : Finset (Σ _ : RegChain, List ℕ) :=
  (Mexp.domTrees i).sigma fun U => labsF (q' + 1) U q

theorem closeCouple_dom {A Xm : RegChain} {Qlp : RegCpl} (h : (A.dominant && Xm.dominant && Qlp.dominant) = true) :
    (SourceApp.closeCouple A Xm Qlp).dominant = true := by
  unfold SourceApp.closeCouple
  split_ifs with hn
  · simp only [Bool.and_eq_true] at h
    exact h.2
  · exact h

theorem half_eq_chain (X : RegChain) : X.size = 2 * (X.size / 2) := by
  obtain ⟨m, hm⟩ := size_even_chain X
  omega

theorem half_eq_cpl (Q : RegCpl) : Q.size = 2 * (Q.size / 2) := by
  obtain ⟨m, hm⟩ := size_even_cpl Q
  omega

/-- The decomposition of a labelled couple. -/
def decC (a q' : ℕ) : (Σ _ : RegCpl, List ℕ) → Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegCpl
  | ⟨.type2 Xp Xm Qlp, ls⟩ =>
    ⟨((splitL q' Xp ls).1.1.size / 2, a - (splitL q' Xp ls).1.1.size / 2),
      (⟨(splitL q' Xp ls).1.1, (splitL q' Xp ls).1.2⟩, SourceApp.closeCouple (splitL q' Xp ls).2 Xm Qlp)⟩
  | ⟨Q, _⟩ => ⟨(0, a), (⟨.nil, []⟩, Q)⟩

/-- The composition. -/
def comC (q' : ℕ) (v : Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegCpl) : Σ _ : RegCpl, List ℕ :=
  ⟨(composeC q' v.2.1.1 v.2.1.2 v.2.2).1, (composeC q' v.2.1.1 v.2.1.2 v.2.2).2⟩

theorem nil_mem_domTrees : RegChain.nil ∈ Mexp.domTrees 0 := Mexp.mem_domTrees.2 ⟨rfl, rfl, rfl⟩

section Decomp

variable {q q' : ℕ} (hqq : q' ≤ q)
include hqq

theorem labOK_weaken {U : RegChain} {lsU : List ℕ} (h : LabOK (q' + 1) U lsU q) : LabOK q' U lsU q := by
  have := labOK_join (Z := .nil) U lsU q h hqq
  rwa [appendChain_nil_right, show topCount RegChain.nil = 0 from rfl, List.replicate_zero, List.append_nil] at this

omit hqq in
theorem decC_mem (a : ℕ) (z : Σ _ : RegCpl, List ℕ) (hz : z ∈ (Mexp.domCodes a).sigma (labC q q')) :
    decC a q' z ∈ (antidiagonal a).sigma fun ia => UP q q' ia.1 ×ˢ Mexp.domCodes ia.2 := by
  obtain ⟨Q, ls⟩ := z
  rw [Finset.mem_sigma] at hz
  obtain ⟨hQ, hls⟩ := hz
  obtain ⟨hwf, hdom, hsize⟩ := Mexp.mem_domCodes.1 hQ
  cases Q with
  | type2 Xp Xm Qlp =>
    have hL := (mem_labsF Xp q ls).1 hls
    have hdec : decC a q' ⟨.type2 Xp Xm Qlp, ls⟩ = ⟨((splitL q' Xp ls).1.1.size / 2, a - (splitL q' Xp ls).1.1.size / 2),
        (⟨(splitL q' Xp ls).1.1, (splitL q' Xp ls).1.2⟩, SourceApp.closeCouple (splitL q' Xp ls).2 Xm Qlp)⟩ := rfl
    rw [hdec]
    have hS := labOK_split Xp ls q hL
    obtain ⟨e1, -⟩ := join_split Xp ls q hL
    generalize splitL q' Xp ls = sp at hS e1 ⊢
    obtain ⟨⟨U, lsU⟩, Xr⟩ := sp
    simp only at hS e1 ⊢
    subst e1
    obtain ⟨hU, hB⟩ := wf_split hwf
    have hd : (appendChain U Xr).dominant = true ∧ Xm.dominant = true ∧ Qlp.dominant = true := by
      simp only [RegCpl.dominant, Bool.and_eq_true] at hdom
      exact ⟨hdom.1.1, hdom.1.2, hdom.2⟩
    rw [appendChain_dominant, Bool.and_eq_true] at hd
    have hsz : (appendChain U Xr).size + Xm.size + Qlp.size = 2 * a := hsize
    rw [appendChain_size] at hsz
    have hBs := closeCouple_size Xr Xm Qlp
    have hUe := half_eq_chain U
    refine Finset.mem_sigma.2 ⟨Finset.HasAntidiagonal.mem_antidiagonal.2
      (by show U.size / 2 + (a - U.size / 2) = a; omega),
      Finset.mem_product.2 ⟨Finset.mem_sigma.2 ⟨Mexp.mem_domTrees.2 ⟨hU, hd.1.1, hUe⟩,
        (mem_labsF U q _).2 hS⟩,
      Mexp.mem_domCodes.2 ⟨hB, closeCouple_dom (by rw [hd.1.2, hd.2.1, hd.2.2]; rfl),
        by show (SourceApp.closeCouple Xr Xm Qlp).size = 2 * (a - U.size / 2); rw [hBs]; omega⟩⟩⟩
  | triv =>
    exact Finset.mem_sigma.2 ⟨Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add a),
      Finset.mem_product.2 ⟨Finset.mem_sigma.2 ⟨nil_mem_domTrees, Finset.mem_singleton_self _⟩, hQ⟩⟩
  | type1 c Q₁ Q₂ Q₃ =>
    exact Finset.mem_sigma.2 ⟨Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add a),
      Finset.mem_product.2 ⟨Finset.mem_sigma.2 ⟨nil_mem_domTrees, Finset.mem_singleton_self _⟩, hQ⟩⟩

theorem comC_mem (a : ℕ) (v : Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegCpl)
    (hv : v ∈ (antidiagonal a).sigma fun ia => UP q q' ia.1 ×ˢ Mexp.domCodes ia.2) :
    comC q' v ∈ (Mexp.domCodes a).sigma (labC q q') := by
  obtain ⟨⟨i, a₀⟩, ⟨U, lsU⟩, B⟩ := v
  simp only [Finset.mem_sigma, Finset.mem_product, UP, Finset.HasAntidiagonal.mem_antidiagonal] at hv
  obtain ⟨hia, ⟨hU, hlsU⟩, hB⟩ := hv
  obtain ⟨hUw, hUd, hUs⟩ := Mexp.mem_domTrees.1 hU
  obtain ⟨hBw, hBd, hBs⟩ := Mexp.mem_domCodes.1 hB
  have hL := (mem_labsF U q lsU).1 hlsU
  rw [Finset.mem_sigma]
  cases B with
  | type2 Xr Xm Qlp =>
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hBw
    obtain ⟨⟨⟨⟨hXr, hXm⟩, hQl⟩, ht⟩, hnn⟩ := hBw
    simp only [RegCpl.dominant, Bool.and_eq_true] at hBd
    refine ⟨Mexp.mem_domCodes.2 ⟨?_, ?_, ?_⟩, (mem_labsF _ q _).2 (labOK_join U lsU q Xr hL hqq)⟩
    · show (RegCpl.type2 (appendChain U Xr) Xm Qlp).wf = true
      simp only [RegCpl.wf, appendChain_wf, appendChain_isNil, hUw, hXr, hXm, hQl, ht]
      revert hnn
      generalize U.isNil = x
      generalize Xr.isNil = y
      generalize Xm.isNil = z
      cases x <;> cases y <;> cases z <;> decide
    · simp only [comC, composeC, RegCpl.dominant, appendChain_dominant, hUd, hBd.1.1, hBd.1.2, hBd.2,
        Bool.and_self]
    · show (appendChain U Xr).size + Xm.size + Qlp.size = 2 * a
      rw [appendChain_size]
      have : Xr.size + Xm.size + Qlp.size = 2 * a₀ := hBs
      omega
  | triv =>
    by_cases hn : U.isNil = true
    · have hU' := isNil_iff.1 hn
      subst hU'
      have hi : i = 0 := by have := hUs; simp [RegChain.size] at this; omega
      have : comC q' ⟨(i, a₀), ⟨.nil, lsU⟩, .triv⟩ = ⟨.triv, []⟩ := rfl
      rw [this]
      exact ⟨by rw [show a = a₀ by omega]; exact hB, Finset.mem_singleton_self _⟩
    · have : comC q' ⟨(i, a₀), ⟨U, lsU⟩, .triv⟩ = ⟨.type2 U .nil .triv, lsU⟩ := by
        simp [comC, composeC, hn]
      rw [this]
      refine ⟨Mexp.mem_domCodes.2 ⟨?_, ?_, ?_⟩, (mem_labsF U q lsU).2 (labOK_weaken hqq hL)⟩
      · have hn' : U.isNil = false := by simpa using hn
        rw [show (RegCpl.type2 U .nil .triv).wf = (U.wf && true && true && !false && !(U.isNil && true)) from rfl,
          hUw, hn']
        rfl
      · rw [show (RegCpl.type2 U .nil .triv).dominant = (U.dominant && true && true) from rfl, hUd]
        rfl
      · show U.size + 0 + 0 = 2 * a
        have : (0 : ℕ) = 2 * a₀ := hBs
        omega
  | type1 c Q₁ Q₂ Q₃ =>
    by_cases hn : U.isNil = true
    · have hU' := isNil_iff.1 hn
      subst hU'
      have hi : i = 0 := by have := hUs; simp [RegChain.size] at this; omega
      have : comC q' ⟨(i, a₀), ⟨.nil, lsU⟩, .type1 c Q₁ Q₂ Q₃⟩ = ⟨.type1 c Q₁ Q₂ Q₃, []⟩ := rfl
      rw [this]
      exact ⟨by rw [show a = a₀ by omega]; exact hB, Finset.mem_singleton_self _⟩
    · have : comC q' ⟨(i, a₀), ⟨U, lsU⟩, .type1 c Q₁ Q₂ Q₃⟩ = ⟨.type2 U .nil (.type1 c Q₁ Q₂ Q₃), lsU⟩ := by
        simp [comC, composeC, hn]
      rw [this]
      refine ⟨Mexp.mem_domCodes.2 ⟨?_, ?_, ?_⟩, (mem_labsF U q lsU).2 (labOK_weaken hqq hL)⟩
      · have hn' : U.isNil = false := by simpa using hn
        rw [show (RegCpl.type2 U .nil (.type1 c Q₁ Q₂ Q₃)).wf =
          (U.wf && true && (RegCpl.type1 c Q₁ Q₂ Q₃).wf && !false && !(U.isNil && true)) from rfl, hUw, hBw, hn']
        rfl
      · rw [show (RegCpl.type2 U .nil (.type1 c Q₁ Q₂ Q₃)).dominant =
          (U.dominant && true && (RegCpl.type1 c Q₁ Q₂ Q₃).dominant) from rfl, hUd, hBd]
        rfl
      · show U.size + 0 + (RegCpl.type1 c Q₁ Q₂ Q₃).size = 2 * a
        have : (RegCpl.type1 c Q₁ Q₂ Q₃).size = 2 * a₀ := hBs
        omega

end Decomp

end WaveTurbulence.PL234
