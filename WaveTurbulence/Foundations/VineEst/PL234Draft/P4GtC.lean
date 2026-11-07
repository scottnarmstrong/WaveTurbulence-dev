/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4GtB

/-!
# The decomposition bijections for labelled couples and trees

* `comC_decC`, `decC_comC` and **`sum_couple_decomp`**;
* `decT`, `comT`, their memberships and inverses, and **`sum_tree_decomp`**.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset
open scoped Classical

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

section Couple

variable {q q' : ℕ} (hqq : q' ≤ q)
include hqq

omit hqq in
theorem comC_decC (a : ℕ) (z : Σ _ : RegCpl, List ℕ) (hz : z ∈ (Mexp.domCodes a).sigma (labC q q')) :
    comC q' (decC a q' z) = z := by
  obtain ⟨Q, ls⟩ := z
  rw [Finset.mem_sigma] at hz
  obtain ⟨hQ, hls⟩ := hz
  obtain ⟨hwf, -, -⟩ := Mexp.mem_domCodes.1 hQ
  cases Q with
  | type2 Xp Xm Qlp =>
    have hL := (mem_labsF Xp q ls).1 hls
    have hdec : decC a q' ⟨.type2 Xp Xm Qlp, ls⟩ = ⟨((splitL q' Xp ls).1.1.size / 2, a - (splitL q' Xp ls).1.1.size / 2),
        (⟨(splitL q' Xp ls).1.1, (splitL q' Xp ls).1.2⟩, SourceApp.closeCouple (splitL q' Xp ls).2 Xm Qlp)⟩ := rfl
    rw [hdec]
    obtain ⟨e1, e2⟩ := join_split Xp ls q hL
    generalize splitL q' Xp ls = sp at e1 e2 ⊢
    obtain ⟨⟨U, lsU⟩, Xr⟩ := sp
    simp only at e1 e2 ⊢
    subst e1
    subst e2
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true', appendChain_wf, appendChain_isNil] at hwf
    obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, ht⟩, hnn⟩ := hwf
    by_cases hc : (Xr.isNil && Xm.isNil) = true
    · simp only [Bool.and_eq_true] at hc
      obtain ⟨hXr, hXm⟩ := hc
      rw [isNil_iff] at hXr hXm
      subst hXr
      subst hXm
      have hU : U.isNil = false := by simpa [RegChain.isNil] using hnn
      have hcomp : ∀ B : RegCpl, B.isType2 = false →
          composeC q' U lsU B = (RegCpl.type2 U .nil B, lsU) := fun B hB => by
        cases B with
        | type2 _ _ _ => simp [RegCpl.isType2] at hB
        | triv => simp [composeC, hU]
        | type1 _ _ _ _ => simp [composeC, hU]
      rw [show SourceApp.closeCouple RegChain.nil RegChain.nil Qlp = Qlp from rfl]
      show (⟨(composeC q' U lsU Qlp).1, (composeC q' U lsU Qlp).2⟩ : Σ _ : RegCpl, List ℕ) = _
      rw [hcomp Qlp ht, appendChain_nil_right, show topCount RegChain.nil = 0 from rfl, List.replicate_zero,
        List.append_nil]
    · have hc2 : SourceApp.closeCouple Xr Xm Qlp = .type2 Xr Xm Qlp := by
        unfold SourceApp.closeCouple
        rw [ite_eq_right hc]
      rw [hc2]
      rfl
  | triv =>
    have hls' : ls = [] := Finset.mem_singleton.1 hls
    subst hls'
    rfl
  | type1 c Q₁ Q₂ Q₃ =>
    have hls' : ls = [] := Finset.mem_singleton.1 hls
    subst hls'
    rfl

omit hqq in
theorem decC_comC (a : ℕ) (v : Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegCpl)
    (hv : v ∈ (antidiagonal a).sigma fun ia => UP q q' ia.1 ×ˢ Mexp.domCodes ia.2) :
    decC a q' (comC q' v) = v := by
  obtain ⟨⟨i, a₀⟩, ⟨U, lsU⟩, B⟩ := v
  simp only [Finset.mem_sigma, Finset.mem_product, UP, Finset.HasAntidiagonal.mem_antidiagonal] at hv
  obtain ⟨hia, ⟨hU, hlsU⟩, hB⟩ := hv
  obtain ⟨-, -, hUs⟩ := Mexp.mem_domTrees.1 hU
  obtain ⟨hBw, -, -⟩ := Mexp.mem_domCodes.1 hB
  have hL := (mem_labsF U q lsU).1 hlsU
  have hi : U.size / 2 = i := by omega
  cases B with
  | type2 Xr Xm Qlp =>
    show decC a q' ⟨.type2 (appendChain U Xr) Xm Qlp, lsU ++ List.replicate (topCount Xr) q'⟩ = _
    have hdec : decC a q' ⟨.type2 (appendChain U Xr) Xm Qlp, lsU ++ List.replicate (topCount Xr) q'⟩ =
        ⟨((splitL q' (appendChain U Xr) (lsU ++ List.replicate (topCount Xr) q')).1.1.size / 2,
          a - (splitL q' (appendChain U Xr) (lsU ++ List.replicate (topCount Xr) q')).1.1.size / 2),
        (⟨(splitL q' (appendChain U Xr) (lsU ++ List.replicate (topCount Xr) q')).1.1,
          (splitL q' (appendChain U Xr) (lsU ++ List.replicate (topCount Xr) q')).1.2⟩,
          SourceApp.closeCouple (splitL q' (appendChain U Xr) (lsU ++ List.replicate (topCount Xr) q')).2 Xm Qlp)⟩ :=
      rfl
    rw [hdec, split_join U lsU q Xr hL]
    have hc : SourceApp.closeCouple Xr Xm Qlp = .type2 Xr Xm Qlp := by
      unfold SourceApp.closeCouple
      have : (Xr.isNil && Xm.isNil) = false := by
        simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hBw
        exact hBw.2
      rw [this]
      rfl
    simp only [hc, hi, show a - i = a₀ by omega]
  | triv =>
    by_cases hn : U.isNil = true
    · have hU' := isNil_iff.1 hn
      subst hU'
      rw [show lsU = [] from hL]
      have : i = 0 := by simp [RegChain.size] at hUs; omega
      subst this
      rw [show a₀ = a by omega]
      rfl
    · have hcomp : comC q' ⟨(i, a₀), ⟨U, lsU⟩, .triv⟩ = ⟨.type2 U .nil .triv, lsU⟩ := by
        simp [comC, composeC, hn]
      rw [hcomp]
      have hs := split_join (q' := q') U lsU q .nil hL
      rw [appendChain_nil_right, show topCount RegChain.nil = 0 from rfl, List.replicate_zero,
        List.append_nil] at hs
      show (⟨((splitL q' U lsU).1.1.size / 2, a - (splitL q' U lsU).1.1.size / 2),
        (⟨(splitL q' U lsU).1.1, (splitL q' U lsU).1.2⟩,
          SourceApp.closeCouple (splitL q' U lsU).2 .nil .triv)⟩ : Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegCpl) = _
      rw [hs]
      simp only [hi, show a - i = a₀ by omega]
      rfl
  | type1 c Q₁ Q₂ Q₃ =>
    by_cases hn : U.isNil = true
    · have hU' := isNil_iff.1 hn
      subst hU'
      rw [show lsU = [] from hL]
      have : i = 0 := by simp [RegChain.size] at hUs; omega
      subst this
      rw [show a₀ = a by omega]
      rfl
    · have hcomp : comC q' ⟨(i, a₀), ⟨U, lsU⟩, .type1 c Q₁ Q₂ Q₃⟩ = ⟨.type2 U .nil (.type1 c Q₁ Q₂ Q₃), lsU⟩ := by
        simp [comC, composeC, hn]
      rw [hcomp]
      have hs := split_join (q' := q') U lsU q .nil hL
      rw [appendChain_nil_right, show topCount RegChain.nil = 0 from rfl, List.replicate_zero,
        List.append_nil] at hs
      show (⟨((splitL q' U lsU).1.1.size / 2, a - (splitL q' U lsU).1.1.size / 2),
        (⟨(splitL q' U lsU).1.1, (splitL q' U lsU).1.2⟩,
          SourceApp.closeCouple (splitL q' U lsU).2 .nil (.type1 c Q₁ Q₂ Q₃))⟩ :
          Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegCpl) = _
      rw [hs]
      simp only [hi, show a - i = a₀ by omega]
      rfl

/-- **Labelled couples are pairs (upper labelled chain, bottom couple).** -/
theorem sum_couple_decomp (a : ℕ) (g : RegCpl → List ℕ → ℂ) :
    ∑ Q ∈ Mexp.domCodes a, ∑ ls ∈ labC q q' Q, g Q ls =
      ∑ ia ∈ antidiagonal a, ∑ x ∈ UP q q' ia.1, ∑ B ∈ Mexp.domCodes ia.2,
        g (composeC q' x.1 x.2 B).1 (composeC q' x.1 x.2 B).2 := by
  rw [Finset.sum_sigma']
  have hr : ∑ ia ∈ antidiagonal a, ∑ x ∈ UP q q' ia.1, ∑ B ∈ Mexp.domCodes ia.2,
      g (composeC q' x.1 x.2 B).1 (composeC q' x.1 x.2 B).2 =
      ∑ v ∈ (antidiagonal a).sigma (fun ia => UP q q' ia.1 ×ˢ Mexp.domCodes ia.2), g (comC q' v).1 (comC q' v).2 := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun ia _ => (Finset.sum_product (UP q q' ia.1) (Mexp.domCodes ia.2)
      (fun w => g (comC q' ⟨ia, w⟩).1 (comC q' ⟨ia, w⟩).2)).symm
  rw [hr]
  exact Finset.sum_nbij' (decC a q') (comC q') (decC_mem a) (comC_mem hqq a) (comC_decC a) (decC_comC a)
    fun z hz => by rw [comC_decC a z hz]

end Couple

/-! ### Trees -/

/-- The decomposition of a labelled tree. -/
def decT (b q' : ℕ) (z : Σ _ : RegChain, List ℕ) : Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegChain :=
  ⟨((splitL q' z.1 z.2).1.1.size / 2, b - (splitL q' z.1 z.2).1.1.size / 2),
    (⟨(splitL q' z.1 z.2).1.1, (splitL q' z.1 z.2).1.2⟩, (splitL q' z.1 z.2).2)⟩

/-- The join. -/
def comT (q' : ℕ) (v : Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegChain) : Σ _ : RegChain, List ℕ :=
  ⟨appendChain v.2.1.1 v.2.2, v.2.1.2 ++ List.replicate (topCount v.2.2) q'⟩

section Tree

variable {q q' : ℕ} (hqq : q' ≤ q)
include hqq

omit hqq in
theorem decT_mem (b : ℕ) (z : Σ _ : RegChain, List ℕ) (hz : z ∈ (Mexp.domTrees b).sigma fun X => labsF q' X q) :
    decT b q' z ∈ (antidiagonal b).sigma fun jb => UP q q' jb.1 ×ˢ Mexp.domTrees jb.2 := by
  obtain ⟨X, μ⟩ := z
  rw [Finset.mem_sigma] at hz
  obtain ⟨hX, hμ⟩ := hz
  obtain ⟨hwf, hdom, hsize⟩ := Mexp.mem_domTrees.1 hX
  have hL := (mem_labsF X q μ).1 hμ
  show (⟨((splitL q' X μ).1.1.size / 2, b - (splitL q' X μ).1.1.size / 2),
    (⟨(splitL q' X μ).1.1, (splitL q' X μ).1.2⟩, (splitL q' X μ).2)⟩ :
      Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegChain) ∈ _
  have hS := labOK_split X μ q hL
  obtain ⟨e1, -⟩ := join_split X μ q hL
  generalize splitL q' X μ = sp at hS e1 ⊢
  obtain ⟨⟨U, lsU⟩, Z⟩ := sp
  simp only at hS e1 ⊢
  subst e1
  rw [appendChain_wf, Bool.and_eq_true] at hwf
  rw [appendChain_dominant, Bool.and_eq_true] at hdom
  rw [appendChain_size] at hsize
  have hUe := half_eq_chain U
  refine Finset.mem_sigma.2 ⟨Finset.HasAntidiagonal.mem_antidiagonal.2
      (by show U.size / 2 + (b - U.size / 2) = b; omega),
    Finset.mem_product.2 ⟨Finset.mem_sigma.2 ⟨Mexp.mem_domTrees.2 ⟨hwf.1, hdom.1, hUe⟩, (mem_labsF U q _).2 hS⟩,
      Mexp.mem_domTrees.2 ⟨hwf.2, hdom.2, by show Z.size = 2 * (b - U.size / 2); omega⟩⟩⟩

theorem comT_mem (b : ℕ) (v : Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegChain)
    (hv : v ∈ (antidiagonal b).sigma fun jb => UP q q' jb.1 ×ˢ Mexp.domTrees jb.2) :
    comT q' v ∈ (Mexp.domTrees b).sigma fun X => labsF q' X q := by
  obtain ⟨⟨j, b₀⟩, ⟨U, lsU⟩, Z⟩ := v
  simp only [Finset.mem_sigma, Finset.mem_product, UP, Finset.HasAntidiagonal.mem_antidiagonal] at hv
  obtain ⟨hjb, ⟨hU, hlsU⟩, hZ⟩ := hv
  obtain ⟨hUw, hUd, hUs⟩ := Mexp.mem_domTrees.1 hU
  obtain ⟨hZw, hZd, hZs⟩ := Mexp.mem_domTrees.1 hZ
  have hL := (mem_labsF U q lsU).1 hlsU
  refine Finset.mem_sigma.2 ⟨Mexp.mem_domTrees.2 ⟨?_, ?_, ?_⟩, (mem_labsF _ q _).2 (labOK_join U lsU q Z hL hqq)⟩
  · show (appendChain U Z).wf = true
    rw [appendChain_wf, hUw, hZw]
    rfl
  · show (appendChain U Z).dominant = true
    rw [appendChain_dominant, hUd, hZd]
    rfl
  · show (appendChain U Z).size = 2 * b
    rw [appendChain_size]
    omega

omit hqq in
theorem comT_decT (b : ℕ) (z : Σ _ : RegChain, List ℕ) (hz : z ∈ (Mexp.domTrees b).sigma fun X => labsF q' X q) :
    comT q' (decT b q' z) = z := by
  obtain ⟨X, μ⟩ := z
  have hL := (mem_labsF X q μ).1 (Finset.mem_sigma.1 hz).2
  obtain ⟨e1, e2⟩ := join_split X μ q hL
  show (⟨appendChain (splitL q' X μ).1.1 (splitL q' X μ).2,
    (splitL q' X μ).1.2 ++ List.replicate (topCount (splitL q' X μ).2) q'⟩ : Σ _ : RegChain, List ℕ) = _
  rw [e1, e2]

omit hqq in
theorem decT_comT (b : ℕ) (v : Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegChain)
    (hv : v ∈ (antidiagonal b).sigma fun jb => UP q q' jb.1 ×ˢ Mexp.domTrees jb.2) :
    decT b q' (comT q' v) = v := by
  obtain ⟨⟨j, b₀⟩, ⟨U, lsU⟩, Z⟩ := v
  simp only [Finset.mem_sigma, Finset.mem_product, UP, Finset.HasAntidiagonal.mem_antidiagonal] at hv
  obtain ⟨hjb, ⟨hU, hlsU⟩, -⟩ := hv
  obtain ⟨-, -, hUs⟩ := Mexp.mem_domTrees.1 hU
  have hL := (mem_labsF U q lsU).1 hlsU
  show (⟨((splitL q' (appendChain U Z) (lsU ++ List.replicate (topCount Z) q')).1.1.size / 2,
    b - (splitL q' (appendChain U Z) (lsU ++ List.replicate (topCount Z) q')).1.1.size / 2),
    (⟨(splitL q' (appendChain U Z) (lsU ++ List.replicate (topCount Z) q')).1.1,
      (splitL q' (appendChain U Z) (lsU ++ List.replicate (topCount Z) q')).1.2⟩,
      (splitL q' (appendChain U Z) (lsU ++ List.replicate (topCount Z) q')).2)⟩ :
      Σ _ : ℕ × ℕ, (Σ _ : RegChain, List ℕ) × RegChain) = _
  rw [split_join U lsU q Z hL]
  simp only [show U.size / 2 = j by omega, show b - j = b₀ by omega]

/-- **Labelled trees are pairs (upper labelled chain, bottom chain).** -/
theorem sum_tree_decomp (b : ℕ) (h : RegChain → List ℕ → ℂ) :
    ∑ X ∈ Mexp.domTrees b, ∑ μ ∈ labsF q' X q, h X μ =
      ∑ jb ∈ antidiagonal b, ∑ y ∈ UP q q' jb.1, ∑ Z ∈ Mexp.domTrees jb.2,
        h (appendChain y.1 Z) (y.2 ++ List.replicate (topCount Z) q') := by
  rw [Finset.sum_sigma']
  have hr : ∑ jb ∈ antidiagonal b, ∑ y ∈ UP q q' jb.1, ∑ Z ∈ Mexp.domTrees jb.2,
      h (appendChain y.1 Z) (y.2 ++ List.replicate (topCount Z) q') =
      ∑ v ∈ (antidiagonal b).sigma (fun jb => UP q q' jb.1 ×ˢ Mexp.domTrees jb.2), h (comT q' v).1 (comT q' v).2 := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun jb _ => (Finset.sum_product (UP q q' jb.1) (Mexp.domTrees jb.2)
      (fun w => h (comT q' ⟨jb, w⟩).1 (comT q' ⟨jb, w⟩).2)).symm
  rw [hr]
  exact Finset.sum_nbij' (decT b q') (comT q') (decT_mem b) (comT_mem hqq b) (comT_decT b) (decT_comT b)
    fun z hz => by rw [comT_decT b z hz]

end Tree

end WaveTurbulence.PL234
