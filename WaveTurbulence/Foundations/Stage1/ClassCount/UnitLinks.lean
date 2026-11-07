/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.ChainFam3
public import WaveTurbulence.Foundations.Stage1.ClassCount.VineData
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitCL
public import WaveTurbulence.Foundations.LayerCnt.Source
public import WaveTurbulence.Foundations.LayerCnt.LayerRange
import Mathlib.Tactic

/-!
# CLASSCOUNT: the transfer matrices of the ingredient vines are `Link.Ok`

* good ingredient (a (CL) vine, with coherent regional attachments and incoherency index `0` for every member of the
  family): the improved bound of `layervine` (`layervine_improved_source`) gives `M(s,t) ≤ C₀^m C₀^{s-t}`, and `M(s,t) = 0`
  for `s < t` (`layer_le_upper`);
* any ingredient with constant incoherency index `g` on the family: the first bound (`vine_sum_le`) bounds the total.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt WaveTurbulence.LFTwist


/-- The `m` of a vine (`card = 2m+2` for the bad types, `2m+5` otherwise). -/
noncomputable def vmOf {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (T : Finset V) (x y : V) : ℕ := by
  classical
  exact if h : ∃ X, M.IsVine X T x y then (vine_card_m (Classical.choose_spec h)).choose else 0

theorem vmOf_spec {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {T : Finset V} {x y : V} (h : IsSomeVine M T x y) :
    ∃ X, M.IsVine X T x y ∧ (X.IsBad = true → T.card = 2 * vmOf M T x y + 2) ∧
      (X.IsBad = false → T.card = 2 * vmOf M T x y + 5) := by
  classical
  have h' : ∃ X, M.IsVine X T x y := h
  refine ⟨Classical.choose h', Classical.choose_spec h', ?_⟩
  unfold vmOf
  rw [dif_pos h']
  exact (vine_card_m (Classical.choose_spec h')).choose_spec

theorem vmOf_le {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {T : Finset V} {x y : V} (h : IsSomeVine M T x y) : vmOf M T x y ≤ T.card := by
  obtain ⟨X, -, h1, h2⟩ := vmOf_spec h
  cases hb : X.IsBad
  · have := h2 hb; omega
  · have := h1 hb; omega

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] in
theorem bw_eq_pow (M : Molecule V D) (B : ℝ) (S : Finset V) (f : V → ℕ) :
    bw M B S f = B ^ bondExp M S f := by
  unfold bw bondExp
  rw [Finset.prod_pow_eq_pow_sum]

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

theorem msum_nonneg (M : Molecule V D) {B : ℝ} (hB : 0 ≤ B) (T : Finset V) (x y : V) (𝓗 : Finset (V → ℕ))
    (s t : ℕ) : 0 ≤ Msum M B T x y 𝓗 s t :=
  Finset.sum_nonneg fun r _ => bw_nonneg M hB _ _

theorem msum_eq_transversal (M : Molecule V D) (B : ℝ) (T : Finset V) (x y : V) (𝓗 : Finset (V → ℕ)) (s t : ℕ) :
    ∃ 𝓕 ⊆ 𝓗.filter (fun f => f x = s ∧ f y = t), DistinctOn T 𝓕 ∧ Msum M B T x y 𝓗 s t = ∑ f ∈ 𝓕, bw M B T f := by
  obtain ⟨𝓕, h1, h2, h3⟩ := exists_transversal T (𝓗.filter (fun f => f x = s ∧ f y = t))
  refine ⟨𝓕, h1, h2, ?_⟩
  unfold Msum
  rw [← h3]
  exact (sum_bw_eq_image M B T h2).symm

/-- **The good link is `Ok`.** -/
theorem link_ok_good : ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ {w : ℕ} (G : Garden w) (hG : G.IsPlain) (p 𝔇 : ℕ) (𝓖 : Finset (GBranch G.tree → ℕ))
      (h𝓖 : ∀ f ∈ 𝓖, IsBranchPrelayering G f)
      (T : Finset (GBranch G.tree)) (x y : GBranch G.tree) (hV : IsSomeVine G.molecule T x y)
      (hCL : Mole.CLParentPattern G T x y)
      (hgood : ∀ f ∈ 𝓖, SourceRegion G hG p T x f ∧ RedSplice.vineIncoh G f T = 0)
      (𝓗 : Finset (GBranch G.tree → ℕ)) (h𝓗 : 𝓗 ⊆ 𝓖),
      (linkOf G.molecule 2 T x y 𝓗 (true, C₀ ^ vmOf G.molecule T x y, 0)).Ok 𝔇 C₀ := by
  obtain ⟨C₀, hC₀, himp⟩ := layervine_improved_source 2 (by norm_num)
  refine ⟨C₀, hC₀, ?_⟩
  intro w G hG p 𝔇 𝓖 h𝓖 T x y hV hCL hgood 𝓗 h𝓗
  obtain ⟨X, hX, hbad, hnorm⟩ := vmOf_spec hV
  obtain ⟨-, ⟨R⟩⟩ := isVine_iff_realization.mp hX
  have hxT : x ∈ T := hX.1.2.1
  have hyT : y ∈ T := hX.1.2.2.1
  refine ⟨fun s t => msum_nonneg G.molecule (by norm_num) T x y 𝓗 s t, fun _ => ⟨pow_nonneg (by linarith) _, ?_⟩, fun _ => ?_, fun h => absurd h (by simp [linkOf])⟩
  · intro s t hts
    obtain ⟨𝓕, h𝓕sub, hdist, hM⟩ := msum_eq_transversal G.molecule 2 T x y 𝓗 s t
    simp only [linkOf]
    rw [hM]
    have hmem : ∀ f ∈ 𝓕, f ∈ 𝓖 ∧ f x = s ∧ f y = t := by
      intro f hf
      have := Finset.mem_filter.mp (h𝓕sub hf)
      exact ⟨h𝓗 this.1, this.2.1, this.2.2⟩
    have := himp G hG X T x y hX hCL R (vmOf G.molecule T x y) hbad hnorm p s t 𝓕
      (fun f hf => (hgood f (hmem f hf).1).1) 
      (fun f hf => (vineIncoh_eq G (Mole.garden_isMolecule G) hX R f).symm.trans (hgood f (hmem f hf).1).2)
      (fun f hf => ⟨(hmem f hf).2.1, (hmem f hf).2.2⟩) hdist
    calc ∑ f ∈ 𝓕, bw G.molecule 2 T f ≤ C₀ ^ (vmOf G.molecule T x y + (s - t)) := this
      _ = C₀ ^ vmOf G.molecule T x y * C₀ ^ (s - t) := pow_add _ _ _
  · intro s t hst
    simp only [linkOf, Msum]
    refine Finset.sum_eq_zero fun r hr => ?_
    exfalso
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hr
    have hfm := Finset.mem_filter.mp hf
    obtain ⟨hf1, hf2, hf3⟩ : f ∈ 𝓗 ∧ f x = s ∧ f y = t := ⟨hfm.1, hfm.2.1, hfm.2.2⟩
    have := layer_le_upper G hX.1 hCL (h𝓖 f (h𝓗 hf1)) y hyT
    omega

theorem sum_msum_le (M : Molecule V D) {B : ℝ} (hB : 0 ≤ B) (T : Finset V) {x y : V} (hx : x ∈ T) (hy : y ∈ T)
    (𝔇 : ℕ) (𝓗 : Finset (V → ℕ)) :
    ∑ s ∈ Finset.range (𝔇 + 1), ∑ t ∈ Finset.range (𝔇 + 1), Msum M B T x y 𝓗 s t ≤
      ∑ r ∈ 𝓗.image (restr T), bw M B T r := by
  classical
  let I : ℕ × ℕ → Finset (V → ℕ) := fun st => (𝓗.filter (fun f => f x = st.1 ∧ f y = st.2)).image (restr T)
  have hdisj : ∀ a ∈ Finset.range (𝔇 + 1) ×ˢ Finset.range (𝔇 + 1), ∀ b ∈ Finset.range (𝔇 + 1) ×ˢ Finset.range (𝔇 + 1),
      a ≠ b → Disjoint (I a) (I b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro r h1 h2
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨f', hf', he⟩ := Finset.mem_image.mp h2
    have hf1 := (Finset.mem_filter.mp hf).2
    have hf2 := (Finset.mem_filter.mp hf').2
    apply hab
    have hxx := congrFun he x
    have hyy := congrFun he y
    simp only [restr, hx, hy, ite_true] at hxx hyy
    exact Prod.ext (by rw [← hf1.1, ← hf2.1, hxx]) (by rw [← hf1.2, ← hf2.2, hyy])
  calc ∑ s ∈ Finset.range (𝔇 + 1), ∑ t ∈ Finset.range (𝔇 + 1), Msum M B T x y 𝓗 s t
      = ∑ st ∈ Finset.range (𝔇 + 1) ×ˢ Finset.range (𝔇 + 1), ∑ r ∈ I st, bw M B T r := by
        rw [Finset.sum_product]; rfl
    _ = ∑ r ∈ (Finset.range (𝔇 + 1) ×ˢ Finset.range (𝔇 + 1)).biUnion I, bw M B T r :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => bw_nonneg M hB _ _
        intro r hr
        obtain ⟨st, -, hst⟩ := Finset.mem_biUnion.mp hr
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hst
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hf).1

/-- **The bad link is `Ok`**: first bound with constant incoherency index. -/
theorem link_ok_bad {w : ℕ} (G : Garden w) (𝔇 : ℕ) (K : ℝ) (𝓖 : Finset (GBranch G.tree → ℕ))
    (h𝓖 : ∀ f ∈ 𝓖, IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇)
    (T : Finset (GBranch G.tree)) (x y : GBranch G.tree) (hV : IsSomeVine G.molecule T x y) (g : ℕ)
    (hg : ∀ f ∈ 𝓖, RedSplice.vineIncoh G f T = g) (𝓗 : Finset (GBranch G.tree → ℕ)) (h𝓗 : 𝓗 ⊆ 𝓖) :
    (linkOf G.molecule 2 T x y 𝓗
      (false, 0, (9 : ℝ) ^ vmOf G.molecule T x y * (((2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60) ^ 𝔇) ^ (g + 1))).Ok 𝔇 K := by
  obtain ⟨X, hX, hbad, hnorm⟩ := vmOf_spec hV
  obtain ⟨-, ⟨R⟩⟩ := isVine_iff_realization.mp hX
  have hxT : x ∈ T := hX.1.2.1
  have hyT : y ∈ T := hX.1.2.2.1
  refine ⟨fun s t => msum_nonneg G.molecule (by norm_num) T x y 𝓗 s t, fun h => absurd h (by simp [linkOf]),
    fun h => absurd h (by simp [linkOf]), fun _ => ?_⟩
  simp only [linkOf]
  refine (sum_msum_le G.molecule (by norm_num) T hxT hyT 𝔇 𝓗).trans ?_
  obtain ⟨𝓕, h𝓕𝓗, hdist, himg⟩ := exists_transversal T 𝓗
  have hs : ∑ r ∈ 𝓗.image (restr T), bw G.molecule 2 T r = ∑ f ∈ 𝓕, bw G.molecule 2 T f := by
    rw [← himg]; exact (sum_bw_eq_image G.molecule 2 T hdist).symm
  rw [hs]
  have hfilter : 𝓕.filter (fun f => realizedIncoherencyIndex R f = g) = 𝓕 := by
    refine Finset.filter_true_of_mem fun f hf => ?_
    rw [← vineIncoh_eq G (Mole.garden_isMolecule G) hX R f]
    exact hg f (h𝓗 (h𝓕𝓗 hf))
  have := vine_sum_le 2 (by norm_num) G X T x y R (vmOf G.molecule T x y) hbad hnorm 𝔇 g 𝓕
    (fun f hf => h𝓖 f (h𝓗 (h𝓕𝓗 hf))) hdist
  rw [hfilter] at this
  simpa only [bw_eq_pow, bondExp] using this

end WaveTurbulence.ClassCount
