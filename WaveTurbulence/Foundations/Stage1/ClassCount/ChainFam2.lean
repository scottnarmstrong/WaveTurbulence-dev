/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.ChainFam
public import WaveTurbulence.Foundations.Molecule.VineChainIngredients
import Mathlib.Tactic

/-!
# CLASSCOUNT: the chain induction for layering sums

`chain_fam`: for a vine chain `U` and a family `𝓗` of layerings distinct on `U`, the sum over the final joint layer is
bounded by the row vector `chainV L 1` of the transfer matrices of the ingredients (`Msum`), whose classification data
`(good, c, T)` is a list `Ls` independent of `𝓗`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

theorem filter_filter_joint (𝓗 : Finset (V → ℕ)) (a b : V) (s z : ℕ) :
    (𝓗.filter (fun f => f b = z)).filter (fun f => f a = s) = 𝓗.filter (fun f => f a = s ∧ f b = z) := by
  ext f; simp only [Finset.mem_filter]; tauto

theorem sum_pair_le (M : Molecule V D) {B : ℝ} (hB : 0 ≤ B) (S T : Finset V) (Fy IS : Finset (V → ℕ))
    (hIS : Fy.image (restr S) ⊆ IS)
    (hinj : ∀ f ∈ Fy, ∀ f' ∈ Fy, (∀ x ∈ S, f x = f' x) → (∀ x ∈ T, f x = f' x) → f = f') :
    ∑ f ∈ Fy, bw M B S f * bw M B T f ≤
      (∑ r ∈ IS, bw M B S r) * ∑ r ∈ Fy.image (restr T), bw M B T r := by
  let ψ : (V → ℕ) → (V → ℕ) × (V → ℕ) := fun f => (restr S f, restr T f)
  have hψ : Set.InjOn ψ (Fy : Set (V → ℕ)) := by
    intro f hf f' hf' he
    refine hinj f hf f' hf' (fun x hx => ?_) (fun x hx => ?_)
    · have := congrFun (congrArg Prod.fst he) x
      simpa [ψ, restr, hx] using this
    · have := congrFun (congrArg Prod.snd he) x
      simpa [ψ, restr, hx] using this
  calc ∑ f ∈ Fy, bw M B S f * bw M B T f
      = ∑ f ∈ Fy, (bw M B S (ψ f).1 * bw M B T (ψ f).2) :=
        Finset.sum_congr rfl fun f _ => by simp only [ψ, bw_restr]
    _ = ∑ q ∈ Fy.image ψ, bw M B S q.1 * bw M B T q.2 :=
        (Finset.sum_image (f := fun q : (V → ℕ) × (V → ℕ) => bw M B S q.1 * bw M B T q.2) hψ).symm
    _ ≤ ∑ q ∈ IS ×ˢ Fy.image (restr T), bw M B S q.1 * bw M B T q.2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ =>
          mul_nonneg (bw_nonneg M hB _ _) (bw_nonneg M hB _ _)
        intro q hq
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_product.mpr ⟨hIS (Finset.mem_image_of_mem _ hf), Finset.mem_image_of_mem _ hf⟩
    _ = _ := by rw [Finset.sum_product, Finset.sum_mul_sum]

theorem chain_fam (M : Molecule V D) (hM : M.IsMolecule) {U : Finset V} {a b : V} {n : ℕ} (hC : Chain M U a b n) :
    ∃ Ts : List (Finset V × V × V), Ts.length = n ∧
      (∀ t ∈ Ts, ChainIngredient M U a b n t.1 t.2.1 t.2.2) ∧
      (Ts.map (fun t => t.1.erase t.2.1)).Pairwise Disjoint ∧
      ∀ {B : ℝ} (hB : 0 ≤ B) (𝔇 : ℕ) (K : ℝ) (𝓖 : Finset (V → ℕ)) (h𝔇 : ∀ f ∈ 𝓖, ∀ x, f x ≤ 𝔇)
        (cls : Finset V → V → V → Bool × ℝ × ℝ) (U₀ : Finset V) (Inv : Finset V → V → V → Prop)
        (Ext : Finset V → V → V → Prop)
        (hInvStep : ∀ {S T : Finset V} {a b c : V} {n : ℕ}, Chain M S a b n → IsSomeVine M T b c → S ∩ T = {b} →
          M.IsBlock (S ∪ T) a c → Inv (S ∪ T) a c → Inv S a b)
        (hing : ∀ T x y, Ext T x y → (∃ U' a' b' n', U' ⊆ U₀ ∧ M.IsBlock U' a' b' ∧ Inv U' a' b' ∧
          ChainIngredient M U' a' b' n' T x y) → ∀ 𝓗 ⊆ 𝓖, (linkOf M B T x y 𝓗 (cls T x y)).Ok 𝔇 K),
        (∀ t ∈ Ts, Ext t.1 t.2.1 t.2.2) → U ⊆ U₀ → M.IsBlock U a b → Inv U a b →
      ∀ 𝓗 ⊆ 𝓖, DistinctOn U 𝓗 → ∃ L : List Link,
        L.map Link.proj = Ts.map (fun t => cls t.1 t.2.1 t.2.2) ∧ (∀ l ∈ L, l.Ok 𝔇 K) ∧
        ∀ z, ∑ f ∈ 𝓗.filter (fun f => f b = z), bw M B U f ≤ chainV 𝔇 L (fun _ => 1) z := by
  induction hC with
  | @single S a b hv =>
    refine ⟨[(S, a, b)], rfl, ?_, by simp, ?_⟩
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact ChainIngredient.single hv
    · intro B hB 𝔇 K 𝓖 h𝔇 cls U₀ Inv Ext hInvStep hing hExt hUU hBU hInv 𝓗 h𝓗 hdist
      refine ⟨[linkOf M B S a b 𝓗 (cls S a b)], rfl, ?_, ?_⟩
      · intro l hl
        rw [List.mem_singleton] at hl
        rw [hl]
        exact hing S a b (hExt (S, a, b) (by simp)) ⟨S, a, b, 1, hUU, hBU, hInv, ChainIngredient.single hv⟩ 𝓗 h𝓗
      · intro z
        simp only [chainV, prop, linkOf, one_mul]
        have hmaps : ∀ f ∈ 𝓗.filter (fun f => f b = z), f a ∈ Finset.range (𝔇 + 1) := by
          intro f hf
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h𝔇 f (h𝓗 (Finset.mem_filter.mp hf).1) a))
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine le_of_eq (Finset.sum_congr rfl fun s _ => ?_)
        rw [filter_filter_joint, Msum]
        exact sum_bw_eq_image M B S ((hdist.subset (Finset.filter_subset _ _)))
  | @append S T a b c n hS hT hi hne ih =>
    have hT' := hT
    obtain ⟨Y, hY⟩ := hT
    have hBT := hY.1
    have hSU : S ⊆ S ∪ T := Finset.subset_union_left
    have hTU : T ⊆ S ∪ T := Finset.subset_union_right
    obtain ⟨Ts, hlen, hmem, hdisj, hmain⟩ := ih
    have hbS : b ∈ S := (chain_joints_mem hS).2
    refine ⟨Ts ++ [(T, b, c)], by simp [hlen], ?_, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact ChainIngredient.append_left (hmem t ht) hT' hi hne
      · rw [List.mem_singleton] at ht
        subst ht
        exact ChainIngredient.append_last hS hT' hi hne
    · rw [List.map_append, List.pairwise_append]
      refine ⟨hdisj, by simp, ?_⟩
      intro R1 hR1 R2 hR2
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hR2
      subst hR2
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hR1
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      have hzS : z ∈ S := (chainIngredient_spec (hmem t ht)).2.2 (Finset.mem_of_mem_erase hz1)
      have hzT : z ∈ T := Finset.mem_of_mem_erase hz2
      have : z ∈ S ∩ T := Finset.mem_inter.mpr ⟨hzS, hzT⟩
      rw [hi, Finset.mem_singleton] at this
      exact (Finset.ne_of_mem_erase hz2) this
    · intro B hB 𝔇 K 𝓖 h𝔇 cls U₀ Inv Ext hInvStep hing hExt hUU hU hInv 𝓗 h𝓗 hdist
      have hBS := chain_prefix_isBlock M hM hS hY hi hU
      have hmain' := hmain hB 𝔇 K 𝓖 h𝔇 cls U₀ Inv Ext hInvStep hing
        (fun t ht => hExt t (List.mem_append_left _ ht)) (hSU.trans hUU) hBS (hInvStep hS hT' hi hU hInv)
      obtain ⟨𝓣, h𝓣𝓗, hdistT, himg⟩ := exists_transversal S 𝓗
      obtain ⟨L, hLmap, hLok, hLb⟩ := hmain' 𝓣 (h𝓣𝓗.trans h𝓗) hdistT
      have hlok : (linkOf M B T b c 𝓗 (cls T b c)).Ok 𝔇 K :=
        hing T b c (hExt (T, b, c) (by simp))
          ⟨S ∪ T, a, c, n + 1, hUU, hU, hInv, ChainIngredient.append_last hS hT' hi hne⟩ 𝓗 h𝓗
      refine ⟨L ++ [linkOf M B T b c 𝓗 (cls T b c)], by simp [hLmap, Link.proj, linkOf], ?_, ?_⟩
      · intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact hLok l hl
        · rw [List.mem_singleton] at hl; rw [hl]; exact hlok
      · intro z
        rw [chainV_append]
        simp only [prop, linkOf, Msum]
        set F : Finset (V → ℕ) := 𝓗.filter (fun f => f b = z) with hF
        have hmaps : ∀ f ∈ 𝓗.filter (fun f => f c = z), f b ∈ Finset.range (𝔇 + 1) := by
          intro f hf
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h𝔇 f (h𝓗 (Finset.mem_filter.mp hf).1) b))
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_le_sum fun y _ => ?_
        have hFy : (𝓗.filter (fun f => f c = z)).filter (fun f => f b = y) =
            𝓗.filter (fun f => f b = y ∧ f c = z) := by
          ext f; simp only [Finset.mem_filter]; tauto
        rw [hFy]
        set Fy : Finset (V → ℕ) := 𝓗.filter (fun f => f b = y ∧ f c = z) with hFydef
        have hFy𝓗 : Fy ⊆ 𝓗 := Finset.filter_subset _ _
        have hunion : ∀ f ∈ Fy, bw M B (S ∪ T) f = bw M B S f * bw M B T f :=
          fun f _ => bw_union M hM B hBS hBT hU hi f
        rw [Finset.sum_congr rfl hunion]
        set IS : Finset (V → ℕ) := (𝓣.filter (fun f => f b = y)).image (restr S) with hIS
        have hsub : Fy.image (restr S) ⊆ IS := by
          intro r hr
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hr
          have hf' := Finset.mem_filter.mp hf
          have : restr S f ∈ 𝓣.image (restr S) := by
            rw [himg]; exact Finset.mem_image_of_mem _ hf'.1
          obtain ⟨f', hf'𝓣, he⟩ := Finset.mem_image.mp this
          refine Finset.mem_image.mpr ⟨f', Finset.mem_filter.mpr ⟨hf'𝓣, ?_⟩, he⟩
          have := congrFun he b
          simp only [restr, hbS, ite_true] at this
          rw [this]; exact hf'.2.1
        refine (sum_pair_le M hB S T Fy IS hsub ?_).trans ?_
        · intro f hf f' hf' h1 h2
          exact hdist f (hFy𝓗 hf) f' (hFy𝓗 hf') fun x hx => (Finset.mem_union.mp hx).elim (h1 x) (h2 x)
        · have hsum : ∑ r ∈ IS, bw M B S r = ∑ f ∈ 𝓣.filter (fun f => f b = y), bw M B S f :=
            (sum_bw_eq_image M B S (hdistT.subset (Finset.filter_subset _ _))).symm
          rw [hsum]
          exact mul_le_mul_of_nonneg_right (hLb y) (Finset.sum_nonneg fun r _ => bw_nonneg M hB _ _)

end WaveTurbulence.ClassCount
