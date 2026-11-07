/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitLinks
import Mathlib.Tactic

/-!
# CLASSCOUNT: the layering sum over a unit (vine chain)

`unit_sum`: for a (CL) vine chain `U` and a family `𝓖` of layerings on which the incoherency index of every ingredient is
constant (`gfix`), the sum `Σ_{f ∈ 𝓗} bw U f` over a subfamily distinct on `U` is at most
`Cu^{3|U|} (Cu^{𝔇+1})^{3 + Σ_{bad ingredients} (g_T + 3)}`.  An ingredient is *good* if its incoherency index is `0` and every
member of the family has coherent regional attachments (`SourceRegion`); all other ingredients are *bad*.  This is the
run/bad accounting of `ChainSum` (TARGET L1519, L2243-L2249 charge `C_2` per ingredient).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt WaveTurbulence.LFTwist

theorem AL_nonneg {α : Type*} (𝔇 : ℕ) (K C₀ : ℝ) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (good : α → Prop) [DecidablePred good] (m g : α → ℕ) (clsv : α → Bool × ℝ × ℝ) :
    ∀ Ts : List α, (∀ t ∈ Ts, clsv t = if good t then (true, C₀ ^ m t, 0)
        else (false, 0, 9 ^ m t * (((2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60) ^ 𝔇) ^ (g t + 1))) →
      0 ≤ AL 𝔇 K (Ts.map clsv)
  | [], _ => by simp [AL]
  | t :: Ts, h => by
    have hih := AL_nonneg 𝔇 K C₀ hK hC₀ good m g clsv Ts fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    have ht := h t (List.mem_cons_self ..)
    simp only [List.map_cons, AL]
    refine mul_nonneg ?_ hih
    by_cases hg : good t
    · rw [ht, if_pos hg]; simp only [if_true]; positivity
    · rw [ht, if_neg hg]; simp only [Bool.false_eq_true, if_false]; positivity

/-- The list bound for the classification product. -/
theorem AL_bound {α : Type*} (𝔇 : ℕ) (K Cu C₀ : ℝ) (hK : K = C₀) (hC₀ : 1 ≤ C₀)
    (hCu : C₀ + 9 + (2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60 ≤ Cu)
    (good : α → Prop) [DecidablePred good] (m g : α → ℕ) (clsv : α → Bool × ℝ × ℝ) :
    ∀ Ts : List α, (∀ t ∈ Ts, clsv t = if good t then (true, C₀ ^ m t, 0)
        else (false, 0, 9 ^ m t * (((2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60) ^ 𝔇) ^ (g t + 1))) →
      AL 𝔇 K (Ts.map clsv) * 2 ^ ngoodL (Ts.map clsv) ≤
        Cu ^ (Ts.map (fun t => m t + 1)).sum *
          (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ good t)).map (fun t => g t + 3)).sum := by
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60 := by positivity
  have hc1 : (2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60 ≤ Cu := by linarith
  have hc9 : (9 : ℝ) ≤ Cu := by linarith
  have hCC : C₀ ≤ Cu := by linarith
  have hCu1 : 1 ≤ Cu := by linarith
  have hCu0 : 0 < Cu := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  intro Ts
  induction Ts with
  | nil => intro _; simp [AL, ngoodL]
  | cons t Ts ih =>
    intro h
    have hh : ∀ t' ∈ Ts, clsv t' = if good t' then (true, C₀ ^ m t', 0)
        else (false, 0, 9 ^ m t' * (((2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60) ^ 𝔇) ^ (g t' + 1)) :=
      fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    have hih := ih hh
    have hAL0 := AL_nonneg 𝔇 K C₀ hK0 (by linarith) good m g clsv Ts hh
    have ht := h t (List.mem_cons_self ..)
    simp only [List.map_cons, AL, ngoodL, List.sum_cons]
    by_cases hg : good t
    · rw [ht, if_pos hg]
      simp only [if_true, List.filter_cons, hg, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      calc C₀ ^ m t * AL 𝔇 K (Ts.map clsv) * 2 ^ (1 + ngoodL (Ts.map clsv))
          = (C₀ ^ m t * 2) * (AL 𝔇 K (Ts.map clsv) * 2 ^ ngoodL (Ts.map clsv)) := by ring
        _ ≤ (Cu ^ (m t + 1)) * (Cu ^ (Ts.map (fun t => m t + 1)).sum *
              (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ good t)).map (fun t => g t + 3)).sum) := by
            refine mul_le_mul ?_ hih (by positivity) (by positivity)
            rw [pow_succ]
            exact mul_le_mul (pow_le_pow_left₀ (by linarith) hCC _) (by linarith) (by norm_num) (by positivity)
        _ = _ := by ring
    · rw [ht, if_neg hg]
      simp only [Bool.false_eq_true, if_false, List.filter_cons, hg, not_false_eq_true, decide_true, if_true,
        List.map_cons, List.sum_cons, zero_add]
      have hf : K ^ 𝔇 * 2 ^ 𝔇 * (9 ^ m t * (((2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60) ^ 𝔇) ^ (g t + 1)) ≤
          Cu ^ (m t + 1) * (Cu ^ (𝔇 + 1)) ^ (g t + 3) := by
        calc K ^ 𝔇 * 2 ^ 𝔇 * (9 ^ m t * (((2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60) ^ 𝔇) ^ (g t + 1))
            ≤ Cu ^ 𝔇 * Cu ^ 𝔇 * (Cu ^ m t * (Cu ^ 𝔇) ^ (g t + 1)) := by
              gcongr
              · rw [hK]; exact hCC
              · linarith
          _ = Cu ^ (m t + 𝔇 * (g t + 3)) := by rw [← pow_mul]; ring_nf
          _ ≤ Cu ^ ((m t + 1) + (𝔇 + 1) * (g t + 3)) := pow_le_pow_right₀ hCu1 (by nlinarith)
          _ = _ := by rw [pow_add, ← pow_mul]
      calc K ^ 𝔇 * 2 ^ 𝔇 * (9 ^ m t * (((2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60) ^ 𝔇) ^ (g t + 1)) * AL 𝔇 K (Ts.map clsv) *
            2 ^ ngoodL (Ts.map clsv)
          = (K ^ 𝔇 * 2 ^ 𝔇 * (9 ^ m t * (((2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60) ^ 𝔇) ^ (g t + 1))) *
              (AL 𝔇 K (Ts.map clsv) * 2 ^ ngoodL (Ts.map clsv)) := by ring
        _ ≤ (Cu ^ (m t + 1) * (Cu ^ (𝔇 + 1)) ^ (g t + 3)) * (Cu ^ (Ts.map (fun t => m t + 1)).sum *
              (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ good t)).map (fun t => g t + 3)).sum) :=
            mul_le_mul hf hih (by positivity) (by positivity)
        _ = _ := by rw [pow_add _ (g t + 3)]; ring

theorem sum_card_le_of_disjoint {V : Type*} [DecidableEq V] (U : Finset V) :
    ∀ Rs : List (Finset V), Rs.Pairwise Disjoint → (∀ R ∈ Rs, R ⊆ U) → (Rs.map Finset.card).sum ≤ U.card
  | [], _, _ => by simp
  | R :: Rs, hd, hsub => by
    rw [List.pairwise_cons] at hd
    have hRU : R ⊆ U := hsub R (List.mem_cons_self ..)
    have h1 := sum_card_le_of_disjoint (U \ R) Rs hd.2 (fun R' hR' => by
      intro z hz
      exact Finset.mem_sdiff.mpr ⟨hsub R' (List.mem_cons_of_mem _ hR') hz,
        fun hzR => Finset.disjoint_left.mp (hd.1 R' hR') hzR hz⟩)
    rw [List.map_cons, List.sum_cons]
    have := Finset.card_sdiff_of_subset hRU
    have := Finset.card_le_card hRU
    omega

variable {w : ℕ}

/-- A good ingredient: (CL), incoherency index `0` and coherent regional attachments for every member. -/
def GoodIng (G : Garden w) (hG : G.IsPlain) (p : ℕ) (𝓖 : Finset (GBranch G.tree → ℕ))
    (gfix : Finset (GBranch G.tree) → ℕ) (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) : Prop :=
  Mole.CLParentPattern G t.1 t.2.1 t.2.2 ∧ gfix t.1 = 0 ∧ ∀ f ∈ 𝓖, SourceRegion G hG p t.1 t.2.1 f

open Classical in
/-- The classification oracle of the ingredients. -/
noncomputable def clsOf (G : Garden w) (hG : G.IsPlain) (p 𝔇 : ℕ) (𝓖 : Finset (GBranch G.tree → ℕ))
    (gfix : Finset (GBranch G.tree) → ℕ) (C₀ : ℝ) (T : Finset (GBranch G.tree)) (x y : GBranch G.tree) :
    Bool × ℝ × ℝ :=
  if GoodIng G hG p 𝓖 gfix (T, x, y) then (true, C₀ ^ vmOf G.molecule T x y, 0)
  else (false, 0, 9 ^ vmOf G.molecule T x y * (((2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60) ^ 𝔇) ^ (gfix T + 1))

open Classical in
/-- **The layering sum over a unit (vine chain).**  The list of ingredient triples depends only on the chain. -/
theorem unit_sum : ∃ Cu : ℝ, 2 ≤ Cu ∧
    ∀ {w : ℕ} (G : Garden w) (hG : G.IsPlain) {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {n : ℕ}
      (hC : Vine.Chain G.molecule U a b n) (hU : G.molecule.IsBlock U a b) (hCL : Mole.CLParentPattern G U a b),
      ∃ Ts : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree), Ts.length = n ∧
        (∀ t ∈ Ts, ChainIngredient G.molecule U a b n t.1 t.2.1 t.2.2 ∧ Mole.CLParentPattern G t.1 t.2.1 t.2.2) ∧
        (Ts.map (fun t => t.1.erase t.2.1)).Pairwise Disjoint ∧
        ∀ (p 𝔇 : ℕ) (𝓖 : Finset (GBranch G.tree → ℕ))
          (h𝓖 : ∀ f ∈ 𝓖, IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇)
          (gfix : Finset (GBranch G.tree) → ℕ)
          (hgfix : ∀ f ∈ 𝓖, ∀ t ∈ Ts, RedSplice.vineIncoh G f t.1 = gfix t.1),
        ∀ 𝓗 ⊆ 𝓖, DistinctOn U 𝓗 →
          ∑ f ∈ 𝓗, bw G.molecule 2 U f ≤ Cu ^ (3 * U.card) *
            (Cu ^ (𝔇 + 1)) ^
              (3 + ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) := by
  obtain ⟨C₀, hC₀, hlink⟩ := link_ok_good
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60 := by positivity
  set Cu : ℝ := C₀ + 9 + (2 : ℝ) ^ 21 * 3 ^ 48 * 2 ^ 60 with hCudef
  have hCu2 : 2 ≤ Cu := by rw [hCudef]; linarith
  have hCu1 : 1 ≤ Cu := by linarith
  refine ⟨Cu, hCu2, ?_⟩
  intro w G hG U a b n hC hU hCL
  have hM := Mole.garden_isMolecule G
  have hInvStep : ∀ {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree} {n : ℕ},
      Vine.Chain G.molecule S a b n → IsSomeVine G.molecule T b c → S ∩ T = {b} →
      G.molecule.IsBlock (S ∪ T) a c → Mole.CLParentPattern G (S ∪ T) a c → Mole.CLParentPattern G S a b := by
    intro S T a b c n hS hT hi hU' hCL'
    obtain ⟨Y, hY⟩ := hT
    have hBS := chain_prefix_isBlock G.molecule hM hS hY hi hU'
    exact (cl_split hM hBS hY.1 hU' hi hY.1.2.2.2.1 hCL').2
  obtain ⟨Ts, hlen, hmem, hdisj, hmain⟩ := chain_total G.molecule hM hC
  refine ⟨Ts, hlen, fun t ht => ⟨hmem t ht, ing_cl hM (hmem t ht) hU hCL⟩, hdisj, ?_⟩
  intro p 𝔇 𝓖 h𝓖 gfix hgfix 𝓗 h𝓗 hdist
  have hing : ∀ T x y, (T, x, y) ∈ Ts →
      (∃ U' a' b' n', U' ⊆ U ∧ G.molecule.IsBlock U' a' b' ∧ Mole.CLParentPattern G U' a' b' ∧
        ChainIngredient G.molecule U' a' b' n' T x y) → ∀ 𝓗 ⊆ 𝓖,
      (linkOf G.molecule 2 T x y 𝓗 (clsOf G hG p 𝔇 𝓖 gfix C₀ T x y)).Ok 𝔇 C₀ := by
    intro T x y hExt ⟨U', a', b', n', hU'U, hB', hCL', hI⟩ 𝓗 h𝓗
    have hV : IsSomeVine G.molecule T x y := (chainIngredient_spec (hmem _ hExt)).2.1
    have hCLT : Mole.CLParentPattern G T x y := ing_cl hM hI hB' hCL'
    by_cases hg : GoodIng G hG p 𝓖 gfix (T, x, y)
    · simp only [clsOf, if_pos hg]
      exact hlink G hG p 𝔇 𝓖 (fun f hf => (h𝓖 f hf).1) T x y hV hCLT
        (fun f hf => ⟨hg.2.2 f hf, by rw [hgfix f hf _ hExt]; exact hg.2.1⟩) 𝓗 h𝓗
    · simp only [clsOf, if_neg hg]
      exact link_ok_bad G 𝔇 C₀ 𝓖 h𝓖 T x y hV (gfix T) (fun f hf => hgfix f hf _ hExt) 𝓗 h𝓗
  have hmain' := hmain (B := 2) (by norm_num) 𝔇 (K := C₀) hC₀ 𝓖
    (fun f hf => (h𝓖 f hf).2) (clsOf G hG p 𝔇 𝓖 gfix C₀) U (fun S a b => Mole.CLParentPattern G S a b)
    (fun T x y => (T, x, y) ∈ Ts) hInvStep hing (fun t ht => ht) (Finset.Subset.refl _) hU hCL 𝓗 h𝓗 hdist
  refine hmain'.trans ?_
  have hAL := AL_bound 𝔇 C₀ Cu C₀ rfl hC₀ le_rfl (GoodIng G hG p 𝓖 gfix)
    (fun t => vmOf G.molecule t.1 t.2.1 t.2.2) (fun t => gfix t.1)
    (fun t => clsOf G hG p 𝔇 𝓖 gfix C₀ t.1 t.2.1 t.2.2) Ts (fun t _ => by simp only [clsOf])
  have hAL' : AL 𝔇 C₀ (Ts.map (fun t => clsOf G hG p 𝔇 𝓖 gfix C₀ t.1 t.2.1 t.2.2)) *
      2 ^ ngoodL (Ts.map (fun t => clsOf G hG p 𝔇 𝓖 gfix C₀ t.1 t.2.1 t.2.2)) ≤
      Cu ^ (Ts.map (fun t => vmOf G.molecule t.1 t.2.1 t.2.2 + 1)).sum *
        (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum := by
    simpa [Function.comp_def] using hAL
  -- the exponent
  have hS : (Ts.map (fun t => vmOf G.molecule t.1 t.2.1 t.2.2 + 1)).sum ≤ 3 * U.card := by
    have hRs := sum_card_le_of_disjoint U (Ts.map (fun t => t.1.erase t.2.1)) hdisj (by
      intro R hR
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hR
      exact (Finset.erase_subset _ _).trans (chainIngredient_spec (hmem t ht)).2.2)
    have hterm : ∀ t ∈ Ts, vmOf G.molecule t.1 t.2.1 t.2.2 + 1 ≤ 3 * (t.1.erase t.2.1).card := by
      intro t ht
      have hV := (chainIngredient_spec (hmem t ht)).2.1
      obtain ⟨X, hX, -, -⟩ := vmOf_spec hV
      have hxT : t.2.1 ∈ t.1 := hX.1.2.1
      have hyT : t.2.2 ∈ t.1 := hX.1.2.2.1
      have hxy : t.2.1 ≠ t.2.2 := hX.1.2.2.2.1
      have hcard : (t.1.erase t.2.1).card = t.1.card - 1 := Finset.card_erase_of_mem hxT
      have hpos' : 0 < (t.1.erase t.2.1).card :=
        Finset.card_pos.mpr ⟨t.2.2, Finset.mem_erase.mpr ⟨hxy.symm, hyT⟩⟩
      have := vmOf_le hV
      omega
    have : (Ts.map (fun t => vmOf G.molecule t.1 t.2.1 t.2.2 + 1)).sum ≤
        (Ts.map (fun t => 3 * (t.1.erase t.2.1).card)).sum :=
      List.sum_le_sum (fun t ht => hterm t ht)
    refine this.trans ?_
    have h3 : (Ts.map (fun t => 3 * (t.1.erase t.2.1).card)).sum =
        3 * ((Ts.map (fun t => t.1.erase t.2.1)).map Finset.card).sum := by
      rw [List.map_map, ← List.sum_map_mul_left]; rfl
    rw [h3]; omega
  have hfac : ((𝔇 + 1 : ℕ) : ℝ) * (C₀ ^ 𝔇 * 2 ^ 𝔇) ≤ (Cu ^ (𝔇 + 1)) ^ 3 := by
    have h1 : ((𝔇 + 1 : ℕ) : ℝ) ≤ 2 ^ 𝔇 := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ 𝔇 ≤ Cu ^ 𝔇 := pow_le_pow_left₀ (by norm_num) hCu2 _
    have h3 : C₀ ^ 𝔇 ≤ Cu ^ 𝔇 := pow_le_pow_left₀ (by linarith) (by rw [hCudef]; linarith) _
    calc ((𝔇 + 1 : ℕ) : ℝ) * (C₀ ^ 𝔇 * 2 ^ 𝔇) ≤ Cu ^ 𝔇 * (Cu ^ 𝔇 * Cu ^ 𝔇) := by
          gcongr; exact h1.trans h2
      _ = Cu ^ (3 * 𝔇) := by ring
      _ ≤ Cu ^ (3 * (𝔇 + 1)) := pow_le_pow_right₀ hCu1 (by omega)
      _ = (Cu ^ (𝔇 + 1)) ^ 3 := by rw [mul_comm, pow_mul]
  have hAL0 : 0 ≤ AL 𝔇 C₀ (Ts.map (fun t => clsOf G hG p 𝔇 𝓖 gfix C₀ t.1 t.2.1 t.2.2)) *
      2 ^ ngoodL (Ts.map (fun t => clsOf G hG p 𝔇 𝓖 gfix C₀ t.1 t.2.1 t.2.2)) := by
    refine mul_nonneg ?_ (by positivity)
    exact AL_nonneg 𝔇 C₀ C₀ (by linarith) (by linarith) (GoodIng G hG p 𝓖 gfix)
      (fun t => vmOf G.molecule t.1 t.2.1 t.2.2) (fun t => gfix t.1)
      (fun t => clsOf G hG p 𝔇 𝓖 gfix C₀ t.1 t.2.1 t.2.2) Ts (fun t _ => by simp only [clsOf])
  calc AL 𝔇 C₀ (Ts.map (fun t => clsOf G hG p 𝔇 𝓖 gfix C₀ t.1 t.2.1 t.2.2)) *
        2 ^ ngoodL (Ts.map (fun t => clsOf G hG p 𝔇 𝓖 gfix C₀ t.1 t.2.1 t.2.2)) *
        (((𝔇 + 1 : ℕ) : ℝ) * (C₀ ^ 𝔇 * 2 ^ 𝔇))
      ≤ (Cu ^ (Ts.map (fun t => vmOf G.molecule t.1 t.2.1 t.2.2 + 1)).sum *
          (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) *
          (Cu ^ (𝔇 + 1)) ^ 3 := mul_le_mul hAL' hfac (by positivity) (by positivity)
    _ ≤ Cu ^ (3 * U.card) * (Cu ^ (𝔇 + 1)) ^
          (3 + ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) := by
        rw [pow_add (Cu ^ (𝔇 + 1)) 3]
        have : Cu ^ (Ts.map (fun t => vmOf G.molecule t.1 t.2.1 t.2.2 + 1)).sum ≤ Cu ^ (3 * U.card) :=
          pow_le_pow_right₀ hCu1 hS
        calc _ = Cu ^ (Ts.map (fun t => vmOf G.molecule t.1 t.2.1 t.2.2 + 1)).sum * ((Cu ^ (𝔇 + 1)) ^ 3 *
              (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) := by ring
          _ ≤ _ := by gcongr

end WaveTurbulence.ClassCount
