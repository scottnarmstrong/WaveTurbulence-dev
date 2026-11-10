/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitSum` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Iso
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitLinks
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitSum
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ChainFam2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.ChainFam3
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCL
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitChain2
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode6
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily
public import WaveTurbulence.Foundations.Stage1.ClassCount.VineData


/-!
# CLASSCOUNT: the layering sum over a unit (vine Fama.Spine.chain)

`unit_sum`: for a (CL) vine Fama.Spine.chain `U` and a family `𝓖` of layerings on which the incoherency index of every ingredient is
constant (`gfix`), the sum `Σ_{f ∈ 𝓗} bw U f` over a subfamily distinct on `U` is at most
`Cu^{3|U|} (Cu^{𝔇+1})^{3 + Σ_{bad ingredients} (g_T + 3)}`.  An ingredient is *good* if its incoherency index is `0` and every
member of the family has coherent regional attachments (`SourceRegion`); all other ingredients are *bad*.  This is the
run/bad accounting of `ChainSum` (TARGET L1519, L2243-L2249 charge `C_2` per ingredient).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt WaveTurbulence.LFTwist WaveTurbulence.GammaLow.FinalCount
variable [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact TVineStructInputs]

variable {w : ℕ}

theorem AL_nonnegG {α : Type*} (𝔇 : ℕ) (K C₀ Cb : ℝ) (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hCb : 0 ≤ Cb)
    (good : α → Prop) [DecidablePred good] (m g : α → ℕ) (clsv : α → Bool × ℝ × ℝ) :
    ∀ Ts : List α, (∀ t ∈ Ts, clsv t = if good t then (true, C₀ ^ m t, 0)
        else (false, 0, Cb ^ m t * (Cb ^ (𝔇 + 1)) ^ (g t + 1))) →
      0 ≤ AL 𝔇 K (Ts.map clsv)
  | [], _ => by simp [AL]
  | t :: Ts, h => by
    have hih := AL_nonnegG 𝔇 K C₀ Cb hK hC₀ hCb good m g clsv Ts fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    have ht := h t (List.mem_cons_self ..)
    simp only [List.map_cons, AL]
    refine mul_nonneg ?_ hih
    by_cases hg : good t
    · rw [ht, if_pos hg]; simp only [if_true]; positivity
    · rw [ht, if_neg hg]; simp only [Bool.false_eq_true, if_false]; positivity

/-- The list bound for the classification product, with the bad weight `Cb^m (Cb^{𝔇+1})^{g+1}` (main `AL_bound`). -/
theorem AL_boundG {α : Type*} (𝔇 : ℕ) (K Cu C₀ Cb : ℝ) (hK : K = C₀) (hC₀ : 1 ≤ C₀) (hCb : 1 ≤ Cb)
    (hCu : C₀ + Cb + 2 ≤ Cu) (good : α → Prop) [DecidablePred good] (m g : α → ℕ) (clsv : α → Bool × ℝ × ℝ) :
    ∀ Ts : List α, (∀ t ∈ Ts, clsv t = if good t then (true, C₀ ^ m t, 0)
        else (false, 0, Cb ^ m t * (Cb ^ (𝔇 + 1)) ^ (g t + 1))) →
      AL 𝔇 K (Ts.map clsv) * 2 ^ ngoodL (Ts.map clsv) ≤
        Cu ^ (Ts.map (fun t => m t + 1)).sum *
          (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ good t)).map (fun t => g t + 3)).sum := by
  have hCC : C₀ ≤ Cu := by linarith
  have hCbC : Cb ≤ Cu := by linarith
  have h2C : (2 : ℝ) ≤ Cu := by linarith
  have hCu1 : 1 ≤ Cu := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  intro Ts
  induction Ts with
  | nil => intro _; simp [AL, ngoodL]
  | cons t Ts ih =>
    intro h
    have hh : ∀ t' ∈ Ts, clsv t' = if good t' then (true, C₀ ^ m t', 0)
        else (false, 0, Cb ^ m t' * (Cb ^ (𝔇 + 1)) ^ (g t' + 1)) :=
      fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    have hih := ih hh
    have hAL0 := AL_nonnegG 𝔇 K C₀ Cb hK0 (by linarith) (by linarith) good m g clsv Ts hh
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
            exact mul_le_mul (pow_le_pow_left₀ (by linarith) hCC _) h2C (by norm_num) (by positivity)
        _ = _ := by ring
    · rw [ht, if_neg hg]
      simp only [Bool.false_eq_true, if_false, List.filter_cons, hg, not_false_eq_true, decide_true, if_true,
        List.map_cons, List.sum_cons, zero_add]
      have hf : K ^ 𝔇 * 2 ^ 𝔇 * (Cb ^ m t * (Cb ^ (𝔇 + 1)) ^ (g t + 1)) ≤
          Cu ^ (m t + 1) * (Cu ^ (𝔇 + 1)) ^ (g t + 3) := by
        calc K ^ 𝔇 * 2 ^ 𝔇 * (Cb ^ m t * (Cb ^ (𝔇 + 1)) ^ (g t + 1))
            ≤ Cu ^ 𝔇 * Cu ^ 𝔇 * (Cu ^ m t * (Cu ^ (𝔇 + 1)) ^ (g t + 1)) := by
              gcongr
              · rw [hK]; exact hCC
          _ = Cu ^ (m t + 2 * 𝔇 + (𝔇 + 1) * (g t + 1)) := by rw [← pow_mul]; ring
          _ ≤ Cu ^ ((m t + 1) + (𝔇 + 1) * (g t + 3)) := pow_le_pow_right₀ hCu1 (by nlinarith)
          _ = _ := by rw [pow_add, ← pow_mul]
      calc K ^ 𝔇 * 2 ^ 𝔇 * (Cb ^ m t * (Cb ^ (𝔇 + 1)) ^ (g t + 1)) * AL 𝔇 K (Ts.map clsv) *
            2 ^ ngoodL (Ts.map clsv)
          = (K ^ 𝔇 * 2 ^ 𝔇 * (Cb ^ m t * (Cb ^ (𝔇 + 1)) ^ (g t + 1))) *
              (AL 𝔇 K (Ts.map clsv) * 2 ^ ngoodL (Ts.map clsv)) := by ring
        _ ≤ (Cu ^ (m t + 1) * (Cu ^ (𝔇 + 1)) ^ (g t + 3)) * (Cu ^ (Ts.map (fun t => m t + 1)).sum *
              (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ good t)).map (fun t => g t + 3)).sum) :=
            mul_le_mul hf hih (by positivity) (by positivity)
        _ = _ := by rw [pow_add _ (g t + 3)]; ring

open Classical in
/-- The classification oracle of the ingredients. -/
noncomputable def clsOfG (G : Garden w) (hG : G.IsPlain) (p 𝔇 : ℕ) (𝓖 : Finset (GBranch G.tree → ℕ))
    (gfix : Finset (GBranch G.tree) → ℕ) (C₀ Cb : ℝ) (T : Finset (GBranch G.tree)) (x y : GBranch G.tree) :
    Bool × ℝ × ℝ :=
  if GoodIng G hG p 𝓖 gfix (T, x, y) then (true, C₀ ^ vmOfG G.molecule T x y, 0)
  else (false, 0, Cb ^ vmOfG G.molecule T x y * (Cb ^ (𝔇 + 1)) ^ (gfix T + 1))

open Classical in
/-- **The layering sum over a unit (vine Fama.Spine.chain).**  The list of ingredient triples depends only on the Fama.Spine.chain. -/
theorem unit_sumG (hImp : LayervineTVineImproved) (hFirst : LayervineTVineFirst) : ∃ Cu : ℝ, 2 ≤ Cu ∧
    ∀ (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (G : Garden w) (hG : G.IsPlain) {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {n : ℕ}
      (hC : Src.Chain γ G.molecule U a b n) (hU : G.molecule.IsBlock U a b) (hCL : Mole.CLParentPattern G U a b),
      ∃ Ts : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree), Ts.length = n ∧
        (∀ t ∈ Ts, ChainIngredientG γ G.molecule U a b n t.1 t.2.1 t.2.2 ∧ Mole.CLParentPattern G t.1 t.2.1 t.2.2) ∧
        (Ts.map (fun t => t.1.erase t.2.1)).Pairwise Disjoint ∧
        ∀ (p 𝔇 : ℕ) (𝓖 : Finset (GBranch G.tree → ℕ))
          (h𝓖 : ∀ f ∈ 𝓖, IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇)
          (gfix : Finset (GBranch G.tree) → ℕ)
          (hgfix : ∀ f ∈ 𝓖, ∀ t ∈ Ts, Fama.vineIncoh γ G f t.1 = gfix t.1),
        ∀ 𝓗 ⊆ 𝓖, DistinctOn U 𝓗 →
          ∑ f ∈ 𝓗, bw G.molecule 2 U f ≤ Cu ^ (3 * U.card) *
            (Cu ^ (𝔇 + 1)) ^
              (3 + ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) := by
  obtain ⟨C₀, hC₀, hlink⟩ := link_ok_goodG hImp
  obtain ⟨Cb, hCb, hbad⟩ := link_ok_badG hFirst
  set Cu : ℝ := C₀ + Cb + 2 with hCudef
  have hCu2 : 2 ≤ Cu := by rw [hCudef]; linarith
  have hCu1 : 1 ≤ Cu := by linarith
  refine ⟨Cu, hCu2, ?_⟩
  intro γ _ w G hG U a b n hC hU hCL
  have hM := Mole.garden_isMolecule G
  have hInvStep : ∀ {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree} {n : ℕ},
      Src.Chain γ G.molecule S a b n → Src.IsSomeVine γ G.molecule T b c → S ∩ T = {b} →
      G.molecule.IsBlock (S ∪ T) a c → Mole.CLParentPattern G (S ∪ T) a c → Mole.CLParentPattern G S a b := by
    intro S T a b c n hS hT hi hU' hCL'
    have hY := hT
    have hBS := chain_prefix_isBlock G.molecule hM hS hY hi hU'
    exact (cl_split hM hBS (Src.isBlock_of_isSomeVine hY) hU' hi (Src.isBlock_of_isSomeVine hY).2.2.2.1 hCL').2
  obtain ⟨Ts, hlen, hmem, hdisj, hmain⟩ := chain_total G.molecule hM hC
  refine ⟨Ts, hlen, fun t ht => ⟨hmem t ht, ing_cl hM (hmem t ht) hU hCL⟩, hdisj, ?_⟩
  intro p 𝔇 𝓖 h𝓖 gfix hgfix 𝓗 h𝓗 hdist
  have hing : ∀ T x y, (T, x, y) ∈ Ts →
      (∃ U' a' b' n', U' ⊆ U ∧ G.molecule.IsBlock U' a' b' ∧ Mole.CLParentPattern G U' a' b' ∧
        ChainIngredientG γ G.molecule U' a' b' n' T x y) → ∀ 𝓗 ⊆ 𝓖,
      (linkOf G.molecule 2 T x y 𝓗 (clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb T x y)).Ok 𝔇 C₀ := by
    intro T x y hExt ⟨U', a', b', n', hU'U, hB', hCL', hI⟩ 𝓗 h𝓗
    have hV : Src.IsSomeVine γ G.molecule T x y := (chainIngredientG_spec (hmem _ hExt)).2.1
    have hCLT : Mole.CLParentPattern G T x y := ing_cl hM hI hB' hCL'
    by_cases hg : GoodIng G hG p 𝓖 gfix (T, x, y)
    · simp only [clsOfG, if_pos hg]
      exact hlink γ G hG p 𝔇 𝓖 (fun f hf => (h𝓖 f hf).1) T x y hV hCLT
        (fun f hf => ⟨hg.2.2 f hf, by rw [hgfix f hf _ hExt]; exact hg.2.1⟩) 𝓗 h𝓗
    · simp only [clsOfG, if_neg hg]
      exact hbad γ G 𝔇 C₀ 𝓖 h𝓖 T x y hV (gfix T) (fun f hf => hgfix f hf _ hExt) 𝓗 h𝓗
  have hmain' := hmain (B := 2) (by norm_num) 𝔇 (K := C₀) hC₀ 𝓖
    (fun f hf => (h𝓖 f hf).2) (clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb) U (fun S a b => Mole.CLParentPattern G S a b)
    (fun T x y => (T, x, y) ∈ Ts) hInvStep hing (fun t ht => ht) (Finset.Subset.refl _) hU hCL 𝓗 h𝓗 hdist
  refine hmain'.trans ?_
  have hAL := AL_boundG 𝔇 C₀ Cu C₀ Cb rfl hC₀ hCb le_rfl (GoodIng G hG p 𝓖 gfix)
    (fun t => vmOfG G.molecule t.1 t.2.1 t.2.2) (fun t => gfix t.1)
    (fun t => clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb t.1 t.2.1 t.2.2) Ts (fun t _ => by simp only [clsOfG])
  have hAL' : AL 𝔇 C₀ (Ts.map (fun t => clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb t.1 t.2.1 t.2.2)) *
      2 ^ ngoodL (Ts.map (fun t => clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb t.1 t.2.1 t.2.2)) ≤
      Cu ^ (Ts.map (fun t => vmOfG G.molecule t.1 t.2.1 t.2.2 + 1)).sum *
        (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum := by
    simpa [Function.comp_def] using hAL
  -- the exponent
  have hS : (Ts.map (fun t => vmOfG G.molecule t.1 t.2.1 t.2.2 + 1)).sum ≤ 3 * U.card := by
    have hRs := sum_card_le_of_disjoint U (Ts.map (fun t => t.1.erase t.2.1)) hdisj (by
      intro R hR
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hR
      exact (Finset.erase_subset _ _).trans (chainIngredientG_spec (hmem t ht)).2.2)
    have hterm : ∀ t ∈ Ts, vmOfG G.molecule t.1 t.2.1 t.2.2 + 1 ≤ 3 * (t.1.erase t.2.1).card := by
      intro t ht
      have hV := (chainIngredientG_spec (hmem t ht)).2.1
      have hB := Src.isBlock_of_isSomeVine hV
      have hxT : t.2.1 ∈ t.1 := hB.2.1
      have hyT : t.2.2 ∈ t.1 := hB.2.2.1
      have hxy : t.2.1 ≠ t.2.2 := hB.2.2.2.1
      have hcard : (t.1.erase t.2.1).card = t.1.card - 1 := Finset.card_erase_of_mem hxT
      have hpos' : 0 < (t.1.erase t.2.1).card :=
        Finset.card_pos.mpr ⟨t.2.2, Finset.mem_erase.mpr ⟨hxy.symm, hyT⟩⟩
      have := vmOfG_le (M := G.molecule) (T := t.1) (x := t.2.1) (y := t.2.2)
      omega
    have : (Ts.map (fun t => vmOfG G.molecule t.1 t.2.1 t.2.2 + 1)).sum ≤
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
  have hAL0 : 0 ≤ AL 𝔇 C₀ (Ts.map (fun t => clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb t.1 t.2.1 t.2.2)) *
      2 ^ ngoodL (Ts.map (fun t => clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb t.1 t.2.1 t.2.2)) := by
    refine mul_nonneg ?_ (by positivity)
    exact AL_nonnegG 𝔇 C₀ C₀ Cb (by linarith) (by linarith) (by linarith) (GoodIng G hG p 𝓖 gfix)
      (fun t => vmOfG G.molecule t.1 t.2.1 t.2.2) (fun t => gfix t.1)
      (fun t => clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb t.1 t.2.1 t.2.2) Ts (fun t _ => by simp only [clsOfG])
  calc AL 𝔇 C₀ (Ts.map (fun t => clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb t.1 t.2.1 t.2.2)) *
        2 ^ ngoodL (Ts.map (fun t => clsOfG G hG p 𝔇 𝓖 gfix C₀ Cb t.1 t.2.1 t.2.2)) *
        (((𝔇 + 1 : ℕ) : ℝ) * (C₀ ^ 𝔇 * 2 ^ 𝔇))
      ≤ (Cu ^ (Ts.map (fun t => vmOfG G.molecule t.1 t.2.1 t.2.2 + 1)).sum *
          (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) *
          (Cu ^ (𝔇 + 1)) ^ 3 := mul_le_mul hAL' hfac (by positivity) (by positivity)
    _ ≤ Cu ^ (3 * U.card) * (Cu ^ (𝔇 + 1)) ^
          (3 + ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) := by
        rw [pow_add (Cu ^ (𝔇 + 1)) 3]
        have : Cu ^ (Ts.map (fun t => vmOfG G.molecule t.1 t.2.1 t.2.2 + 1)).sum ≤ Cu ^ (3 * U.card) :=
          pow_le_pow_right₀ hCu1 hS
        calc _ = Cu ^ (Ts.map (fun t => vmOfG G.molecule t.1 t.2.1 t.2.2 + 1)).sum * ((Cu ^ (𝔇 + 1)) ^ 3 *
              (Cu ^ (𝔇 + 1)) ^ ((Ts.filter (fun t => ¬ GoodIng G hG p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) := by ring
          _ ≤ _ := by gcongr

end WaveTurbulence.GammaLow.Famc.ClassCount
