/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.ProdRestr2
public import WaveTurbulence.Foundations.Stage1.ClassCount.BondSplit
public import WaveTurbulence.Foundations.Stage1.ClassCount.SpliceLayer
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitSum
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitChain2
public import WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.LayerCnt.Layerlad
import Mathlib.Tactic

/-!
# CLASSCOUNT (B2): the weight sum `Σ_f 2^{bondExp M(S) f}` over a class of layerings

Blocks: the ladders of the spliced garden (transported through `ob`) and the interiors of the units.  Each block is
bounded by `layerlad` resp. `unit_sum`; the free atoms contribute `(p+1)` each, and the remaining bonds `2^p` each
(`bondExp_splice_le`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LayerCnt WaveTurbulence.Vine

/-- **Generic block bound.**  If `E f ≤ c + Σ_k e k f` on the family and each block's `2^{e k}`-sum over distinct-on-block
subfamilies is at most `X k`, then `Σ_f 2^{E f} ≤ 2^c (𝔇+1)^{#outside} ∏ X k`. -/
theorem sum_pow_le_of_blocks {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (𝓕 : Finset (V → ℕ)) (𝔇 : ℕ) (hf : ∀ f ∈ 𝓕, ∀ x, f x ≤ 𝔇) (A : ι → Finset V)
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (e : ι → (V → ℕ) → ℕ) (X : ι → ℝ) (E : (V → ℕ) → ℕ) (c : ℕ)
    (hE : ∀ f ∈ 𝓕, E f ≤ c + ∑ k, e k f)
    (hX : ∀ k, ∀ 𝓖 ⊆ 𝓕, (∀ f ∈ 𝓖, ∀ f' ∈ 𝓖, (∀ x ∈ A k, f x = f' x) → f = f') →
      ∑ f ∈ 𝓖, (2 : ℝ) ^ (e k f) ≤ X k) :
    ∑ f ∈ 𝓕, (2 : ℝ) ^ (E f) ≤ (2 : ℝ) ^ c * (((𝔇 + 1 : ℕ) : ℝ) ^ (Finset.univ \ Finset.univ.biUnion A).card *
      ∏ k, X k) := by
  have h1 := sum_prod_restr_le' 𝓕 𝔇 hf A hA (fun k f => (2 : ℝ) ^ (e k f)) (fun k f => by positivity) X hX
  calc ∑ f ∈ 𝓕, (2 : ℝ) ^ (E f) ≤ ∑ f ∈ 𝓕, (2 : ℝ) ^ c * ∏ k, (2 : ℝ) ^ (e k f) := by
        refine Finset.sum_le_sum fun f hf' => ?_
        rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (hE f hf')
    _ = (2 : ℝ) ^ c * ∑ f ∈ 𝓕, ∏ k, (2 : ℝ) ^ (e k f) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Ladder block bound** (TARGET `layerlad` through the transport `ob`). -/
theorem ladder_block : ∃ CL : ℝ, 1 ≤ CL ∧ ∀ {w' : ℕ} (V : Type) [Fintype V] [DecidableEq V]
    (G' : Garden w') (ob : GBranch G'.tree → V) (hob : Function.Injective ob) {m : ℕ}
    (u v : Fin (m + 1) → GBranch G'.tree) (hL : G'.molecule.IsLadder u v) (p γ : ℕ) (𝓗 : Finset (V → ℕ))
    (hpre : ∀ f ∈ 𝓗, LFTwist.IsBranchPrelayering G' (f ∘ ob) ∧ ∀ x, f x ≤ p)
    (hγ : ∀ f ∈ 𝓗, incoherencyIndex (f ∘ ob) (ladderGroups u v) = γ)
    (hdist : ∀ f ∈ 𝓗, ∀ f' ∈ 𝓗, (∀ x ∈ (Molecule.ladderAtoms u v).image ob, f x = f' x) → f = f'),
    ∑ f ∈ 𝓗, (2 : ℝ) ^ (bondExp G'.molecule (Molecule.ladderAtoms u v) (f ∘ ob)) ≤
      CL ^ m * (CL ^ (p + 1)) ^ (γ + 1) := by
  obtain ⟨CL, hCL, hlad⟩ := layerlad 2 (by norm_num)
  refine ⟨CL, hCL, ?_⟩
  intro w' V _ _ G' ob hob m u v hL p γ 𝓗 hpre hγ hdist
  classical
  by_cases hne : 𝓗 = ∅
  · subst hne; simp only [Finset.sum_empty]
    have : 0 ≤ CL := by linarith
    positivity
  obtain ⟨f0, hf0⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hγle : γ ≤ m + 1 := by
    rw [← hγ f0 hf0]
    have := incoherencyIndex_le (f0 ∘ ob) (ladderGroups u v)
    simpa [ladderGroups] using this
  have hinj : Set.InjOn (fun f => f ∘ ob) (𝓗 : Set (V → ℕ)) := by
    intro f hf f' hf' he
    refine hdist f hf f' hf' fun x hx => ?_
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact congrFun he c
  have hf' : ∀ g ∈ 𝓗.image (fun f => f ∘ ob), LFTwist.IsBranchPrelayering G' g ∧ ∀ x, g x ≤ p := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
    exact ⟨(hpre f hf).1, fun x => (hpre f hf).2 _⟩
  have hd' : ∀ g ∈ 𝓗.image (fun f => f ∘ ob), ∀ g' ∈ 𝓗.image (fun f => f ∘ ob),
      (∀ x ∈ Molecule.ladderAtoms u v, g x = g' x) → g = g' := by
    intro g hg g' hg' h
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hg'
    have : f = f' := hdist f hf f' hf' fun x hx => by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hx
      exact h c hc
    rw [this]
  have key := hlad G' u v hL p (CL ^ (p + 1)) le_rfl γ hγle (𝓗.image (fun f => f ∘ ob)) hf' hd'
  rw [Finset.filter_true_of_mem (by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
    exact hγ f hf)] at key
  have hpr : ∀ g : GBranch G'.tree → ℕ,
      ∏ x ∈ bondsIn G'.molecule (Molecule.ladderAtoms u v),
        (2 : ℝ) ^ dst (g (G'.molecule.atom x)) (g (G'.molecule.atom (G'.molecule.mate x))) =
      (2 : ℝ) ^ bondExp G'.molecule (Molecule.ladderAtoms u v) g := fun g => by
    unfold bondExp; rw [Finset.prod_pow_eq_pow_sum]
  simp only [hpr] at key
  rw [Finset.sum_image hinj] at key
  exact key

open Classical in
/-- B2d: **unit block bound** at any marked set. -/
theorem unit_blockMk : ∃ Cu : ℝ, 2 ≤ Cu ∧ ∀ {w : ℕ} (S : Garden w) (hS : S.IsPlain) (σ : Prescription S)
    (Mk : Set (Stage1.CLVine S)) (u : CLBlock S) (hu : u ∈ unitBlocks S σ Mk),
    ∃ Ts : List (Finset (GBranch S.tree) × GBranch S.tree × GBranch S.tree),
      (∃ n, ∀ t ∈ Ts, ChainIngredient S.molecule u.atoms u.upper u.lower n t.1 t.2.1 t.2.2 ∧
        Mole.CLParentPattern S t.1 t.2.1 t.2.2) ∧
      (Ts.map (fun t => t.1.erase t.2.1)).Pairwise Disjoint ∧
      ∀ (p : ℕ) (𝓖 : Finset (GBranch S.tree → ℕ)) (h𝓖 : ∀ f ∈ 𝓖, LFTwist.IsBranchPrelayering S f ∧ ∀ x, f x ≤ p)
        (gfix : Finset (GBranch S.tree) → ℕ) (hgfix : ∀ f ∈ 𝓖, ∀ t ∈ Ts, vineIncoh S f t.1 = gfix t.1),
      ∀ 𝓗 ⊆ 𝓖, DistinctOn u.atoms 𝓗 →
        ∑ f ∈ 𝓗, (2 : ℝ) ^ (bondExp S.molecule u.atoms f) ≤ Cu ^ (3 * u.atoms.card) *
          (Cu ^ (p + 1)) ^ (3 + ((Ts.filter (fun t => ¬ GoodIng S hS p 𝓖 gfix t)).map
            (fun t => gfix t.1 + 3)).sum) := by
  obtain ⟨Cu, hCu, hsum⟩ := unit_sum
  refine ⟨Cu, hCu, ?_⟩
  intro w S hS σ Mk u hu
  have hM := Mole.garden_isMolecule S
  obtain ⟨n, hn⟩ := unit_chainMk S hM σ (Mk := Mk) hu
  obtain ⟨Ts, hlen, hmem, hdisj, hbound⟩ := hsum S hS hn u.isBlock u.cl
  refine ⟨Ts, ⟨n, hmem⟩, hdisj, ?_⟩
  intro p 𝓖 h𝓖 gfix hgfix 𝓗 h𝓗 hd
  have := hbound p p 𝓖 h𝓖 gfix hgfix 𝓗 h𝓗 hd
  simpa only [bw_eq_pow] using this

open Classical in
/-- **Unit block bound** (`unit_sum` for the unit `u`, with the ingredient list exposed; the list depends only on `u`). -/
theorem unit_block : ∃ Cu : ℝ, 2 ≤ Cu ∧ ∀ {w : ℕ} (S : Garden w) (hS : S.IsPlain) (σ : Prescription S)
    (u : CLBlock S) (hu : u ∈ unitBlocks S σ),
    ∃ Ts : List (Finset (GBranch S.tree) × GBranch S.tree × GBranch S.tree),
      (∃ n, ∀ t ∈ Ts, ChainIngredient S.molecule u.atoms u.upper u.lower n t.1 t.2.1 t.2.2 ∧
        Mole.CLParentPattern S t.1 t.2.1 t.2.2) ∧
      (Ts.map (fun t => t.1.erase t.2.1)).Pairwise Disjoint ∧
      ∀ (p : ℕ) (𝓖 : Finset (GBranch S.tree → ℕ)) (h𝓖 : ∀ f ∈ 𝓖, LFTwist.IsBranchPrelayering S f ∧ ∀ x, f x ≤ p)
        (gfix : Finset (GBranch S.tree) → ℕ) (hgfix : ∀ f ∈ 𝓖, ∀ t ∈ Ts, vineIncoh S f t.1 = gfix t.1),
      ∀ 𝓗 ⊆ 𝓖, DistinctOn u.atoms 𝓗 →
        ∑ f ∈ 𝓗, (2 : ℝ) ^ (bondExp S.molecule u.atoms f) ≤ Cu ^ (3 * u.atoms.card) *
          (Cu ^ (p + 1)) ^ (3 + ((Ts.filter (fun t => ¬ GoodIng S hS p 𝓖 gfix t)).map
            (fun t => gfix t.1 + 3)).sum) :=
  let ⟨Cu, hCu, h⟩ := unit_blockMk
  ⟨Cu, hCu, fun S hS σ u hu => h S hS σ ∅ u hu⟩

theorem card_atomsOf {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {ι : Type}
    (F : LadderFam M ι) (i : ι) : (F.atomsOf i).card = 2 * (F.len i + 1) := by
  classical
  unfold LadderFam.atomsOf Molecule.ladderAtoms
  have hdisj : Disjoint (Finset.univ.image (F.u i)) (Finset.univ.image (F.v i)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hb
    exact F.ne_uv i x y hy.symm
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun a b h => F.inj_u i h),
    Finset.card_image_of_injective _ (fun a b h => F.inj_v i h)]
  simp; ring

theorem sum_len_le {V D : Type*} [DecidableEq V] [Fintype V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : LadderFam M ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j)) :
    ∑ i, F.len i ≤ Fintype.card V := by
  classical
  have h1 : ∑ i, (F.atomsOf i).card = ((Finset.univ : Finset ι).biUnion F.atomsOf).card :=
    (Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)).symm
  have h2 : ((Finset.univ : Finset ι).biUnion F.atomsOf).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  simp only [card_atomsOf] at h1
  have h3 : ∑ i, 2 * (F.len i + 1) = 2 * ∑ i, F.len i + 2 * Fintype.card ι := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp [mul_add]
  omega

abbrev Trip {w : ℕ} (S : Garden w) := Finset (GBranch S.tree) × GBranch S.tree × GBranch S.tree

theorem weight_numerics {ι J : Type} [Fintype ι] [Fintype J] (K CL Cu : ℝ) (hK2 : 2 ≤ K) (hCL1 : 1 ≤ CL)
    (hCLK : CL ≤ K) (hCu : 2 ≤ Cu) (hCuK : Cu ≤ K) (p free out : ℕ) (hout : out ≤ free)
    (len γ : ι → ℕ) (b E : J → ℕ) (n : ℕ) (hL : ∑ i, len i ≤ n) (hU : ∑ j, b j ≤ n) :
    (2 : ℝ) ^ (p * (4 * Fintype.card J + (4 * free + 4 * Fintype.card ι))) *
      (((p + 1 : ℕ) : ℝ) ^ out * ((∏ i, (CL ^ (len i) * (CL ^ (p + 1)) ^ (γ i + 1))) *
        ∏ j, (Cu ^ (3 * b j) * (Cu ^ (p + 1)) ^ (3 + E j)))) ≤
      K ^ (4 * n) * (K ^ (p + 1)) ^ (8 * (free + Fintype.card ι + Fintype.card J) + ∑ i, γ i + ∑ j, E j) := by
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hCL0 : 0 ≤ CL := by linarith
  have hCu0 : 0 ≤ Cu := by linarith
  set a : ℝ := K ^ (p + 1) with ha
  have ha1 : 1 ≤ a := one_le_pow₀ hK1
  have h2p : (2 : ℝ) ^ p ≤ a := by
    calc (2 : ℝ) ^ p ≤ K ^ p := pow_le_pow_left₀ (by norm_num) hK2 p
      _ ≤ K ^ (p + 1) := pow_le_pow_right₀ hK1 (by omega)
  have hp1 : ((p + 1 : ℕ) : ℝ) ≤ a := by
    have : (p + 1 : ℕ) ≤ 2 ^ p := Nat.lt_two_pow_self
    calc ((p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ p := by exact_mod_cast this
      _ ≤ a := h2p
  have hc : (2 : ℝ) ^ (p * (4 * Fintype.card J + (4 * free + 4 * Fintype.card ι))) ≤
      a ^ (4 * Fintype.card J + (4 * free + 4 * Fintype.card ι)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) h2p _
  have hop : ((p + 1 : ℕ) : ℝ) ^ out ≤ a ^ free :=
    (pow_le_pow_left₀ (by positivity) hp1 _).trans (pow_le_pow_right₀ ha1 hout)
  have hXi : ∏ i, (CL ^ (len i) * (CL ^ (p + 1)) ^ (γ i + 1)) ≤
      K ^ (∑ i, len i) * a ^ (∑ i, γ i + Fintype.card ι) := by
    calc ∏ i, (CL ^ (len i) * (CL ^ (p + 1)) ^ (γ i + 1)) ≤ ∏ i, (K ^ (len i) * a ^ (γ i + 1)) := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
          rw [ha, ← pow_mul, ← pow_mul]
          gcongr
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
          congr 2
          rw [Finset.sum_add_distrib]; simp
  have hXj : ∏ j, (Cu ^ (3 * b j) * (Cu ^ (p + 1)) ^ (3 + E j)) ≤
      K ^ (3 * ∑ j, b j) * a ^ (Fintype.card J * 3 + ∑ j, E j) := by
    calc ∏ j, (Cu ^ (3 * b j) * (Cu ^ (p + 1)) ^ (3 + E j)) ≤ ∏ j, (K ^ (3 * b j) * a ^ (3 + E j)) := by
          refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
          rw [ha, ← pow_mul, ← pow_mul]
          gcongr
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
            Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
  have hKe : K ^ (∑ i, len i) * K ^ (3 * ∑ j, b j) ≤ K ^ (4 * n) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hK1 (by omega)
  calc (2 : ℝ) ^ (p * (4 * Fintype.card J + (4 * free + 4 * Fintype.card ι))) *
        (((p + 1 : ℕ) : ℝ) ^ out * ((∏ i, (CL ^ (len i) * (CL ^ (p + 1)) ^ (γ i + 1))) *
          ∏ j, (Cu ^ (3 * b j) * (Cu ^ (p + 1)) ^ (3 + E j))))
      ≤ a ^ (4 * Fintype.card J + (4 * free + 4 * Fintype.card ι)) *
        (a ^ free * ((K ^ (∑ i, len i) * a ^ (∑ i, γ i + Fintype.card ι)) *
          (K ^ (3 * ∑ j, b j) * a ^ (Fintype.card J * 3 + ∑ j, E j)))) := by
        gcongr
    _ = (K ^ (∑ i, len i) * K ^ (3 * ∑ j, b j)) *
        a ^ ((4 * Fintype.card J + (4 * free + 4 * Fintype.card ι)) + free + (∑ i, γ i + Fintype.card ι) +
          (Fintype.card J * 3 + ∑ j, E j)) := by
        rw [pow_add, pow_add, pow_add, pow_add]; ring
    _ ≤ K ^ (4 * n) * a ^ (8 * (free + Fintype.card ι + Fintype.card J) + ∑ i, γ i + ∑ j, E j) := by
        exact mul_le_mul hKe (pow_le_pow_right₀ ha1 (by omega)) (by positivity) (by positivity)

open Classical in
/-- B2d: **the weight sum over a class of layerings** at any marked set. -/
theorem weight_sum_leMk : ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ {w : ℕ} (S : Garden w) (hS : S.IsPlain) (σ : Prescription S)
    (Mk : Set (Stage1.CLVine S)),
    ∃ Tss : Fin (unitBlocks S σ Mk).length → List (Trip S),
      (∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ Mk).get j).atoms
          ((unitBlocks S σ Mk).get j).upper ((unitBlocks S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2) ∧
      (∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint) ∧
      ∀ (p : ℕ) (𝓖 : Finset (GBranch S.tree → ℕ)) (h𝓖 : ∀ f ∈ 𝓖, LFTwist.IsBranchPrelayering S f ∧ ∀ x, f x ≤ p)
        (γ : {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders} → ℕ)
        (hγ : ∀ f ∈ 𝓖, ∀ i, incoherencyIndex (f ∘ (stSt S σ Mk).M.ob)
          (ladderGroups ((ladderDataOf (stSt S σ Mk).G).upper i) ((ladderDataOf (stSt S σ Mk).G).lower i)) = γ i)
        (gfix : Finset (GBranch S.tree) → ℕ)
        (hgfix : ∀ f ∈ 𝓖, ∀ j, ∀ t ∈ Tss j, vineIncoh S f t.1 = gfix t.1),
      ∑ f ∈ 𝓖, (2 : ℝ) ^ (bondExp S.molecule S.molecule.atoms f) ≤
        K0 ^ (4 * Fintype.card (GBranch S.tree)) * (K0 ^ (p + 1)) ^
          (8 * ((stSt S σ Mk).G.molecule.rho + (unitBlocks S σ Mk).length) + ∑ i, γ i +
            ∑ j, (((Tss j).filter (fun t => ¬ GoodIng S hS p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) := by
  obtain ⟨CL, hCL, hlad⟩ := ladder_block
  obtain ⟨Cu, hCu, hunit⟩ := unit_blockMk
  refine ⟨max CL Cu, le_max_of_le_right hCu, ?_⟩
  intro w S hS σ Mk
  classical
  have hM := Mole.garden_isMolecule S
  have hU : ∀ j : Fin (unitBlocks S σ Mk).length, ∃ Ts : List (Trip S),
      (∃ n, ∀ t ∈ Ts, ChainIngredient S.molecule ((unitBlocks S σ Mk).get j).atoms
          ((unitBlocks S σ Mk).get j).upper ((unitBlocks S σ Mk).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2) ∧
      (Ts.map (fun t => t.1.erase t.2.1)).Pairwise Disjoint ∧
      ∀ (p : ℕ) (𝓖 : Finset (GBranch S.tree → ℕ)) (h𝓖 : ∀ f ∈ 𝓖, LFTwist.IsBranchPrelayering S f ∧ ∀ x, f x ≤ p)
        (gfix : Finset (GBranch S.tree) → ℕ) (hgfix : ∀ f ∈ 𝓖, ∀ t ∈ Ts, vineIncoh S f t.1 = gfix t.1),
      ∀ 𝓗 ⊆ 𝓖, DistinctOn ((unitBlocks S σ Mk).get j).atoms 𝓗 →
        ∑ f ∈ 𝓗, (2 : ℝ) ^ (bondExp S.molecule ((unitBlocks S σ Mk).get j).atoms f) ≤
          Cu ^ (3 * ((unitBlocks S σ Mk).get j).atoms.card) *
          (Cu ^ (p + 1)) ^ (3 + ((Ts.filter (fun t => ¬ GoodIng S hS p 𝓖 gfix t)).map
            (fun t => gfix t.1 + 3)).sum) := fun j =>
    hunit S hS σ Mk _ (List.get_mem _ _)
  choose Tss hTss1 hTss2 hTss3 using hU
  refine ⟨Tss, hTss1, hTss2, ?_⟩
  intro p 𝓖 h𝓖 γ hγ gfix hgfix
  by_cases hne : Nonempty (GBranch S.tree)
  · obtain ⟨v0⟩ := hne
    have hM' : (stSt S σ Mk).G.molecule.IsMolecule := Mole.garden_isMolecule _
    set SD := spliceDataOfMk S hM σ Mk v0 with hSD
    set F := ladderFamOf (stSt S σ Mk).G with hF
    have hFd := ladderFamOf_disj (stSt S σ Mk).G hM'
    set ob := (stSt S σ Mk).M.ob with hob
    have hob_inj : Function.Injective ob := (stSt S σ Mk).M.ob_inj
    set A : {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders} ⊕ Fin (unitBlocks S σ Mk).length →
        Finset (GBranch S.tree) :=
      Sum.elim (fun i => (F.atomsOf i).image ob)
        (fun j => ((unitBlocks S σ Mk).get j).atoms.erase ((unitBlocks S σ Mk).get j).upper) with hA
    set e : {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders} ⊕ Fin (unitBlocks S σ Mk).length →
        (GBranch S.tree → ℕ) → ℕ :=
      Sum.elim (fun i f => bondExp (stSt S σ Mk).G.molecule (F.atomsOf i) (f ∘ ob))
        (fun j f => bondExp S.molecule ((unitBlocks S σ Mk).get j).atoms f) with he
    set X : {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders} ⊕ Fin (unitBlocks S σ Mk).length → ℝ :=
      Sum.elim (fun i => CL ^ (F.len i) * (CL ^ (p + 1)) ^ (γ i + 1))
        (fun j => Cu ^ (3 * ((unitBlocks S σ Mk).get j).atoms.card) *
          (Cu ^ (p + 1)) ^ (3 + (((Tss j).filter (fun t => ¬ GoodIng S hS p 𝓖 gfix t)).map
            (fun t => gfix t.1 + 3)).sum)) with hX
    have hpair := List.pairwise_iff_get.mp (unitBlocks_pairwiseMk hM σ Mk)
    have hinl_inr : ∀ (i : {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders}) (j : Fin (unitBlocks S σ Mk).length),
        Disjoint ((F.atomsOf i).image ob)
          (((unitBlocks S σ Mk).get j).atoms.erase ((unitBlocks S σ Mk).get j).upper) := by
      intro i j
      rw [Finset.disjoint_left]
      intro v hv hv'
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨hne', hmem⟩ := Finset.mem_erase.1 hv'
      have h1 := stSt_cls_memMk (Mk := Mk) hM σ (List.get_mem _ _) hmem
      have h2 := (stSt S σ Mk).M.ob_range (ob c) |>.1 ⟨c, rfl⟩
      rcases h2 with h2 | h2
      · rw [h1] at h2; exact absurd h2 (by simp)
      · rw [h1] at h2
        exact hne' (Option.some.inj h2).symm
    have hdisj : ∀ k k', k ≠ k' → Disjoint (A k) (A k') := by
      rintro (i | j) (i' | j') hne'
      · exact (Finset.disjoint_image hob_inj).2 (hFd i i' fun h => hne' (by rw [h]))
      · exact hinl_inr i j'
      · exact (hinl_inr i' j).symm
      · have hjj : j ≠ j' := fun h => hne' (by rw [h])
        have : Disjoint ((unitBlocks S σ Mk).get j).atoms ((unitBlocks S σ Mk).get j').atoms := by
          rcases lt_or_gt_of_ne hjj with h | h
          · exact hpair j j' h
          · exact (hpair j' j h).symm
        exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) this)
    have hXb : ∀ k, ∀ 𝓗 ⊆ 𝓖, (∀ f ∈ 𝓗, ∀ f' ∈ 𝓗, (∀ x ∈ A k, f x = f' x) → f = f') →
        ∑ f ∈ 𝓗, (2 : ℝ) ^ (e k f) ≤ X k := by
      rintro (i | j) 𝓗 h𝓗 hd
      · exact hlad (GBranch S.tree) (stSt S σ Mk).G ob hob_inj (F.u i) (F.v i) (F.lad i) p (γ i) 𝓗
          (fun f hf => ⟨ob_prelayeringMk S hM σ (Mk := Mk) (h𝓖 f (h𝓗 hf)).1, (h𝓖 f (h𝓗 hf)).2⟩)
          (fun f hf => hγ f (h𝓗 hf) i) hd
      · exact hTss3 j p 𝓖 h𝓖 gfix (fun f hf t ht => hgfix f hf j t ht) 𝓗 h𝓗 (fun f hf f' hf' h =>
          hd f hf f' hf' (fun x hx => h x (Finset.mem_of_mem_erase hx)))
    have hE : ∀ f ∈ 𝓖, bondExp S.molecule S.molecule.atoms f ≤
        p * (4 * (unitBlocks S σ Mk).length + (4 * ((stSt S σ Mk).G.molecule.atoms.filter
          (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders})) +
        ∑ k, e k f := by
      intro f hf
      have h1 := bondExp_splice_le SD hM' F hFd p f (fun x => (h𝓖 f hf).2 x)
      have h2 : ∑ i ∈ Finset.range SD.q, bondExp S.molecule (SD.U i) f =
          ∑ j : Fin (unitBlocks S σ Mk).length, bondExp S.molecule ((unitBlocks S σ Mk).get j).atoms f := by
        rw [Finset.sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [spliceDataOf_UMk S hM σ Mk v0 j.2]
        rfl
      rw [Fintype.sum_sum_type]
      simp only [he, Sum.elim_inl, Sum.elim_inr]
      have h3 : SD.q = (unitBlocks S σ Mk).length := rfl
      rw [h2, h3] at h1
      have h4 : SD.ob = ob := rfl
      rw [h4] at h1
      omega
    have hmain := sum_pow_le_of_blocks 𝓖 p (fun f hf x => (h𝓖 f hf).2 x) A hdisj e X
      (fun f => bondExp S.molecule S.molecule.atoms f)
      (p * (4 * (unitBlocks S σ Mk).length + (4 * ((stSt S σ Mk).G.molecule.atoms.filter
          (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card {T // T ∈ (stSt S σ Mk).G.molecule.maximalLadders})))
      hE hXb
    -- the outside atoms are free atoms of the spliced garden
    have hout : (Finset.univ \ Finset.univ.biUnion A).card ≤
        ((stSt S σ Mk).G.molecule.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card := by
      have hsub : Finset.univ \ Finset.univ.biUnion A ⊆
          ((stSt S σ Mk).G.molecule.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).image ob := by
        intro v hv
        have hv2 : v ∉ Finset.univ.biUnion A := (Finset.mem_sdiff.1 hv).2
        have hr : ∃ c, ob c = v := by
          rw [(stSt S σ Mk).M.ob_range]
          by_cases hu : ∃ u ∈ unitBlocks S σ Mk, v ∈ u.atoms
          · obtain ⟨u, hu, hvu⟩ := hu
            right
            rw [stSt_cls_memMk (Mk := Mk) hM σ hu hvu]
            by_contra hne
            obtain ⟨j, hj⟩ := List.mem_iff_get.1 hu
            apply hv2
            rw [Finset.mem_biUnion]
            refine ⟨Sum.inr j, Finset.mem_univ _, ?_⟩
            show v ∈ ((unitBlocks S σ Mk).get j).atoms.erase ((unitBlocks S σ Mk).get j).upper
            rw [hj]
            exact Finset.mem_erase.2 ⟨fun h => hne (by rw [h]), hvu⟩
          · left
            exact stSt_cls_noneMk (Mk := Mk) hM σ (by push_neg at hu; exact hu)
        obtain ⟨c, rfl⟩ := hr
        refine Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => ?_⟩, rfl⟩
        apply hv2
        rw [Finset.mem_biUnion]
        exact ⟨Sum.inl i, Finset.mem_univ _, Finset.mem_image_of_mem _ hi⟩
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    have hn_le : Fintype.card (GBranch (stSt S σ Mk).G.tree) ≤ Fintype.card (GBranch S.tree) :=
      Fintype.card_le_of_injective ob hob_inj
    have hm : ∑ i, F.len i ≤ Fintype.card (GBranch S.tree) :=
      (sum_len_le F hFd).trans hn_le
    have hUc : ∑ j : Fin (unitBlocks S σ Mk).length, ((unitBlocks S σ Mk).get j).atoms.card ≤
        Fintype.card (GBranch S.tree) := by
      have hpair := List.pairwise_iff_get.mp (unitBlocks_pairwiseMk hM σ Mk)
      have h1 := (Finset.card_biUnion (s := (Finset.univ : Finset (Fin (unitBlocks S σ Mk).length)))
        (t := fun j => ((unitBlocks S σ Mk).get j).atoms) (fun i _ j _ hij => by
          rcases lt_or_gt_of_ne hij with h | h
          · exact hpair i j h
          · exact (hpair j i h).symm)).symm
      rw [h1, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    have hrho := ladderFamOf_r (stSt S σ Mk).G
    have hK2 : 2 ≤ max CL Cu := le_max_of_le_right hCu
    have key := weight_numerics (max CL Cu) CL Cu hK2 hCL (le_max_left _ _) hCu (le_max_right _ _) p
      ((stSt S σ Mk).G.molecule.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card
      (Finset.univ \ Finset.univ.biUnion A).card hout F.len γ
      (fun j : Fin (unitBlocks S σ Mk).length => ((unitBlocks S σ Mk).get j).atoms.card)
      (fun j : Fin (unitBlocks S σ Mk).length => (((Tss j).filter (fun t => ¬ GoodIng S hS p 𝓖 gfix t)).map
        (fun t => gfix t.1 + 3)).sum) (Fintype.card (GBranch S.tree)) hm hUc
    rw [Fintype.prod_sum_type] at hmain
    rw [Fintype.card_fin] at key
    rw [← hrho]
    exact hmain.trans key
  · -- no atoms: at most one layering, no bonds
    have hemp : IsEmpty (GBranch S.tree) := not_nonempty_iff.1 hne
    have hbe : ∀ f : GBranch S.tree → ℕ, bondExp S.molecule S.molecule.atoms f = 0 := by
      intro f
      unfold bondExp bondsIn
      refine Finset.sum_eq_zero fun x hx => ?_
      exact (hemp.false (S.molecule.atom x)).elim
    have hsub : Subsingleton (GBranch S.tree → ℕ) := inferInstance
    have hc : 𝓖.card ≤ 1 := Finset.card_le_one.2 fun a _ b _ => Subsingleton.elim a b
    have hK1 : (1 : ℝ) ≤ max CL Cu := by
      have := le_max_right CL Cu
      linarith
    simp only [hbe, pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ((𝓖.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hc
    refine this.trans ?_
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) (one_le_pow₀ (one_le_pow₀ hK1))

open Classical in
/-- **The weight sum over a class of layerings (B2).**  The ingredient lists `Tss` depend only on `(S, σ)`. -/
theorem weight_sum_le : ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ {w : ℕ} (S : Garden w) (hS : S.IsPlain) (σ : Prescription S),
    ∃ Tss : Fin (unitBlocks S σ).length → List (Trip S),
      (∀ j, ∃ n, ∀ t ∈ Tss j, ChainIngredient S.molecule ((unitBlocks S σ).get j).atoms
          ((unitBlocks S σ).get j).upper ((unitBlocks S σ).get j).lower n t.1 t.2.1 t.2.2 ∧
          Mole.CLParentPattern S t.1 t.2.1 t.2.2) ∧
      (∀ j, ((Tss j).map (fun t => t.1.erase t.2.1)).Pairwise Disjoint) ∧
      ∀ (p : ℕ) (𝓖 : Finset (GBranch S.tree → ℕ)) (h𝓖 : ∀ f ∈ 𝓖, LFTwist.IsBranchPrelayering S f ∧ ∀ x, f x ≤ p)
        (γ : {T // T ∈ (stSt S σ).G.molecule.maximalLadders} → ℕ)
        (hγ : ∀ f ∈ 𝓖, ∀ i, incoherencyIndex (f ∘ (stSt S σ).M.ob)
          (ladderGroups ((ladderDataOf (stSt S σ).G).upper i) ((ladderDataOf (stSt S σ).G).lower i)) = γ i)
        (gfix : Finset (GBranch S.tree) → ℕ)
        (hgfix : ∀ f ∈ 𝓖, ∀ j, ∀ t ∈ Tss j, vineIncoh S f t.1 = gfix t.1),
      ∑ f ∈ 𝓖, (2 : ℝ) ^ (bondExp S.molecule S.molecule.atoms f) ≤
        K0 ^ (4 * Fintype.card (GBranch S.tree)) * (K0 ^ (p + 1)) ^
          (8 * ((stSt S σ).G.molecule.rho + (unitBlocks S σ).length) + ∑ i, γ i +
            ∑ j, (((Tss j).filter (fun t => ¬ GoodIng S hS p 𝓖 gfix t)).map (fun t => gfix t.1 + 3)).sum) :=
  let ⟨K0, hK0, h⟩ := weight_sum_leMk
  ⟨K0, hK0, fun S hS σ => h S hS σ ∅⟩

end WaveTurbulence.ClassCount
