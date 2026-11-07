/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Slots2
public import WaveTurbulence.Foundations.LayerCnt.BondExp
import Mathlib.Tactic

/-!
# CLASSCOUNT: the slot distances are the bond exponent of the skeleton molecule

`Σ_s slotDist` (the `2^{|q-q'|}` factors of `layerreg2`) is at most `bondExp M(S) f` plus `p` for each root
(trees at root branches and couples with a root leaf have parent layer `p` and no bond).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree LayerCnt

variable {w : ℕ}

/-- The bond exponent of a garden molecule, read dart by dart. -/
theorem bondExp_garden (G : Garden w) (f : GBranch G.tree → ℕ) :
    bondExp G.molecule Finset.univ f =
      (∑ c : {c : GBranch G.tree // c.1.2 ≠ []},
        dst (f (GNode.parent c.1.toNode c.2)) (f c.1)) +
      ∑ ℓ : {ℓ : GLeaf G.tree // G.mark ℓ = none ∧ ℓ.1.2 ≠ [] ∧ (G.pair ℓ).1.2 ≠ []},
        if G.molecule.out (Sum.inr ℓ) = true then
          dst (f (G.molecule.atom (Sum.inr ℓ))) (f (G.molecule.atom (G.molecule.mate (Sum.inr ℓ)))) else 0 := by
  classical
  unfold bondExp bondsIn
  simp only [Molecule.bonds, Finset.filter_filter, Finset.mem_univ, and_true, true_and]
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fintype.sum_bool]
    simp only [Garden.molecule]
    by_cases h : G.sign c.1.toNode = 1
    · simp [h, dst_comm]
    · simp [h, dst_comm]

variable {S : Garden w}

theorem pv_le (p : ℕ) (f : GBranch S.tree → ℕ) (hp : ∀ b, f b ≤ p) (n : GNode S.tree) : pv p f n ≤ p := by
  unfold pv; split_ifs <;> simp [hp]

/-- The tree slots: `Σ_b (q - q')` is the PC bond exponent plus `p` per root branch. -/
theorem tree_dist_le (p : ℕ) (f : GBranch S.tree → ℕ) (hp : ∀ b, f b ≤ p) :
    ∑ b : GBranch S.tree, (pv p f b.toNode - f b) ≤
      (∑ c : {c : GBranch S.tree // c.1.2 ≠ []}, dst (f (GNode.parent c.1.toNode c.2)) (f c.1)) +
        p * (Finset.univ.filter (fun b : GBranch S.tree => b.1.2 = [])).card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : GBranch S.tree => b.1.2 = [])]
  rw [add_comm]
  refine add_le_add ?_ ?_
  · rw [Finset.sum_subtype (Finset.univ.filter (fun b : GBranch S.tree => ¬ b.1.2 = []))
      (p := fun b : GBranch S.tree => b.1.2 ≠ []) (by simp)]
    refine Finset.sum_le_sum fun c _ => ?_
    have h : pv p f c.1.toNode = f (GNode.parent c.1.toNode c.2) := by
      unfold pv; exact dif_neg c.2
    rw [h]
    unfold dst
    omega
  · calc ∑ b ∈ Finset.univ.filter (fun b : GBranch S.tree => b.1.2 = []), (pv p f b.toNode - f b)
        ≤ ∑ b ∈ Finset.univ.filter (fun b : GBranch S.tree => b.1.2 = []), p :=
          Finset.sum_le_sum fun b _ => (Nat.sub_le _ _).trans (pv_le p f hp _)
      _ = _ := by simp [mul_comm]

theorem sourcePair_facts (hS : S.IsPlain) (pr : SourcePair S) :
    ∃ ℓ : GLeaf S.tree, nodeSign S.sig ℓ.1 = 1 ∧ pr.firstLeaf hS = ℓ ∧ pr.secondLeaf hS = S.pair ℓ := by
  obtain ⟨ℓ, hℓ, he⟩ := Finset.mem_image.1 pr.2
  refine ⟨ℓ, (Finset.mem_filter.1 hℓ).2, Subtype.ext ?_, Subtype.ext ?_⟩
  · exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.snd he).symm

/-- A couple with exactly one root leaf. -/
def exactOne (hS : S.IsPlain) (pr : SourcePair S) : Prop :=
  ((pr.firstLeaf hS).1.2 = [] ∧ ¬ (pr.secondLeaf hS).1.2 = []) ∨
    (¬ (pr.firstLeaf hS).1.2 = [] ∧ (pr.secondLeaf hS).1.2 = [])

open Classical in
/-- The couple slots: `Σ_pr |q - q'|` is the LP bond exponent plus `p` per couple with a root leaf. -/
theorem couple_dist_le (hS : S.IsPlain) (p : ℕ) (f : GBranch S.tree → ℕ) (hp : ∀ b, f b ≤ p) :
    ∑ pr : SourcePair S, ldist (pv p f (pr.firstLeaf hS).toNode) (pv p f (pr.secondLeaf hS).toNode) ≤
      (∑ ℓ : {ℓ : GLeaf S.tree // S.mark ℓ = none ∧ ℓ.1.2 ≠ [] ∧ (S.pair ℓ).1.2 ≠ []},
        if S.molecule.out (Sum.inr ℓ) = true then
          dst (f (S.molecule.atom (Sum.inr ℓ))) (f (S.molecule.atom (S.molecule.mate (Sum.inr ℓ)))) else 0) +
      p * (Finset.univ.filter (fun pr : SourcePair S => exactOne hS pr)).card := by
  classical
  set R : SourcePair S → Prop := fun pr => (pr.firstLeaf hS).1.2 = [] ∨ (pr.secondLeaf hS).1.2 = [] with hR
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ R, add_comm]
  refine add_le_add ?_ ?_
  · -- both leaves non-root: injection into the LP leaves
    let φ : {pr : SourcePair S // ¬ R pr} →
        {ℓ : GLeaf S.tree // S.mark ℓ = none ∧ ℓ.1.2 ≠ [] ∧ (S.pair ℓ).1.2 ≠ []} := fun pr =>
      ⟨pr.1.secondLeaf hS, hS _, fun h => pr.2 (Or.inr h), by
        obtain ⟨ℓ, -, h1, h2⟩ := sourcePair_facts hS pr.1
        rw [h2, S.pair_pair, ← h1]
        exact fun h => pr.2 (Or.inl h)⟩
    have hφ : Function.Injective φ := by
      intro a b hab
      have h2 : a.1.secondLeaf hS = b.1.secondLeaf hS := congrArg Subtype.val hab
      obtain ⟨ℓa, -, ha1, ha2⟩ := sourcePair_facts hS a.1
      obtain ⟨ℓb, -, hb1, hb2⟩ := sourcePair_facts hS b.1
      rw [ha2, hb2] at h2
      have : ℓa = ℓb := by
        have := congrArg S.pair h2
        rwa [S.pair_pair, S.pair_pair] at this
      subst this
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (congrArg Subtype.val (ha1.trans hb1.symm)) (congrArg Subtype.val (ha2.trans hb2.symm))
    rw [Finset.sum_subtype (Finset.univ.filter (fun pr : SourcePair S => ¬ R pr))
      (p := fun pr => ¬ R pr) (by simp)]
    calc ∑ pr : {pr : SourcePair S // ¬ R pr},
          ldist (pv p f (pr.1.firstLeaf hS).toNode) (pv p f (pr.1.secondLeaf hS).toNode)
        = ∑ y ∈ Finset.univ.image φ, (if S.molecule.out (Sum.inr y) = true then
          dst (f (S.molecule.atom (Sum.inr y))) (f (S.molecule.atom (S.molecule.mate (Sum.inr y)))) else 0) := by
          rw [Finset.sum_image (fun a _ b _ h => hφ h)]
          refine Finset.sum_congr rfl fun pr _ => ?_
          obtain ⟨ℓ, hs, h1, h2⟩ := sourcePair_facts hS pr.1
          have hout : S.molecule.out (Sum.inr (φ pr)) = true := by
            change decide (S.sign (pr.1.secondLeaf hS).toNode ≠ 1) = true
            rw [h2]
            have hn := S.pair_sign ℓ (Comb.pair_ne_of_plain hS ℓ)
            simp only [decide_eq_true_eq]
            change nodeSign S.sig (S.pair ℓ).1 ≠ 1
            rw [hn, hs]; decide
          rw [if_pos hout]
          have hr1 : ¬ (pr.1.firstLeaf hS).1.2 = [] := fun h => pr.2 (Or.inl h)
          have hr2 : ¬ (pr.1.secondLeaf hS).1.2 = [] := fun h => pr.2 (Or.inr h)
          have e1 : pv p f (pr.1.firstLeaf hS).toNode = f (GNode.parent (pr.1.firstLeaf hS).toNode hr1) :=
            dif_neg hr1
          have e2 : pv p f (pr.1.secondLeaf hS).toNode = f (GNode.parent (pr.1.secondLeaf hS).toNode hr2) :=
            dif_neg hr2
          rw [e1, e2, dst_comm]
          unfold ldist dst
          have ea : S.molecule.atom (Sum.inr (φ pr)) = GNode.parent (pr.1.secondLeaf hS).toNode hr2 := rfl
          have eb : S.molecule.atom (S.molecule.mate (Sum.inr (φ pr))) =
              GNode.parent (S.pair (pr.1.secondLeaf hS)).toNode (by
                rw [h2, S.pair_pair, ← h1]; exact hr1) := rfl
          rw [ea, eb]
          have hP : S.pair (pr.1.secondLeaf hS) = pr.1.firstLeaf hS := by
            rw [h2, S.pair_pair, h1]
          have hpar : ∀ (ℓ ℓ' : GLeaf S.tree) (h : ℓ = ℓ') (hr : ℓ.toNode.1.2 ≠ []) (hr' : ℓ'.toNode.1.2 ≠ []),
              GNode.parent ℓ.toNode hr = GNode.parent ℓ'.toNode hr' := by
            intro ℓ ℓ' h; subst h; intros; rfl
          rw [hpar _ _ hP _ hr1]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by positivity)
  · calc ∑ pr ∈ Finset.univ.filter R, ldist (pv p f (pr.firstLeaf hS).toNode) (pv p f (pr.secondLeaf hS).toNode)
        ≤ ∑ pr ∈ Finset.univ.filter R, (if exactOne hS pr then p else 0) := by
          refine Finset.sum_le_sum fun pr hpr => ?_
          have h1 := pv_le p f hp (pr.firstLeaf hS).toNode
          have h2 := pv_le p f hp (pr.secondLeaf hS).toNode
          have hR' := (Finset.mem_filter.1 hpr).2
          by_cases hb : (pr.firstLeaf hS).1.2 = [] ∧ (pr.secondLeaf hS).1.2 = []
          · have e1 : pv p f (pr.firstLeaf hS).toNode = p := dif_pos hb.1
            have e2 : pv p f (pr.secondLeaf hS).toNode = p := dif_pos hb.2
            rw [e1, e2]; unfold ldist; omega
          · have hx : exactOne hS pr := by
              unfold exactOne
              rcases hR' with h | h
              · by_cases h' : (pr.secondLeaf hS).1.2 = []
                · exact absurd ⟨h, h'⟩ hb
                · exact Or.inl ⟨h, h'⟩
              · by_cases h' : (pr.firstLeaf hS).1.2 = []
                · exact absurd ⟨h', h⟩ hb
                · exact Or.inr ⟨h', h⟩
            rw [if_pos hx]
            unfold ldist; omega
      _ ≤ ∑ pr, (if exactOne hS pr then p else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = _ := by rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]

open Classical in
/-- The root things of the skeleton: root branches and couples with exactly one root leaf (the slots whose parent
layer is `p`). -/
noncomputable def rootThings (hS : S.IsPlain) : ℕ :=
  (Finset.univ.filter (fun b : GBranch S.tree => b.1.2 = [])).card +
    (Finset.univ.filter (fun pr : SourcePair S => exactOne hS pr)).card

/-- **The slot distances are the bond exponent of `M(S)`, plus `p` per root** (`≤ p w`). -/
theorem slotDist_sum_le (hS : S.IsPlain) (p : ℕ) (f : GBranch S.tree → ℕ) (hp : ∀ b, f b ≤ p) :
    ∑ s, slotDist hS p f s ≤ bondExp S.molecule Finset.univ f + p * rootThings hS := by
  classical
  rw [Fintype.sum_sum_type, bondExp_garden]
  have h1 := couple_dist_le hS p f hp
  have h2 := tree_dist_le (S := S) p f hp
  have h4 : p * rootThings hS = p * (Finset.univ.filter (fun b : GBranch S.tree => b.1.2 = [])).card +
      p * (Finset.univ.filter (fun pr : SourcePair S => exactOne hS pr)).card := by
    unfold rootThings; ring
  have e1 : ∑ pr : SourcePair S, slotDist hS p f (.inl pr) =
      ∑ pr : SourcePair S, ldist (pv p f (pr.firstLeaf hS).toNode) (pv p f (pr.secondLeaf hS).toNode) := rfl
  have e2 : ∑ b : GBranch S.tree, slotDist hS p f (.inr b) = ∑ b : GBranch S.tree, (pv p f b.toNode - f b) := rfl
  rw [e1, e2]
  omega

/-- **B1 class bound.**  Layered gardens decoded by `D` with common slot incoherencies `gs`:
`#A ≤ (2^{9p})^{Σ gs} 2^{|D|} 2^{p w} Σ_f 2^{bondExp M(S) f}` over the core layerings `f` of `A`. -/
theorem card_class_le_bond (D : ReconstructionData S) (hS : S.IsPlain) (p : ℕ) (gs : ReplacementSlot S → ℕ)
    (A : Finset (LayeredGarden w))
    (hA : ∀ LG ∈ A, LG.CanonCriterion p ∧ LG.garden.IsPlain ∧ D.Decodes hS LG.garden ∧
      ∀ s, slotInc D hS LG s = gs s) :
    (A.card : ℝ) ≤ (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size * 2 ^ (p * rootThings hS) *
      ∑ f ∈ A.image (coreOf D hS), (2 : ℝ) ^ bondExp S.molecule Finset.univ f := by
  classical
  refine (card_class_le D hS p gs A hA).trans ?_
  have : ∀ f ∈ A.image (coreOf D hS), (2 : ℝ) ^ (∑ s, slotDist hS p f s) ≤
      2 ^ (p * rootThings hS) * (2 : ℝ) ^ bondExp S.molecule Finset.univ f := by
    intro f hf
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨hc, hpl, hd, -⟩ := hA LG hLG
    have hle : ∀ b, coreOf D hS LG b ≤ p := by
      intro b; rw [coreOf_eq D hS hd]; exact hc.1 _
    have := slotDist_sum_le hS p (coreOf D hS LG) hle
    calc (2 : ℝ) ^ (∑ s, slotDist hS p (coreOf D hS LG) s) ≤ 2 ^ (bondExp S.molecule Finset.univ (coreOf D hS LG) + p * rootThings hS) :=
          pow_le_pow_right₀ (by norm_num) this
      _ = _ := by rw [pow_add]; ring
  calc (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size * ∑ f ∈ A.image (coreOf D hS), (2 : ℝ) ^ (∑ s, slotDist hS p f s)
      ≤ (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size * ∑ f ∈ A.image (coreOf D hS),
          (2 ^ (p * rootThings hS) * (2 : ℝ) ^ bondExp S.molecule Finset.univ f) := by
        gcongr with f hf
        exact this f hf
    _ = _ := by rw [← Finset.mul_sum]; ring

end WaveTurbulence.ClassCount
