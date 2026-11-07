/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4Const
public import WaveTurbulence.Foundations.VineEst.MexpDraft.RegCancelB2

/-!
# Prop 6.3, realness of the paired sum for equal parent layers `q = q'`

For `q = q'` the source approximations are the single-layer B2 terms (`SourceApp.couple_same_layer`,
`SourceApp.tree_same_layer`). Each well-formed code has exactly one coherent carrier at `(p, q, q)`: the constant
layering of its decoded garden (`P4Decode`, `P4Const`). The fixed top-branch count is therefore constant on the
carrier (`topBranchCount_const`). So the carrier sum is J7's code sum (`finsum_codes_eq`), and J7 `regcancel`
applies:

* `carrier_const_iff`, **`carrier_sum_eq`**: the carrier sum as a sum over codes;
* `finsum_codes_eq`: a code sum with dominance-supported summands is the antidiagonal sum over `domCodes`,
  `domTrees`;
* **`reality_same`**: `(∑ᶠ … CoherentPairCarrier p q q n b …).im = 0` on `timeBoxGt q q`, for every real input
  family `F`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset ComplexConjugate
open scoped Classical

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

theorem topBranchCount_const {w : ℕ} (G : Garden w) (q p : ℕ) :
    topBranchCount (constLayered G q) p = if q = p then G.order else 0 := by
  show ((univ : Finset (GBranch G.tree)).filter fun _ => q = p).card = _
  split_ifs with h
  · rw [Finset.filter_true_of_mem (fun b _ => h), Finset.card_univ, card_gbranch]
    rfl
  · rw [Finset.filter_false_of_mem (fun b _ => h), Finset.card_empty]

/-- The top-branch condition on the carrier at `(p, q, q)`: it does not depend on the codes. -/
def BOk (p q n : ℕ) : Option ℕ → Prop
  | none => True
  | some m => (if q = p then 2 * n else 0) = m

section Carrier

variable {p q : ℕ} (hqp : q ≤ p) (n : ℕ) (b : Option ℕ)

include hqp in
theorem carrier_const_iff (Q : RegCpl) (X : RegChain) :
    CoherentPairCarrier p q q n b Q X (constLayered (decodedCouple Q) q) (constLayered (decodedTree X 1) q) ↔
      Q.wf = true ∧ X.wf = true ∧ Q.size + X.size = 2 * n ∧ BOk p q n b := by
  constructor
  · rintro ⟨h1, h2, -, h4, h5⟩
    have h4' : (decodedCouple Q).order + (decodedTree X 1).order = 2 * n := h4
    rw [decodedCouple_order, decodedTree_order] at h4'
    refine ⟨h1.1, h2.1, h4', ?_⟩
    cases b with
    | none => trivial
    | some m =>
      have h5' : topBranchCount (constLayered (decodedCouple Q) q) p +
          topBranchCount (constLayered (decodedTree X 1) q) p = m := h5
      rw [topBranchCount_const, topBranchCount_const, decodedCouple_order, decodedTree_order] at h5'
      show (if q = p then 2 * n else 0) = m
      split_ifs at h5' ⊢ <;> omega
  · rintro ⟨h1, h2, h4, h5⟩
    refine ⟨coherentCouple_exists Q hqp h1, coherentTree_exists X hqp h2, rfl, ?_, ?_⟩
    · show (decodedCouple Q).order + (decodedTree X 1).order = 2 * n
      rw [decodedCouple_order, decodedTree_order]
      exact h4
    · cases b with
      | none => trivial
      | some m =>
        show topBranchCount (constLayered (decodedCouple Q) q) p +
          topBranchCount (constLayered (decodedTree X 1) q) p = m
        rw [topBranchCount_const, topBranchCount_const, decodedCouple_order, decodedTree_order]
        have h5' : (if q = p then 2 * n else 0) = m := h5
        split_ifs at h5' ⊢ <;> omega

include hqp in
/-- **The carrier sum at `(p, q, q)` is a sum over codes.** -/
theorem carrier_sum_eq (f : RegCpl → RegChain → LayeredGarden 2 → LayeredGarden 1 → ℂ) :
    (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
      (_ : CoherentPairCarrier p q q n b Q X LQ LX), f Q X LQ LX) =
    ∑ᶠ (Q : RegCpl) (X : RegChain),
      if Q.wf = true ∧ X.wf = true ∧ Q.size + X.size = 2 * n ∧ BOk p q n b then
        f Q X (constLayered (decodedCouple Q) q) (constLayered (decodedTree X 1) q) else 0 := by
  refine finsum_congr fun Q => finsum_congr fun X => ?_
  have hX : ∀ LX : LayeredGarden 1, LX ≠ constLayered (decodedTree X 1) q →
      (∑ᶠ (_ : CoherentPairCarrier p q q n b Q X (constLayered (decodedCouple Q) q) LX),
        f Q X (constLayered (decodedCouple Q) q) LX) = 0 := by
    intro LX hLX
    rw [finsum_eq_if, ite_eq_right]
    intro hC
    exact hLX (coherentTree_unique hC.2.1 (coherentTree_exists X hqp hC.2.1.1) hC.2.2.1)
  have hQ : ∀ LQ : LayeredGarden 2, LQ ≠ constLayered (decodedCouple Q) q →
      (∑ᶠ (LX : LayeredGarden 1) (_ : CoherentPairCarrier p q q n b Q X LQ LX), f Q X LQ LX) = 0 := by
    intro LQ hLQ
    refine finsum_eq_zero_of_forall_eq_zero fun LX => ?_
    rw [finsum_eq_if, ite_eq_right]
    intro hC
    exact hLQ (coherentCouple_unique hC.1 (coherentCouple_exists Q hqp hC.1.1))
  rw [finsum_eq_single _ _ hQ, finsum_eq_single _ _ hX, finsum_eq_if]
  exact if_congr (carrier_const_iff hqp n b Q X) rfl rfl

end Carrier

/-! ### From code sums to J7's antidiagonal sum -/

theorem half_size_code (Q : RegCpl) : Q.size = 2 * (Q.size / 2) := by
  obtain ⟨m, hm⟩ := code_size_even Q
  omega

theorem half_size_chain (X : RegChain) : X.size = 2 * (X.size / 2) := by
  obtain ⟨m, hm⟩ := chain_size_even X
  omega

section Codes

variable (n : ℕ) (G : RegCpl → RegChain → ℂ)
  (hG : ∀ Q X, (Q.dominant = false ∨ X.dominant = false) → G Q X = 0)

/-- The codes of the antidiagonal. -/
noncomputable def codesN : Finset RegCpl := (antidiagonal n).biUnion fun ab => Mexp.domCodes ab.1

/-- The chains of the antidiagonal. -/
noncomputable def chainsN : Finset RegChain := (antidiagonal n).biUnion fun ab => Mexp.domTrees ab.2

theorem mem_codesN {Q : RegCpl} (hwf : Q.wf = true) (hd : Q.dominant = true) (hs : Q.size ≤ 2 * n) :
    Q ∈ codesN n := by
  have e := half_size_code Q
  refine Finset.mem_biUnion.2 ⟨(Q.size / 2, n - Q.size / 2), Finset.HasAntidiagonal.mem_antidiagonal.2 (show Q.size / 2 + (n - Q.size / 2) = n by omega), ?_⟩
  exact Mexp.mem_domCodes.2 ⟨hwf, hd, e⟩

theorem mem_chainsN {X : RegChain} (hwf : X.wf = true) (hd : X.dominant = true) (hs : X.size ≤ 2 * n) :
    X ∈ chainsN n := by
  have e := half_size_chain X
  refine Finset.mem_biUnion.2 ⟨(n - X.size / 2, X.size / 2), Finset.HasAntidiagonal.mem_antidiagonal.2 (show n - X.size / 2 + X.size / 2 = n by omega), ?_⟩
  exact Mexp.mem_domTrees.2 ⟨hwf, hd, e⟩

/-- The summand of the code sum. -/
noncomputable def codeTerm (Q : RegCpl) (X : RegChain) : ℂ :=
  if Q.wf = true ∧ X.wf = true ∧ Q.size + X.size = 2 * n then G Q X else 0

include hG in
theorem codeTerm_ne {Q : RegCpl} {X : RegChain} (h : codeTerm n G Q X ≠ 0) :
    Q ∈ codesN n ∧ X ∈ chainsN n ∧ Q.wf = true ∧ X.wf = true ∧ Q.size + X.size = 2 * n := by
  unfold codeTerm at h
  split_ifs at h with hc
  · obtain ⟨h1, h2, h3⟩ := hc
    have hdQ : Q.dominant = true := by
      by_contra hn
      exact h (hG Q X (Or.inl (by simpa using hn)))
    have hdX : X.dominant = true := by
      by_contra hn
      exact h (hG Q X (Or.inr (by simpa using hn)))
    exact ⟨mem_codesN n h1 hdQ (by omega), mem_chainsN n h2 hdX (by omega), h1, h2, h3⟩
  · exact absurd rfl h

include hG in
/-- **A dominance-supported code sum is J7's antidiagonal sum.** -/
theorem finsum_codes_eq :
    (∑ᶠ (Q : RegCpl) (X : RegChain), codeTerm n G Q X) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ Q ∈ Mexp.domCodes ab.1, ∑ X ∈ Mexp.domTrees ab.2, G Q X := by
  have hX : ∀ Q, (∑ᶠ X, codeTerm n G Q X) = ∑ X ∈ chainsN n, codeTerm n G Q X := fun Q =>
    finsum_eq_sum_of_support_subset _ fun X hX => (codeTerm_ne n G hG hX).2.1
  rw [finsum_congr hX, finsum_eq_sum_of_support_subset _ (s := codesN n) fun Q hQ => by
    obtain ⟨X, -, hX⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
    exact (codeTerm_ne n G hG hX).1]
  have hin : ∀ ab ∈ antidiagonal n, ∀ Q ∈ Mexp.domCodes ab.1,
      ∑ X ∈ Mexp.domTrees ab.2, G Q X = ∑ X ∈ chainsN n, codeTerm n G Q X := by
    intro ab hab Q hQ
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    obtain ⟨hQw, -, hQs⟩ := Mexp.mem_domCodes.1 hQ
    rw [← Finset.sum_subset (s₂ := chainsN n) (f := codeTerm n G Q)
      (fun X hX => Finset.mem_biUnion.2 ⟨ab, hab, hX⟩) ?_]
    · refine Finset.sum_congr rfl fun X hX => ?_
      obtain ⟨hXw, -, hXs⟩ := Mexp.mem_domTrees.1 hX
      unfold codeTerm
      exact (ite_eq_left ⟨hQw, hXw, by omega⟩).symm
    · intro X _ hX
      by_contra hne
      have h := codeTerm_ne n G hG hne
      obtain ⟨ab', -, h''⟩ := Finset.mem_biUnion.1 h.2.1
      obtain ⟨-, hXd, -⟩ := Mexp.mem_domTrees.1 h''
      exact hX (Mexp.mem_domTrees.2 ⟨h.2.2.2.1, hXd, by omega⟩)
  rw [Finset.sum_congr rfl fun ab hab => Finset.sum_congr rfl (hin ab hab), codesN, Finset.sum_biUnion]
  intro ab hab ab' hab' hne
  refine Finset.disjoint_left.2 fun Q h1 h2 => hne ?_
  have e1 := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  have e2 := Finset.HasAntidiagonal.mem_antidiagonal.1 hab'
  have s1 := (Mexp.mem_domCodes.1 h1).2.2
  have s2 := (Mexp.mem_domCodes.1 h2).2.2
  exact Prod.ext (by omega) (by omega)

end Codes

/-- **Prop 6.3, realness for `q = q'`.** -/
theorem reality_same {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {p q : ℕ} (hqp : q ≤ p) (n : ℕ) (b : Option ℕ)
    (ts : Fin 2 → ℝ) (hts : ts ∈ timeBoxGt q q) (k : Mom d) :
    (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
      (_ : CoherentPairCarrier p q q n b Q X LQ LX),
      SourceApp.couple δ F LQ Q q q (ts 0) (ts 1) k *
        star (SourceApp.tree δ F LX X q q (ts 0) (ts 1) k)).im = 0 := by
  rw [carrier_sum_eq hqp n b]
  by_cases hb : BOk p q n b
  · have e : ∀ Q X, (if Q.wf = true ∧ X.wf = true ∧ Q.size + X.size = 2 * n ∧ BOk p q n b then
        SourceApp.couple δ F (constLayered (decodedCouple Q) q) Q q q (ts 0) (ts 1) k *
          star (SourceApp.tree δ F (constLayered (decodedTree X 1) q) X q q (ts 0) (ts 1) k) else 0) =
        codeTerm n (fun Q X => Q.app δ q (F q) (ts 0) (ts 1) k * conj (X.app δ q (F q) 1 (ts 0) (ts 1) k)) Q X := by
      intro Q X
      rw [SourceApp.couple_same_layer, SourceApp.tree_same_layer]
      exact if_congr (by simp only [hb, and_true]) rfl rfl
    rw [finsum_congr fun Q => finsum_congr fun X => e Q X, finsum_codes_eq]
    · exact Mexp.regcancel δ q (F q) n hts.1.2.1 hts.2.le k
    · rintro Q X (h | h)
      · rw [RegCpl.app_of_not_dominant δ q (F q) Q h, zero_mul]
      · have h0 : X.app δ q (F q) 1 (ts 0) (ts 1) k = 0 := by
          unfold RegChain.app
          rw [h]
          rfl
        rw [h0, map_zero, mul_zero]
  · have e : ∀ Q X, (if Q.wf = true ∧ X.wf = true ∧ Q.size + X.size = 2 * n ∧ BOk p q n b then
        SourceApp.couple δ F (constLayered (decodedCouple Q) q) Q q q (ts 0) (ts 1) k *
          star (SourceApp.tree δ F (constLayered (decodedTree X 1) q) X q q (ts 0) (ts 1) k) else 0) = 0 :=
      fun Q X => ite_eq_right fun h => hb h.2.2.2
    rw [finsum_congr fun Q => finsum_congr fun X => e Q X]
    simp

end WaveTurbulence.PL234
