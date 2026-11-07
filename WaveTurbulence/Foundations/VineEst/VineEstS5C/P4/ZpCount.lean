/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.CohCountTree
public import WaveTurbulence.Foundations.VineEst.ZpSurj.Export

/-! # P4 count bridge (3): the number of states of the twist class `Zp(A)` (TARGET L1919-L1922, Prop `layerreg2`)

Every state `G ∈ Zp(A)` is the output of an operation at `pstar` (ZP-SURJ `classify`) and is determined by its sign and its carrier-side
couple and tree `(ν, zpObjC, zpObjT)` (`zp_eq_of_sigStar`, the conjugation involutions).  By `ZpSurj.coherent` these are coherent, with
parents read off `G`: the couple at `(numR G, L₂)`, the tree at `(zpBranchQ G).1, L₂)`, and both numbers lie in `{q_r, q_b}` (`op_numbers`);
the total order is that of `A` (`ExcDatum.size`, `two_zpN`).  So with `N = zpN A pstar`:

  `#Zp(A) ≤ 16 (N + 1) (4·12⁹)^N · 4^p`     (**`card_zpFinset_le`**)

(TARGET: `C₂ C₀^{n(Q)+n(T)}`; here `C₀ = 4·12⁹` and the `C₂`-part is `16 (N+1) 4^p`, the `4^p` coming from `2^{|q - q'|}` twice,
finding F-COUNTGAIN / R54).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj
  WaveTurbulence.Stage1 WaveTurbulence.ConjCoh WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1

set_option linter.unusedSectionVars false

open Classical in
/-- The target of the class count: sign, coherent couple and coherent tree, with parents in `{qr, qb}` over `L₂` and total order `2N`. -/
noncomputable def zpTarget (p qr qb L2 N : ℕ) : Finset (ℤˣ × LayeredGarden 2 × LayeredGarden 1) :=
  (Finset.univ : Finset ℤˣ) ×ˢ ((Finset.range (N + 1)).biUnion fun m => ({qr, qb} : Finset ℕ).biUnion fun q₁ =>
    ({qr, qb} : Finset ℕ).biUnion fun q₂ => (Finset.univ : Finset ℤˣ).biUnion fun ζ =>
      (ncard_coherentCouples_le p q₁ L2 m).1.toFinset ×ˢ (ncard_coherentTrees_le p q₂ L2 ζ (N - m)).1.toFinset)

theorem card_biUnion_le_mul {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β) (n : ℕ)
    (h : ∀ a ∈ s, (t a).card ≤ n) : (s.biUnion t).card ≤ s.card * n :=
  Finset.card_biUnion_le.trans (by simpa using Finset.sum_le_card_nsmul s (fun a => (t a).card) n h)

theorem ldist_le {x y p : ℕ} (hx : x ≤ p) (hy : y ≤ p) : ldist x y ≤ p := by unfold ldist; omega

theorem card_pair_le (x y : ℕ) : ({x, y} : Finset ℕ).card ≤ 2 :=
  (Finset.card_insert_le _ _).trans (by simp)

theorem card_zpTarget_le (p qr qb L2 N : ℕ) (hr : qr ≤ p) (hb : qb ≤ p) (hL : L2 ≤ p) :
    (zpTarget p qr qb L2 N).card ≤ 16 * (N + 1) * ((4 * 12 ^ 9) ^ N * 4 ^ p) := by
  classical
  set X := (4 * 12 ^ 9) ^ N * 4 ^ p with hX
  have hterm : ∀ m ∈ Finset.range (N + 1), ∀ q₁ ∈ ({qr, qb} : Finset ℕ), ∀ q₂ ∈ ({qr, qb} : Finset ℕ), ∀ ζ : ℤˣ,
      ((ncard_coherentCouples_le p q₁ L2 m).1.toFinset ×ˢ (ncard_coherentTrees_le p q₂ L2 ζ (N - m)).1.toFinset).card ≤ X := by
    intro m hm q₁ hq₁ q₂ hq₂ ζ
    have hmN : m ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    obtain ⟨k, rfl⟩ : ∃ k, N = m + k := ⟨N - m, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have hq₁p : q₁ ≤ p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq₁; rcases hq₁ with rfl | rfl <;> assumption
    have hq₂p : q₂ ≤ p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq₂; rcases hq₂ with rfl | rfl <;> assumption
    rw [Finset.card_product, ← Set.ncard_eq_toFinset_card _ (ncard_coherentCouples_le p q₁ L2 m).1,
      ← Set.ncard_eq_toFinset_card _ (ncard_coherentTrees_le p q₂ L2 ζ k).1]
    have h1 := (ncard_coherentCouples_le p q₁ L2 m).2
    have h2 := (ncard_coherentTrees_le p q₂ L2 ζ k).2
    have e1 : ldist q₁ L2 ≤ p := ldist_le hq₁p hL
    have e2 : q₂ - L2 ≤ p := by omega
    calc _ ≤ ((12 ^ 9) ^ m * 2 ^ (2 * m + ldist q₁ L2)) * ((12 ^ 9) ^ k * 2 ^ (2 * k + (q₂ - L2))) :=
          Nat.mul_le_mul h1 h2
      _ ≤ ((12 ^ 9) ^ m * 2 ^ (2 * m + p)) * ((12 ^ 9) ^ k * 2 ^ (2 * k + p)) := by
          gcongr
      _ = X := by
          rw [hX, mul_pow (4 : ℕ) (12 ^ 9) (m + k), show (4 : ℕ) ^ (m + k) = 2 ^ (2 * (m + k)) by rw [pow_mul]; norm_num,
            show (4 : ℕ) ^ p = 2 ^ (2 * p) by rw [pow_mul]; norm_num]
          ring
  have hζ : ∀ m ∈ Finset.range (N + 1), ∀ q₁ ∈ ({qr, qb} : Finset ℕ), ∀ q₂ ∈ ({qr, qb} : Finset ℕ),
      ((Finset.univ : Finset ℤˣ).biUnion fun ζ =>
        (ncard_coherentCouples_le p q₁ L2 m).1.toFinset ×ˢ (ncard_coherentTrees_le p q₂ L2 ζ (N - m)).1.toFinset).card ≤
        2 * X := fun m hm q₁ hq₁ q₂ hq₂ =>
    (card_biUnion_le_mul _ _ X fun ζ _ => hterm m hm q₁ hq₁ q₂ hq₂ ζ).trans (le_of_eq (by rw [Finset.card_univ, Fintype.card_units_int]))
  have hq₂ : ∀ m ∈ Finset.range (N + 1), ∀ q₁ ∈ ({qr, qb} : Finset ℕ),
      (({qr, qb} : Finset ℕ).biUnion fun q₂ => (Finset.univ : Finset ℤˣ).biUnion fun ζ =>
        (ncard_coherentCouples_le p q₁ L2 m).1.toFinset ×ˢ (ncard_coherentTrees_le p q₂ L2 ζ (N - m)).1.toFinset).card ≤
        2 * (2 * X) := fun m hm q₁ hq₁ =>
    (card_biUnion_le_mul _ _ _ fun q₂ hq₂ => hζ m hm q₁ hq₁ q₂ hq₂).trans (Nat.mul_le_mul_right _ (card_pair_le _ _))
  have hq₁ : ∀ m ∈ Finset.range (N + 1),
      (({qr, qb} : Finset ℕ).biUnion fun q₁ => ({qr, qb} : Finset ℕ).biUnion fun q₂ => (Finset.univ : Finset ℤˣ).biUnion fun ζ =>
        (ncard_coherentCouples_le p q₁ L2 m).1.toFinset ×ˢ (ncard_coherentTrees_le p q₂ L2 ζ (N - m)).1.toFinset).card ≤
        2 * (2 * (2 * X)) := fun m hm =>
    (card_biUnion_le_mul _ _ _ fun q₁ hq₁ => hq₂ m hm q₁ hq₁).trans (Nat.mul_le_mul_right _ (card_pair_le _ _))
  have hm := card_biUnion_le_mul (Finset.range (N + 1)) _ _ hq₁
  rw [Finset.card_range] at hm
  unfold zpTarget
  rw [Finset.card_product]
  calc _ ≤ 2 * ((N + 1) * (2 * (2 * (2 * X)))) := Nat.mul_le_mul (le_of_eq (by rw [Finset.card_univ, Fintype.card_units_int])) hm
    _ = 16 * (N + 1) * X := by ring

section Zp
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]
variable (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

/-- The carrier-side triple of a state. -/
noncomputable def zpTriple (G : ST w ι pstar J) : ℤˣ × LayeredGarden 2 × LayeredGarden 1 :=
  (nuOf G.1 pstar, zpObjC G.1 pstar, zpObjT G.1 pstar)

include hcan hel htc hcc in
/-- **Every state of `Zp(A)` lands in the target.** -/
theorem zpTriple_mem (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    zpTriple G ∈ zpTarget p (numR A pstar) (zpBranchQ A pstar).1 (zpBranchQ A pstar).2 (zpN A pstar) := by
  classical
  obtain ⟨hC, hT⟩ := (zpSurj_of_state A sp0 hA hcan hel htc hcc).coherent G hG
  obtain ⟨ε, con, he⟩ := classify A hcan hel htc hcc hA ((mem_zpFinset hA).1 hG).batch
  obtain ⟨hL2, hnum⟩ := op_numbers A hcan hel htc hcc con
  have hQQ := zpQQ_eq G.1 pstar
  -- sizes
  have hd := zpData_op A hcan hel htc hcc con
  have hsC : (zpCodeC G.1 pstar).size = con.newCouple.size := by
    unfold zpCodeC; rw [he, hd]; split_ifs <;> simp [size_conjCpl]
  have hsT : (zpCodeT G.1 pstar).size = con.newTree.size := by
    unfold zpCodeT; rw [he, hd]; split_ifs <;> simp [size_conjChain]
  have hsum : con.newTree.size + con.newCouple.size = 2 * zpN A pstar := by
    rw [two_zpN A]; exact (con_excDatum con).size
  obtain ⟨m₁, hm₁⟩ := regCpl_size_even (zpCodeC G.1 pstar)
  obtain ⟨m₂, hm₂⟩ := regChain_size_even (zpCodeT G.1 pstar)
  have hmN : m₁ + m₂ = zpN A pstar := by omega
  -- parents
  have hq1 : (zpQQ G.1 pstar).1 ∈ ({numR A pstar, (zpBranchQ A pstar).1} : Finset ℕ) := by
    rw [hQQ, he]
    rcases hnum with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  have hq2 : (zpBranchQ G.1 pstar).1 ∈ ({numR A pstar, (zpBranchQ A pstar).1} : Finset ℕ) := by
    rw [he]
    rcases hnum with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hL2' : (zpBranchQ G.1 pstar).2 = (zpBranchQ A pstar).2 := by rw [he]; exact hL2
  have hQQ2 : (zpQQ G.1 pstar).2 = (zpBranchQ A pstar).2 := by rw [hQQ]; exact hL2'
  rw [hQQ2] at hC
  rw [hL2'] at hT
  unfold zpTriple zpTarget
  refine Finset.mem_product.2 ⟨Finset.mem_univ _, ?_⟩
  refine Finset.mem_biUnion.2 ⟨m₁, Finset.mem_range.2 (by omega), ?_⟩
  refine Finset.mem_biUnion.2 ⟨_, hq1, ?_⟩
  refine Finset.mem_biUnion.2 ⟨_, hq2, ?_⟩
  refine Finset.mem_biUnion.2 ⟨(zpObjT G.1 pstar).garden.sig 0, Finset.mem_univ _, ?_⟩
  refine Finset.mem_product.2 ⟨?_, ?_⟩
  · rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.2 ⟨⟨zpCodeC G.1 pstar, hC.1, by omega⟩, hC⟩
  · rw [Set.Finite.mem_toFinset, show zpN A pstar - m₁ = m₂ by omega]
    exact Set.mem_iUnion.2 ⟨⟨zpCodeT G.1 pstar, hT.1, by omega⟩, hT, rfl⟩

/-- The native objects are recovered from the carrier-side ones. -/
theorem sigStar_of_triple (G : FamilyReconstruction w ι) :
    sigStar G pstar = (nuOf G pstar,
      (if nuOf G pstar = -1 then zpObjC G pstar else conjLayered (zpObjC G pstar) (Equiv.swap (0 : Fin 2) 1)),
      (if nuOf G pstar = -1 then conjLayered (zpObjT G pstar) (Equiv.refl (Fin 1)) else zpObjT G pstar)) := by
  classical
  unfold zpObjC zpObjT
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · by_cases h : nuOf G pstar = -1
    · simp only [h, if_true]
    · simp only [h, if_false]
      exact (conjLayered_invol _ (fun x => Equiv.swap_apply_self _ _ x) _).symm
  · by_cases h : nuOf G pstar = -1
    · simp only [h, if_true]
      exact (conjLayered_refl_refl _).symm
    · simp only [h, if_false]

theorem zpTriple_injOn : Set.InjOn (zpTriple (w := w) (pstar := pstar) (J := J)) (zpFinset p kind pstar J A sp0 hA : Set (ST w ι pstar J)) := by
  intro G1 hG1 G2 hG2 he
  have hs : sigStar G1.1 pstar = sigStar G2.1 pstar := by
    rw [sigStar_of_triple G1.1, sigStar_of_triple G2.1]
    unfold zpTriple at he
    simp only [Prod.mk.injEq] at he
    rw [he.1, he.2.1, he.2.2]
  exact st_ext A sp0 ((mem_zpFinset hA).1 hG1) ((mem_zpFinset hA).1 hG2)
    (zp_eq_of_sigStar hA ((mem_zpFinset hA).1 hG1).batch ((mem_zpFinset hA).1 hG2).batch hs)

include hcan hel htc hcc in
/-- **The class count** (TARGET L1919-L1922): `#Zp(A) ≤ 16 (N+1) (4·12⁹)^N 4^p`, `N = zpN A pstar`. -/
theorem card_zpFinset_le :
    (zpFinset p kind pstar J A sp0 hA).card ≤ 16 * (zpN A pstar + 1) * ((4 * 12 ^ 9) ^ zpN A pstar * 4 ^ p) := by
  have hr := (zpLayers_of_state (J := J) A sp0 hA hcan hel htc hcc)
  refine (Finset.card_le_card_of_injOn (zpTriple (w := w) (pstar := pstar) (J := J)) (fun G hG => zpTriple_mem A sp0 hA hcan hel htc hcc G hG)
    (zpTriple_injOn A sp0 hA)).trans (card_zpTarget_le _ _ _ _ _ ?_ ?_ ?_)
  · exact q1_le_p A pstar hcan hel htc hcc
  · exact q2_le_p A pstar hcan hel htc hcc
  · exact (L2_le_q2 A pstar hcan hel htc hcc).trans (q2_le_p A pstar hcan hel htc hcc)

end Zp

end WaveTurbulence.VineEstS5C.P4
