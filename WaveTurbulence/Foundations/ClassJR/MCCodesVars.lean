/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCCodes

/-!
# The variables of a code

The induction of DH21 Proposition 5.1 needs the variables of the sub-couples and of the chain pairs
to be distinct (the hypotheses of `MCExp.type1`, `MCExp.type2`). They are addresses of distinct
nodes; this file proves it through the subtrees `Up x` of the addresses:
* the chosen nodes of a couple code with roots `x, y` lie in `Up x ∪ Up y` (`RegCpl.chosen_sub`);
* those of a chain rooted at `x` lie in `Up x` minus the subtree at its lone leaf
  (`RegChain.chosen_sub`).
-/

public section

open Set Finset

namespace WaveTurbulence.ClassJR

section Up

/-- The addresses at or below `x`. -/
@[expose] def Up (x : Addr) : Set Addr := {v | v.1 = x.1 ∧ x.2 <+: v.2}

theorem self_mem_up (x : Addr) : x ∈ Up x := ⟨rfl, List.prefix_refl _⟩

theorem up_addrExt_subset (x : Addr) (p : Path) : Up (addrExt x p) ⊆ Up x :=
  fun _ hv => ⟨hv.1, (List.prefix_append _ _).trans hv.2⟩

theorem addrExt_addrExt (x : Addr) (p q : Path) :
    addrExt (addrExt x p) q = addrExt x (p ++ q) := by
  simp [addrExt, List.append_assoc]

/-- Subtrees at different children are disjoint. -/
theorem disjoint_up_cons (x : Addr) {i j : Fin 3} (hij : i ≠ j) (p q : Path) :
    Disjoint (Up (addrExt x (i :: p))) (Up (addrExt x (j :: q))) := by
  rw [Set.disjoint_left]
  rintro v ⟨-, hv⟩ ⟨-, hw⟩
  have h1 : x.2 ++ [i] <+: v.2 := (List.prefix_append_right_inj x.2).2
    ((List.prefix_cons_inj i).2 (List.nil_prefix)) |>.trans hv
  have h2 : x.2 ++ [j] <+: v.2 := (List.prefix_append_right_inj x.2).2
    ((List.prefix_cons_inj j).2 (List.nil_prefix)) |>.trans hw
  have e := List.prefix_of_prefix_length_le h1 h2 (by simp)
  have := e.eq_of_length (by simp)
  simp at this
  exact hij this

theorem disjoint_up_ext {x y : Addr} (h : Disjoint (Up x) (Up y)) (p q : Path) :
    Disjoint (Up (addrExt x p)) (Up (addrExt y q)) :=
  h.mono (up_addrExt_subset _ _) (up_addrExt_subset _ _)

theorem notMem_up_cons (x : Addr) (i : Fin 3) (p : Path) : x ∉ Up (addrExt x (i :: p)) := by
  rintro ⟨-, h⟩
  have := h.length_le
  simp [addrExt] at this

end Up

section Mini

theorem MiniTreeCode.red_fst_ne_c (m : MiniTreeCode) : m.red.1 ≠ m.c := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide

theorem MiniTreeCode.green_fst_ne_c (m : MiniTreeCode) : m.green.1 ≠ m.c := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide

theorem MiniTreeCode.red_fst_ne_green_fst (m : MiniTreeCode) : m.red.1 ≠ m.green.1 := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide

theorem MiniTreeCode.red_snd_ne_lone (m : MiniTreeCode) : m.red.2 ≠ m.lone := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide

theorem MiniTreeCode.green_snd_ne_lone (m : MiniTreeCode) : m.green.2 ≠ m.lone := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide

theorem MiniTreeCode.red_snd_ne_green_snd (m : MiniTreeCode) : m.red.2 ≠ m.green.2 := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide

theorem MiniCplCode.partner_zero_ne_one (c : MiniCplCode) : c.partner 0 ≠ 1 := by
  fin_cases c <;> decide

theorem MiniCplCode.partner_two_ne_one (c : MiniCplCode) : c.partner 2 ≠ 1 := by
  fin_cases c <;> decide

theorem MiniCplCode.partner_zero_ne_two (c : MiniCplCode) : c.partner 0 ≠ c.partner 2 := by
  fin_cases c <;> decide

end Mini

section Chosen

theorem chosenSet_nil {w : ℕ} : chosenSet ([] : List ((Fin w × Path) × (Fin w × Path))) = ∅ := rfl

theorem chosenSet_cons {w : ℕ} (l : (Fin w × Path) × (Fin w × Path))
    (L : List ((Fin w × Path) × (Fin w × Path))) :
    chosenSet (l :: L) = insert l.1 (chosenSet L) := by
  simp [chosenSet]

theorem chosenSet_append {w : ℕ} (L₁ L₂ : List ((Fin w × Path) × (Fin w × Path))) :
    chosenSet (L₁ ++ L₂) = chosenSet L₁ ∪ chosenSet L₂ := by
  simp [chosenSet, List.toFinset_append]

theorem subset_up_diff {S : Set Addr} {a x lp : Addr} (hS : S ⊆ Up a) (hax : Up a ⊆ Up x)
    (hd : Disjoint (Up a) (Up lp)) : S ⊆ Up x \ Up lp :=
  fun _ hv => ⟨hax (hS hv), Set.disjoint_left.1 hd (hS hv)⟩

mutual
/-- **The chosen nodes of a couple code lie below its roots.** -/
theorem RegCpl.chosen_sub : ∀ (Q : RegCpl) (x y : Addr),
    (↑(chosenSet (Q.linksAt x y)) : Set Addr) ⊆ Up x ∪ Up y
  | .triv, x, y => by simp [RegCpl.linksAt, chosenSet_nil]
  | .type1 c Q₁ Q₂ Q₃, x, y => by
    simp only [RegCpl.linksAt, chosenSet_cons, chosenSet_append, Finset.coe_insert,
      Finset.coe_union]
    refine Set.insert_subset (Or.inl (self_mem_up x)) (Set.union_subset (Set.union_subset ?_ ?_) ?_)
    · exact (RegCpl.chosen_sub Q₁ _ _).trans
        (Set.union_subset_union (up_addrExt_subset _ _) (up_addrExt_subset _ _))
    · exact (RegCpl.chosen_sub Q₂ _ _).trans (by
        rw [Set.union_comm]
        exact Set.union_subset_union (up_addrExt_subset _ _) (up_addrExt_subset _ _))
    · exact (RegCpl.chosen_sub Q₃ _ _).trans
        (Set.union_subset_union (up_addrExt_subset _ _) (up_addrExt_subset _ _))
  | .type2 Xp Xm Qlp, x, y => by
    simp only [RegCpl.linksAt, chosenSet_append, Finset.coe_union]
    refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · exact (RegChain.chosen_sub Xp 1 x).trans (Set.sdiff_subset.trans Set.subset_union_left)
    · exact (RegChain.chosen_sub Xm (-1) y).trans (Set.sdiff_subset.trans Set.subset_union_right)
    · exact (RegCpl.chosen_sub Qlp _ _).trans
        (Set.union_subset_union (up_addrExt_subset _ _) (up_addrExt_subset _ _))

/-- **The chosen nodes of a chain lie below its root and off the subtree at its lone leaf.** -/
theorem RegChain.chosen_sub : ∀ (X : RegChain) (ζ : ℤˣ) (x : Addr),
    (↑(chosenSet (X.linksAt ζ x)) : Set Addr) ⊆ Up x \ Up (addrExt x X.lonePath)
  | .nil, ζ, x => by simp [RegChain.linksAt, chosenSet_nil]
  | .pair m Qr Qg inner rest, ζ, x => by
    have hlp : addrExt x (RegChain.pair m Qr Qg inner rest).lonePath =
        addrExt (addrExt x (m.c :: inner.lonePath)) (m.lone :: rest.lonePath) := by
      rw [addrExt_addrExt]; simp [RegChain.lonePath]
    rw [hlp]
    have hk : ∀ k : Fin 3, addrExt x ([m.c] ++ inner.lonePath ++ [k]) =
        addrExt (addrExt x (m.c :: inner.lonePath)) [k] := fun k => by
      rw [addrExt_addrExt]; simp
    -- the couples of the pair
    have hcpl : ∀ (i k : Fin 3), i ≠ m.c → k ≠ m.lone → ∀ (Q : RegCpl),
        (∀ x' y', (↑(chosenSet (Q.linksAt x' y')) : Set Addr) ⊆ Up x' ∪ Up y') → ∀ (b : Bool),
        (↑(chosenSet (if b then Q.linksAt (addrExt x [i]) (addrExt x ([m.c] ++ inner.lonePath ++ [k]))
          else Q.linksAt (addrExt x ([m.c] ++ inner.lonePath ++ [k])) (addrExt x [i]))) : Set Addr) ⊆
          Up x \ Up (addrExt (addrExt x (m.c :: inner.lonePath)) (m.lone :: rest.lonePath)) := by
      intro i k hi hk' Q hQ b
      have h1 : Up (addrExt x [i]) ⊆
          Up x \ Up (addrExt (addrExt x (m.c :: inner.lonePath)) (m.lone :: rest.lonePath)) :=
        subset_up_diff le_rfl (up_addrExt_subset _ _) (by
          rw [addrExt_addrExt]
          exact disjoint_up_cons x hi [] _)
      have h2 : Up (addrExt x ([m.c] ++ inner.lonePath ++ [k])) ⊆
          Up x \ Up (addrExt (addrExt x (m.c :: inner.lonePath)) (m.lone :: rest.lonePath)) := by
        rw [hk]
        exact subset_up_diff le_rfl ((up_addrExt_subset _ _).trans (up_addrExt_subset _ _))
          (disjoint_up_cons _ hk' [] _)
      cases b
      · exact (hQ _ _).trans (Set.union_subset h2 h1)
      · exact (hQ _ _).trans (Set.union_subset h1 h2)
    simp only [RegChain.linksAt, chosenSet_cons, chosenSet_append, Finset.coe_insert,
      Finset.coe_union]
    refine Set.insert_subset ⟨self_mem_up x, by
        rw [addrExt_addrExt]; exact notMem_up_cons x m.c _⟩
      (Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_)
    · have := hcpl m.red.1 m.red.2 m.red_fst_ne_c m.red_snd_ne_lone Qr (RegCpl.chosen_sub Qr)
        (decide (slotSign ζ m.red.1 = 1))
      by_cases h : slotSign ζ m.red.1 = 1 <;> simp_all
    · have := hcpl m.green.1 m.green.2 m.green_fst_ne_c m.green_snd_ne_lone Qg
        (RegCpl.chosen_sub Qg) (decide (slotSign ζ m.green.1 = 1))
      by_cases h : slotSign ζ m.green.1 = 1 <;> simp_all
    · have e : addrExt (addrExt x [m.c]) inner.lonePath = addrExt x (m.c :: inner.lonePath) := by
        rw [addrExt_addrExt]; simp
      refine (RegChain.chosen_sub inner _ _).trans fun v hv => ⟨(up_addrExt_subset _ _) hv.1, ?_⟩
      rw [e] at hv
      exact fun hlv => hv.2 (up_addrExt_subset _ _ hlv)
    · have e : addrExt (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath =
          addrExt (addrExt x (m.c :: inner.lonePath)) (m.lone :: rest.lonePath) := by
        rw [hk, addrExt_addrExt]; simp
      refine (RegChain.chosen_sub rest _ _).trans fun v hv => ⟨(up_addrExt_subset _ _) hv.1, ?_⟩
      rw [e] at hv
      exact hv.2
end

end Chosen

section Flat

variable (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ) (x : Addr) (q : ℕ)

theorem code_size_pair :
    (RegChain.pair m Qr Qg inner rest).code.size = inner.code.size + rest.code.size + 1 := rfl

theorem sigmaAt_pair_self : (RegChain.pair m Qr Qg inner rest).sigmaAt x q q = x := by
  simp [RegChain.sigmaAt]

theorem sigmaAt_pair_inner {j : ℕ} (hj : j ∈ Set.Ico (q + 1) (q + 1 + inner.code.size)) :
    (RegChain.pair m Qr Qg inner rest).sigmaAt x q j = inner.sigmaAt (addrExt x [m.c]) (q + 1) j := by
  simp only [Set.mem_Ico] at hj
  simp only [RegChain.sigmaAt, show j ≠ q by omega, show j < q + 1 + inner.code.size by omega,
    ↓reduceIte]

theorem sigmaAt_pair_rest {j : ℕ}
    (hj : j ∈ Set.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size)) :
    (RegChain.pair m Qr Qg inner rest).sigmaAt x q j =
      rest.sigmaAt (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + inner.code.size + 1) j := by
  simp only [Set.mem_Ico] at hj
  simp only [RegChain.sigmaAt, show j ≠ q by omega, show ¬ j < q + 1 + inner.code.size by omega,
    ↓reduceIte]

theorem varsAt_pair_self : (RegChain.pair m Qr Qg inner rest).varsAt ζ x q q =
    chosenSet (if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt x [m.red.1]) (addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt x [m.red.1])) ∪
    chosenSet (if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt x [m.green.1]) (addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.linksAt (addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt x [m.green.1])) := by
  simp only [RegChain.varsAt, ↓reduceIte]

theorem varsAt_pair_inner {j : ℕ} (hj : j ∈ Set.Ico (q + 1) (q + 1 + inner.code.size)) :
    (RegChain.pair m Qr Qg inner rest).varsAt ζ x q j =
      inner.varsAt (slotSign ζ m.c) (addrExt x [m.c]) (q + 1) j := by
  simp only [Set.mem_Ico] at hj
  simp only [RegChain.varsAt, show j ≠ q by omega, show j < q + 1 + inner.code.size by omega,
    ↓reduceIte]

theorem varsAt_pair_rest {j : ℕ}
    (hj : j ∈ Set.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size)) :
    (RegChain.pair m Qr Qg inner rest).varsAt ζ x q j =
      rest.varsAt (slotSign (slotSign ζ m.c) m.lone)
        (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + inner.code.size + 1) j := by
  simp only [Set.mem_Ico] at hj
  simp only [RegChain.varsAt, show j ≠ q by omega, show ¬ j < q + 1 + inner.code.size by omega,
    ↓reduceIte]

theorem coefAt_pair_inner {j : ℕ} (hj : j ∈ Set.Ico (q + 1) (q + 1 + inner.code.size)) :
    (RegChain.pair m Qr Qg inner rest).coefAt ζ x q j =
      inner.coefAt (slotSign ζ m.c) (addrExt x [m.c]) (q + 1) j := by
  simp only [Set.mem_Ico] at hj
  simp only [RegChain.coefAt, show j ≠ q by omega, show j < q + 1 + inner.code.size by omega,
    ↓reduceIte]

theorem coefAt_pair_rest {j : ℕ}
    (hj : j ∈ Set.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size)) :
    (RegChain.pair m Qr Qg inner rest).coefAt ζ x q j =
      rest.coefAt (slotSign (slotSign ζ m.c) m.lone)
        (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + inner.code.size + 1) j := by
  simp only [Set.mem_Ico] at hj
  simp only [RegChain.coefAt, show j ≠ q by omega, show ¬ j < q + 1 + inner.code.size by omega,
    ↓reduceIte]

theorem NBAt_pair_self (θ a b : ℝ) :
    (RegChain.pair m Qr Qg inner rest).NBAt θ a b q q = 4 * Qr.NB θ a b * Qg.NB θ a b := by
  simp [RegChain.NBAt]

theorem NBAt_pair_inner (θ a b : ℝ) {j : ℕ} (hj : j ∈ Set.Ico (q + 1) (q + 1 + inner.code.size)) :
    (RegChain.pair m Qr Qg inner rest).NBAt θ a b q j = inner.NBAt θ a b (q + 1) j := by
  simp only [Set.mem_Ico] at hj
  simp only [RegChain.NBAt, show j ≠ q by omega, show j < q + 1 + inner.code.size by omega,
    ↓reduceIte]

theorem NBAt_pair_rest (θ a b : ℝ) {j : ℕ}
    (hj : j ∈ Set.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size)) :
    (RegChain.pair m Qr Qg inner rest).NBAt θ a b q j =
      rest.NBAt θ a b (q + inner.code.size + 1) j := by
  simp only [Set.mem_Ico] at hj
  simp only [RegChain.NBAt, show j ≠ q by omega, show ¬ j < q + 1 + inner.code.size by omega,
    ↓reduceIte]

/-- The three ranges of a pair node. -/
theorem mem_Ico_pair {j : ℕ}
    (hj : j ∈ Set.Ico q (q + (RegChain.pair m Qr Qg inner rest).code.size)) :
    j = q ∨ j ∈ Set.Ico (q + 1) (q + 1 + inner.code.size) ∨
      j ∈ Set.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size) := by
  rw [code_size_pair] at hj
  simp only [Set.mem_Ico] at hj ⊢
  omega

end Flat

section ChainFacts

/-- **The flattened pairs of a chain**: the chosen chain nodes and the variables of the pair
coefficients lie in the region of the chain, are distinct, and make up its chosen nodes. -/
structure ChainFacts (X : RegChain) (ζ : ℤˣ) (x : Addr) (q : ℕ) : Prop where
  sig_mem : ∀ j ∈ Set.Ico q (q + X.code.size), X.sigmaAt x q j ∈ Up x \ Up (addrExt x X.lonePath)
  vars_sub : ∀ j ∈ Set.Ico q (q + X.code.size),
    (↑(X.varsAt ζ x q j) : Set Addr) ⊆ Up x \ Up (addrExt x X.lonePath)
  inj : Set.InjOn (X.sigmaAt x q) (Set.Ico q (q + X.code.size))
  disj : ∀ j ∈ Set.Ico q (q + X.code.size), ∀ k ∈ Set.Ico q (q + X.code.size), j ≠ k →
    Disjoint (X.varsAt ζ x q j) (X.varsAt ζ x q k)
  sig_notMem : ∀ j ∈ Set.Ico q (q + X.code.size), ∀ k ∈ Set.Ico q (q + X.code.size),
    X.sigmaAt x q k ∉ X.varsAt ζ x q j
  chosen : chosenSet (X.linksAt ζ x) =
    unionS (X.varsAt ζ x q) q X.code.size ∪ (Finset.Ico q (q + X.code.size)).image (X.sigmaAt x q)

/-- The variables of the two couples of a pair lie in the subtrees of their roots. -/
theorem varsAt_pair_self_sub (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain)
    (ζ : ℤˣ) (x : Addr) (q : ℕ) :
    (↑((RegChain.pair m Qr Qg inner rest).varsAt ζ x q q) : Set Addr) ⊆
      (Up (addrExt x [m.red.1]) ∪ Up (addrExt (addrExt x (m.c :: inner.lonePath)) [m.red.2])) ∪
      (Up (addrExt x [m.green.1]) ∪ Up (addrExt (addrExt x (m.c :: inner.lonePath)) [m.green.2])) := by
  have hk : ∀ k : Fin 3, addrExt x ([m.c] ++ inner.lonePath ++ [k]) =
      addrExt (addrExt x (m.c :: inner.lonePath)) [k] := fun k => by
    rw [addrExt_addrExt]; simp
  rw [varsAt_pair_self, Finset.coe_union]
  refine Set.union_subset_union ?_ ?_
  · split_ifs
    · rw [hk]; exact RegCpl.chosen_sub Qr _ _
    · rw [hk, Set.union_comm]; exact RegCpl.chosen_sub Qr _ _
  · split_ifs
    · rw [hk]; exact RegCpl.chosen_sub Qg _ _
    · rw [hk, Set.union_comm]; exact RegCpl.chosen_sub Qg _ _

theorem RegChain.chainFacts : ∀ (X : RegChain) (ζ : ℤˣ) (x : Addr) (q : ℕ), ChainFacts X ζ x q
  | .nil, ζ, x, q => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [RegChain.code, LegalCode.size, RegChain.linksAt, chosenSet_nil, unionS]
  | .pair m Qr Qg inner rest, ζ, x, q => by
    have hi := RegChain.chainFacts inner (slotSign ζ m.c) (addrExt x [m.c]) (q + 1)
    have hr := RegChain.chainFacts rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + inner.code.size + 1)
    -- the nodes
    obtain ⟨nb, hnb⟩ : ∃ nb, nb = addrExt x (m.c :: inner.lonePath) := ⟨_, rfl⟩
    have e_in : addrExt (addrExt x [m.c]) inner.lonePath = nb := by
      rw [hnb, addrExt_addrExt]; simp
    have e_xr : addrExt x ([m.c] ++ inner.lonePath ++ [m.lone]) = addrExt nb [m.lone] := by
      rw [hnb, addrExt_addrExt]; simp
    have e_rlp : addrExt (addrExt nb [m.lone]) rest.lonePath = addrExt nb (m.lone :: rest.lonePath) := by
      rw [addrExt_addrExt]; simp
    have e_lp : addrExt x (RegChain.pair m Qr Qg inner rest).lonePath =
        addrExt nb (m.lone :: rest.lonePath) := by
      rw [hnb, addrExt_addrExt]; simp [RegChain.lonePath]
    have Rin_eq : Up (addrExt x [m.c]) \ Up (addrExt (addrExt x [m.c]) inner.lonePath) =
        Up (addrExt x [m.c]) \ Up nb := by rw [e_in]
    have Rr_eq : Up (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) \
        Up (addrExt (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath) =
        Up (addrExt nb [m.lone]) \ Up (addrExt nb (m.lone :: rest.lonePath)) := by
      rw [e_xr, e_rlp]
    have hnbc : Up nb ⊆ Up (addrExt x [m.c]) := by
      rw [← e_in]; exact up_addrExt_subset _ _
    -- the regions
    have f1 := varsAt_pair_self_sub m Qr Qg inner rest ζ x q
    rw [← hnb] at f1
    have hA : ∀ i : Fin 3, i ≠ m.c → Disjoint (Up (addrExt x [i])) (Up nb) := fun i hi' => by
      rw [hnb]; exact disjoint_up_cons x hi' [] _
    have hB : ∀ k : Fin 3, k ≠ m.lone →
        Disjoint (Up (addrExt nb [k])) (Up (addrExt nb [m.lone])) := fun k hk =>
      disjoint_up_cons nb hk [] []
    have hLpr : Up (addrExt nb (m.lone :: rest.lonePath)) ⊆ Up (addrExt nb [m.lone]) := by
      rw [show (m.lone :: rest.lonePath) = [m.lone] ++ rest.lonePath from rfl, ← addrExt_addrExt]
      exact up_addrExt_subset _ _
    have hxrnb : Up (addrExt nb [m.lone]) ⊆ Up nb := up_addrExt_subset _ _
    have hnbx : Up nb ⊆ Up x := hnbc.trans (up_addrExt_subset _ _)
    -- `V0` is the region of the couples of the pair
    have f2 : (Up (addrExt x [m.red.1]) ∪ Up (addrExt nb [m.red.2])) ∪
        (Up (addrExt x [m.green.1]) ∪ Up (addrExt nb [m.green.2])) ⊆
        Up x \ Up (addrExt nb (m.lone :: rest.lonePath)) := by
      have h1 : ∀ i : Fin 3, i ≠ m.c →
          Up (addrExt x [i]) ⊆ Up x \ Up (addrExt nb (m.lone :: rest.lonePath)) := fun i hi' =>
        subset_up_diff le_rfl (up_addrExt_subset _ _)
          ((hA i hi').mono_right ((hLpr.trans hxrnb)))
      have h2 : ∀ k : Fin 3, k ≠ m.lone →
          Up (addrExt nb [k]) ⊆ Up x \ Up (addrExt nb (m.lone :: rest.lonePath)) := fun k hk =>
        subset_up_diff le_rfl ((up_addrExt_subset _ _).trans hnbx) ((hB k hk).mono_right hLpr)
      exact Set.union_subset (Set.union_subset (h1 _ m.red_fst_ne_c) (h2 _ m.red_snd_ne_lone))
        (Set.union_subset (h1 _ m.green_fst_ne_c) (h2 _ m.green_snd_ne_lone))
    have f3 : x ∈ Up x \ Up (addrExt nb (m.lone :: rest.lonePath)) :=
      ⟨self_mem_up x, fun h => notMem_up_cons x m.c inner.lonePath (by
        rw [← hnb]; exact (hLpr.trans hxrnb) h)⟩
    have f4 : Up (addrExt x [m.c]) \ Up nb ⊆ Up x \ Up (addrExt nb (m.lone :: rest.lonePath)) :=
      fun v hv => ⟨up_addrExt_subset _ _ hv.1, fun h => hv.2 ((hLpr.trans hxrnb) h)⟩
    have f5 : Up (addrExt nb [m.lone]) \ Up (addrExt nb (m.lone :: rest.lonePath)) ⊆
        Up x \ Up (addrExt nb (m.lone :: rest.lonePath)) :=
      fun v hv => ⟨(hxrnb.trans hnbx) hv.1, hv.2⟩
    have hxV0 : x ∉ (Up (addrExt x [m.red.1]) ∪ Up (addrExt nb [m.red.2])) ∪
        (Up (addrExt x [m.green.1]) ∪ Up (addrExt nb [m.green.2])) := by
      have hnx : ∀ (i : Fin 3) (p : Path), x ∉ Up (addrExt x (i :: p)) := notMem_up_cons x
      have hnx' : ∀ k : Fin 3, x ∉ Up (addrExt nb [k]) := fun k h => by
        have := (up_addrExt_subset nb [k]) h
        rw [hnb] at this; exact hnx _ _ this
      simp only [Set.mem_union, not_or]
      exact ⟨⟨hnx _ _, hnx' _⟩, hnx _ _, hnx' _⟩
    have hxin : x ∉ Up (addrExt x [m.c]) \ Up nb := fun h => notMem_up_cons x m.c [] h.1
    have hxr : x ∉ Up (addrExt nb [m.lone]) \ Up (addrExt nb (m.lone :: rest.lonePath)) :=
      fun h => notMem_up_cons x m.c inner.lonePath (by rw [← hnb]; exact hxrnb h.1)
    have f9 : Disjoint ((Up (addrExt x [m.red.1]) ∪ Up (addrExt nb [m.red.2])) ∪
        (Up (addrExt x [m.green.1]) ∪ Up (addrExt nb [m.green.2])))
        (Up (addrExt x [m.c]) \ Up nb) := by
      have hc : ∀ i : Fin 3, i ≠ m.c → Disjoint (Up (addrExt x [i])) (Up (addrExt x [m.c])) :=
        fun i hi' => disjoint_up_cons x hi' [] []
      have hd : ∀ k : Fin 3, Disjoint (Up (addrExt nb [k])) (Up (addrExt x [m.c]) \ Up nb) :=
        fun k => Set.disjoint_left.2 fun v hv hv' => hv'.2 (up_addrExt_subset _ _ hv)
      refine Disjoint.union_left (Disjoint.union_left ?_ (hd _)) (Disjoint.union_left ?_ (hd _))
      · exact (hc _ m.red_fst_ne_c).mono_right Set.sdiff_subset
      · exact (hc _ m.green_fst_ne_c).mono_right Set.sdiff_subset
    have f10 : Disjoint ((Up (addrExt x [m.red.1]) ∪ Up (addrExt nb [m.red.2])) ∪
        (Up (addrExt x [m.green.1]) ∪ Up (addrExt nb [m.green.2])))
        (Up (addrExt nb [m.lone]) \ Up (addrExt nb (m.lone :: rest.lonePath))) := by
      refine Disjoint.union_left (Disjoint.union_left ?_ ?_) (Disjoint.union_left ?_ ?_)
      · exact ((hA _ m.red_fst_ne_c).mono_right hxrnb).mono_right Set.sdiff_subset
      · exact (hB _ m.red_snd_ne_lone).mono_right Set.sdiff_subset
      · exact ((hA _ m.green_fst_ne_c).mono_right hxrnb).mono_right Set.sdiff_subset
      · exact (hB _ m.green_snd_ne_lone).mono_right Set.sdiff_subset
    have f11 : Disjoint (Up (addrExt x [m.c]) \ Up nb)
        (Up (addrExt nb [m.lone]) \ Up (addrExt nb (m.lone :: rest.lonePath))) :=
      Set.disjoint_left.2 fun v hv hv' => hv.2 (hxrnb hv'.1)
    -- the pieces
    have s0 := sigmaAt_pair_self m Qr Qg inner rest x q
    have sIn : ∀ k ∈ Set.Ico (q + 1) (q + 1 + inner.code.size),
        (RegChain.pair m Qr Qg inner rest).sigmaAt x q k ∈ Up (addrExt x [m.c]) \ Up nb :=
      fun k hk => by rw [sigmaAt_pair_inner _ _ _ _ _ _ _ hk, ← Rin_eq]; exact hi.sig_mem k hk
    have sR : ∀ k ∈ Set.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size),
        (RegChain.pair m Qr Qg inner rest).sigmaAt x q k ∈
          Up (addrExt nb [m.lone]) \ Up (addrExt nb (m.lone :: rest.lonePath)) :=
      fun k hk => by rw [sigmaAt_pair_rest _ _ _ _ _ _ _ hk, ← Rr_eq]; exact hr.sig_mem k hk
    have vIn : ∀ k ∈ Set.Ico (q + 1) (q + 1 + inner.code.size),
        (↑((RegChain.pair m Qr Qg inner rest).varsAt ζ x q k) : Set Addr) ⊆
          Up (addrExt x [m.c]) \ Up nb :=
      fun k hk => by rw [varsAt_pair_inner _ _ _ _ _ _ _ _ hk, ← Rin_eq]; exact hi.vars_sub k hk
    have vR : ∀ k ∈ Set.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size),
        (↑((RegChain.pair m Qr Qg inner rest).varsAt ζ x q k) : Set Addr) ⊆
          Up (addrExt nb [m.lone]) \ Up (addrExt nb (m.lone :: rest.lonePath)) :=
      fun k hk => by rw [varsAt_pair_rest _ _ _ _ _ _ _ _ hk, ← Rr_eq]; exact hr.vars_sub k hk
    have dset : ∀ {A B : Finset Addr} {S T : Set Addr}, (↑A : Set Addr) ⊆ S → (↑B : Set Addr) ⊆ T →
        Disjoint S T → Disjoint A B := fun hA hB hST => Finset.disjoint_coe.1 (hST.mono hA hB)
    have nset : ∀ {v : Addr} {A : Finset Addr} {S T : Set Addr}, v ∈ S → (↑A : Set Addr) ⊆ T →
        Disjoint S T → v ∉ A := fun hv hA hST h => Set.disjoint_left.1 hST hv (hA h)
    -- the fields
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj k hk hjk => ?_, fun j hj k hk hjk => ?_,
      fun j hj k hk => ?_, ?_⟩
    · rw [e_lp]
      rcases mem_Ico_pair m Qr Qg inner rest q hj with rfl | hj' | hj'
      · rw [s0]; exact f3
      · exact f4 (sIn j hj')
      · exact f5 (sR j hj')
    · rw [e_lp]
      rcases mem_Ico_pair m Qr Qg inner rest q hj with rfl | hj' | hj'
      · exact f1.trans f2
      · exact (vIn j hj').trans f4
      · exact (vR j hj').trans f5
    · rcases mem_Ico_pair m Qr Qg inner rest q hj with hj0 | hj' | hj' <;>
        rcases mem_Ico_pair m Qr Qg inner rest q hk with hk0 | hk' | hk'
      · rw [hj0, hk0]
      · rw [hj0, s0] at hjk
        exact absurd (sIn k hk') (by rw [← hjk]; exact hxin)
      · rw [hj0, s0] at hjk
        exact absurd (sR k hk') (by rw [← hjk]; exact hxr)
      · rw [hk0, s0] at hjk
        exact absurd (sIn j hj') (by rw [hjk]; exact hxin)
      · rw [sigmaAt_pair_inner _ _ _ _ _ _ _ hj', sigmaAt_pair_inner _ _ _ _ _ _ _ hk'] at hjk
        exact hi.inj hj' hk' hjk
      · exact absurd (sR k hk') (Set.disjoint_left.1 f11 (hjk ▸ sIn j hj'))
      · rw [hk0, s0] at hjk
        exact absurd (sR j hj') (by rw [hjk]; exact hxr)
      · exact absurd (sR j hj') (Set.disjoint_left.1 f11 (hjk.symm ▸ sIn k hk'))
      · rw [sigmaAt_pair_rest _ _ _ _ _ _ _ hj', sigmaAt_pair_rest _ _ _ _ _ _ _ hk'] at hjk
        exact hr.inj hj' hk' hjk
    · rcases mem_Ico_pair m Qr Qg inner rest q hj with hj0 | hj' | hj' <;>
        rcases mem_Ico_pair m Qr Qg inner rest q hk with hk0 | hk' | hk'
      · exact absurd (hj0.trans hk0.symm) hjk
      · rw [hj0]; exact dset f1 (vIn k hk') f9
      · rw [hj0]; exact dset f1 (vR k hk') f10
      · rw [hk0]; exact dset (vIn j hj') f1 f9.symm
      · rw [varsAt_pair_inner _ _ _ _ _ _ _ _ hj', varsAt_pair_inner _ _ _ _ _ _ _ _ hk']
        exact hi.disj j hj' k hk' hjk
      · exact dset (vIn j hj') (vR k hk') f11
      · rw [hk0]; exact dset (vR j hj') f1 f10.symm
      · exact dset (vR j hj') (vIn k hk') f11.symm
      · rw [varsAt_pair_rest _ _ _ _ _ _ _ _ hj', varsAt_pair_rest _ _ _ _ _ _ _ _ hk']
        exact hr.disj j hj' k hk' hjk
    · rcases mem_Ico_pair m Qr Qg inner rest q hj with hj0 | hj' | hj' <;>
        rcases mem_Ico_pair m Qr Qg inner rest q hk with hk0 | hk' | hk'
      · rw [hj0, hk0, s0]; exact fun h => hxV0 (f1 h)
      · rw [hj0]; exact nset (sIn k hk') f1 f9.symm
      · rw [hj0]; exact nset (sR k hk') f1 f10.symm
      · rw [hk0, s0]; exact fun h => hxin (vIn j hj' h)
      · rw [varsAt_pair_inner _ _ _ _ _ _ _ _ hj', sigmaAt_pair_inner _ _ _ _ _ _ _ hk']
        exact hi.sig_notMem j hj' k hk'
      · exact nset (sR k hk') (vIn j hj') f11.symm
      · rw [hk0, s0]; exact fun h => hxr (vR j hj' h)
      · exact nset (sIn k hk') (vR j hj') f11
      · rw [varsAt_pair_rest _ _ _ _ _ _ _ _ hj', sigmaAt_pair_rest _ _ _ _ _ _ _ hk']
        exact hr.sig_notMem j hj' k hk'
    · have hL : chosenSet ((RegChain.pair m Qr Qg inner rest).linksAt ζ x) =
          insert x ((RegChain.pair m Qr Qg inner rest).varsAt ζ x q q ∪
            chosenSet (inner.linksAt (slotSign ζ m.c) (addrExt x [m.c])) ∪
            chosenSet (rest.linksAt (slotSign (slotSign ζ m.c) m.lone)
              (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])))) := by
        rw [varsAt_pair_self]
        simp only [RegChain.linksAt, chosenSet_cons, chosenSet_append]
      have hU : unionS ((RegChain.pair m Qr Qg inner rest).varsAt ζ x q) q
          (RegChain.pair m Qr Qg inner rest).code.size =
          (RegChain.pair m Qr Qg inner rest).varsAt ζ x q q ∪
            unionS (inner.varsAt (slotSign ζ m.c) (addrExt x [m.c]) (q + 1)) (q + 1)
              inner.code.size ∪
            unionS (rest.varsAt (slotSign (slotSign ζ m.c) m.lone)
              (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + inner.code.size + 1))
              (q + inner.code.size + 1) rest.code.size := by
        have h1 : unionS ((RegChain.pair m Qr Qg inner rest).varsAt ζ x q) (q + 1) inner.code.size =
            unionS (inner.varsAt (slotSign ζ m.c) (addrExt x [m.c]) (q + 1)) (q + 1)
              inner.code.size := by
          unfold unionS
          exact Finset.biUnion_congr rfl fun j hj =>
            varsAt_pair_inner _ _ _ _ _ _ _ _ (by simpa [Finset.mem_Ico] using hj)
        have h2 : unionS ((RegChain.pair m Qr Qg inner rest).varsAt ζ x q) (q + inner.code.size + 1)
            rest.code.size =
            unionS (rest.varsAt (slotSign (slotSign ζ m.c) m.lone)
              (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + inner.code.size + 1))
              (q + inner.code.size + 1) rest.code.size := by
          unfold unionS
          exact Finset.biUnion_congr rfl fun j hj =>
            varsAt_pair_rest _ _ _ _ _ _ _ _ (by simpa [Finset.mem_Ico] using hj)
        rw [show (RegChain.pair m Qr Qg inner rest).code = .node inner.code rest.code from rfl,
          unionS_node, h1, h2]
      have hI : (Finset.Ico q (q + (RegChain.pair m Qr Qg inner rest).code.size)).image
          ((RegChain.pair m Qr Qg inner rest).sigmaAt x q) =
          insert x ((Finset.Ico (q + 1) (q + 1 + inner.code.size)).image
              (inner.sigmaAt (addrExt x [m.c]) (q + 1)) ∪
            (Finset.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size)).image
              (rest.sigmaAt (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone]))
                (q + inner.code.size + 1))) := by
        have hsplit : Finset.Ico q (q + (RegChain.pair m Qr Qg inner rest).code.size) =
            insert q (Finset.Ico (q + 1) (q + 1 + inner.code.size) ∪
              Finset.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size)) := by
          ext j
          simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_union, code_size_pair]
          omega
        rw [hsplit, Finset.image_insert, Finset.image_union, s0]
        congr 2
        · exact Finset.image_congr fun j hj =>
            sigmaAt_pair_inner _ _ _ _ _ _ _ (by simpa [Finset.mem_Ico] using hj)
        · exact Finset.image_congr fun j hj =>
            sigmaAt_pair_rest _ _ _ _ _ _ _ (by simpa [Finset.mem_Ico] using hj)
      rw [hL, hi.chosen, hr.chosen, hU, hI]
      ext v
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto

end ChainFacts

end WaveTurbulence.ClassJR
