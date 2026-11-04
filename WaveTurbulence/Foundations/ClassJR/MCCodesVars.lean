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

theorem addrExt_mem_up (x : Addr) (p : Path) : addrExt x p ∈ Up x :=
  ⟨rfl, List.prefix_append _ _⟩

theorem up_addrExt_subset (x : Addr) (p : Path) : Up (addrExt x p) ⊆ Up x :=
  fun _ hv => ⟨hv.1, (List.prefix_append _ _).trans hv.2⟩

theorem addrExt_addrExt (x : Addr) (p q : Path) :
    addrExt (addrExt x p) q = addrExt x (p ++ q) := by
  simp [addrExt, List.append_assoc]

theorem addrExt_nil (x : Addr) : addrExt x [] = x := by simp [addrExt]

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

theorem addrExt_cons_notMem_up_self {x : Addr} (i : Fin 3) (p : Path) {v : Addr}
    (hv : v ∈ Up (addrExt x (i :: p))) : v ∉ ({x} : Set Addr) := by
  rintro rfl
  exact notMem_up_cons v i p hv

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
  fun v hv => ⟨hax (hS hv), Set.disjoint_left.1 hd (hS hv)⟩

/-- The address `x⬝(c :: l ++ [k])` below the node `x⬝(c :: l)`. -/
theorem addrExt_chain (x : Addr) (c : Fin 3) (l : Path) (p : Path) :
    addrExt x ([c] ++ l ++ p) = addrExt (addrExt x (c :: l)) p := by
  rw [addrExt_addrExt]; simp

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

end WaveTurbulence.ClassJR
