/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Enhanced.TreeIncoh1

/-!
# Special subsets: the two definitions agree (packet C5)

* TARGET Def 6.4 (`defencpl`, L1127) and the B2 draft `IsSpecialSet`: `Z ⊆ 𝒩^ch` is special if for
  each `𝔫 ∈ Z` the node `𝔫'` linked with `𝔫` is a child of `𝔫`.
* DH21 Def 4.18 (`equivcpl`, L862–L870), recursive: `∅` is special; type 1: `Z = Z₁ ∪ Z₂ ∪ Z₃`
  with `Z_j` special in `𝒬_j` (the root is never in `Z`); type 2:
  `Z = ⋃ Z_{j,ε,ι} ∪ Z_lp ∪ {𝔫^±_{2j-1} : j ∈ Z^±}` (unionz).

`cplSpecial` / `chainSpecial` list the recursive candidates: the chosen node `𝔫_a`
of every chain pair `{a, b}` with `b = a + 1` (code: `inner = nil`; in a dominant chain this is every
pair), at every level, and nothing at type-1 roots. `mem_cplSpecial_iff` shows that these are
exactly the chosen nodes whose linked node is a child, so the two definitions of special subsets
coincide (`isSpecialSet_iff`, `mem_specialSets_iff`, and the tree versions).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

mutual
/-- **The special candidates of a couple code** (DH21 Def 4.18, recursive form) placed at `(a, b)`:
type 1 contributes no root; type 2 contributes the chosen nodes of its chain pairs `{a, a+1}`. -/
def cplSpecial : RegCpl → (Fin w × Path) → (Fin w × Path) → List (Fin w × Path)
  | .triv, _, _ => []
  | .type1 c Q₁ Q₂ Q₃, a, b =>
    cplSpecial Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) ++
      cplSpecial Q₂ (addrExt b [1]) (addrExt a [1]) ++
      cplSpecial Q₃ (addrExt a [2]) (addrExt b [c.partner 2])
  | .type2 Xp Xm Qlp, a, b =>
    chainSpecial Xp 1 a ++ chainSpecial Xm (-1) b ++
      cplSpecial Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)

/-- The special candidates of a chain code rooted at `a` with root sign `ζ`. -/
def chainSpecial : RegChain → ℤˣ → (Fin w × Path) → List (Fin w × Path)
  | .nil, _, _ => []
  | .pair m Qr Qg inner rest, ζ, a =>
    (if inner.isNil then [a] else []) ++
    ((if slotSign ζ m.red.1 = 1 then
        cplSpecial Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else cplSpecial Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ++
    (if slotSign ζ m.green.1 = 1 then
        cplSpecial Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else
        cplSpecial Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ++
    chainSpecial inner (slotSign ζ m.c) (addrExt a [m.c]) ++
    chainSpecial rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])))
end

mutual
/-- The special candidates are chosen nodes, in the order of `𝒩^ch`. -/
theorem cplSpecial_sublist : (Q : RegCpl) → (a b : Fin w × Path) →
    (cplSpecial Q a b).Sublist ((Q.linksAt a b).map Prod.fst)
  | .triv, _, _ => by simp [cplSpecial, RegCpl.linksAt]
  | .type1 c Q₁ Q₂ Q₃, a, b => by
    simp only [cplSpecial, RegCpl.linksAt, List.map_cons, List.map_append]
    exact List.Sublist.cons _ (((cplSpecial_sublist Q₁ _ _).append
      (cplSpecial_sublist Q₂ _ _)).append (cplSpecial_sublist Q₃ _ _))
  | .type2 Xp Xm Qlp, a, b => by
    simp only [cplSpecial, RegCpl.linksAt, List.map_append]
    exact ((chainSpecial_sublist Xp _ _).append (chainSpecial_sublist Xm _ _)).append
      (cplSpecial_sublist Qlp _ _)

theorem chainSpecial_sublist : (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) →
    (chainSpecial X ζ a).Sublist ((X.linksAt ζ a).map Prod.fst)
  | .nil, _, _ => by simp [chainSpecial, RegChain.linksAt]
  | .pair m Qr Qg inner rest, ζ, a => by
    have hr : (if slotSign ζ m.red.1 = 1 then
        cplSpecial Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else cplSpecial Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
        ).Sublist ((if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
        ).map Prod.fst) := by
      split_ifs <;> exact cplSpecial_sublist Qr _ _
    have hg : (if slotSign ζ m.green.1 = 1 then
        cplSpecial Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else
        cplSpecial Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
        ).Sublist ((if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else
        Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
        ).map Prod.fst) := by
      split_ifs <;> exact cplSpecial_sublist Qg _ _
    have hrest := (((hr.append hg).append
      (chainSpecial_sublist inner (slotSign ζ m.c) (addrExt a [m.c]))).append
      (chainSpecial_sublist rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))))
    simp only [chainSpecial, RegChain.linksAt, List.map_cons, List.map_append]
    by_cases hn : inner.isNil = true
    · simp only [hn, ↓reduceIte]
      exact List.Sublist.cons_cons _ hrest
    · simp only [hn, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      exact List.Sublist.cons _ hrest
end

theorem lonePath_eq_nil_iff (X : RegChain) : X.lonePath = [] ↔ X.isNil = true := by
  cases X with
  | nil => simp [RegChain.lonePath, RegChain.isNil]
  | pair m Qr Qg inner rest => simp [RegChain.lonePath, RegChain.isNil]

theorem addrExt_inj {a : Fin w × Path} {p q : Path} (h : addrExt a p = addrExt a q) : p = q := by
  simpa [addrExt] using congrArg Prod.snd h

mutual
/-- **The two definitions of special nodes agree, couples**: a node is a recursive special
candidate iff it is linked with one of its children (needs only that the two roots are
independent). -/
theorem mem_cplSpecial_iff : (Q : RegCpl) → (a b : Fin w × Path) → Indep a b →
    ∀ z, z ∈ cplSpecial Q a b ↔ ∃ i : Fin 3, (z, addrExt z [i]) ∈ Q.linksAt a b
  | .triv, _, _, _, z => by simp [cplSpecial, RegCpl.linksAt]
  | .type1 c Q₁ Q₂ Q₃, a, b, h, z => by
    have h₁ := mem_cplSpecial_iff Q₁ (addrExt a [0]) (addrExt b [c.partner 0])
      (h.ext _ _) z
    have h₂ := mem_cplSpecial_iff Q₂ (addrExt b [1]) (addrExt a [1]) (h.symm.ext _ _) z
    have h₃ := mem_cplSpecial_iff Q₃ (addrExt a [2]) (addrExt b [c.partner 2])
      (h.ext _ _) z
    simp only [cplSpecial, RegCpl.linksAt, List.mem_append, List.mem_cons]
    rw [h₁, h₂, h₃]
    constructor
    · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | ⟨i, hi⟩)
      · exact ⟨i, Or.inr (Or.inl (Or.inl hi))⟩
      · exact ⟨i, Or.inr (Or.inl (Or.inr hi))⟩
      · exact ⟨i, Or.inr (Or.inr hi)⟩
    · rintro ⟨i, hi | (hi | hi) | hi⟩
      · simp only [Prod.mk.injEq] at hi
        obtain ⟨rfl, hb⟩ := hi
        exact absurd (hb ▸ under_ext z [i]) h.1
      · exact Or.inl (Or.inl ⟨i, hi⟩)
      · exact Or.inl (Or.inr ⟨i, hi⟩)
      · exact Or.inr ⟨i, hi⟩
  | .type2 Xp Xm Qlp, a, b, h, z => by
    have hp := mem_chainSpecial_iff Xp 1 a z
    have hm := mem_chainSpecial_iff Xm (-1) b z
    have hl := mem_cplSpecial_iff Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)
      (h.ext _ _) z
    simp only [cplSpecial, RegCpl.linksAt, List.mem_append]
    rw [hp, hm, hl]
    constructor
    · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | ⟨i, hi⟩)
      · exact ⟨i, Or.inl (Or.inl hi)⟩
      · exact ⟨i, Or.inl (Or.inr hi)⟩
      · exact ⟨i, Or.inr hi⟩
    · rintro ⟨i, (hi | hi) | hi⟩
      · exact Or.inl (Or.inl ⟨i, hi⟩)
      · exact Or.inl (Or.inr ⟨i, hi⟩)
      · exact Or.inr ⟨i, hi⟩

/-- **The two definitions of special nodes agree, chains.** -/
theorem mem_chainSpecial_iff : (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) →
    ∀ z, z ∈ chainSpecial X ζ a ↔ ∃ i : Fin 3, (z, addrExt z [i]) ∈ X.linksAt ζ a
  | .nil, _, _, z => by simp [chainSpecial, RegChain.linksAt]
  | .pair m Qr Qg inner rest, ζ, a, z => by
    have hr : z ∈ (if slotSign ζ m.red.1 = 1 then
        cplSpecial Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else cplSpecial Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))
        ↔ ∃ i : Fin 3, (z, addrExt z [i]) ∈ (if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) := by
      split_ifs
      · exact mem_cplSpecial_iff Qr _ _ (indep_red m _ a) z
      · exact mem_cplSpecial_iff Qr _ _ (indep_red m _ a).symm z
    have hg : z ∈ (if slotSign ζ m.green.1 = 1 then
        cplSpecial Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else
        cplSpecial Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]))
        ↔ ∃ i : Fin 3, (z, addrExt z [i]) ∈ (if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else
        Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) := by
      split_ifs
      · exact mem_cplSpecial_iff Qg _ _ (indep_green m _ a) z
      · exact mem_cplSpecial_iff Qg _ _ (indep_green m _ a).symm z
    have hi := mem_chainSpecial_iff inner (slotSign ζ m.c) (addrExt a [m.c]) z
    have hs := mem_chainSpecial_iff rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) z
    have hhead : (z ∈ (if inner.isNil then [a] else [])) ↔ ∃ i : Fin 3,
        (z, addrExt z [i]) = (a, addrExt a ([m.c] ++ inner.lonePath)) := by
      constructor
      · intro hz
        split_ifs at hz with hn
        · rw [List.mem_singleton] at hz
          subst hz
          refine ⟨m.c, ?_⟩
          rw [(lonePath_eq_nil_iff inner).2 hn]
          rfl
        · simp at hz
      · rintro ⟨i, he⟩
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, he⟩ := he
        have hp := addrExt_inj he
        have hl : inner.lonePath = [] := by
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at hp
          exact hp.2.symm
        simp only [(lonePath_eq_nil_iff inner).1 hl, ↓reduceIte]
        exact List.mem_singleton_self _
    simp only [chainSpecial, RegChain.linksAt, List.mem_append, List.mem_cons]
    rw [hhead, hr, hg, hi, hs]
    constructor
    · rintro (⟨i, he⟩ | ((⟨i, h1⟩ | ⟨i, h1⟩) | ⟨i, h1⟩) | ⟨i, h1⟩)
      · exact ⟨i, Or.inl he⟩
      · exact ⟨i, Or.inr (Or.inl (Or.inl (Or.inl h1)))⟩
      · exact ⟨i, Or.inr (Or.inl (Or.inl (Or.inr h1)))⟩
      · exact ⟨i, Or.inr (Or.inl (Or.inr h1))⟩
      · exact ⟨i, Or.inr (Or.inr h1)⟩
    · rintro ⟨i, he | (((h1 | h1) | h1) | h1)⟩
      · exact Or.inl ⟨i, he⟩
      · exact Or.inr (Or.inl (Or.inl (Or.inl ⟨i, h1⟩)))
      · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨i, h1⟩)))
      · exact Or.inr (Or.inl (Or.inr ⟨i, h1⟩))
      · exact Or.inr (Or.inr ⟨i, h1⟩)
end

theorem indep_roots2 : Indep ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) :=
  ⟨fun h => by simp [Under] at h, fun h => by simp [Under] at h⟩

/-- **Special subsets of a couple: TARGET's definition = DH21's recursive definition.** -/
theorem isSpecialSet_iff (Q : RegCpl) (Z : Finset (Fin 2 × Path)) :
    IsSpecialSet Q.links Z ↔ ∀ z ∈ Z, z ∈ cplSpecial Q (0, []) (1, []) := by
  unfold IsSpecialSet
  exact forall₂_congr fun z _ => (mem_cplSpecial_iff Q _ _ indep_roots2 z).symm

/-- **Special subsets of a tree: TARGET's definition = the recursive definition.** -/
theorem tree_isSpecialSet_iff (X : RegChain) (ζ : ℤˣ) (Z : Finset (Fin 1 × Path)) :
    IsSpecialSet (X.treeLinks ζ) Z ↔ ∀ z ∈ Z, z ∈ chainSpecial X ζ (0, []) := by
  unfold IsSpecialSet
  exact forall₂_congr fun z _ => (mem_chainSpecial_iff X ζ _ z).symm

theorem chosenSet_of_special {L : List ((Fin w × Path) × (Fin w × Path))}
    {Z : Finset (Fin w × Path)} (h : IsSpecialSet L Z) : Z ⊆ chosenSet L := by
  intro z hz
  obtain ⟨i, hi⟩ := h z hz
  exact List.mem_toFinset.2 (List.mem_map.2 ⟨_, hi, rfl⟩)

theorem mem_specialSets_iff' {L : List ((Fin w × Path) × (Fin w × Path))}
    (Z : Finset (Fin w × Path)) : Z ∈ specialSets L ↔ IsSpecialSet L Z := by
  unfold specialSets
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨chosenSet_of_special h, h⟩⟩

/-- `Z ∈ specialSets 𝒬` iff every element of `Z` is a recursive special candidate. -/
theorem mem_specialSets_iff (Q : RegCpl) (Z : Finset (Fin 2 × Path)) :
    Z ∈ specialSets Q.links ↔ ∀ z ∈ Z, z ∈ cplSpecial Q (0, []) (1, []) := by
  rw [mem_specialSets_iff', isSpecialSet_iff]

theorem tree_mem_specialSets_iff (X : RegChain) (ζ : ℤˣ) (Z : Finset (Fin 1 × Path)) :
    Z ∈ specialSets (X.treeLinks ζ) ↔ ∀ z ∈ Z, z ∈ chainSpecial X ζ (0, []) := by
  rw [mem_specialSets_iff', tree_isSpecialSet_iff]

/-- The special candidates of a couple have no repetition. -/
theorem specialList_nodup (Q : RegCpl) :
    (cplSpecial Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))).Nodup :=
  (cplSpecial_sublist Q _ _).nodup (chosen_nodup Q)

theorem tree_specialList_nodup (X : RegChain) (ζ : ℤˣ) :
    (chainSpecial X ζ ((0 : Fin 1), ([] : Path))).Nodup :=
  (chainSpecial_sublist X ζ _).nodup (tree_chosen_nodup X ζ)

end WaveTurbulence.Links
