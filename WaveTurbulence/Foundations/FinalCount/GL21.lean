/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL20
/-! **G3-LOWDEG (R48), part 21: vines have no loops.**  The expanded vine templates `X.expand k` have no bond `(i, i)`; hence an atom of a
vine, VC (a chain of vines) or of the adjoint of a hyper-object carries no self-loop. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

/-- Consecutive distinctness of a rail. -/
def railOK : ℕ → List ℕ → ℕ → Prop
  | z, [], z' => z ≠ z'
  | z, w :: ws, z' => z ≠ w ∧ railOK w ws z'

theorem railBonds_ne : ∀ (ws : List ℕ) (z z' : ℕ), railOK z ws z' → ∀ p ∈ railBonds z ws z', p.1 ≠ p.2
  | [], z, z', h, p, hp => by
    have : p = (z, z') := by simpa [railBonds] using hp
    subst this; exact h
  | w :: ws, z, z', h, p, hp => by
    have e : railBonds z (w :: ws) z' = (z, w) :: railBonds w ws z' := by
      simp [railBonds, List.zip_cons_cons]
    rw [e] at hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact railBonds_ne ws w z' h.2 p hp

theorem railOK_range : ∀ (k m z z' : ℕ), z < m → z' < m → railOK z ((List.range (k + 1)).map (m + ·)) z'
  | 0, m, z, z', hz, hz' => by
    simp [List.range_succ, railOK]
    omega
  | k + 1, m, z, z', hz, hz' => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine ⟨by omega, ?_⟩
    have := railOK_range k (m + 1) (m + 0) z' (by omega) (by omega)
    convert this using 2
    funext i; simp [Function.comp]; omega

/-- The slots lie below the atom count and the bonds have distinct ends. -/
def TplOK (T : VineTemplate) : Prop :=
  (∀ p ∈ T.bonds, p.1 ≠ p.2) ∧ ∀ s ∈ T.slots, s.1.1 < T.n ∧ s.1.2 < T.n ∧ s.2.1 < T.n ∧ s.2.2 < T.n

theorem tplOK_insertRungs {T : VineTemplate} (hT : TplOK T) {slot : (ℕ × ℕ) × (ℕ × ℕ)} (hs : slot ∈ T.slots) (k : ℕ) :
    TplOK (insertRungs T slot k) := by
  unfold insertRungs
  by_cases hk : k = 0
  · simpa [hk] using hT
  rw [if_neg hk]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h1, h2, h3, h4⟩ := hT.2 slot hs
  refine ⟨?_, fun s hs' => ?_⟩
  · intro p hp
    simp only [List.mem_append] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · exact hT.1 p (List.mem_of_mem_erase (List.mem_of_mem_erase hp))
    · exact railBonds_ne _ _ _ (railOK_range k' T.n _ _ h1 h2) p hp
    · exact railBonds_ne _ _ _ (railOK_range k' (T.n + (k' + 1)) _ _ (by omega) (by omega)) p hp
    · simp only [List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hp
      obtain ⟨q, hq, hq'⟩ := hp
      have hq2 := List.of_mem_zip hq
      simp only [List.mem_map, List.mem_range] at hq2
      obtain ⟨⟨i, hi, hi'⟩, ⟨j, hj, hj'⟩⟩ := hq2
      have hpq : p = q := by rcases hq' with h | h <;> exact h
      rw [hpq]
      show q.1 ≠ q.2
      omega
  · have := hT.2 s hs'
    simp only
    omega

theorem tplOK_template (X : VineType) : TplOK X.template := by
  unfold TplOK
  cases X <;> decide

theorem tplOK_foldl : ∀ (l : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) (T : VineTemplate), TplOK T →
    (∀ sk ∈ l, sk.1 ∈ T.slots) →
    TplOK (l.foldl (fun T sk => insertRungs T sk.1 sk.2) T) ∧
      (l.foldl (fun T sk => insertRungs T sk.1 sk.2) T).slots = T.slots
  | [], T, hT, _ => ⟨hT, rfl⟩
  | sk :: l, T, hT, hs => by
    have h1 : TplOK (insertRungs T sk.1 sk.2) := tplOK_insertRungs hT (hs sk (List.mem_cons_self)) _
    have h2 : (insertRungs T sk.1 sk.2).slots = T.slots := by
      unfold insertRungs; split_ifs <;> rfl
    have := tplOK_foldl l (insertRungs T sk.1 sk.2) h1 (fun sk' hsk' => by rw [h2]; exact hs sk' (List.mem_cons_of_mem _ hsk'))
    exact ⟨this.1, this.2.trans h2⟩

theorem expand_noLoop (X : VineType) (k : List ℕ) : ∀ p ∈ (X.expand k).bonds, p.1 ≠ p.2 := by
  unfold VineType.expand
  exact (tplOK_foldl _ _ (tplOK_template X) (fun sk hsk => (List.of_mem_zip hsk).1)).1.1

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

theorem isVine_noLoop {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (h : M.IsVine X S a b) :
    ∀ y : D, M.atom y ∈ S → M.atom y ≠ M.atom (M.mate y) := by
  intro y hy hloop
  obtain ⟨-, k, -, f, -, -, -, hbd⟩ := h
  obtain ⟨y', hy'o, hy'a, hy'm⟩ : ∃ y' : D, M.out y' = true ∧ M.atom y' = M.atom y ∧ M.atom (M.mate y') = M.atom y := by
    by_cases ho : M.out y = true
    · exact ⟨y, ho, rfl, hloop.symm⟩
    · refine ⟨M.mate y, ?_, hloop.symm, by rw [M.mate_mate]⟩
      have := M.out_mate y
      simp only [Bool.not_eq_true] at ho
      rw [this, ho]; rfl
  have hmem : (s(M.atom y, M.atom y) : Sym2 V) ∈ M.groupBonds S := by
    unfold Molecule.groupBonds
    refine Multiset.mem_map.2 ⟨y', ?_, ?_⟩
    · simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hy'o, by rw [hy'a]; exact hy, by rw [hy'm]; exact hy⟩
    · simp [Molecule.ends, hy'a, hy'm]
  have h2 : Sym2.map f s(M.atom y, M.atom y) ∈ (M.groupBonds S).map (Sym2.map f) := Multiset.mem_map_of_mem _ hmem
  rw [hbd] at h2
  obtain ⟨p, hp, hpe⟩ := List.mem_map.1 (Multiset.mem_coe.1 h2)
  rw [Sym2.map_mk] at hpe
  have := Sym2.eq_iff.1 hpe
  have hne := expand_noLoop X k p hp
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hne (h1.trans h2.symm)

theorem chain_noLoop {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) :
    ∀ y : D, M.atom y ∈ S → M.atom y ≠ M.atom (M.mate y) := by
  induction h with
  | single h =>
    obtain ⟨X, hX⟩ := h
    exact isVine_noLoop hX
  | append hc hv hinter hne ih =>
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · exact ih y h
    · obtain ⟨X, hX⟩ := hv
      exact isVine_noLoop hX y h

theorem isVC_noLoop {M : Molecule V D} {S : Finset V} {a b : V} (h : IsVC M S a b) :
    ∀ y : D, M.atom y ∈ S → M.atom y ≠ M.atom (M.mate y) := by
  obtain ⟨-, n, hn⟩ := h
  exact chain_noLoop hn

end WaveTurbulence.FinalCountG3
