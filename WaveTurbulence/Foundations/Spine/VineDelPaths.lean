/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineExpansionInvariant
public import WaveTurbulence.Foundations.Molecule.VineInsertionPaths
public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
import Mathlib.Tactic
/-! # Filtered vertex-predicate paths in vine templates and rung insertion -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Vine

/-- Adjacency through edges accepted by `f`, between vertices satisfying `P`. -/
@[expose] def FAdj (P : ℕ → Prop) (f : ℕ × ℕ → Bool) (es : List (ℕ × ℕ)) (u v : ℕ) : Prop :=
  P u ∧ P v ∧ (((u, v) ∈ es ∧ f (u, v) = true) ∨ ((v, u) ∈ es ∧ f (v, u) = true))

theorem fpath_mono {P Q : ℕ → Prop} {f g : ℕ × ℕ → Bool} {es fs : List (ℕ × ℕ)}
    (hPQ : ∀ x, P x → Q x) (hfg : ∀ e, f e = true → g e = true)
    (h : ∀ e ∈ es, e ∈ fs) {u v : ℕ} (hp : Relation.EqvGen (FAdj P f es) u v) :
    Relation.EqvGen (FAdj Q g fs) u v := by
  induction hp with
  | rel u v huv =>
    refine Relation.EqvGen.rel _ _ ⟨hPQ _ huv.1, hPQ _ huv.2.1, ?_⟩
    rcases huv.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h _ h1, hfg _ h2⟩
    · exact Or.inr ⟨h _ h1, hfg _ h2⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem fpath_edge {P : ℕ → Prop} {f : ℕ × ℕ → Bool} {es : List (ℕ × ℕ)} {u v : ℕ}
    (hu : P u) (hv : P v) (h : (u, v) ∈ es) (hf : f (u, v) = true) :
    Relation.EqvGen (FAdj P f es) u v :=
  Relation.EqvGen.rel _ _ ⟨hu, hv, Or.inl ⟨h, hf⟩⟩

theorem rail_fpath (P : ℕ → Prop) (f : ℕ × ℕ → Bool) (b : ℕ) (ws : List ℕ) :
    ∀ (a : ℕ), P a → P b → (∀ x ∈ ws, P x) → (∀ e ∈ railBonds a ws b, f e = true) →
    Relation.EqvGen (FAdj P f (railBonds a ws b)) a b := by
  induction ws with
  | nil =>
    intro a ha hb _ hf
    exact fpath_edge ha hb (List.mem_singleton_self _) (hf _ (List.mem_singleton_self _))
  | cons w ws ih =>
    intro a ha hb hw hf
    have heq : railBonds a (w :: ws) b = (a, w) :: railBonds w ws b := rfl
    rw [heq] at hf ⊢
    have hwP := hw w List.mem_cons_self
    refine Relation.EqvGen.trans _ _ _
      (fpath_edge ha hwP List.mem_cons_self (hf _ List.mem_cons_self))
      (fpath_mono (fun _ h => h) (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h)
        (ih w hwP hb (fun x hx => hw x (List.mem_cons_of_mem _ hx))
          (fun e he => hf e (List.mem_cons_of_mem _ he))))

theorem rail_fprefix (P : ℕ → Prop) (f : ℕ × ℕ → Bool) (b : ℕ) (ws : List ℕ) :
    ∀ (a : ℕ), P a → (∀ x ∈ ws, P x) → (∀ e ∈ railBonds a ws b, f e = true) →
    ∀ v ∈ ws, Relation.EqvGen (FAdj P f (railBonds a ws b)) a v := by
  induction ws with
  | nil => intro a _ _ _ v hv; exact absurd hv (List.not_mem_nil)
  | cons w ws ih =>
    intro a ha hw hf v hv
    have heq : railBonds a (w :: ws) b = (a, w) :: railBonds w ws b := rfl
    rw [heq] at hf ⊢
    have hwP := hw w List.mem_cons_self
    have he := fpath_edge (f := f) ha hwP (List.mem_cons_self (a := (a, w))
      (l := railBonds w ws b)) (hf _ List.mem_cons_self)
    rcases List.mem_cons.mp hv with rfl | hv
    · exact he
    · exact Relation.EqvGen.trans _ _ _ he
        (fpath_mono (fun _ h => h) (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h)
          (ih w hwP (fun x hx => hw x (List.mem_cons_of_mem _ hx))
            (fun e he => hf e (List.mem_cons_of_mem _ he)) v hv))

theorem rail_fsuffix (P : ℕ → Prop) (f : ℕ × ℕ → Bool) (b : ℕ) (ws : List ℕ) :
    ∀ (a : ℕ), P b → (∀ x ∈ ws, P x) → (∀ e ∈ railBonds a ws b, f e = true) →
    ∀ v ∈ ws, Relation.EqvGen (FAdj P f (railBonds a ws b)) v b := by
  induction ws with
  | nil => intro a _ _ _ v hv; exact absurd hv (List.not_mem_nil)
  | cons w ws ih =>
    intro a hb hw hf v hv
    have heq : railBonds a (w :: ws) b = (a, w) :: railBonds w ws b := rfl
    rw [heq] at hf ⊢
    have hwP := hw w List.mem_cons_self
    have hws := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    have hf' := fun e he => hf e (List.mem_cons_of_mem _ he)
    rcases List.mem_cons.mp hv with rfl | hv
    · exact fpath_mono (fun _ h => h) (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h)
        (rail_fpath P f b ws v hwP hb hws hf')
    · exact fpath_mono (fun _ h => h) (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h)
        (ih w hb hws hf' v hv)

theorem railBonds_new (a b : ℕ) (ws : List ℕ) (hws : ws ≠ []) :
    ∀ e ∈ railBonds a ws b, e.1 ∈ ws ∨ e.2 ∈ ws := by
  induction ws generalizing a with
  | nil => exact absurd rfl hws
  | cons w ws ih =>
    intro e he
    have heq : railBonds a (w :: ws) b = (a, w) :: railBonds w ws b := rfl
    rw [heq] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact Or.inr List.mem_cons_self
    · by_cases hw : ws = []
      · subst hw
        have : railBonds w [] b = [(w, b)] := rfl
        rw [this] at he
        rw [List.mem_singleton.mp he]
        exact Or.inl List.mem_cons_self
      · rcases ih w hw e he with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (List.mem_cons_of_mem _ h)

end WaveTurbulence.LGSpine
