/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5Bad
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PostFacts
import Mathlib.Tactic

/-! # Prop 9.6, case (5): lifting a cut of the post molecule of a two-exit removal -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}

/-- The dart of `N` corresponding to a dart of the post molecule (the new bond stands for the chain). -/
def liftDart (T : TwoExit N) : Degen.RetainedDart N T.Y ⊕ Bool → D
  | Sum.inl z => z.val
  | Sum.inr true => N.mate T.y
  | Sum.inr false => N.mate T.x

theorem liftDart_atom (T : TwoExit N) (e : Degen.RetainedDart N T.Y ⊕ Bool) :
    N.atom (liftDart T e) = T.post.atom e := by
  rcases e with z | b
  · rfl
  · cases b <;> rfl

theorem liftDart_out (T : TwoExit N) (e : Degen.RetainedDart N T.Y ⊕ Bool) :
    N.out (liftDart T e) = T.post.out e := by
  rcases e with z | b
  · rfl
  · cases b
    · change N.out (N.mate T.x) = false
      rw [N.out_mate, T.out_x]; rfl
    · change N.out (N.mate T.y) = true
      rw [N.out_mate, T.out_y]; rfl

theorem liftDart_inj (T : TwoExit N) : Function.Injective (liftDart T) := by
  intro e e' h
  rcases e with z | b <;> rcases e' with z' | b'
  · exact congrArg Sum.inl (Subtype.ext h)
  · exfalso
    have hz := z.2.2
    cases b'
    · change z.val = N.mate T.x at h
      rw [h, N.mate_mate] at hz; exact hz T.atom_x
    · change z.val = N.mate T.y at h
      rw [h, N.mate_mate] at hz; exact hz T.atom_y
  · exfalso
    have hz := z'.2.2
    cases b
    · change N.mate T.x = z'.val at h
      rw [← h, N.mate_mate] at hz; exact hz T.atom_x
    · change N.mate T.y = z'.val at h
      rw [← h, N.mate_mate] at hz; exact hz T.atom_y
  · cases b <;> cases b'
    · rfl
    · exact absurd (Mole.mate_injective N h) T.ne
    · exact absurd (Mole.mate_injective N h) T.ne.symm
    · rfl

/-- The exit darts `x`, `y` are not lifts. -/
theorem exit_not_lift (T : TwoExit N) (e : Degen.RetainedDart N T.Y ⊕ Bool) :
    liftDart T e ≠ T.x ∧ liftDart T e ≠ T.y := by
  have hx : N.atom T.x ∈ T.Y := T.atom_x
  have hy : N.atom T.y ∈ T.Y := T.atom_y
  have hnot : N.atom (liftDart T e) ∉ T.Y := by
    rw [liftDart_atom]
    have : T.post.atom e ∈ T.post.atoms := T.post.atom_mem e
    rw [T.post_atoms] at this
    exact (mem_sdiff.mp this).2
  exact ⟨fun h => hnot (h ▸ hx), fun h => hnot (h ▸ hy)⟩


/-- **Lifting a cut of the post molecule to `N`.** If the new atom is separated from `v` in the cut of `T.post`, the
corresponding cut of `N` (same darts) separates `v` from the new atom, and its component of `v` (outside `Y`) lies in
the component of `v` of the cut of `T.post`. -/
theorem cut_lift_post (T : TwoExit N) {v v₂ v₂' : V} {x₁ x₂ : Degen.RetainedDart N T.Y ⊕ Bool}
    (hc : T.post.IsCutData v v₂ x₁ x₂) (hsep : ¬ (T.post.cut v v₂ x₁ x₂).SameComponent v v₂)
    (hv₂' : v₂' ∉ N.atoms) :
    N.IsCutData v v₂' (liftDart T x₁) (liftDart T x₂) ∧
      ¬ (N.cut v v₂' (liftDart T x₁) (liftDart T x₂)).SameComponent v v₂' ∧
      ∀ u ∈ N.atoms, u ∉ T.Y → (N.cut v v₂' (liftDart T x₁) (liftDart T x₂)).SameComponent v u →
        (T.post.cut v v₂ x₁ x₂).SameComponent v u := by
  classical
  set P := T.post with hP
  set KP := P.cut v v₂ x₁ x₂ with hKP
  set KN := N.cut v v₂' (liftDart T x₁) (liftDart T x₂) with hKN
  have hvP : v ∈ N.atoms \ T.Y := by rw [← T.post_atoms]; exact hc.1
  have hvY : v ∉ T.Y := (mem_sdiff.mp hvP).2
  have hY : ∀ y ∈ T.Y, y ∈ N.atoms := fun y hy => T.sub hy
  have hv₂'Y : v₂' ∉ T.Y := fun h => hv₂' (T.sub h)
  have hmateL : ∀ z : Degen.RetainedDart N T.Y, liftDart T (P.mate (Sum.inl z)) = N.mate (liftDart T (Sum.inl z)) :=
    fun z => rfl
  have hcN : N.IsCutData v v₂' (liftDart T x₁) (liftDart T x₂) := by
    refine ⟨(mem_sdiff.mp hvP).1, hv₂', by rw [liftDart_atom]; exact hc.2.2.1, by rw [liftDart_atom]; exact hc.2.2.2.1,
      ?_, by rw [liftDart_out]; exact hc.2.2.2.2.2.1, by rw [liftDart_out]; exact hc.2.2.2.2.2.2⟩
    intro h
    rcases x₁ with z | b
    · apply hc.2.2.2.2.1
      apply liftDart_inj T
      rw [h]; rfl
    · cases b
      · change liftDart T x₂ = N.mate (N.mate T.x) at h
        rw [N.mate_mate] at h; exact (exit_not_lift T x₂).1 h
      · change liftDart T x₂ = N.mate (N.mate T.y) at h
        rw [N.mate_mate] at h; exact (exit_not_lift T x₂).2 h
  -- the fold map
  set ct : V := KP.atom (Sum.inr false) with hct
  let ψ : V → V := fun a => if a ∈ T.Y then ct else if a = v₂' then v₂ else a
  have hψrange : ∀ e, ψ (KN.atom (liftDart T e)) = KP.atom e := by
    intro e
    have h1 : KN.atom (liftDart T e) = if (P.atom e = v ∧ e ≠ x₁ ∧ e ≠ x₂) then v₂' else P.atom e := by
      change (if (N.atom (liftDart T e) = v ∧ liftDart T e ≠ liftDart T x₁ ∧ liftDart T e ≠ liftDart T x₂)
        then v₂' else N.atom (liftDart T e)) = _
      rw [liftDart_atom]
      have hiff : (P.atom e = v ∧ liftDart T e ≠ liftDart T x₁ ∧ liftDart T e ≠ liftDart T x₂) ↔
          (P.atom e = v ∧ e ≠ x₁ ∧ e ≠ x₂) :=
        ⟨fun ⟨a, b, c⟩ => ⟨a, fun h => b (by rw [h]), fun h => c (by rw [h])⟩,
         fun ⟨a, b, c⟩ => ⟨a, fun h => b (liftDart_inj T h), fun h => c (liftDart_inj T h)⟩⟩
      by_cases hh : P.atom e = v ∧ e ≠ x₁ ∧ e ≠ x₂
      · rw [if_pos hh, if_pos (hiff.mpr hh)]
      · rw [if_neg hh, if_neg (fun h' => hh (hiff.mp h'))]
    have h2 : KP.atom e = if (P.atom e = v ∧ e ≠ x₁ ∧ e ≠ x₂) then v₂ else P.atom e := rfl
    rw [h1, h2]
    by_cases hh : P.atom e = v ∧ e ≠ x₁ ∧ e ≠ x₂
    · rw [if_pos hh, if_pos hh]; simp only [ψ, hv₂'Y, if_false, if_true]
    · rw [if_neg hh, if_neg hh]
      have hmem : P.atom e ∈ N.atoms \ T.Y := by rw [← T.post_atoms]; exact P.atom_mem e
      simp only [ψ, (mem_sdiff.mp hmem).2, if_false]
      rw [if_neg (fun h => hv₂' (by rw [← h]; exact (mem_sdiff.mp hmem).1))]
  have hfold : ∀ a b, KN.SameComponent a b → KP.SameComponent (ψ a) (ψ b) := by
    intro a b h
    induction h with
    | rel a b hab =>
      obtain ⟨z, rfl, rfl⟩ := hab
      have hKNat : ∀ w, N.atom w ∈ T.Y → KN.atom w = N.atom w := by
        intro w hw
        change (if _ then _ else _) = _
        rw [if_neg]
        rintro ⟨h1, _⟩; exact hvY (h1 ▸ hw)
      have hψY : ∀ w, N.atom w ∈ T.Y → ψ (KN.atom w) = ct := by
        intro w hw; rw [hKNat w hw]; simp only [ψ, hw, if_true]
      rcases T.dart_cases z with h | h | rfl | rfl | rfl | rfl
      · rw [hψY z h.1]
        have := hKNat (N.mate z) h.2
        change KP.SameComponent _ (ψ (KN.atom (N.mate z)))
        rw [hψY _ h.2]; exact Relation.EqvGen.refl _
      · have hz : z = liftDart T (Sum.inl ⟨z, h.1, h.2⟩) := rfl
        have hm : N.mate z = liftDart T (P.mate (Sum.inl ⟨z, h.1, h.2⟩)) := rfl
        rw [hz, hψrange]
        change KP.SameComponent _ (ψ (KN.atom (N.mate (liftDart T (Sum.inl ⟨z, h.1, h.2⟩)))))
        rw [← hmateL, hψrange]
        exact Relation.EqvGen.rel _ _ ⟨Sum.inl ⟨z, h.1, h.2⟩, rfl, rfl⟩
      · -- z = T.x
        rw [hψY _ T.atom_x]
        have : N.mate T.x = liftDart T (Sum.inr false) := rfl
        change KP.SameComponent _ (ψ (KN.atom (N.mate T.x)))
        rw [this, hψrange]; exact Relation.EqvGen.refl _
      · -- z = T.y
        rw [hψY _ T.atom_y]
        have : N.mate T.y = liftDart T (Sum.inr true) := rfl
        change KP.SameComponent _ (ψ (KN.atom (N.mate T.y)))
        rw [this, hψrange]
        exact Relation.EqvGen.rel _ _ ⟨Sum.inr false, rfl, rfl⟩
      · -- z = mate x
        have : N.mate T.x = liftDart T (Sum.inr false) := rfl
        change KP.SameComponent (ψ (KN.atom (N.mate T.x))) (ψ (KN.atom (N.mate (N.mate T.x))))
        rw [N.mate_mate, this, hψrange, hψY _ T.atom_x]; exact Relation.EqvGen.refl _
      · have : N.mate T.y = liftDart T (Sum.inr true) := rfl
        change KP.SameComponent (ψ (KN.atom (N.mate T.y))) (ψ (KN.atom (N.mate (N.mate T.y))))
        rw [N.mate_mate, this, hψrange, hψY _ T.atom_y]
        exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨Sum.inr false, rfl, rfl⟩)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have hψv : ψ v = v := by
    simp only [ψ, hvY, if_false]
    rw [if_neg (fun h => hv₂' (by rw [← h]; exact (mem_sdiff.mp hvP).1))]
  refine ⟨hcN, ?_, ?_⟩
  · intro hsame
    have := hfold _ _ hsame
    have hψv₂ : ψ v₂' = v₂ := by simp only [ψ, hv₂'Y, if_false, if_true]
    rw [hψv, hψv₂] at this
    exact hsep this
  · intro u hu huY hsame
    have := hfold _ _ hsame
    have hψu : ψ u = u := by
      simp only [ψ, huY, if_false]
      rw [if_neg (fun h => hv₂' (by rw [← h]; exact hu))]
    rw [hψv, hψu] at this
    exact this


/-- **The post molecule of a chain contraction after an erasure has no `β`-cut** (S2). -/
theorem not_bad_post (M : Molecule V D) (Ka : Finset V)
    (hconn : ∀ u ∈ M.atoms, ∀ w ∈ M.atoms, M.SameComponent u w)
    (T : TwoExit (Degen.eraseAtoms M Ka))
    (hconnP : ∀ u ∈ T.post.atoms, ∀ w ∈ T.post.atoms, T.post.SameComponent u w)
    (hfr : ∃ w, w ∉ M.atoms) (hdeg4 : ∀ u ∈ T.post.atoms, M.deg u = 4)
    (hYdeg : ∀ u ∈ T.Y, (Degen.eraseAtoms M Ka).deg u = M.deg u)
    (hNB : ∀ v ∈ T.post.atoms, ∀ v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ → M.IsAlphaCut v v₂ x₁ x₂) :
    ¬ HasBadBetaCut T.post := by
  classical
  rintro ⟨v, v₂, x₁, x₂, hc, hna, hdeg⟩
  obtain ⟨v₂', hv₂'⟩ := hfr
  have hsepP := not_sameComponent_of_not_alpha _ hconnP hc hna
  have hv₂'N : v₂' ∉ (Degen.eraseAtoms M Ka).atoms := fun h => hv₂' (mem_sdiff.mp h).1
  obtain ⟨hcN, hsepN, hrel⟩ := cut_lift_post T hc hsepP hv₂'N
  have hdegN : ∀ u ∈ (Degen.eraseAtoms M Ka).atoms,
      ((Degen.eraseAtoms M Ka).cut v v₂' (liftDart T x₁) (liftDart T x₂)).SameComponent v u → u ≠ v →
      (Degen.eraseAtoms M Ka).deg u = M.deg u := by
    intro u hu hsame hne
    by_cases huY : u ∈ T.Y
    · exact hYdeg u huY
    · have huP : u ∈ T.post.atoms := by rw [T.post_atoms]; exact mem_sdiff.mpr ⟨hu, huY⟩
      have h1 := hdeg u (by change u ∈ insert v₂ _; exact mem_insert_of_mem huP) (hrel u hu huY hsame) hne
      have hu2 : u ≠ v₂ := fun h => hc.2.1 (h ▸ huP)
      have h2 : (T.post.cut v v₂ x₁ x₂).deg u = T.post.deg u := cut_deg_of_ne' _ hne hu2
      rw [h1] at h2
      rw [← T.post_deg huY, ← h2, hdeg4 u huP]
  obtain ⟨hcM, hsepM⟩ := cut_lift_erase M Ka hcN hsepN hdegN hv₂'
  have hvN : v ∈ (Degen.eraseAtoms M Ka).atoms := hcN.1
  exact not_alpha_of_not_sameComponent M hconn hcM hsepM (hNB v hc.1 v₂' _ _ hcM)

end
end WaveTurbulence.FinalCountG8
