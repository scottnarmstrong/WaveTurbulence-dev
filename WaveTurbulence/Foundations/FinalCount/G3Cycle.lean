/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Cyc3
public import WaveTurbulence.Foundations.FinalCount.G3ChainEnds
/-! **FINALCOUNT-G3: the `cycles` conclusion of DH23 Prop 9.5** (L1807): an even component without `ε`-atom is a
double bond, a cycle of length `≥ 4`, or a triangle with at most one `α`-atom.  A single atom would be a self-loop
(irreducibility); a triangle with two `α`-atoms is a triangle with two SG triples, excluded by `NoSGTriangle`
(Step 2 completed, preserved by the cuts of Steps 3, 4). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- `cycles` with the triangle hypothesis in the form it is used: no triangle has `α`-atoms at its first two vertices. -/
theorem cycles_of_key [Infinite V] {s : St.{u} V D₀}
    (hab : ∀ c ∈ s.M.atoms, s.cls c ≠ .eps → s.M.deg c ≤ 2) (hdr : ∀ c ∈ s.M.atoms, 1 ≤ s.M.deg c)
    (hB : BalS s) (hnl : ∀ x, s.M.atom x ≠ s.M.atom (s.M.mate x))
    (hkey : ∀ T : TriData s.M, (∃ ρ kp, s.cls (T.t 0) = .alpha ρ kp) → (∃ ρ kp, s.cls (T.t 1) = .alpha ρ kp) →
      s.cls (T.t 2) ≠ .eps → False)
    {a : V} (ha : a ∈ s.M.atoms) (hev : EvenComp s.M a) (hne : ∀ b ∈ compAtoms s.M a, s.cls b ≠ .eps) :
    CycleShape s a := by
  set A := compAtoms s.M a with hA
  have hmemA : ∀ c, c ∈ A ↔ c ∈ s.M.atoms ∧ s.M.SameComponent a c := fun c => by
    rw [hA]; unfold compAtoms; simp [Finset.mem_filter]
  have haA : a ∈ A := (hmemA a).2 ⟨ha, Relation.EqvGen.refl _⟩
  have hdeg : ∀ c ∈ A, s.M.deg c = 2 := by
    intro c hc
    obtain ⟨hcm, hsc⟩ := (hmemA c).1 hc
    have h1 := hab c hcm (hne c hc)
    have h2 := hdr c hcm
    obtain ⟨k, hk⟩ := hev c hcm hsc
    omega
  have hcl : ∀ z, s.M.atom z ∈ A → s.M.atom (s.M.mate z) ∈ A := by
    intro z hz
    obtain ⟨-, hsc⟩ := (hmemA _).1 hz
    refine (hmemA _).2 ⟨s.M.atom_mem _, Relation.EqvGen.trans _ _ _ hsc (Relation.EqvGen.rel _ _ ⟨z, rfl, rfl⟩)⟩
  have hconn : ∀ c ∈ A, ∀ c' ∈ A, s.M.SameComponent c c' := by
    intro c hc c' hc'
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ((hmemA c).1 hc).2) ((hmemA c').1 hc').2
  have hone : A.card ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := Finset.card_eq_one.1 h1
    have hdp : 0 < (s.M.dartsAt a).card := by
      have := hdeg a haA; unfold Molecule.deg at this; omega
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hdp
    have hz' : s.M.atom z = a := (mem_dartsAt _ _ _).1 hz
    have h1' : s.M.atom (s.M.mate z) ∈ A := hcl z (hz' ▸ haA)
    rw [hc, Finset.mem_singleton] at h1'
    have h2 : a ∈ A := haA
    rw [hc, Finset.mem_singleton] at h2
    exact hnl z (by rw [hz', h1', h2])
  have hpos : 0 < A.card := Finset.card_pos.2 ⟨a, haA⟩
  unfold CycleShape
  rw [← hA]
  by_cases h3 : A.card = 3
  · right; right
    refine ⟨h3, ?_⟩
    by_contra hgt
    have hgt := not_le.1 hgt
    obtain ⟨u, hu, u', hu', hne'⟩ := Finset.one_lt_card.1 hgt
    simp only [Finset.mem_filter] at hu hu'
    obtain ⟨huA, ρ, kp, hcu⟩ := hu
    obtain ⟨hu'A, ρ', kp', hcu'⟩ := hu'
    -- two consecutive alpha atoms give a triangle with two SG triples
    have hT2 : ∀ T : TriData s.M, T.t 0 ∈ A → s.cls (T.t 2) ≠ .eps := by
      intro T h0
      have step : ∀ j : Fin 3, T.t j ∈ A → T.t (j + 1) ∈ A := by
        intro j hj
        have := hcl (T.b j) (by rw [T.atom_b j]; exact hj)
        rwa [show s.M.mate (T.b j) = T.a (j + 1) from T.mate_b j, T.atom_a] at this
      have h1 := step 0 h0
      have h2 : T.t 2 ∈ A := step 1 h1
      exact hne _ h2
    have key : ∀ T : TriData s.M, T.t 0 ∈ A → (∃ ρ kp, s.cls (T.t 0) = .alpha ρ kp) →
        (∃ ρ kp, s.cls (T.t 1) = .alpha ρ kp) → False := fun T h0 a0 a1 => hkey T a0 a1 (hT2 T h0)
    obtain ⟨b₀, hb₀, hob₀⟩ := bal_exists_out (hB.2 u ((hmemA u).1 huA).1 (hne u huA) (hdeg u huA))
    obtain ⟨T, ht0, htb0, hTA⟩ := cycle3_tri hnl (fun c hc => ((hmemA c).1 hc).1) hdeg (fun c hc => hB.2 c ((hmemA c).1 hc).1 (hne c hc) (hdeg c hc)) hcl hconn h3 huA hb₀ hob₀
    rcases hTA u' hu'A with h | h | h
    · exact hne' (h.trans ht0).symm
    · exact key T (ht0 ▸ huA) ⟨ρ, kp, ht0 ▸ hcu⟩ ⟨ρ', kp', h ▸ hcu'⟩
    · -- start again from u' = T.t 2
      have hT2A : T.t 2 ∈ A := h ▸ hu'A
      obtain ⟨T', ht0', htb0', hTA'⟩ := cycle3_tri hnl (fun c hc => ((hmemA c).1 hc).1) hdeg (fun c hc => hB.2 c ((hmemA c).1 hc).1 (hne c hc) (hdeg c hc)) hcl hconn h3
        hT2A (b₀ := T.b 2) (T.atom_b 2) (T.out_b 2)
      have ht1' : T'.t 1 = T.t 0 := by
        have e1 : s.M.mate (T'.b 0) = T'.a 1 := T'.mate_b 0
        have e2 : s.M.mate (T.b 2) = T.a 0 := T.mate_b 2
        rw [← T'.atom_a 1, ← e1, htb0', e2, T.atom_a 0]
      refine key T' (by rw [ht0']; exact hT2A) ⟨ρ', kp', ?_⟩ ⟨ρ, kp, ?_⟩
      · rw [ht0', ← h]; exact hcu'
      · rw [ht1', ht0]; exact hcu
  · rcases Nat.lt_or_ge A.card 3 with hlt | hge
    · left; omega
    · right; left; omega

end WaveTurbulence.FinalCountG3
