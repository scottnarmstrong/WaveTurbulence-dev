/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm9
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 10: `FamTame` at a state, from class-level tameness of `M₀`.**
Class hypotheses (for every `k0 ∈ A`): `k0` is constant on the darts at a tame atom (`IsTame`), `k0 (mate x) = k0 x` (decoration), and the label of a tame atom
of degree `< 4` is a constant of the class (`hfix`, the roots).  At a state, the darts at an `ε`-atom are those of `M₀` (`AncRel.surj`, `inj`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- At an `ε`-atom the darts of the state and of `M₀` correspond. -/
theorem deg_eq_of_eps {M₀ : Molecule V D₀} {s : St.{u} V D₀} {an : V → V} (hA : AncRel M₀ s an) {b : V} (hb : b ∈ s.M.atoms)
    (he : s.cls b = .eps) : s.M.deg b = M₀.deg b := by
  unfold Molecule.deg
  refine Finset.card_bij (fun x _ => s.down x) ?_ (fun x _ y _ h => hA.inj h) ?_
  · intro x hx
    have hx' : s.M.atom x = b := by simpa [Molecule.dartsAt] using hx
    have := hA.atom x
    rw [hx', hA.eps b hb he] at this
    simpa [Molecule.dartsAt] using this
  · intro z hz
    have hz' : M₀.atom z = b := by simpa [Molecule.dartsAt] using hz
    obtain ⟨x, hx⟩ := hA.surj b hb he z hz'
    refine ⟨x, ?_, hx⟩
    have := hA.atom x
    rw [hx, hz'] at this
    have h2 := hA.uniq (s.M.atom x) (s.M.atom_mem x) b hb he this.symm
    simpa [Molecule.dartsAt] using h2

theorem famTame_state {M₀ : Molecule V D₀} {s : St.{u} V D₀} (hc : LCtx M₀ s) (Tm : V → Prop) (A : Set (D₀ → (Fin d → ℤ)))
    (hTame : ∀ k0 ∈ A, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y)
    (hmate : ∀ k0 ∈ A, ∀ x, k0 (M₀.mate x) = k0 x)
    (hfix : ∀ v ∈ M₀.atoms, Tm v → M₀.deg v < 4 → ∃ k, ∀ k0 ∈ A, ∀ x, M₀.atom x = v → k0 x = k)
    (𝒦 : Finset (Finset V))
    (hK : ∀ K ∈ 𝒦, (∀ a ∈ K, a ∈ s.M.atoms ∧ s.cls a = .eps ∧ Tm a) ∧ (∀ a ∈ K, 1 ≤ s.M.deg a) ∧
      ∀ a ∈ K, ∀ b ∈ K, (eraseSet s.M (s.M.atoms \ K)).SameComponent a b) :
    FamTame s.M 𝒦 (AdmS (fun k => k ∈ A) s) := by
  obtain ⟨an, han⟩ := hc.anc
  have hrel := hc.rel
  intro K hKm
  obtain ⟨hK1, hK2, hK3⟩ := hK K hKm
  -- values at darts of the state at atoms of `K`
  have hat : ∀ x : s.D, s.M.atom x ∈ K → M₀.atom (s.down x) = s.M.atom x := fun x hx =>
    hrel.eps x (hK1 _ hx).2.1
  refine ⟨?_, ?_⟩
  · rintro κ ⟨k0, hk0, rfl⟩
    -- same atom
    have same : ∀ x y : s.D, s.M.atom x = s.M.atom y → s.M.atom x ∈ K → k0 (s.down x) = k0 (s.down y) := by
      intro x y hxy hx
      have h1 := hat x hx
      have h2 := hat y (hxy ▸ hx)
      exact hTame k0 hk0 _ (h1 ▸ M₀.atom_mem _) (hK1 _ hx).2.2 _ _ h1 (h2.trans hxy.symm)
    -- along a bond
    have bond : ∀ x : s.D, s.M.atom x ∈ K → k0 (s.down (s.M.mate x)) = k0 (s.down x) := by
      intro x _
      rw [← hrel.mate x]; exact hmate k0 hk0 _
    have conn : ∀ u v, (eraseSet s.M (s.M.atoms \ K)).SameComponent u v →
        (u ∈ K ↔ v ∈ K) ∧ (u ∈ K → ∀ x y : s.D, s.M.atom x = u → s.M.atom y = v → k0 (s.down x) = k0 (s.down y)) := by
      intro u v huv
      induction huv with
      | rel u v hr =>
        obtain ⟨hadj, huK, hvK⟩ := (eraseSet_compl_adj_iff s.M K).1 hr
        obtain ⟨z, hz1, hz2⟩ := hadj
        refine ⟨iff_of_true huK hvK, fun hu x y hx hy => ?_⟩
        have e1 : k0 (s.down x) = k0 (s.down z) := same x z (hx.trans hz1.symm) (hx ▸ hu)
        have e2 : k0 (s.down (s.M.mate z)) = k0 (s.down y) := same _ y (hz2.trans hy.symm) (hz2 ▸ hvK)
        rw [e1, ← e2, bond z (hz1 ▸ hu)]
      | refl u =>
        exact ⟨Iff.rfl, fun hu x y hx hy => same x y (hx.trans hy.symm) (hx ▸ hu)⟩
      | symm u v _ ih =>
        refine ⟨ih.1.symm, fun hv x y hx hy => ?_⟩
        exact (ih.2 (ih.1.2 hv) y x hy hx).symm
      | trans u v w _ _ ih1 ih2 =>
        refine ⟨ih1.1.trans ih2.1, fun hu x y hx hy => ?_⟩
        have hv := ih1.1.1 hu
        obtain ⟨z, hz⟩ : ∃ z : s.D, s.M.atom z = v := by
          have := hK2 v hv
          obtain ⟨z, hz⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one this)
          exact ⟨z, by simpa [Molecule.dartsAt] using hz⟩
        exact (ih1.2 hu x z hx hz).trans (ih2.2 hv z y hz hy)
    intro x y hx hy
    exact (conn _ _ (hK3 _ hx _ hy)).2 hx x y rfl rfl
  · intro a ha hdeg
    have hae := hK1 a ha
    rw [deg_eq_of_eps han hae.1 hae.2.1] at hdeg
    have haM : a ∈ M₀.atoms := by
      have := han.mem a hae.1
      rwa [han.eps a hae.1 hae.2.1] at this
    obtain ⟨k, hk⟩ := hfix a haM hae.2.2 hdeg
    refine ⟨k, ?_⟩
    rintro κ ⟨k0, hk0, rfl⟩ x hx
    have hxa : s.M.atom x = a := by simpa [Molecule.dartsAt] using hx
    exact hk k0 hk0 (s.down x) ((hrel.eps x (by rw [hxa]; exact hae.2.1)).trans hxa)

end WaveTurbulence.FinalCountAsm
