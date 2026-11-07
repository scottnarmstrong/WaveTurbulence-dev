/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL23
public import WaveTurbulence.Foundations.FinalCount.GV01
public import WaveTurbulence.Foundations.Spine.SourceBlockJointGaps
/-! **G3-LOWDEG (R48), part 24: vine-like objects of `M.unloop` with a small gap contain no loop atom of `M`.**  A loop atom `v` has
`deg' v ≤ 2` in `M.unloop`, so it can only be a joint of a block of `M.unloop`; on the `ε`-support all its legs are equal, so the gap
at `v` vanishes, and by the conservation `block_gaps_neg` so does the gap of the object: it is not SG. (Hyper-objects: a joint
has the added bond as a third dart.) -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem SubHypL.isMolecule {R : ℕ} {M : Molecule V D} (hS : SubHypL R M) : M.IsMolecule := by
  refine ⟨hS.bounds, fun v hv => ?_⟩
  by_contra hcon
  push Not at hcon
  have hall : ∀ b ∈ M.atoms, M.deg b = 4 := fun b hb => hcon b hb (hS.conn v hv b hb)
  exact sum_deg_ne_fourL hS hall

theorem loop_deg_le (M : Molecule V D) {v : V} {y : D} (hy : M.atom y = v) (hl : M.atom (M.mate y) = v)
    (h4 : M.deg v ≤ 4) : M.unloop.deg v ≤ 2 := by
  have hyv : y ∈ M.dartsAt v := (mem_dartsAt' M v y).2 hy
  have hne : M.mate y ≠ y := M.mate_ne y
  have hmv : M.mate y ∈ (M.dartsAt v).erase y := Finset.mem_erase.2 ⟨hne, (mem_dartsAt' M v _).2 hl⟩
  have h1 : M.unloop.deg v ≤ (((M.dartsAt v).erase y).erase (M.mate y)).card := by
    unfold Molecule.deg
    refine Finset.card_le_card_of_injOn (fun x => x.1) (fun x hx => ?_) (fun a _ b _ e => Subtype.ext e)
    have hx' := (mem_dartsAt' M.unloop v x).1 hx
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, (mem_dartsAt' M v x.1).2 hx'⟩⟩
    · intro e; have e' : x.1 = M.mate y := e
      apply x.2; rw [e', M.mate_mate]; exact hl.trans hy.symm
    · intro e; have e' : x.1 = y := e
      apply x.2; rw [e']; exact hy.trans hl.symm
  rw [Finset.card_erase_of_mem hmv, Finset.card_erase_of_mem hyv] at h1
  have : M.deg v = (M.dartsAt v).card := rfl
  omega

theorem gap_zero_at_loop (M : Molecule V D) (L : ℝ) (w : Mom d) {κ : D → Fin d → ℤ}
    (heq : ∀ y : D, M.atom y = M.atom (M.mate y) → ∀ z : D, M.atom z = M.atom y → κ z = κ y) {v : V}
    (hl : ∃ y, M.atom y = v ∧ M.atom (M.mate y) = v) (x₁ x₂ : NonLoop M) (h1 : M.atom x₁.1 = v) (h2 : M.atom x₂.1 = v) :
    Molecule.gapAt L w (fun x : NonLoop M => κ x.1) x₁ x₂ = 0 := by
  obtain ⟨y, hy, hym⟩ := hl
  have k1 := heq y (hy.trans hym.symm) x₁.1 (h1.trans hy.symm)
  have k2 := heq y (hy.trans hym.symm) x₂.1 (h2.trans hy.symm)
  unfold Molecule.gapAt Molecule.kvec
  simp only [k1, k2, sub_self]

theorem gapKind_zero (L γ η : ℝ) : Molecule.gapKind L γ η (0 : Mom d) = .ZG := by
  unfold Molecule.gapKind; simp

theorem erase_deg_le (M : Molecule V D) (e : D) (v : V) : (M.eraseBond e).deg v ≤ M.deg v := by
  unfold Molecule.deg
  refine Finset.card_le_card_of_injOn (fun x => x.1) (fun x hx => ?_) (fun a _ b _ e => Subtype.ext e)
  exact (mem_dartsAt' M v x.1).2 ((mem_dartsAt' (M.eraseBond e) v x).1 hx)

theorem erase_deg_lt (M : Molecule V D) (e : D) (v : V) (hv : ∃ d₀, M.atom d₀ = v ∧ (d₀ = e ∨ d₀ = M.mate e)) :
    (M.eraseBond e).deg v + 1 ≤ M.deg v := by
  obtain ⟨d₀, hd, hc⟩ := hv
  have hm : d₀ ∈ M.dartsAt v := (mem_dartsAt' M v d₀).2 hd
  have h1 : (M.eraseBond e).deg v ≤ ((M.dartsAt v).erase d₀).card := by
    unfold Molecule.deg
    refine Finset.card_le_card_of_injOn (fun x => x.1) (fun x hx => ?_) (fun a _ b _ e => Subtype.ext e)
    refine Finset.mem_erase.2 ⟨?_, (mem_dartsAt' M v x.1).2 ((mem_dartsAt' (M.eraseBond e) v x).1 hx)⟩
    rcases hc with rfl | rfl
    · exact x.2.1
    · exact x.2.2
  rw [Finset.card_erase_of_mem hm] at h1
  have : M.deg v = (M.dartsAt v).card := rfl
  have : 0 < (M.dartsAt v).card := Finset.card_pos.2 ⟨d₀, hm⟩
  omega

theorem degIn_le_deg' (M : Molecule V D) (S : Finset V) (v : V) : M.degIn S v ≤ M.deg v := Finset.card_filter_le _ _

theorem outIn_le_outdeg (M : Molecule V D) (S : Finset V) (v : V) : M.outIn S v ≤ M.outdeg v := by
  unfold Molecule.outIn Molecule.outdeg
  exact Finset.card_le_card (fun x hx => by
    have := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨this.1, this.2.2⟩)

theorem inIn_le_indeg (M : Molecule V D) (S : Finset V) (v : V) : M.inIn S v ≤ M.indeg v := by
  unfold Molecule.inIn Molecule.indeg
  exact Finset.card_le_card (fun x hx => by
    have := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨this.1, this.2.2⟩)

end WaveTurbulence.FinalCountG3
