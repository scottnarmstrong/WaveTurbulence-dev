/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.BondErase
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Peel
import Mathlib.Tactic

/-! # Common facts for `ylem2` with a removed bond `ℓ`

`𝕄 ∖ {ℓ}` is G6's `MoleProp.eraseBond M e`. Its degrees and bond counts are those of `𝕄` corrected at the ends of `ℓ`;
it keeps the in/out caps; a chain of `𝕄` not using `ℓ` is a chain of `𝕄 ∖ {ℓ}`; and once a set `Y` containing an end
of `ℓ` is erased, `ℓ` is gone anyway: `(𝕄 ∖ {ℓ}) ∖ Y ≅ 𝕄 ∖ Y`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem ite_of_not {α : Type*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem ite_of_pos {α : Type*} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

omit [DecidableEq V] in
theorem sym2_ne_of_right {u w p q : V} (hp : w ≠ p) (hq : w ≠ q) : s(u, w) ≠ s(p, q) := by
  intro h
  have : w ∈ s(p, q) := by rw [← h]; exact Sym2.mem_mk_right _ _
  rcases Sym2.mem_iff.mp this with h1 | h1
  · exact hp h1
  · exact hq h1

omit [DecidableEq V] in
theorem sym2_ne_of_left {u w p q : V} (hp : u ≠ p) (hq : u ≠ q) : s(u, w) ≠ s(p, q) := by
  rw [Sym2.eq_swap]; exact sym2_ne_of_right hp hq

section
variable (M : Molecule V D) (e : D)

/-- Degrees after removing a bond with ends `p ≠ q`. -/
theorem deg_eraseBond_of_ends {p q : V} (h : M.ends e = s(p, q)) (v : V) :
    (MoleProp.eraseBond M e).deg v + (if p = v then 1 else 0) + (if q = v then 1 else 0) = M.deg v := by
  have := deg_eraseBond_add M e v
  change s(M.atom e, M.atom (M.mate e)) = s(p, q) at h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at this; exact this
  · rw [h1, h2] at this; omega

/-- Bond counts after removing a bond with ends `p, q`. -/
theorem bondsBetween_eraseBond_of_ends {p q : V} (h : M.ends e = s(p, q)) (u w : V) :
    (MoleProp.eraseBond M e).bondsBetween u w + (if s(p, q) = s(u, w) then 1 else 0) = M.bondsBetween u w := by
  have := bondsBetween_eraseBond_add M e u w
  rw [h] at this; exact this

/-- **Removing a bond keeps the in/out caps.** -/
theorem caps_eraseBond (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) :
    ∀ v ∈ (MoleProp.eraseBond M e).atoms, (MoleProp.eraseBond M e).outdeg v ≤ 2 ∧
      (MoleProp.eraseBond M e).indeg v ≤ 2 := by
  intro v hv
  have hle : ∀ b : Bool, (((MoleProp.eraseBond M e).dartsAt v).filter fun x => (MoleProp.eraseBond M e).out x = b).card ≤
      ((M.dartsAt v).filter fun x => M.out x = b).card := by
    intro b
    refine card_le_card_of_injOn (fun x => x.val) ?_ (fun x _ y _ h => Subtype.ext h)
    intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, Molecule.dartsAt, mem_filter, mem_univ, true_and] at hx ⊢
    exact hx
  exact ⟨(hle true).trans (hcap v hv).1, (hle false).trans (hcap v hv).2⟩

/-- A connected molecule with an atom of degree `≠ 4` is a molecule (given the caps). -/
theorem isMolecule_of_connected {W E : Type*} [DecidableEq W] [Fintype E] [DecidableEq E] (N : Molecule W E)
    (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (hconn : ∀ u ∈ N.atoms, ∀ v ∈ N.atoms, N.SameComponent u v) {z : W} (hz : z ∈ N.atoms) (h4 : N.deg z ≠ 4) :
    N.IsMolecule :=
  ⟨hcap, fun v hv => ⟨z, hz, hconn v hv z hz, h4⟩⟩

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- A dart whose bond has other ends is neither `e` nor `mate e`. -/
theorem ne_of_ends_ne {z : D} (h : M.ends z ≠ M.ends e) : z ≠ e ∧ z ≠ M.mate e := by
  refine ⟨fun hz => h (hz ▸ rfl), fun hz => h ?_⟩
  rw [hz]; unfold Molecule.ends; rw [M.mate_mate]; exact Sym2.eq_swap

/-- **`(𝕄 ∖ {ℓ}) ∖ Y ≅ 𝕄 ∖ Y`** when `ℓ` has an end in `Y`. -/
def eraseBondEraseEquiv (Y : Finset V) (he : M.atom e ∈ Y ∨ M.atom (M.mate e) ∈ Y) :
    Degen.RetainedDart (MoleProp.eraseBond M e) Y ≃ Degen.RetainedDart M Y where
  toFun x := ⟨x.val.val, x.property⟩
  invFun y := ⟨⟨y.val, by
    constructor
    · intro h
      have p := y.property
      rw [h] at p
      rcases he with h' | h'
      · exact p.1 h'
      · exact p.2 h'
    · intro h
      have p := y.property
      rw [h, M.mate_mate] at p
      rcases he with h' | h'
      · exact p.2 h'
      · exact p.1 h'⟩, y.property⟩
  left_inv x := rfl
  right_inv y := rfl

theorem afree_eraseBond_erase_le (Y : Finset V) (he : M.atom e ∈ Y ∨ M.atom (M.mate e) ∈ Y) {d : ℕ}
    (L γ δ η C1 : ℝ) (P : Finset V → ℝ) :
    AFree (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) d L γ δ η C1 P ≤
      AFree (Degen.eraseAtoms M Y) d L γ δ η C1 P :=
  afree_le_of_dart_equiv _ _ (eraseBondEraseEquiv M e Y he) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    L γ δ η C1 P

theorem ladderCells_eraseBond_erase (Y : Finset V) (he : M.atom e ∈ Y ∨ M.atom (M.mate e) ∈ Y) :
    MoleProp.ladderCells (Degen.eraseAtoms (MoleProp.eraseBond M e) Y) =
      MoleProp.ladderCells (Degen.eraseAtoms M Y) := by
  classical
  exact ladderCells_eq_of_dart_equiv' _ _ (eraseBondEraseEquiv M e Y he) rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)

end

namespace YChain
variable {M : Molecule V D} (C : YChain M)

/-- **A chain of `𝕄` not using the bond `ℓ` (and with `ℓ` away from its saturated pairs) is a chain of `𝕄 ∖ {ℓ}`.** -/
def onErase (e : D) (hout : ∀ p ∈ C.set, ∀ q ∈ C.set, M.ends e ≠ s(p, q))
    (hlow : ∀ i < C.n, M.atom e ≠ C.a i ∧ M.atom e ≠ C.b i ∧ M.atom (M.mate e) ≠ C.a i ∧
      M.atom (M.mate e) ≠ C.b i) : YChain (MoleProp.eraseBond M e) where
  n := C.n
  a := C.a
  b := C.b
  inj_a := C.inj_a
  inj_b := C.inj_b
  ne_ab := C.ne_ab
  mem := C.mem
  triple := by
    rw [bondsBetween_eraseBond_of_ne M e (hout _ (C.a_mem (Nat.zero_le _)) _ (C.b_mem (Nat.zero_le _)))]
    exact C.triple
  rung i h1 h2 := by
    rw [bondsBetween_eraseBond_of_ne M e (hout _ (C.a_mem h2) _ (C.b_mem h2))]
    exact C.rung i h1 h2
  rail i hi := by
    rw [bondsBetween_eraseBond_of_ne M e (hout _ (C.a_mem hi.le) _ (C.a_mem hi)),
      bondsBetween_eraseBond_of_ne M e (hout _ (C.b_mem hi.le) _ (C.b_mem hi))]
    exact C.rail i hi
  sat i hi := by
    obtain ⟨h1, h2, h3, h4⟩ := hlow i hi
    rw [deg_eraseBond_of_ne M e h1 h3, deg_eraseBond_of_ne M e h2 h4]
    exact C.sat i hi

/-- The first `k + 1` pairs of a chain. -/
def low (k : ℕ) (hk : k ≤ C.n) : YChain M where
  n := k
  a := C.a
  b := C.b
  inj_a i hi j hj := C.inj_a i (hi.trans hk) j (hj.trans hk)
  inj_b i hi j hj := C.inj_b i (hi.trans hk) j (hj.trans hk)
  ne_ab i hi j hj := C.ne_ab i (hi.trans hk) j (hj.trans hk)
  mem i hi := C.mem i (hi.trans hk)
  triple := C.triple
  rung i h1 h2 := C.rung i h1 (h2.trans hk)
  rail i hi := C.rail i (by omega)
  sat i hi := C.sat i (by omega)

omit [DecidableEq D] in
theorem low_set_sub (k : ℕ) (hk : k ≤ C.n) : (C.low k hk).set ⊆ C.set := by
  intro v hv
  obtain ⟨i, hi, h⟩ := (C.low k hk).mem_set.mp hv
  exact C.mem_set.mpr ⟨i, hi.trans hk, h⟩

omit [DecidableEq D] in
theorem a_notMem_low {k : ℕ} (hk : k ≤ C.n) {j : ℕ} (hj : k < j) (hjn : j ≤ C.n) : C.a j ∉ (C.low k hk).set := by
  intro h
  obtain ⟨i, hi, h | h⟩ := (C.low k hk).mem_set.mp h
  · have := C.inj_a j hjn i (hi.trans hk) h; change i ≤ k at hi; omega
  · exact C.ne_ab j hjn i (hi.trans hk) h

omit [DecidableEq D] in
theorem b_notMem_low {k : ℕ} (hk : k ≤ C.n) {j : ℕ} (hj : k < j) (hjn : j ≤ C.n) : C.b j ∉ (C.low k hk).set := by
  intro h
  obtain ⟨i, hi, h | h⟩ := (C.low k hk).mem_set.mp h
  · exact C.ne_ab i (hi.trans hk) j hjn h.symm
  · have := C.inj_b j hjn i (hi.trans hk) h; change i ≤ k at hi; omega

end YChain

end WaveTurbulence.MoleProp4
