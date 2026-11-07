/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain23
/-! **FINALCOUNT LOW-CHAIN, session 5 (2): the first-stage end bound with deleted joints (`state_rem_isoE`, `fst_boundL`).**
Along a vine history that may include Step D1, the state has `E` fewer components than `remMol M₀ ps`: `remMol` keeps the degree-`2` joints
that Step D1 deletes as isolated atoms.  `state_rem_isoE`: `(remMol M₀ ps).numComponents = h.s.M.numComponents + E`, and a degree-`0` atom of
`remMol` forces `E ≥ 1` or a degree-`0` state atom.  `fst_boundL`: the `CnBound` argument of `fst_bound`, with `E`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem state_rem_isoE {M₀ : Molecule V D₀} {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    (ps : List (Object M₀ × Quad D₀))
    (hinj : ∀ c ∈ h.s.M.atoms, ∀ b ∈ h.s.M.atoms, h.anc c = h.anc b → c = b)
    (hpres : ∀ z : D₀, (∀ x : h.s.D, h.s.down x ≠ z) → ∃ p ∈ ps, z ∈ PieceKill p.1 p.2)
    (he1 : ∀ x : h.s.D, ∀ p ∈ ps, h.s.down x ∉ PieceKill p.1 p.2)
    (he3 : ∀ c ∈ h.s.M.atoms, ∀ p ∈ ps, ¬ PieceInt p.1 (h.anc c)) :
    ∃ E : ℕ, (remMol M₀ ps).numComponents = h.s.M.numComponents + E ∧
      ∀ v ∈ (remMol M₀ ps).atoms, (remMol M₀ ps).deg v = 0 → 1 ≤ E ∨ ∃ c ∈ h.s.M.atoms, h.s.M.deg c = 0 := by
  have hmem : ∀ x : h.s.D, h.s.down x ∉ KillS ps ∧ M₀.mate (h.s.down x) ∉ KillS ps := by
    intro x
    refine ⟨fun ⟨p, hp, hk⟩ => he1 x p hp hk, fun ⟨p, hp, hk⟩ => ?_⟩
    rw [hD.mate] at hk
    exact he1 _ p hp hk
  let e : h.s.D ≃ {z : D₀ // z ∉ KillS ps ∧ M₀.mate z ∉ KillS ps} := Equiv.ofBijective (fun x => ⟨h.s.down x, hmem x⟩)
    ⟨fun a b hab => hA.inj (congrArg Subtype.val hab), fun z => by
      by_contra hno
      push Not at hno
      have : ∀ x : h.s.D, h.s.down x ≠ z.1 := fun x hx => hno x (Subtype.ext hx)
      obtain ⟨p, hp, hk⟩ := hpres z.1 this
      exact z.2.1 ⟨p, hp, hk⟩⟩
  let N := remMol M₀ ps
  let P : V → Prop := fun v => v ∈ h.s.M.atoms.image h.anc
  have hatomN : ∀ x, N.atom (e x) = h.anc (h.s.M.atom x) := fun x => hA.atom x
  have hPall : ∀ x : {z : D₀ // z ∉ KillS ps ∧ M₀.mate z ∉ KillS ps}, P (N.atom x) := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    show N.atom (e y) ∈ h.s.M.atoms.image h.anc
    rw [hatomN y]
    exact Finset.mem_image_of_mem _ (h.s.M.atom_mem y)
  have hPc : PClosed N P := fun x _ => hPall _
  let e' : h.s.D ≃ PDart N P := Equiv.ofBijective (fun y => ⟨e y, hPall _⟩)
    ⟨fun a b hab => e.injective (congrArg Subtype.val hab), fun z => by
      obtain ⟨y, hy⟩ := e.surjective z.1
      exact ⟨y, Subtype.ext hy⟩⟩
  have hatoms : (restrictP N P hPc).atoms = h.s.M.atoms.image h.anc := by
    show N.atoms.filter P = _
    ext v
    simp only [Finset.mem_filter]
    constructor
    · exact fun ⟨_, hv⟩ => hv
    · intro hv
      refine ⟨?_, hv⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hv
      exact Finset.mem_filter.2 ⟨hA.mem c hc, he3 c hc⟩
  have h1 : (restrictP N P hPc).numComponents = h.s.M.numComponents :=
    numComponents_rename e' h.anc hatoms hinj (fun y => hA.atom y) (fun y => Subtype.ext (Subtype.ext (hD.mate y)))
  have hadd := numComponents_restrictP_add N P hPc
  have hemp : IsEmpty (PDart N (fun a => ¬ P a)) := ⟨fun x => x.2 (hPall x.1)⟩
  have hdl := dartless_numComponents (restrictP N (fun a => ¬ P a) hPc.neg)
  have hdl' : (restrictP N (fun a => ¬ P a) hPc.neg).atoms.card = (N.atoms.filter fun a => ¬ P a).card := rfl
  rw [hdl, hdl', h1] at hadd
  refine ⟨(N.atoms.filter fun a => ¬ P a).card, hadd.symm, ?_⟩
  intro v hv hv0
  by_cases hPv : P v
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hPv
    right
    refine ⟨c, hc, ?_⟩
    rw [← deg_rename e h.anc hinj hatomN hc]
    exact hv0
  · left
    exact Finset.card_pos.2 ⟨v, Finset.mem_filter.2 ⟨hv, hPv⟩⟩

end WaveTurbulence.FinalCountAsm
