/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveRung

/-!
# Derivation of the cell decomposition, XII: placing the junction (L3)

`place_junction`: the 2-atom piece of a (P-a) attachment, with one internal bond, an input port, an exit port and a
pendant port (one bond of each at each atom, M4 Lemma A), is a local embedding of a chart of `junctionTable`.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

theorem fun7 {P : (Fin 7 → Bool) → Prop} (h : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, P ![b0, b1, b2, b3, b4, b5, b6])
    (b : Fin 7 → Bool) : P b := by
  have : b = ![b 0, b 1, b 2, b 3, b 4, b 5, b 6] := by funext i; fin_cases i <;> rfl
  rw [this]; exact h _ _ _ _ _ _ _

/-- An output bond does not cross a region containing the piece and everything outside the output region. -/
theorem outAt_not_cross_side {X Y : Finset V} (pt : Port2 M S X a b) {u w : V} (huw : u ≠ w) (hE : OutEnds pt u w)
    (hcomp : ∀ v ∈ S, v ∉ X → v ∈ Y) (huY : u ∈ Y) : ¬ Crosses Y (outAt pt u) := by
  rcases outAt_end huw hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact not_cross_in (by rw [h1]; exact huY) (hcomp _ (hd_mem _) h2)
  · exact not_cross_in (hcomp _ (tl_mem _) h2) (by rw [h1]; exact huY)

/-- **Placing the junction.** -/
theorem place_junction (tab : List (LocalChart 2 2 7))
    (htab : ∀ c ∈ tab, c.Valid ∧ PairOK c ∧ junctionShape.RoleCompat c ∧ c.Rel 1 1 0 ∧ c.ExtrasOK ∧ c.mu = 1)
    (hcov : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, junctionShape.OK ![b0, b1, b2, b3, b4, b5, b6] →
      ∃ c ∈ tab, c.src = junctionShape.src ![b0, b1, b2, b3, b4, b5, b6] ∧
        c.dst = junctionShape.dst ![b0, b1, b2, b3, b4, b5, b6])
    (hM : M.IsMolecule) {u w : V} (huw : u ≠ w) (hmu : u ∈ M.atoms) (hmw : w ∈ M.atoms)
    (hdu : M.degIn S u = 4) (hdw : M.degIn S w = 4)
    (d₀ : Bond M S) (hd₀ : (tl d₀ = u ∧ hd d₀ = w) ∨ (tl d₀ = w ∧ hd d₀ = u))
    {Xi Xo Xb : Finset V} (pti : Port2 M S Xi a b) (pto : Port2 M S Xo a b) (ptb : Port2 M S Xb a b)
    (hXio : Xi ⊆ Xo) (hXib : Xi ⊆ Xb) (hob : ∀ v ∈ S, v ∉ Xo → v ∈ Xb) (hbo : ∀ v ∈ S, v ∉ Xb → v ∈ Xo)
    (huXi : u ∉ Xi) (hwXi : w ∉ Xi) (huXo : u ∈ Xo) (hwXo : w ∈ Xo) (huXb : u ∈ Xb) (hwXb : w ∈ Xb)
    (hEi : InEnds pti u w) (hEo : OutEnds pto u w) (hEb : OutEnds ptb u w) :
    ∃ c ∈ tab, ∃ φ : LocEmb c.graph M S, φ.atom = ![u, w] ∧
      φ.bond = ![d₀, inAt pti u, inAt pti w, outAt pto u, outAt pto w, outAt ptb u, outAt ptb w] ∧
      φ.bond c.eO = pti.out ∧ φ.bond c.eI = pti.inn ∧
      (∃ p, c.outM = some p ∧ φ.bond p.1 = pto.out ∧ φ.bond p.2 = pto.inn) ∧
      ∃ p, c.outB = some p ∧ φ.bond p.1 = ptb.out ∧ φ.bond p.2 = ptb.inn := by
  classical
  set φA : Fin 2 → V := ![u, w]
  set φB : Fin 7 → Bond M S := ![d₀, inAt pti u, inAt pti w, outAt pto u, outAt pto w, outAt ptb u, outAt ptb w]
  have hAinj : Function.Injective φA := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [φA]
  have hAmem : ∀ i, φA i ∈ ({u, w} : Finset V) := by intro i; fin_cases i <;> simp [φA]
  have hAnotXi : ∀ i, φA i ∉ Xi := by intro i; fin_cases i <;> simp [φA, huXi, hwXi]
  have hAXo : ∀ i, φA i ∈ Xo := by intro i; fin_cases i <;> simp [φA, huXo, hwXo]
  have hAXb : ∀ i, φA i ∈ Xb := by intro i; fin_cases i <;> simp [φA, huXb, hwXb]
  let R : SRole → Finset V := fun ρ => if ρ = .inp then Xi else if ρ = .exM then Xo else Xb
  have hcov' : ∀ bb : Fin 7 → Bool, junctionShape.OK bb →
      ∃ c ∈ tab, c.src = junctionShape.src bb ∧ c.dst = junctionShape.dst bb :=
    fun bb => fun7 (P := fun bb => junctionShape.OK bb →
      ∃ c ∈ tab, c.src = junctionShape.src bb ∧ c.dst = junctionShape.dst bb) hcov bb
  have hintNo : ∀ (e : Bond M S), ((tl e = u ∧ hd e = w) ∨ (tl e = w ∧ hd e = u)) → ∀ ρ : SRole, ¬ Crosses (R ρ) e := by
    intro e he ρ
    by_cases hρ : ρ = .inp
    · simp only [R, hρ, ite_true]
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact not_cross_out (h1 ▸ huXi) (h2 ▸ hwXi)
      · exact not_cross_out (h1 ▸ hwXi) (h2 ▸ huXi)
    by_cases hρ' : ρ = .exM
    · simp only [R, hρ, hρ', ite_true, ite_false, reduceCtorEq]
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact not_cross_in (h1 ▸ huXo) (h2 ▸ hwXo)
      · exact not_cross_in (h1 ▸ hwXo) (h2 ▸ huXo)
    · simp only [R, hρ, hρ', ite_false]
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact not_cross_in (h1 ▸ huXb) (h2 ▸ hwXb)
      · exact not_cross_in (h1 ▸ hwXb) (h2 ▸ huXb)
  have hstubIn : ∀ (v v' : V), v ≠ v' → InEnds pti v v' → (∀ i, φA i ∈ ({v, v'} : Finset V) ∨ True) →
      (hd (inAt pti v) = v ∧ ∀ i, tl (inAt pti v) ≠ φA i) ∨ (tl (inAt pti v) = v ∧ ∀ i, hd (inAt pti v) ≠ φA i) := by
    intro v v' hvv' hE _
    rcases inAt_end hvv' hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun i h => hAnotXi i (h ▸ h2)⟩
    · exact Or.inr ⟨h1, fun i h => hAnotXi i (h ▸ h2)⟩
  have hstubOut : ∀ (v v' : V), v ≠ v' → OutEnds pto v v' →
      (tl (outAt pto v) = v ∧ ∀ i, hd (outAt pto v) ≠ φA i) ∨ (hd (outAt pto v) = v ∧ ∀ i, tl (outAt pto v) ≠ φA i) := by
    intro v v' hvv' hE
    rcases outAt_end hvv' hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun i h => h2 (h ▸ hAXo i)⟩
    · exact Or.inr ⟨h1, fun i h => h2 (h ▸ hAXo i)⟩
  have hstubB : ∀ (v v' : V), v ≠ v' → OutEnds ptb v v' →
      (tl (outAt ptb v) = v ∧ ∀ i, hd (outAt ptb v) ≠ φA i) ∨ (hd (outAt ptb v) = v ∧ ∀ i, tl (outAt ptb v) ≠ φA i) := by
    intro v v' hvv' hE
    rcases outAt_end hvv' hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun i h => h2 (h ▸ hAXb i)⟩
    · exact Or.inr ⟨h1, fun i h => h2 (h ▸ hAXb i)⟩
  obtain ⟨c, hc, hcs, hcd, φ, hφA, hφB⟩ := place_cell junctionShape tab hcov' hM φA φB R hAinj
    (by intro i; fin_cases i <;> simp [φA, hmu, hmw]) (by intro i; fin_cases i <;> simp [φA, hdu, hdw])
    (by decide) (by decide) (by decide) (by decide)
    (by
      intro l u' w' h
      fin_cases l <;> simp [junctionShape] at h
      · obtain ⟨rfl, rfl⟩ := h; simpa [φA, φB] using hd₀)
    (by
      intro l l' u' w' u'' w'' hne h h' _
      fin_cases l <;> fin_cases l' <;> simp [junctionShape] at h h' hne)
    (by
      intro l u' w' ρ h hρ
      fin_cases l <;> simp [junctionShape] at h
      · exact hintNo d₀ hd₀ ρ)
    (by
      intro l u' h
      fin_cases l <;> simp [junctionShape] at h <;> subst h <;> unfold StubAt
      · rcases hstubIn u w huw hEi (fun _ => Or.inr trivial) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rcases hstubIn w u huw.symm hEi.symm (fun _ => Or.inr trivial) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · exact hstubOut u w huw hEo
      · exact hstubOut w u huw.symm hEo.symm
      · exact hstubB u w huw hEb
      · exact hstubB w u huw.symm hEb.symm)
    (by
      intro l u' h
      fin_cases l <;> simp [junctionShape] at h <;> simp only [R, φB, junctionShape]
      · exact inAt_cross pti u
      · exact inAt_cross pti w
      · exact outAt_cross pto u
      · exact outAt_cross pto w
      · exact outAt_cross ptb u
      · exact outAt_cross ptb w)
    (by
      intro l l' u' u'' h h' hr
      fin_cases l <;> fin_cases l' <;> simp [junctionShape] at h h' hr <;> simp only [R, φB, junctionShape]
      · exact inAt_not_cross pti huw hEi hXio huXo
      · exact inAt_not_cross pti huw hEi hXio huXo
      · exact inAt_not_cross pti huw hEi hXib huXb
      · exact inAt_not_cross pti huw hEi hXib huXb
      · exact inAt_not_cross pti huw.symm hEi.symm hXio hwXo
      · exact inAt_not_cross pti huw.symm hEi.symm hXio hwXo
      · exact inAt_not_cross pti huw.symm hEi.symm hXib hwXb
      · exact inAt_not_cross pti huw.symm hEi.symm hXib hwXb
      · exact outAt_not_cross pto huw hEo hXio huXi
      · exact outAt_not_cross pto huw hEo hXio huXi
      · exact outAt_not_cross_side pto huw hEo hob huXb
      · exact outAt_not_cross_side pto huw hEo hob huXb
      · exact outAt_not_cross pto huw.symm hEo.symm hXio hwXi
      · exact outAt_not_cross pto huw.symm hEo.symm hXio hwXi
      · exact outAt_not_cross_side pto huw.symm hEo.symm hob hwXb
      · exact outAt_not_cross_side pto huw.symm hEo.symm hob hwXb
      · exact outAt_not_cross ptb huw hEb hXib huXi
      · exact outAt_not_cross ptb huw hEb hXib huXi
      · exact outAt_not_cross_side ptb huw hEb hbo huXo
      · exact outAt_not_cross_side ptb huw hEb hbo huXo
      · exact outAt_not_cross ptb huw.symm hEb.symm hXib hwXi
      · exact outAt_not_cross ptb huw.symm hEb.symm hXib hwXi
      · exact outAt_not_cross_side ptb huw.symm hEb.symm hbo hwXo
      · exact outAt_not_cross_side ptb huw.symm hEb.symm hbo hwXo)
    (by
      intro ρ hρ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
      rcases hρ with rfl | rfl | rfl
      · apply pair_count _ _ 1 2 (by decide) (by decide)
        simp only [placeBits, φB, φA, junctionShape]
        exact inAt_bits huw hEi
      · apply pair_count _ _ 3 4 (by decide) (by decide)
        simp only [placeBits, φB, φA, junctionShape]
        exact outAt_bits huw hEo
      · apply pair_count _ _ 5 6 (by decide) (by decide)
        simp only [placeBits, φB, φA, junctionShape]
        exact outAt_bits huw hEb)
  -- wiring
  obtain ⟨-, -, hRC, -, -, -⟩ := htab c hc
  obtain ⟨hrO, hrI, hsO, hdI, hM', hB'⟩ := hRC
  have hinp : ∀ l, junctionShape.role l = .inp ↔ l = 1 ∨ l = 2 := by decide
  have hexm : ∀ l, junctionShape.role l = .exM ↔ l = 3 ∨ l = 4 := by decide
  have hexb : ∀ l, junctionShape.role l = .exB ↔ l = 5 ∨ l = 6 := by decide
  have hA0 : φ.atom 0 = u := by rw [hφA]; rfl
  have hA1 : φ.atom 1 = w := by rw [hφA]; rfl
  have b2 : φ.bond 1 = inAt pti u := by rw [hφB]; rfl
  have b3 : φ.bond 2 = inAt pti w := by rw [hφB]; rfl
  have b4 : φ.bond 3 = outAt pto u := by rw [hφB]; rfl
  have b5 : φ.bond 4 = outAt pto w := by rw [hφB]; rfl
  have b6 : φ.bond 5 = outAt ptb u := by rw [hφB]; rfl
  have b7 : φ.bond 6 = outAt ptb w := by rw [hφB]; rfl
  refine ⟨c, hc, φ, hφA, hφB, ?_, ?_, ?_, ?_⟩
  · have hs := φ.tl_out c.eO hsO
    rcases (hinp _).mp hrO with h | h <;> rw [h] at hs ⊢
    · rw [b2]; have := hs 0; rw [b2, hA0] at this; exact inAt_eq_out pti huw hEi this
    · rw [b3]; have := hs 1; rw [b3, hA1] at this; exact inAt_eq_out pti huw.symm hEi.symm this
  · have hs := φ.hd_out c.eI hdI
    rcases (hinp _).mp hrI with h | h <;> rw [h] at hs ⊢
    · rw [b2]; have := hs 0; rw [b2, hA0] at this; exact inAt_eq_inn' pti this
    · rw [b3]; have := hs 1; rw [b3, hA1] at this; exact inAt_eq_inn' pti this
  · revert hM'
    cases hp : c.outM with
    | none => intro h; exact absurd (h 3) (by decide)
    | some p =>
      rintro ⟨hr1, hr2, hd1, hs2⟩
      refine ⟨p, rfl, ?_, ?_⟩
      · have hs := φ.hd_out p.1 hd1
        rcases (hexm _).mp hr1 with h | h <;> rw [h] at hs ⊢
        · rw [b4]; have := hs 0; rw [b4, hA0] at this; exact outAt_eq_out pto huw hEo this
        · rw [b5]; have := hs 1; rw [b5, hA1] at this; exact outAt_eq_out pto huw.symm hEo.symm this
      · have hs := φ.tl_out p.2 hs2
        rcases (hexm _).mp hr2 with h | h <;> rw [h] at hs ⊢
        · rw [b4]; have := hs 0; rw [b4, hA0] at this; exact outAt_eq_inn pto huw hEo this
        · rw [b5]; have := hs 1; rw [b5, hA1] at this; exact outAt_eq_inn pto huw.symm hEo.symm this
  · revert hB'
    cases hp : c.outB with
    | none => intro h; exact absurd (h 5) (by decide)
    | some p =>
      rintro ⟨hr1, hr2, hd1, hs2⟩
      refine ⟨p, rfl, ?_, ?_⟩
      · have hs := φ.hd_out p.1 hd1
        rcases (hexb _).mp hr1 with h | h <;> rw [h] at hs ⊢
        · rw [b6]; have := hs 0; rw [b6, hA0] at this; exact outAt_eq_out ptb huw hEb this
        · rw [b7]; have := hs 1; rw [b7, hA1] at this; exact outAt_eq_out ptb huw.symm hEb.symm this
      · have hs := φ.tl_out p.2 hs2
        rcases (hexb _).mp hr2 with h | h <;> rw [h] at hs ⊢
        · rw [b6]; have := hs 0; rw [b6, hA0] at this; exact outAt_eq_inn ptb huw hEb this
        · rw [b7]; have := hs 1; rw [b7, hA1] at this; exact outAt_eq_inn ptb huw.symm hEb.symm this

end WaveTurbulence.TVine.Chart
