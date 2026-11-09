/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DerivePortAt
public import WaveTurbulence.Foundations.TVine.Chart.ConfigsPair

/-!
# Derivation of the cell decomposition, VIII: placing a rung (L1, L2)

`place_rung`: a 2-atom piece `{u, w}` with two internal bonds, an input port (region `Xi`, the piece outside it) and
an output port (region `Xo ⊇ Xi`, the piece inside it), each with one bond at `u` and one at `w`, is a local
embedding of a chart of the rung table (spine `rungTable` or pendant `pendRungTable`), whose input pair is the input
port and whose exit pair is the output port.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

theorem fun6 {P : (Fin 6 → Bool) → Prop} (h : ∀ b0 b1 b2 b3 b4 b5 : Bool, P ![b0, b1, b2, b3, b4, b5])
    (b : Fin 6 → Bool) : P b := by
  have : b = ![b 0, b 1, b 2, b 3, b 4, b 5] := by funext i; fin_cases i <;> rfl
  rw [this]; exact h _ _ _ _ _ _

theorem not_cross_out {X : Finset V} {e : Bond M S} (h1 : tl e ∉ X) (h2 : hd e ∉ X) : ¬ Crosses X e := by
  unfold Crosses; tauto

theorem not_cross_in {X : Finset V} {e : Bond M S} (h1 : tl e ∈ X) (h2 : hd e ∈ X) : ¬ Crosses X e := by
  unfold Crosses; tauto

/-- An input-port bond does not cross a larger region containing the piece. -/
theorem inAt_not_cross {X Y : Finset V} (pt : Port2 M S X a b) {u w : V} (huw : u ≠ w) (hE : InEnds pt u w)
    (hXY : X ⊆ Y) (huY : u ∈ Y) : ¬ Crosses Y (inAt pt u) := by
  rcases inAt_end huw hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact not_cross_in (hXY h2) (by rw [h1]; exact huY)
  · exact not_cross_in (by rw [h1]; exact huY) (hXY h2)

/-- An output-port bond does not cross a smaller region not containing the piece. -/
theorem outAt_not_cross {X Y : Finset V} (pt : Port2 M S X a b) {u w : V} (huw : u ≠ w) (hE : OutEnds pt u w)
    (hYX : Y ⊆ X) (huY : u ∉ Y) : ¬ Crosses Y (outAt pt u) := by
  rcases outAt_end huw hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact not_cross_out (by rw [h1]; exact huY) (fun h => h2 (hYX h))
  · exact not_cross_out (fun h => h2 (hYX h)) (by rw [h1]; exact huY)

theorem inAt_eq_out {X : Finset V} (pt : Port2 M S X a b) {u w : V} (huw : u ≠ w) (hE : InEnds pt u w)
    (h : ¬ tl (inAt pt u) = u) : inAt pt u = pt.out := by
  unfold inAt at *
  split_ifs at h ⊢ with h1
  · rfl
  · exfalso; rcases hE with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact h1 h2
    · exact h h3

theorem inAt_eq_inn {X : Finset V} (pt : Port2 M S X a b) {u w : V} (huw : u ≠ w) (hE : InEnds pt u w)
    (h : tl (inAt pt u) = u) : inAt pt u = pt.inn := by
  unfold inAt at *
  split_ifs at h ⊢ with h1
  · exfalso; have h2 := pt.out_tl; have h3 := pt.out_hd; rw [h] at h2; rw [h1] at h3; exact h3 h2
  · rfl

theorem outAt_eq_out {X : Finset V} (pt : Port2 M S X a b) {u w : V} (huw : u ≠ w) (hE : OutEnds pt u w)
    (h : ¬ hd (outAt pt u) = u) : outAt pt u = pt.out := by
  unfold outAt at *
  split_ifs at h ⊢ with h1
  · rfl
  · exfalso; rcases hE with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact h1 h2
    · exact h h3

theorem inAt_eq_inn' {X : Finset V} (pt : Port2 M S X a b) {u : V} (h : ¬ hd (inAt pt u) = u) :
    inAt pt u = pt.inn := by
  unfold inAt at *
  split_ifs at h ⊢ with h1
  · exact absurd h1 h
  · rfl

theorem outAt_eq_inn {X : Finset V} (pt : Port2 M S X a b) {u w : V} (huw : u ≠ w) (hE : OutEnds pt u w)
    (h : ¬ tl (outAt pt u) = u) : outAt pt u = pt.inn := by
  unfold outAt at *
  split_ifs at h ⊢ with h1
  · exact absurd h1 h
  · rfl

/-- **Placing a rung.** -/
theorem place_rung (tab : List (LocalChart 2 2 6)) {rin rM : ℤ}
    (htab : ∀ c ∈ tab, c.Valid ∧ PairOK c ∧ rungShape.RoleCompat c ∧ c.Rel rin rM 0 ∧ c.ExtrasOK ∧ c.mu = 2)
    (hcov : ∀ b0 b1 b2 b3 b4 b5 : Bool, rungShape.OK ![b0, b1, b2, b3, b4, b5] →
      ∃ c ∈ tab, c.src = rungShape.src ![b0, b1, b2, b3, b4, b5] ∧ c.dst = rungShape.dst ![b0, b1, b2, b3, b4, b5])
    (hM : M.IsMolecule) {u w : V} (huw : u ≠ w) (hmu : u ∈ M.atoms) (hmw : w ∈ M.atoms)
    (hdu : M.degIn S u = 4) (hdw : M.degIn S w = 4)
    (d₀ d₁ : Bond M S) (hdd : d₀ ≠ d₁) (hd₀ : (tl d₀ = u ∧ hd d₀ = w) ∨ (tl d₀ = w ∧ hd d₀ = u))
    (hd₁ : (tl d₁ = u ∧ hd d₁ = w) ∨ (tl d₁ = w ∧ hd d₁ = u))
    {Xi Xo : Finset V} (pti : Port2 M S Xi a b) (pto : Port2 M S Xo a b) (hXio : Xi ⊆ Xo)
    (huXi : u ∉ Xi) (hwXi : w ∉ Xi) (huXo : u ∈ Xo) (hwXo : w ∈ Xo)
    (hEi : InEnds pti u w) (hEo : OutEnds pto u w) :
    ∃ c ∈ tab, ∃ φ : LocEmb c.graph M S, φ.atom = ![u, w] ∧
      φ.bond = ![d₀, d₁, inAt pti u, inAt pti w, outAt pto u, outAt pto w] ∧
      φ.bond c.eO = pti.out ∧ φ.bond c.eI = pti.inn ∧
      ∃ p, c.outM = some p ∧ φ.bond p.1 = pto.out ∧ φ.bond p.2 = pto.inn := by
  classical
  set φA : Fin 2 → V := ![u, w]
  set φB : Fin 6 → Bond M S := ![d₀, d₁, inAt pti u, inAt pti w, outAt pto u, outAt pto w]
  have hAinj : Function.Injective φA := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [φA]
  have hAmem : ∀ i, φA i ∈ ({u, w} : Finset V) := by intro i; fin_cases i <;> simp [φA]
  have hAnotXi : ∀ i, φA i ∉ Xi := by intro i; fin_cases i <;> simp [φA, huXi, hwXi]
  have hAXo : ∀ i, φA i ∈ Xo := by intro i; fin_cases i <;> simp [φA, huXo, hwXo]
  let R : SRole → Finset V := fun ρ => if ρ = .inp then Xi else Xo
  have hcov' : ∀ bb : Fin 6 → Bool, rungShape.OK bb → ∃ c ∈ tab, c.src = rungShape.src bb ∧ c.dst = rungShape.dst bb :=
    fun bb => fun6 (P := fun bb => rungShape.OK bb → ∃ c ∈ tab, c.src = rungShape.src bb ∧ c.dst = rungShape.dst bb)
      hcov bb
  have hintNo : ∀ (e : Bond M S), ((tl e = u ∧ hd e = w) ∨ (tl e = w ∧ hd e = u)) → ∀ ρ : SRole, ¬ Crosses (R ρ) e := by
    intro e he ρ
    by_cases hρ : ρ = .inp
    · simp only [R, hρ, ite_true]
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact not_cross_out (h1 ▸ huXi) (h2 ▸ hwXi)
      · exact not_cross_out (h1 ▸ hwXi) (h2 ▸ huXi)
    · simp only [R, hρ, ite_false]
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact not_cross_in (h1 ▸ huXo) (h2 ▸ hwXo)
      · exact not_cross_in (h1 ▸ hwXo) (h2 ▸ huXo)
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
  obtain ⟨c, hc, hcs, hcd, φ, hφA, hφB⟩ := place_cell rungShape tab hcov' hM φA φB R hAinj
    (by intro i; fin_cases i <;> simp [φA, hmu, hmw]) (by intro i; fin_cases i <;> simp [φA, hdu, hdw])
    (by decide) (by decide) (by decide) (by decide)
    (by
      intro l u' w' h
      fin_cases l <;> simp [rungShape] at h
      · obtain ⟨rfl, rfl⟩ := h; simpa [φA, φB] using hd₀
      · obtain ⟨rfl, rfl⟩ := h; simpa [φA, φB] using hd₁)
    (by
      intro l l' u' w' u'' w'' hne h h' _
      fin_cases l <;> fin_cases l' <;> simp [rungShape] at h h' hne <;> simp [φB, hdd, Ne.symm hdd])
    (by
      intro l u' w' ρ h hρ
      fin_cases l <;> simp [rungShape] at h
      · exact hintNo d₀ hd₀ ρ
      · exact hintNo d₁ hd₁ ρ)
    (by
      intro l u' h
      fin_cases l <;> simp [rungShape] at h <;> subst h <;> unfold StubAt
      · rcases hstubIn u w huw hEi (fun _ => Or.inr trivial) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rcases hstubIn w u huw.symm hEi.symm (fun _ => Or.inr trivial) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · exact hstubOut u w huw hEo
      · exact hstubOut w u huw.symm hEo.symm)
    (by
      intro l u' h
      fin_cases l <;> simp [rungShape] at h <;> simp only [R, φB, rungShape]
      · exact inAt_cross pti u
      · exact inAt_cross pti w
      · exact outAt_cross pto u
      · exact outAt_cross pto w)
    (by
      intro l l' u' u'' h h' hr
      fin_cases l <;> fin_cases l' <;> simp [rungShape] at h h' hr <;> simp only [R, φB, rungShape]
      · exact inAt_not_cross pti huw hEi hXio huXo
      · exact inAt_not_cross pti huw hEi hXio huXo
      · exact inAt_not_cross pti huw.symm hEi.symm hXio hwXo
      · exact inAt_not_cross pti huw.symm hEi.symm hXio hwXo
      · exact outAt_not_cross pto huw hEo hXio huXi
      · exact outAt_not_cross pto huw hEo hXio huXi
      · exact outAt_not_cross pto huw.symm hEo.symm hXio hwXi
      · exact outAt_not_cross pto huw.symm hEo.symm hXio hwXi)
    (by
      intro ρ hρ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
      rcases hρ with rfl | rfl | rfl
      · apply pair_count _ _ 2 3 (by decide) (by decide)
        simp only [placeBits, φB, φA, rungShape]
        exact inAt_bits huw hEi
      · apply pair_count _ _ 4 5 (by decide) (by decide)
        simp only [placeBits, φB, φA, rungShape]
        exact outAt_bits huw hEo
      · exact absent_count _ _ (by decide) _)
  -- wiring
  obtain ⟨-, -, hRC, -, -, -⟩ := htab c hc
  obtain ⟨hrO, hrI, hsO, hdI, hM', -⟩ := hRC
  have hinp : ∀ l, rungShape.role l = .inp ↔ l = 2 ∨ l = 3 := by decide
  have hexm : ∀ l, rungShape.role l = .exM ↔ l = 4 ∨ l = 5 := by decide
  have hA0 : φ.atom 0 = u := by rw [hφA]; rfl
  have hA1 : φ.atom 1 = w := by rw [hφA]; rfl
  have b2 : φ.bond 2 = inAt pti u := by rw [hφB]; rfl
  have b3 : φ.bond 3 = inAt pti w := by rw [hφB]; rfl
  have b4 : φ.bond 4 = outAt pto u := by rw [hφB]; rfl
  have b5 : φ.bond 5 = outAt pto w := by rw [hφB]; rfl
  refine ⟨c, hc, φ, hφA, hφB, ?_, ?_, ?_⟩
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
    | none => intro h; exact absurd (h 4) (by decide)
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

end WaveTurbulence.TVine.Chart
