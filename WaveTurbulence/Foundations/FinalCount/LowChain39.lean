/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain38
public import WaveTurbulence.Foundations.FinalCount.GM03
public import WaveTurbulence.Foundations.FinalCount.GV14
/-! **FINALCOUNT LOW-CHAIN, session 6 (13): the shape of an untouched component at the effective index** (R79, referee F3).
`shape_oddDegL'` replaces the hypothesis `R = 1` (and `odd_comp`) by the component-level hypothesis that the component has at most `2`
odd-degree atoms; `finalShape_compL'` is `finalShape_compL` with it.  `odd_comp_card_le`: if a component contains no loop atom of `B`, its odd atoms
number at most `2r` (every odd atom outside `B` has `contrib ≥ 1`, `Σ_{v ∉ B} contrib ≤ 2(R' - k)`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {hf : HSt V D₀}

section shape4
variable (hC : Prop95ConclAtL L γ η w κ R hf Tm) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms)
include hC ha₀

theorem shape_oddDegL' (hcard : ((compMol hf.s.M a₀).atoms.filter fun b => ¬ Even ((compMol hf.s.M a₀).deg b)).card ≤ 2) :
    CompOddL hf a₀ → ∃ u ∈ (compMol hf.s.M a₀).atoms, ∃ x ∈ (compMol hf.s.M a₀).atoms,
    u ≠ x ∧ ((compMol hf.s.M a₀).deg u = 1 ∨ (compMol hf.s.M a₀).deg u = 3) ∧
    ((compMol hf.s.M a₀).deg x = 1 ∨ (compMol hf.s.M a₀).deg x = 3) ∧
    ∀ a ∈ (compMol hf.s.M a₀).atoms, a ≠ u → a ≠ x →
      (compMol hf.s.M a₀).deg a = 2 ∨ (compMol hf.s.M a₀).deg a = 4 := by
  rintro ⟨b, hb, hbo⟩
  have hev := card_odd_even (compMol hf.s.M a₀)
  have hpos : 0 < ((compMol hf.s.M a₀).atoms.filter fun b => ¬ Even ((compMol hf.s.M a₀).deg b)).card :=
    Finset.card_pos.2 ⟨b, Finset.mem_filter.2 ⟨hb, hbo⟩⟩
  have hc2 : ((compMol hf.s.M a₀).atoms.filter fun b => ¬ Even ((compMol hf.s.M a₀).deg b)).card = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  obtain ⟨u, x, hux, hset⟩ := Finset.card_eq_two.1 hc2
  have hmem : ∀ a, a ∈ (compMol hf.s.M a₀).atoms ∧ ¬ Even ((compMol hf.s.M a₀).deg a) ↔ a = u ∨ a = x := by
    intro a
    have := congrArg (fun S => a ∈ S) hset
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, eq_iff_iff] at this
    exact this
  have hu := (hmem u).2 (Or.inl rfl)
  have hx := (hmem x).2 (Or.inr rfl)
  have hu' := (mem_compMol _ _).1 hu.1
  have hx' := (mem_compMol _ _).1 hx.1
  refine ⟨u, hu.1, x, hx.1, hux, ?_, ?_, ?_⟩
  · have := hC.struct.odd_deg u hu'.1 (by rw [compMol_deg _ _ hu'.2] at hu; exact hu.2)
    rw [compMol_deg _ _ hu'.2]; exact this
  · have := hC.struct.odd_deg x hx'.1 (by rw [compMol_deg _ _ hx'.2] at hx; exact hx.2)
    rw [compMol_deg _ _ hx'.2]; exact this
  · intro a ha hau hax
    have h := (mem_compMol _ _).1 ha
    have hev' : Even ((compMol hf.s.M a₀).deg a) := by
      by_contra hc
      rcases (hmem a).1 ⟨ha, hc⟩ with e | e
      · exact hau e
      · exact hax e
    rw [compMol_deg _ _ h.2] at hev' ⊢
    have hr := hC.struct.deg_range a h.1
    obtain ⟨k, hk⟩ := hev'
    omega

theorem finalShape_compL' (hcard : ((compMol hf.s.M a₀).atoms.filter fun b => ¬ Even ((compMol hf.s.M a₀).deg b)).card ≤ 2)
    (hT : TameFree hf Tm a₀) (hE : LowFree hf a₀) :
    G8Copy.FinalShape (compMol hf.s.M a₀) (fun a => toCls (hf.s.cls a)) (CompOddL hf a₀) where
  nonempty := shape_nonemptyL hC ha₀
  caps := shape_capsL hC ha₀
  noLoop := shape_noLoopL hC ha₀
  conn := shape_connL hC ha₀
  degPos := shape_degPosL hC ha₀
  classes := shape_classesL hC ha₀ hE
  dir2 := shape_dir2L hC ha₀ hE
  oddDeg := fun hod => shape_oddDegL' hC ha₀ hcard hod
  evenDeg := shape_evenDegL hC ha₀
  noTriple := shape_noTripleL hC ha₀
  evenBeta := shape_evenBetaL hC ha₀ hE
  cycle := shape_cycleL hC ha₀ hE
  chains := shape_chainsL hC ha₀ hT hE

end shape4

end WaveTurbulence.FinalCountG3

namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **Odd atoms of a component without loop atoms.** -/
theorem odd_comp_card_le {s : St.{u} V D₀} {R' r k : ℕ} {B : Finset V} (hg : Good R' s) (hRk : r + k = R')
    (hBsub : B ⊆ s.M.atoms) (hBε : ∀ b ∈ B, s.cls b = .eps) (hBdeg : ∀ b ∈ B, s.M.deg b ≤ 2) (hBcard : B.card = k)
    {a : V} (hB : ∀ b ∈ B, ¬ s.M.SameComponent a b) :
    ((compMol s.M a).atoms.filter fun b => ¬ Even ((compMol s.M a).deg b)).card ≤ 2 * r := by
  set S := (compMol s.M a).atoms.filter fun b => ¬ Even ((compMol s.M a).deg b) with hS
  have hSsub : ∀ v ∈ S, v ∈ s.M.atoms ∧ v ∉ B ∧ 1 ≤ contrib s v := by
    intro v hv
    obtain ⟨hvm, hodd⟩ := Finset.mem_filter.1 hv
    have hvc := (mem_compMol _ _).1 hvm
    rw [compMol_deg _ _ hvc.2] at hodd
    refine ⟨hvc.1, fun hvB => hB v hvB hvc.2, ?_⟩
    have h0 := Good.contrib_nonneg hg hvc.1
    by_contra hlt
    have h00 : contrib s v = 0 := by omega
    apply hodd
    unfold contrib at h00
    have he := Cls.even_base (s.cls v)
    have h1 : ((s.M.deg v : ℕ) : ℤ) = (s.cls v).base := by omega
    have : Even (((s.M.deg v : ℕ) : ℤ)) := by rw [h1]; exact he
    exact (Int.even_coe_nat _).1 this
  have h1 : (S.card : ℤ) ≤ ∑ v ∈ S, contrib s v := by
    calc (S.card : ℤ) = ∑ _v ∈ S, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun v hv => (hSsub v hv).2.2
  have h2 : ∑ v ∈ S, contrib s v ≤ ∑ v ∈ s.M.atoms \ B, contrib s v := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v hv _ => Good.contrib_nonneg hg (Finset.mem_sdiff.1 hv).1)
    intro v hv
    exact Finset.mem_sdiff.2 ⟨(hSsub v hv).1, (hSsub v hv).2.1⟩
  have h3 := Finset.sum_sdiff hBsub (f := contrib s)
  have h4 := hg.sum_contrib
  have hB2 : ∀ b ∈ B, (2 : ℤ) ≤ contrib s b := by
    intro b hb
    have := hBdeg b hb
    unfold contrib
    rw [hBε b hb]
    simp only [Cls.base]
    omega
  have h5 : ∑ b ∈ B, (2 : ℤ) ≤ ∑ b ∈ B, contrib s b := Finset.sum_le_sum hB2
  have h6 : ∑ b ∈ B, (2 : ℤ) = 2 * (k : ℤ) := by rw [← hBcard]; simp [mul_comm]
  have : ((r : ℤ)) + k = R' := by exact_mod_cast hRk
  omega

end WaveTurbulence.FinalCountAsm
