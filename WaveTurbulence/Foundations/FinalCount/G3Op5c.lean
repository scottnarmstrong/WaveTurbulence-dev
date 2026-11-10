/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Op5b
public import WaveTurbulence.Foundations.FinalCount.G3ConclN
/-! **FINALCOUNT-G3 (R29 item 3): Operation 5 on a run, conclusions.**  `HSt.op5 h Tm` erases the set of tame `ε`-atoms.
* `Op5.good`: `Good R₅ (op5)` with `2R₅ + 4|T| ≤ 2R + tch(T)`;
* `Op5.imperfect`: at most `R₅` imperfect components;
* `Op5.epsLG`: strict LG at every `ε`-atom of `op5` (the tame ones are gone; the rest are LG by `Prop95ConclN.eps_LG`);
* `Op5.label`: the labels of the `α`-atoms of `op5` lie in `[L⁻¹, L^{-γ+η}]`;
* `Op5.perfect_tameFree`: a perfect component of `op5` lies in a component of the input without tame atoms. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop}

/-- The tame `ε`-atoms of a state. -/
noncomputable def tameSet (h : HSt V D₀) (Tm : V → Prop) : Finset V :=
  h.s.M.atoms.filter (fun v => h.s.cls v = .eps ∧ Tm v)

/-- **Operation 5**: erase every tame `ε`-atom (one maximal cluster at a time = the whole set at once). -/
noncomputable def HSt.op5 (h : HSt V D₀) (Tm : V → Prop) : HSt V D₀ :=
  ⟨h.s.eraseSetSt (tameSet h Tm), h.hist, h.crec, h.anc⟩

theorem tameSet_mem {h : HSt V D₀} {v : V} : v ∈ tameSet h Tm ↔ v ∈ h.s.M.atoms ∧ h.s.cls v = .eps ∧ Tm v := by
  unfold tameSet; simp [Finset.mem_filter]

theorem Op5.good {h : HSt V D₀} (hg : Good R h.s) :
    ∃ R₅ : ℕ, 2 * (R₅ : ℤ) + 4 * ((tameSet h Tm).card : ℤ) ≤ 2 * (R : ℤ) + (tch h.s.M (tameSet h Tm) : ℤ) ∧
      Good R₅ (h.op5 Tm).s :=
  hg.erase_set (fun v hv => by have := tameSet_mem.1 hv; exact ⟨this.1, this.2.1⟩)

theorem Op5.atoms_sub {h : HSt V D₀} {a : V} (ha : a ∈ (h.op5 Tm).s.M.atoms) :
    a ∈ h.s.M.atoms ∧ a ∉ tameSet h Tm := by
  have := Finset.mem_filter.1 ha
  have h2 := Finset.mem_sdiff.1 this.1
  exact h2

/-- Strict LG at the `ε`-atoms of the state after Operation 5. -/
theorem Op5.epsLG {h : HSt V D₀} (hC : Prop95ConclN L γ η w κ Tm R h) :
    ∀ a ∈ (h.op5 Tm).s.M.atoms, (h.op5 Tm).s.cls a = .eps → ∀ x y : (h.op5 Tm).s.D,
      (h.op5 Tm).s.M.atom x = a → (h.op5 Tm).s.M.atom y = a → (h.op5 Tm).s.M.out x = false →
      (h.op5 Tm).s.M.out y = true → y ≠ (h.op5 Tm).s.M.mate x →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ (h.op5 Tm).s.down) x y) = .LG := by
  intro a ha hae x y hx hy hox hoy hxy
  obtain ⟨haM, haT⟩ := Op5.atoms_sub ha
  have hae' : h.s.cls a = .eps := hae
  have hnT : ¬ Tm a := fun hT => haT (tameSet_mem.2 ⟨haM, hae', hT⟩)
  have := (hC.eps_LG a haM hae').resolve_left hnT x.1.1 y.1.1 hx hy hox hoy (by
    intro e; apply hxy; exact Subtype.ext (Subtype.ext e))
  exact this

/-- The labels of the `α`-atoms of the state after Operation 5. -/
theorem Op5.label {h : HSt V D₀} (hC : Prop95ConclN L γ η w κ Tm R h) :
    ∀ a ∈ (h.op5 Tm).s.M.atoms, ∀ ρ kp, (h.op5 Tm).s.cls a = .alpha ρ kp → IsLabel L γ η ρ := by
  intro a ha ρ kp hc
  obtain ⟨haM, -⟩ := Op5.atoms_sub ha
  exact (hC.label a haM ρ kp hc).1


/-- **Perfect components are tame-free** (R29 item 3): a component of the state after Operation 5 all of whose atoms have `contrib = 0`
lies in a component of the input state without tame `ε`-atoms. -/
theorem Op5.perfect_tameFree {h : HSt V D₀} (hg : Good R h.s) {a : V} (ha : a ∈ (h.op5 Tm).s.M.atoms)
    (hper : ∀ b ∈ (h.op5 Tm).s.M.atoms, (h.op5 Tm).s.M.SameComponent a b → contrib (h.op5 Tm).s b = 0) :
    TameFree h Tm a := by
  intro e he hsc hee hTm
  set T := tameSet h Tm with hT
  have eT : e ∈ T := tameSet_mem.2 ⟨he, hee, hTm⟩
  let Q : V → Prop := fun x => x ∈ (h.op5 Tm).s.M.atoms ∧ (h.op5 Tm).s.M.SameComponent a x
  have step : ∀ x y, h.s.M.Adj x y → Q x → Q y := by
    intro x y hadj ⟨hx5, hsc5⟩
    obtain ⟨z, hz1, hz2⟩ := hadj
    obtain ⟨hxM, hxT⟩ := Op5.atoms_sub hx5
    have hxE : x ∉ T := hxT
    by_cases hy : y ∈ T
    · exfalso
      have hk : keepS h.s T x := (Finset.mem_filter.1 hx5).2
      have hd5 : (h.op5 Tm).s.M.deg x = (eraseSet h.s.M T).deg x := eraseSetSt_deg hk
      have hdc := eraseSet_deg_card h.s.M T hxE
      have hm : 1 ≤ multS h.s.M T x := by
        unfold multS
        refine Finset.card_pos.2 ⟨z, ?_⟩
        simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hz1, by rw [hz2]; exact hy⟩
      have h0 := hper x hx5 hsc5
      have h1 := hg.contrib_nonneg hxM
      unfold contrib at h0 h1
      have hcl : ((h.op5 Tm).s.cls x) = h.s.cls x := rfl
      rw [hcl] at h0
      omega
    · have hyM : y ∈ h.s.M.atoms := hz2 ▸ h.s.M.atom_mem _
      have hzE : h.s.M.atom z ∉ T ∧ h.s.M.atom (h.s.M.mate z) ∉ T := by rw [hz1, hz2]; exact ⟨hxE, hy⟩
      have hmE : h.s.M.atom (h.s.M.mate z) ∉ T ∧ h.s.M.atom (h.s.M.mate (h.s.M.mate z)) ∉ T := by
        rw [h.s.M.mate_mate, hz1, hz2]; exact ⟨hy, hxE⟩
      have hky : keepS h.s T y := by
        unfold keepS Molecule.deg
        refine Finset.card_pos.2 ⟨⟨h.s.M.mate z, hmE⟩, ?_⟩
        simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hz2
      have hy5 : y ∈ (h.op5 Tm).s.M.atoms :=
        Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hyM, hy⟩, hky⟩
      have hadj5 : (eraseSet h.s.M T).Adj x y := ⟨⟨z, hzE⟩, hz1, hz2⟩
      have hadj : (h.op5 Tm).s.M.Adj x y :=
        restrictP_adj_of (eraseSet h.s.M T) (keepS h.s T) (keepS_closed h.s T) (Finset.mem_filter.1 hx5).2 hadj5
      exact ⟨hy5, Relation.EqvGen.trans _ _ _ hsc5 (Relation.EqvGen.rel _ _ hadj)⟩
  have iff' : ∀ x y, h.s.M.SameComponent x y → (Q x ↔ Q y) := by
    intro x y hxy
    induction hxy with
    | rel x y hr => exact ⟨step x y hr, step y x (adj_symm_er hr)⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  have hQa : Q a := ⟨ha, Relation.EqvGen.refl _⟩
  have hQe : Q e := (iff' a e hsc).1 hQa
  exact (Op5.atoms_sub hQe.1).2 eT

end WaveTurbulence.FinalCountG3
