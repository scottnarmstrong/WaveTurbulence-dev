/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCAdm`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 24: `VCLadderScale` from the molecule-level ladder-scale restriction of `Adm`.

`LadderScaleAdm M L w P κ` is the molecule-level reading of requirement (ii) of DH23 `kqmainest2` (L1692: "the gap
`r_j` of each ladder `𝕃_j` satisfies `|r_j| ∼ P_j`", `P_j ∈ [L⁻¹, 1] ∪ {0}`): for every ladder of `M`, every gap of
it, and every maximal ladder `S` containing it, `r = 0` when `P S = 0` and `|r| ∼ P S` (comparison constant `2`)
otherwise.  `vcLadderScale_of_adm` derives the vine-level `VCLadderScale` from it with the heredity hypotheses `hP1`,
`hP2` of `FinalCount.prop94_vine_single` (a maximal ladder of the removed vine lies in a maximal ladder of the cut
chain `cutMol → m1 → M`, with the same `P`).  No block hypothesis is used, so it serves for a hyper object as well. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

-- `LadderScaleAdm`, `ladderScaleLow_of_adm`: main's (`VineCount`, family-free).

section Gen
variable {M : Molecule V D} (K : VineCut g M)

theorem mem_vc_atoms_gen {z : V} (hz : z ∈ K.vc.atoms) : z ∈ K.C.atoms :=
  not_not.mp (Finset.mem_filter.mp hz).2

/-- A ladder of the removed vine avoids the joints and the fresh atoms; it is a ladder of the doubly cut molecule,
of the singly cut one and of `M`. -/
theorem vc_ladder_chain {m : ℕ} {u v : Fin (m + 1) → V} (h : K.vc.IsLadder u v) :
    (∀ j, u j ∈ K.C.atoms ∧ v j ∈ K.C.atoms) ∧ K.cutMol.IsLadder u v ∧ K.m1.IsLadder u v ∧ M.IsLadder u v ∧
      Avoid K.C.lower K.fb u ∧ Avoid K.C.lower K.fb v ∧ Avoid K.C.upper K.fa u ∧ Avoid K.C.upper K.fa v := by
  have hS : ∀ j, u j ∈ K.C.atoms ∧ v j ∈ K.C.atoms := fun j =>
    ⟨mem_vc_atoms_gen K (h.2.2.1 j).1, mem_vc_atoms_gen K (h.2.2.1 j).2⟩
  have hP : ∀ j, ¬ (u j ∉ K.C.atoms) ∧ ¬ (v j ∉ K.C.atoms) := fun j => ⟨not_not.mpr (hS j).1, not_not.mpr (hS j).2⟩
  have h1 : K.cutMol.IsLadder u v :=
    (restrictP_isLadder_iff K.cutMol (fun a => ¬ (a ∉ K.C.atoms)) K.closed.neg (fun j => (hP j).1)
      (fun j => (hP j).2)).1 h
  have hb2 : K.cutMol.deg K.C.lower = 2 := cut_deg_v K.m1 K.cut_b
  have hfb : ∀ z, z ∈ K.C.atoms → z ≠ K.fb := fun z hz e => K.fb_fresh (e ▸ objectAtoms_sub K.C hz)
  have hfa : ∀ z, z ∈ K.C.atoms → z ≠ K.fa := fun z hz e => K.fa_fresh (e ▸ objectAtoms_sub K.C hz)
  have avu : Avoid K.C.lower K.fb u := fun j => ⟨fun e => by
      have := ladder_deg_ge_three_u K.cutMol h1 j; rw [e, hb2] at this; omega, hfb _ (hS j).1⟩
  have avv : Avoid K.C.lower K.fb v := fun j => ⟨fun e => by
      have := ladder_deg_ge_three_w K.cutMol h1 j; rw [e, hb2] at this; omega, hfb _ (hS j).2⟩
  have h2 : K.m1.IsLadder u v := (cut_isLadder_iff K.m1 K.cut_b avu avv).1 h1
  have ha2 : K.m1.deg K.C.upper = 2 := cut_deg_v M K.cut_a
  have avu' : Avoid K.C.upper K.fa u := fun j => ⟨fun e => by
      have := ladder_deg_ge_three_u K.m1 h2 j; rw [e, ha2] at this; omega, hfa _ (hS j).1⟩
  have avv' : Avoid K.C.upper K.fa v := fun j => ⟨fun e => by
      have := ladder_deg_ge_three_w K.m1 h2 j; rw [e, ha2] at this; omega, hfa _ (hS j).2⟩
  exact ⟨hS, h1, h2, (cut_isLadder_iff M K.cut_a avu' avv').1 h2, avu, avv, avu', avv'⟩

/-- Every ladder of the removed vine is a ladder of `M` inside the object (no block hypothesis). -/
theorem vc_isLadder_gen {m : ℕ} {u v : Fin (m + 1) → V} (h : K.vc.IsLadder u v) :
    M.IsLadder u v ∧ (∀ j, u j ∈ K.C.atoms ∧ v j ∈ K.C.atoms) := by
  obtain ⟨hS, -, -, h4, -⟩ := vc_ladder_chain K h
  exact ⟨h4, hS⟩

/-- A gap of a ladder of the removed vine is a gap of the same ladder in `M`. -/
theorem vc_gap_gen {m : ℕ} {u v : Fin (m + 1) → V} (h : K.vc.IsLadder u v) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) {r : Mom d} (hr : K.vc.IsLadderGap L w (fun x => κ x.1) u v h.1 r) :
    M.IsLadderGap L w κ u v (vc_isLadder_gen K h).1.1 r := by
  obtain ⟨-, -, -, -, avb, bvb, ava, bva⟩ := vc_ladder_chain K h
  obtain ⟨x, y, hx, hy, hxa, hya, rfl⟩ := hr
  have h1 : (⟨1, by have := h.1; omega⟩ : Fin (m + 1)) = (⟨1, by have := h.1; omega⟩ : Fin (m + 1)) := rfl
  refine ⟨x.1, y.1, ?_, ?_, ?_, ?_, rfl⟩
  · have e : K.cutMol.ends x.1 = _ := hx
    have e1 : K.m1.ends x.1 = _ := (cut_ends_eq_iff K.m1 x.1 (avb 0).1 (avb 0).2 (avb _).1 (avb _).2).1 e
    exact (cut_ends_eq_iff M x.1 (ava 0).1 (ava 0).2 (ava _).1 (ava _).2).1 e1
  · have e : K.cutMol.ends y.1 = _ := hy
    have e1 : K.m1.ends y.1 = _ := (cut_ends_eq_iff K.m1 y.1 (bvb 0).1 (bvb 0).2 (bvb _).1 (bvb _).2).1 e
    exact (cut_ends_eq_iff M y.1 (bva 0).1 (bva 0).2 (bva _).1 (bva _).2).1 e1
  · have e : K.cutMol.atom x.1 = u 0 := hxa
    have e1 : K.m1.atom x.1 = u 0 := (cut_atom_eq_iff K.m1 x.1 (avb 0).1 (avb 0).2).1 e
    exact (cut_atom_eq_iff M x.1 (ava 0).1 (ava 0).2).1 e1
  · have e : K.cutMol.atom y.1 = v 0 := hya
    have e1 : K.m1.atom y.1 = v 0 := (cut_atom_eq_iff K.m1 y.1 (bvb 0).1 (bvb 0).2).1 e
    exact (cut_atom_eq_iff M y.1 (bva 0).1 (bva 0).2).1 e1

/-- A maximal ladder of the removed vine lies in a maximal ladder of `M`, with the same weight `P` (heredity). -/
theorem vc_maximal_sub (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (P : Finset V → ℝ)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    {S' : Finset V} (hS' : S' ∈ K.vc.maximalLadders) :
    ∃ S ∈ M.maximalLadders, S' ⊆ S ∧ P S' = P S := by
  have hc : S' ∈ K.cutMol.maximalLadders :=
    ((restrictP_maximal_iff K.cutMol (fun a => ¬ (a ∉ K.C.atoms)) K.closed.neg).1 hS').1
  obtain ⟨S1, hS1, hsub1⟩ := cut_maximal_sub K.m1 K.cut_b
    (K.deg_m1 hM _ (Finset.mem_insert_of_mem K.b_atom)) hc
  obtain ⟨S0, hS0, hsub0⟩ := cut_maximal_sub M K.cut_a (hM _ K.a_atom) hS1
  exact ⟨S0, hS0, hsub1.trans hsub0, (hP2 S' hc S1 hS1 hsub1).trans (hP1 S1 hS1 S0 hS0 hsub0)⟩

/-- **`VCLadderScale` from the lower-bound ladder-scale restriction** and the heredity hypotheses `hP1`, `hP2`. -/
theorem vcLadderScale_of_low (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L : ℝ) (w : Mom d) (P : Finset V → ℝ)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    {κ : D → (Fin d → ℤ)} (h : LadderScaleLow M L w P κ) : VCLadderScale K L w P κ := by
  intro S' hS' m u v hlad hat r hr
  obtain ⟨S0, hS0, hsub, hP⟩ := vc_maximal_sub K hM P hP1 hP2 hS'
  have hMl := vc_isLadder_gen K hlad
  have hgap := vc_gap_gen K hlad L w κ hr
  have := h m u v hMl.1 r hgap S0 hS0 (hat ▸ hsub)
  rw [hP]; exact this

/-- **`VCLadderScale` from the molecule-level restriction of `Adm`** (the original two-sided form; kept as the internal
route of session 2). -/
theorem vcLadderScale_of_adm (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L : ℝ) (w : Mom d) (P : Finset V → ℝ)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    {κ : D → (Fin d → ℤ)} (h : LadderScaleAdm M L w P κ) : VCLadderScale K L w P κ :=
  vcLadderScale_of_low K hM L w P hP1 hP2 (ladderScaleLow_of_adm h)

end Gen

end WaveTurbulence.GammaLow.FinalCount.Step1
