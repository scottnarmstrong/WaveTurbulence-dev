/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain36
/-! **FINALCOUNT LOW-CHAIN, session 6 (11): bookkeeping of effective contributions.**  `sum_outdeg_eq_sum_indeg` (handshake for directions),
`eps_defect_le_L`: the surviving `ε`-atoms of degree `≠ 4` after Operation 5 number at most `e + 2r`
(`B ⊆ T` erased; every other defect has `contrib ≥ 1`, and `Σ_{v ∉ B} contrib = 2(R' - k)`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

section hs
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem sum_outdeg_eq_sum_indeg (M : Molecule V D) :
    ∑ a ∈ M.atoms, M.outdeg a = ∑ a ∈ M.atoms, M.indeg a := by
  have h1 := Finset.card_eq_sum_card_fiberwise (f := M.atom) (s := Finset.univ.filter fun x : D => M.out x = true) (t := M.atoms)
    (fun x _ => M.atom_mem x)
  have h2 := Finset.card_eq_sum_card_fiberwise (f := M.atom) (s := Finset.univ.filter fun x : D => ¬ M.out x = true) (t := M.atoms)
    (fun x _ => M.atom_mem x)
  have e1 : ∀ a, M.outdeg a = ((Finset.univ.filter fun x : D => M.out x = true).filter fun x => M.atom x = a).card := by
    intro a; unfold Molecule.outdeg Molecule.dartsAt
    congr 1; ext x; simp [and_comm]
  have e2 : ∀ a, M.indeg a = ((Finset.univ.filter fun x : D => ¬ M.out x = true).filter fun x => M.atom x = a).card := by
    intro a; unfold Molecule.indeg Molecule.dartsAt
    congr 1; ext x; simp [and_comm]
  have hc : (Finset.univ.filter fun x : D => M.out x = true).card = (Finset.univ.filter fun x : D => ¬ M.out x = true).card := by
    refine Finset.card_bij (fun x _ => M.mate x) ?_ ?_ ?_
    · intro x hx
      have := M.out_mate x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [this, hx]; simp
    · intro x _ y _ e; simpa [M.mate_mate] using congrArg M.mate e
    · intro y hy
      refine ⟨M.mate y, ?_, M.mate_mate y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      have := M.out_mate y
      cases hh : M.out y
      · rw [hh] at this; simpa using this
      · exact absurd hh hy
  simp only [e1, e2]
  rw [← h1, ← h2, hc]

end hs

section epsdef
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **`Z₅ ≤ e + 2r`:** the surviving `ε`-atoms of degree `≠ 4` are touched by the erased set, or have positive effective contribution. -/
theorem eps_defect_le_L {hf : HSt V D₀} {Tm : V → Prop} {R' r k : ℕ} {B : Finset V} (hg : Good R' hf.s) (hRk : r + k = R')
    (hBT : ∀ b ∈ B, b ∈ tameSet hf Tm) (hBdeg : ∀ b ∈ B, hf.s.M.deg b ≤ 2) (hBcard : B.card = k)
    {Rs : Finset V} (hR : CompRep (hf.op5 Tm).s.M Rs) :
    ∑ a ∈ Rs, WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) ≤
      eDart hf.s.M (tameSet hf Tm) + 2 * r := by
  set M5 := (hf.op5 Tm).s.M with hM5
  have hsum : ∑ a ∈ Rs, WaveTurbulence.FinalCountG8.epsDefect (compMol M5 a) (cl8 hf) =
      (M5.atoms.filter fun v => hf.s.cls v = .eps ∧ M5.deg v ≠ 4).card := by
    unfold WaveTurbulence.FinalCountG8.epsDefect
    simp only [Finset.card_filter, compMol_atoms_eq]
    rw [hR.sum_atoms (fun v => if hf.s.cls v = .eps ∧ M5.deg v ≠ 4 then 1 else 0)]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun v hv => ?_
    have hsc := (Finset.mem_filter.1 hv).2
    rw [compMol_deg _ _ hsc]
    simp only [cl8, g8Cls_isEps, toCls_isEps]
  rw [hsum]
  set T := tameSet hf Tm with hT
  set S := hf.s.M.atoms.filter (fun v => v ∉ B ∧ hf.s.cls v = .eps ∧ hf.s.M.deg v ≠ 4) with hS
  have hsub : (M5.atoms.filter fun v => hf.s.cls v = .eps ∧ M5.deg v ≠ 4) ⊆
      (M5.atoms.filter fun v => v ∉ T ∧ 1 ≤ multS hf.s.M T v) ∪ S := by
    intro v hv
    obtain ⟨hv5, hε, hd⟩ := Finset.mem_filter.1 hv
    obtain ⟨hvM, hvT⟩ := Op5.atoms_sub hv5
    have hk : keepS hf.s T v := (Finset.mem_filter.1 hv5).2
    have hd5 : M5.deg v = (eraseSet hf.s.M T).deg v := eraseSetSt_deg hk
    have hdc := eraseSet_deg_card hf.s.M T hvT
    by_cases hm : 1 ≤ multS hf.s.M T v
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hv5, hvT, hm⟩)
    · apply Finset.mem_union_right
      have hm0 : multS hf.s.M T v = 0 := by omega
      refine Finset.mem_filter.2 ⟨hvM, fun hb => hvT (hBT v hb), hε, ?_⟩
      omega
  -- counting `S`
  have hBsub : B ⊆ hf.s.M.atoms := fun b hb => (tameSet_mem.1 (hBT b hb)).1
  have hSle : S.card ≤ 2 * r := by
    have hc1 : ∀ v ∈ S, (1 : ℤ) ≤ contrib hf.s v := by
      intro v hv
      obtain ⟨hvM, -, hε, hd4⟩ := Finset.mem_filter.1 hv
      have := (Good.contrib_nonneg hg hvM)
      have h4 := deg_le_four hf.s.M (hg.1.bounds v hvM)
      unfold contrib at *
      rw [hε] at *
      simp only [Cls.base] at *
      omega
    have hB2 : ∀ b ∈ B, (2 : ℤ) ≤ contrib hf.s b := by
      intro b hb
      have hε := (tameSet_mem.1 (hBT b hb)).2.1
      have := hBdeg b hb
      unfold contrib
      rw [hε]
      simp only [Cls.base]
      omega
    have h1 : (S.card : ℤ) ≤ ∑ v ∈ S, contrib hf.s v := by
      calc (S.card : ℤ) = ∑ _v ∈ S, (1 : ℤ) := by simp
        _ ≤ _ := Finset.sum_le_sum hc1
    have h2 : ∑ v ∈ S, contrib hf.s v ≤ ∑ v ∈ hf.s.M.atoms \ B, contrib hf.s v := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v hv _ => Good.contrib_nonneg hg (Finset.mem_sdiff.1 hv).1)
      intro v hv
      obtain ⟨hvM, hvB, -⟩ := Finset.mem_filter.1 hv
      exact Finset.mem_sdiff.2 ⟨hvM, hvB⟩
    have h3 := Finset.sum_sdiff hBsub (f := contrib hf.s)
    have h4 := hg.sum_contrib
    have h5 : ∑ b ∈ B, (2 : ℤ) ≤ ∑ b ∈ B, contrib hf.s b := Finset.sum_le_sum hB2
    have h6 : ∑ b ∈ B, (2 : ℤ) = 2 * (k : ℤ) := by rw [← hBcard]; simp [mul_comm]
    have : ((r : ℤ)) + k = R' := by exact_mod_cast hRk
    omega
  calc _ ≤ ((M5.atoms.filter fun v => v ∉ T ∧ 1 ≤ multS hf.s.M T v) ∪ S).card := Finset.card_le_card hsub
    _ ≤ (M5.atoms.filter fun v => v ∉ T ∧ 1 ≤ multS hf.s.M T v).card + S.card := Finset.card_union_le _ _
    _ ≤ eDart hf.s.M T + 2 * r := by
        refine Nat.add_le_add (le_trans (Finset.card_le_card ?_) (touched_card_le hf.s.M T)) hSle
        intro v hv
        obtain ⟨hv5, hh⟩ := Finset.mem_filter.1 hv
        exact Finset.mem_filter.2 ⟨(Op5.atoms_sub hv5).1, hh⟩

end epsdef

end WaveTurbulence.FinalCountAsm
