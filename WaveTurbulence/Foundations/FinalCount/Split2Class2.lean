/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Split2Class1
import Mathlib.Tactic

/-! # The second class of the two-chain split (finalcount-g8, F6-1)

`class2_bound`: if every good pair of multipliers transports `κ` to a decoration of `𝕄₁` with `Q`, then operation (d)
on the first chain (`opDW`) followed by operation (c) on the second chain (`opCFree`) reduces the count to the second
clause of `SplitBound`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section Relabel
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

omit [DecidableEq D] [DecidableEq E] [Fintype D] [Fintype E] in
theorem largeGap_relabel (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (ha : ∀ x, N.atom (f x) = M.atom x) (ho : ∀ x, N.out (f x) = M.out x) {d : ℕ} {L γ η : ℝ}
    {κ : D → (Fin d → ℤ)} (h : MoleProp.LargeGap M L γ η (0 : Mom d) κ) :
    MoleProp.LargeGap N L γ η (0 : Mom d) (MoleProp.relabelDartLabels f κ) := by
  have hkv (x : D) : Molecule.kvec L 0 (MoleProp.relabelDartLabels f κ) (f x) = Molecule.kvec L 0 κ x := by
    simp only [Molecule.kvec, MoleProp.relabelDartLabels, Equiv.coe_fn_mk, f.symm_apply_apply]
  intro y₁ y₂ h12 hdir
  obtain ⟨x₁, rfl⟩ := f.surjective y₁
  obtain ⟨x₂, rfl⟩ := f.surjective y₂
  rw [hkv, hkv]
  exact h x₁ x₂ (by rw [← ha, ← ha]; exact h12) (by rw [← ho, ← ho]; exact hdir)

omit [DecidableEq D] [DecidableEq E] [Fintype D] [Fintype E] in
theorem relabel_apply (f : D ≃ E) {K : Type*} (κ : D → K) (x : D) :
    MoleProp.relabelDartLabels f κ (f x) = κ x := by
  simp only [MoleProp.relabelDartLabels, Equiv.coe_fn_mk, f.symm_apply_apply]

end Relabel

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem class2_bound {d : ℕ} {L γ δ η C1 ε₂ : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hη : 0 ≤ η)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (hL11a : 11 ≤ L ^ (η / 2)) (hL11b : 11 ≤ L ^ (η / 2 / 2))
    {M₀ : Molecule V D} (Ta : TwoExit M₀) (Tb : TwoExit Ta.post) (Bs : Finset V)
    (hcap : ∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) (hloop : ∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z))
    (hconn : ∀ a ∈ M₀.atoms, ∀ b ∈ M₀.atoms, M₀.SameComponent a b)
    (hY3a : Ta.Y.card ≤ 3) (hcha : ∀ b ∈ Ta.Y, M₀.outdeg b = 1 ∧ M₀.indeg b = 1)
    (hYconna : ∀ a ∈ Ta.Y, ∀ b ∈ Ta.Y, (piece M₀ Ta.Y).SameComponent a b)
    (hcBa : Ta.c ∉ Bs) (hdBa : Ta.d ∉ Bs)
    (hpostA : ∀ a ∈ Ta.post.atoms, ∀ b ∈ Ta.post.atoms, Ta.post.SameComponent a b)
    (hopenA : ∀ S ∈ MoleProp.ladderCells Ta.post, GoodCell Ta.post S)
    (hcap1 : ∀ a ∈ Ta.post.atoms, Ta.post.outdeg a ≤ 2 ∧ Ta.post.indeg a ≤ 2)
    (hloop1 : ∀ z, Ta.post.atom z ≠ Ta.post.atom (Ta.post.mate z))
    (hchb : ∀ b ∈ Tb.Y, Ta.post.outdeg b = 1 ∧ Ta.post.indeg b = 1)
    (hYconnb : ∀ a ∈ Tb.Y, ∀ b ∈ Tb.Y, (piece Ta.post Tb.Y).SameComponent a b)
    (hcBb : Tb.c ∉ Bs \ Ta.Y) (hdBb : Tb.d ∉ Bs \ Ta.Y)
    (hpostE : ∀ a ∈ (Degen.eraseAtoms Ta.post Tb.Y).atoms, ∀ b ∈ (Degen.eraseAtoms Ta.post Tb.Y).atoms,
      (Degen.eraseAtoms Ta.post Tb.Y).SameComponent a b)
    (hxy : Ta.post.atom Tb.y = Ta.post.atom Tb.x)
    (hBs : (Bs \ Ta.Y) \ Tb.Y = ∅)
    {Dcl : Type*} [Fintype Dcl] [DecidableEq Dcl] (cl : Molecule V Dcl)
    (Φ : Degen.RetainedDart Ta.post Tb.Y ⊕ Bool ≃ Dcl)
    (hA : Tb.post.atoms = cl.atoms) (ha : ∀ x, cl.atom (Φ x) = Tb.post.atom x)
    (hm : ∀ x, cl.mate (Φ x) = Φ (Tb.post.mate x)) (ho : ∀ x, cl.out (Φ x) = Tb.post.out x)
    (Q : (Dcl → (Fin d → ℤ)) → Prop)
    (hQ2 : ∀ P : Finset V → ℝ,
      (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond cl (Φ (Sum.inr true))), 0 ≤ P S) →
      MoleProp.countAFree (MoleProp.eraseBond cl (Φ (Sum.inr true))) L γ δ C1 (0 : Mom d)
        (fun κ => lgAdm (MoleProp.eraseBond cl (Φ (Sum.inr true))) L γ (η / 2 / 2) P κ ∧
          MoleProp.erasedBondAdmissibility cl (Φ (Sum.inr true))
            (fun κ0 => MoleProp.LargeGap cl L γ (η / 2 / 2) (0 : Mom d) κ0 ∧ Q κ0) κ) P ≤ ENNReal.ofReal ε₂)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S)
    (Adm : (D → (Fin d → ℤ)) → Prop) (hAdm : ∀ κ, Adm κ → lgAdmOff M₀ Bs L γ η P κ)
    (hgap : ∀ κ, Adm κ → ∀ g, Ta.postLabels κ g Tb.x ≠ Ta.postLabels κ g Tb.y) :
    MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧ ¬ Cls1 Ta Tb Φ Q Bs L γ η κ) P ≤
      ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) *
        (ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ (1 - γ)) * ENNReal.ofReal ε₂) := by
  classical
  have hY3a' := hY3a
  have hA1 := opDW hL hlog hδ hC1 M₀ Ta hcap hloop hconn Bs hY3a hcha hYconna hpostA hopenA P hP
    (fun κ => Adm κ ∧ ¬ Cls1 Ta Tb Φ Q Bs L γ η κ) (fun κ h => hAdm κ h.1)
    (fun g₁ κ => ∀ g₂ ∈ Icc (0 : ℤ) 4, Tb.PostGoodOff (Bs \ Ta.Y) L γ (η / 2 / 2) (Ta.postLabels κ g₁) g₂ →
      Q (MoleProp.relabelDartLabels Φ (Tb.postLabels (Ta.postLabels κ g₁) g₂)))
    (by
      rintro κ ⟨hκ, hn⟩ hsym
      obtain ⟨g₁, hg₁, hpa⟩ := Ta.exists_postGoodOff hL hL11a hsym hcap Bs hcBa hdBa (hAdm κ hκ).1
      refine ⟨g₁, hg₁, hpa, fun g₂ hg₂ hpb => ?_⟩
      by_contra hq
      exact hn ⟨g₁, hg₁, g₂, hg₂, hpa, hpb, hq⟩)
  refine hA1.trans (mul_le_mul' le_rfl ?_)
  refine iSup₂_le fun g₁ hg₁ => ?_
  unfold TwoExit.afreeSupPost
  refine iSup₂_le fun P' hP' => ?_
  -- the dart isomorphism between the erased post and `𝕄₁ ∖ ℓ`
  have hmt : cl.mate (Φ (Sum.inr true)) = Φ (Sum.inr false) := by rw [hm]; rfl
  set e := Φ (Sum.inr true) with he
  let ι := withoutEquiv cl Φ hmt
  have hAe : (Degen.eraseAtoms Ta.post Tb.Y).atoms = (MoleProp.eraseBond cl e).atoms := by
    change Ta.post.atoms \ Tb.Y = cl.atoms
    rw [← Tb.post_atoms]; exact hA
  have hae : ∀ z, (MoleProp.eraseBond cl e).atom (ι z) = (Degen.eraseAtoms Ta.post Tb.Y).atom z :=
    fun z => ha (Sum.inl z)
  have hme : ∀ z, (MoleProp.eraseBond cl e).mate (ι z) = ι ((Degen.eraseAtoms Ta.post Tb.Y).mate z) :=
    fun z => Subtype.ext (hm (Sum.inl z))
  have hoe : ∀ z, (MoleProp.eraseBond cl e).out (ι z) = (Degen.eraseAtoms Ta.post Tb.Y).out z :=
    fun z => ho (Sum.inl z)
  have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms Ta.post Tb.Y), 0 ≤ P' S' := fun S' hS' => by
    have := (MoleProp.isLadderCell_erase_iff Ta.post Tb.Y S').mp (mem_filter.mp hS').2
    exact hP' S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms Ta.post this.1), this.1⟩)
  have hcellsE := MoleProp.ladderCells_eq_of_dart_equiv (Degen.eraseAtoms Ta.post Tb.Y) (MoleProp.eraseBond cl e)
    ι hAe hae hme hoe
  -- operation (c) on the second chain
  have hC := opCFree hγ hL hlog hδ hC1 Ta.post hloop1 hcap1 hpostA Tb.Y Tb.x Tb.y Tb.sub hchb Tb.cross Tb.far
    hYconnb hpostE P' hP'
    (Ta.postAdmOff Bs (fun κ => Adm κ ∧ ¬ Cls1 Ta Tb Φ Q Bs L γ η κ)
      (fun g₁ κ => ∀ g₂ ∈ Icc (0 : ℤ) 4, Tb.PostGoodOff (Bs \ Ta.Y) L γ (η / 2 / 2) (Ta.postLabels κ g₁) g₂ →
        Q (MoleProp.relabelDartLabels Φ (Tb.postLabels (Ta.postLabels κ g₁) g₂))) L γ (η / 2) P' g₁)
    (by
      rintro κ' ⟨_, κ, ⟨hκ, _⟩, _, _, rfl⟩
      exact ⟨Tb.x, Tb.y, Tb.atom_x, hxy, Tb.ne, hgap κ hκ g₁⟩)
  refine hC.trans (mul_le_mul' le_rfl ?_)
  refine (MoleProp.countAFree_le_of_dart_equiv (Degen.eraseAtoms Ta.post Tb.Y) (MoleProp.eraseBond cl e) ι hAe hae
    hme hoe L γ δ C1 0 _ (fun κ => lgAdm (MoleProp.eraseBond cl e) L γ (η / 2 / 2) P' κ ∧
      MoleProp.erasedBondAdmissibility cl e (fun κ0 => MoleProp.LargeGap cl L γ (η / 2 / 2) (0 : Mom d) κ0 ∧ Q κ0) κ)
    ?_ P').trans (hQ2 P' (fun S hS => hPerase S (by rw [hcellsE]; exact hS)))
  rintro κ'' ⟨κ', ⟨hlg', κ, ⟨hκ, hn⟩, hsym, hW, rfl⟩, hsym', rfl⟩
  have hlgE := lgAdmOff_erase Ta.post (Bs \ Ta.Y) Tb.Y hlg'
  rw [hBs] at hlgE
  have h2 := lgAdm_mono (Degen.eraseAtoms Ta.post Tb.Y) hL (show η / 2 / 2 ≤ η / 2 by linarith) (lgAdmOff_empty hlgE)
  refine ⟨lgAdm_relabel _ _ ι hAe hae hme hoe h2, ?_⟩
  obtain ⟨g₂, hg₂, hpb⟩ := Tb.exists_postGoodOff hL hL11b (κ := Ta.postLabels κ g₁) hsym' hcap1 (Bs \ Ta.Y) hcBb hdBb
    hlg'.1
  refine ⟨MoleProp.relabelDartLabels Φ (Tb.postLabels (Ta.postLabels κ g₁) g₂),
    ⟨largeGap_relabel Tb.post cl Φ ha ho (postGoodOff_largeGap Tb hBs hpb), hW g₂ hg₂ hpb⟩, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := Φ.surjective x
    rw [hm, relabel_apply, relabel_apply]
    exact Tb.postLabels_mate hsym' g₂ y
  · funext x
    obtain ⟨z, rfl⟩ := ι.surjective x
    change MoleProp.relabelDartLabels Φ _ (Φ (Sum.inl z)) = MoleProp.relabelDartLabels ι _ (ι z)
    rw [relabel_apply, relabel_apply]
    rfl

end WaveTurbulence.FinalCountG8
