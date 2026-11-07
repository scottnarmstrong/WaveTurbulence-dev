/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineCover
public import WaveTurbulence.Foundations.FinalCount.CoverProjU
/-! Vine removal, part 3 (FINALCOUNT-G2): the exact-label cover `𝔈(M) ≤ N · 𝔈(post)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical Set
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace VineCut
variable {M : Molecule V D} (K : VineCut M)

theorem restrS_x₁ (κ : D → (Fin d → ℤ)) : K.restrS κ K.x₁ = κ K.x₁ := by
  unfold restrS; rw [if_pos (K.atom_x₁ ▸ K.a_mem)]
theorem restrS_x₂ (κ : D → (Fin d → ℤ)) : K.restrS κ K.x₂ = κ K.x₂ := by
  unfold restrS; rw [if_pos (K.atom_x₂ ▸ K.a_mem)]
theorem restrS_y₁ (κ : D → (Fin d → ℤ)) : K.restrS κ K.y₁ = κ K.y₁ := by
  unfold restrS; rw [if_pos (K.atom_y₁ ▸ K.b_mem)]
theorem restrS_y₂ (κ : D → (Fin d → ℤ)) : K.restrS κ K.y₂ = κ K.y₂ := by
  unfold restrS; rw [if_pos (K.atom_y₂ ▸ K.b_mem)]

theorem atom_cases {z : V} (hz : z ∈ K.post.atoms) :
    z = K.fa ∨ z = K.fb ∨ (z ∈ M.atoms ∧ z ≠ K.C.upper ∧ z ≠ K.C.lower ∧ z ∉ K.C.atoms) := by
  have hz' : z ∈ K.cutMol.atoms ∧ z ∉ K.C.atoms := Finset.mem_filter.mp hz
  have := hz'.1
  rw [show K.cutMol.atoms = insert K.fb (insert K.fa M.atoms) from rfl] at this
  simp only [Finset.mem_insert] at this
  rcases this with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨h, fun e => hz'.2 (e ▸ K.a_mem), fun e => hz'.2 (e ▸ K.b_mem), hz'.2⟩)

theorem rho_mem (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) :
    (fun x : PDart K.cutMol (fun a => a ∉ K.C.atoms) => κ x.1) ∈ decSet K.post L γ δ w Adm'
      (K.postParams L w c β k0 (K.restrS κ)).1 (K.postParams L w c β k0 (K.restrS κ)).2.1
      (K.postParams L w c β k0 (K.restrS κ)).2.2 := by
  obtain ⟨hdec, hres, hadm⟩ := hκ
  have hJa : jointC (M := M) L w (K.restrS κ) K.x₁ K.x₂ = jointC (M := M) L w κ K.x₁ K.x₂ := by
    unfold jointC Molecule.kvec; rw [K.restrS_x₁, K.restrS_x₂]
  have hJb : jointC (M := M) L w (K.restrS κ) K.y₁ K.y₂ = jointC (M := M) L w κ K.y₁ K.y₂ := by
    unfold jointC Molecule.kvec; rw [K.restrS_y₁, K.restrS_y₂]
  have hEa : jointE (M := M) L w (K.restrS κ) K.x₁ K.x₂ = jointE (M := M) L w κ K.x₁ K.x₂ := by
    unfold jointE Molecule.kvec; rw [K.restrS_x₁, K.restrS_x₂]
  have hEb : jointE (M := M) L w (K.restrS κ) K.y₁ K.y₂ = jointE (M := M) L w κ K.y₁ K.y₂ := by
    unfold jointE Molecule.kvec; rw [K.restrS_y₁, K.restrS_y₂]
  refine ⟨⟨fun x => hdec.1 x.1, fun z hz => ?_⟩, ⟨fun z hz => ?_, fun x => hres.2 x.1⟩, hAdm' κ hadm⟩
  · have hP : z ∉ K.C.atoms := (Finset.mem_filter.mp hz).2
    have e : (∑ x ∈ K.post.dartsAt z, K.post.dartSign x • Molecule.kvec L w (fun y : PDart K.cutMol (fun a => a ∉ K.C.atoms) => κ y.1) x) =
        ∑ x ∈ K.post.dartsAt z, (fun y => M.dartSign y • Molecule.kvec L w κ y) x.1 := rfl
    rw [e]
    refine (restrictP_sum K.cutMol (fun a => a ∉ K.C.atoms) K.closed hP (fun y => M.dartSign y • Molecule.kvec L w κ y)).trans ?_
    rcases K.atom_cases hz with rfl | rfl | ⟨hzM, hza, hzb, -⟩
    · have h := K.sum_a (fun y => M.dartSign y • Molecule.kvec L w κ y)
      rw [hdec.2 _ K.a_atom] at h
      have : (K.postParams L w c β k0 (K.restrS κ)).1 K.fa = c K.C.upper - jointC (M := M) L w κ K.x₁ K.x₂ := by
        simp [postParams, hJa]
      rw [this]; unfold jointC
      exact eq_sub_of_add_eq h.symm
    · have h := K.sum_b (fun y => M.dartSign y • Molecule.kvec L w κ y)
      rw [hdec.2 _ K.b_atom] at h
      have : (K.postParams L w c β k0 (K.restrS κ)).1 K.fb = c K.C.lower - jointC (M := M) L w κ K.y₁ K.y₂ := by
        simp [postParams, K.fa_ne_fb.symm, hJb]
      rw [this]; unfold jointC
      exact eq_sub_of_add_eq h.symm
    · have hf : z ≠ K.fa := fun e => K.fa_fresh (e ▸ hzM)
      have hf' : z ≠ K.fb := fun e => K.fb_fresh (e ▸ hzM)
      have : (K.postParams L w c β k0 (K.restrS κ)).1 z = c z := by
        unfold postParams; simp only [if_neg hf, if_neg hf']
      rw [this, K.dartsAt_other hzM hza hzb]
      exact hdec.2 z hzM
  · have hP : z ∉ K.C.atoms := (Finset.mem_filter.mp hz).2
    have e : K.post.Gamma L w (fun y : PDart K.cutMol (fun a => a ∉ K.C.atoms) => κ y.1) z =
        ∑ x ∈ K.post.dartsAt z, (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2) x.1 := rfl
    have e2 : K.post.Gamma L w (fun y : PDart K.cutMol (fun a => a ∉ K.C.atoms) => κ y.1) z =
        ∑ x ∈ K.cutMol.dartsAt z, (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2) x :=
      restrictP_sum K.cutMol (fun a => a ∉ K.C.atoms) K.closed hP (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2)
    rw [e2]
    rcases K.atom_cases hz with rfl | rfl | ⟨hzM, hza, hzb, -⟩
    · have h := K.sum_a (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2)
      have h3 : ∑ x ∈ M.dartsAt K.C.upper, M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 = M.Gamma L w κ K.C.upper := rfl
      rw [h3] at h
      have : (K.postParams L w c β k0 (K.restrS κ)).2.1 K.fa = β K.C.upper - jointE (M := M) L w κ K.x₁ K.x₂ := by
        simp [postParams, hEa]
      rw [this]
      have h4 : ∑ x ∈ K.cutMol.dartsAt K.fa, M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 - (β K.C.upper - jointE (M := M) L w κ K.x₁ K.x₂) =
          M.Gamma L w κ K.C.upper - β K.C.upper := by unfold jointE; linarith
      rw [h4]; exact hres.1 _ K.a_atom
    · have h := K.sum_b (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2)
      have h3 : ∑ x ∈ M.dartsAt K.C.lower, M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 = M.Gamma L w κ K.C.lower := rfl
      rw [h3] at h
      have : (K.postParams L w c β k0 (K.restrS κ)).2.1 K.fb = β K.C.lower - jointE (M := M) L w κ K.y₁ K.y₂ := by
        simp [postParams, K.fa_ne_fb.symm, hEb]
      rw [this]
      have h4 : ∑ x ∈ K.cutMol.dartsAt K.fb, M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 - (β K.C.lower - jointE (M := M) L w κ K.y₁ K.y₂) =
          M.Gamma L w κ K.C.lower - β K.C.lower := by unfold jointE; linarith
      rw [h4]; exact hres.1 _ K.b_atom
    · have hf : z ≠ K.fa := fun e => K.fa_fresh (e ▸ hzM)
      have hf' : z ≠ K.fb := fun e => K.fb_fresh (e ▸ hzM)
      have : (K.postParams L w c β k0 (K.restrS κ)).2.1 z = β z := by
        unfold postParams; simp only [if_neg hf, if_neg hf']
      rw [this, K.dartsAt_other hzM hza hzb]
      exact hres.1 z hzM

theorem kappa_eq (κ κ' : D → (Fin d → ℤ)) (h1 : K.restrS κ = K.restrS κ')
    (h2 : (fun x : PDart K.cutMol (fun a => a ∉ K.C.atoms) => κ x.1) = fun x => κ' x.1) : κ = κ' := by
  funext x
  by_cases hx : K.cutMol.atom x ∈ K.C.atoms
  · have := congrFun h1 x
    unfold restrS at this
    rwa [if_pos hx, if_pos hx] at this
  · exact congrFun h2 ⟨x, hx⟩

/-- The set of label vectors of the removed VC. -/
def labelSet (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) :
    Set (D → (Fin d → ℤ)) :=
  K.restrS '' decSet M L γ δ w Adm c β k0

/-- **The exact-label cover.** -/
theorem countE_le_vine (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (N : ℕ)
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (K.labelSet L γ δ w Adm c β k0).encard ≤ N) :
    M.countE L γ δ w Adm ≤ (N : ℕ∞) * K.post.countE L γ δ w Adm' := by
  refine countE_le_mul_of_cover_projU M K.post L γ δ w Adm Adm' (fun κ x => κ x.1) N ?_
  intro c β k0 hP
  have hfin : (K.labelSet L γ δ w Adm c β k0).Finite := Set.finite_of_encard_le_coe (hN c β k0 hP)
  refine ⟨D → (Fin d → ℤ), hfin.toFinset, fun i => {κ | K.restrS κ = i},
    fun i => K.postParams L w c β k0 i, ?_, ?_, ?_, ?_⟩
  · have := hN c β k0 hP
    rw [hfin.encard_eq_coe_toFinset_card] at this
    exact_mod_cast this
  · intro i _
    exact K.postParams_ok hM L w c β k0 hP i
  · intro κ hκ
    refine Set.mem_iUnion₂.mpr ⟨K.restrS κ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨κ, hκ, rfl⟩
  · intro i _
    refine ⟨?_, ?_⟩
    · intro κ hκ κ' hκ' h
      exact K.kappa_eq κ κ' (hκ.1.trans hκ'.1.symm) h
    · rintro _ ⟨κ, ⟨hz, hκ⟩, rfl⟩
      have := K.rho_mem L γ δ w Adm Adm' hAdm' c β k0 κ hκ
      rw [hz] at this
      exact this

end VineCut
end WaveTurbulence.FinalCount
