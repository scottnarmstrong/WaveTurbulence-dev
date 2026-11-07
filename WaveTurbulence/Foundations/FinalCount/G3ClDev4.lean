/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev3
/-! **FINALCOUNT-G3 (R29 item 4, step 4): the flux identity and the pinned count of a cluster** (set version of `G3EraseDev4`).

For a decoration with all darts at the atoms of `K` equal to `k`, a component `C` of `M - K` satisfies
`∑_{b ∈ C} c_b = sgnCS C • (w + k/L)`; an unbalanced atom `a ∈ K` gives `c_a = (out_a - in_a) • (w + k/L)`.  Hence a pinned `K`
(`PinnedS`, A3) has its value `k` determined by `c` (clauses 1, 2) or fixed by subpro (3) (clause 3, the named input `hfix`),
so `𝔈(M) ≤ 𝔈(M - K)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {M : Molecule V D} {K : Finset V}

theorem mate_atom_cmpS {a : V} {x : D} (hx : M.atom x ∈ cmpS M K a) (hy : M.atom (M.mate x) ∉ K) :
    M.atom (M.mate x) ∈ cmpS M K a := by
  obtain ⟨hxm, hsc⟩ := mem_cmpS.1 hx
  refine mem_cmpS.2 ⟨Finset.mem_sdiff.2 ⟨M.atom_mem _, hy⟩, ?_⟩
  exact Relation.EqvGen.trans _ _ _ hsc
    (Relation.EqvGen.rel _ _ (eraseSet_adj_iff.2 ⟨⟨x, rfl, rfl⟩, (Finset.mem_sdiff.1 hxm).2, hy⟩))

/-- **The flux identity** for a component of `M - K`. -/
theorem flux_identityS {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c : V → Mom d} {k : Fin d → ℤ}
    (hdec : M.IsDecoration L w c κ) (hk : ∀ x, M.atom x ∈ K → κ x = k) (a : V) :
    ∑ b ∈ cmpS M K a, c b = sgnCS M K (cmpS M K a) • (w + latticePoint L k) := by
  set C := cmpS M K a with hC
  set f : D → Mom d := fun x => M.dartSign x • Molecule.kvec L w κ x with hf
  have hCatoms : ∀ b ∈ C, b ∈ M.atoms := fun b hb => (Finset.mem_sdiff.1 (mem_cmpS.1 hb).1).1
  have hCK : ∀ b ∈ C, b ∉ K := fun b hb => (Finset.mem_sdiff.1 (mem_cmpS.1 hb).1).2
  have h1 : ∑ b ∈ C, c b = ∑ b ∈ C, ∑ x ∈ M.dartsAt b, f x :=
    Finset.sum_congr rfl fun b hb => (hdec.2 b (hCatoms b hb)).symm
  have h2 : ∑ b ∈ C, ∑ x ∈ M.dartsAt b, f x = ∑ x ∈ Finset.univ.filter (fun x => M.atom x ∈ C), f x := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => M.atom x ∈ C)) (t := C)
      (g := M.atom) (fun x hx => (Finset.mem_filter.1 hx).2)]
    refine Finset.sum_congr rfl fun b hb => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hb, h⟩
    · intro h; exact h.2
  have h3 := Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun x => M.atom x ∈ C))
    (fun x => M.atom (M.mate x) ∈ C) f
  have h4 : ∑ x ∈ (Finset.univ.filter (fun x => M.atom x ∈ C)).filter (fun x => M.atom (M.mate x) ∈ C), f x = 0 := by
    refine Finset.sum_involution (fun x _ => M.mate x) (fun x hx => ?_) (fun x hx hne => ?_) (fun x hx => ?_)
      (fun x hx => M.mate_mate x)
    · have hm : κ (M.mate x) = κ x := hdec.1 x
      simp only [hf, Molecule.kvec, hm, dartSign_mate, neg_smul]
      abel
    · exact fun e => M.mate_ne x e
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.2, by rw [M.mate_mate]; exact hx.1⟩
  have h5 : ∑ x ∈ (Finset.univ.filter (fun x => M.atom x ∈ C)).filter (fun x => ¬ M.atom (M.mate x) ∈ C), f x =
      sgnCS M K C • (w + latticePoint L k) := by
    have hset : (Finset.univ.filter (fun x => M.atom x ∈ C)).filter (fun x => ¬ M.atom (M.mate x) ∈ C) =
        crossDS M K C := by
      ext x
      simp only [crossDS, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        by_contra hne
        exact h2 (mate_atom_cmpS h1 hne)
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun hmem => ?_⟩
        exact hCK _ hmem h2
    rw [hset]
    unfold sgnCS
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxv : M.atom (M.mate x) ∈ K := (Finset.mem_filter.1 hx).2.2
    have hm : κ (M.mate x) = k := hk _ hxv
    have : κ x = k := by rw [← hm]; exact (hdec.1 x).symm
    simp only [hf, Molecule.kvec, this]
  rw [h1, h2, ← h3, h4, h5, zero_add]

theorem latticePoint_injective (L : ℝ) (hL : 0 < L) : Function.Injective (latticePoint (d := d) L) := by
  intro z z' h
  funext i
  have h' := congrArg (fun v : Mom d => v i) h
  have h'' : ((z i : ℤ) : ℝ) / L = ((z' i : ℤ) : ℝ) / L := by simpa [latticePoint] using h'
  have : ((z i : ℤ) : ℝ) = ((z' i : ℤ) : ℝ) := by
    field_simp at h''; exact h''
  exact_mod_cast this

/-- At an unbalanced atom `a ∈ K` the label is determined by `c a`. -/
theorem unbalanced_label {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {c : V → Mom d} {k : Fin d → ℤ}
    (hdec : M.IsDecoration L w c κ) (hk : ∀ x, M.atom x ∈ K → κ x = k) {a : V} (haM : a ∈ M.atoms) (haK : a ∈ K) :
    c a = ((M.outdeg a : ℝ) - M.indeg a) • (w + latticePoint L k) := by
  rw [← hdec.2 a haM, ← sum_dartSign_dartsAt, Finset.sum_smul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxa : M.atom x = a := by simpa [Molecule.dartsAt] using hx
  have : κ x = k := hk x (hxa ▸ haK)
  simp only [Molecule.kvec, this]

/-- **Pinned clusters** (A3): `𝔈(M) ≤ 𝔈(M - K)`. `hfix` is subpro (3): an atom of degree `< 4` has its label fixed. -/
theorem countE_eraseSet_le_pinned {L γ δ : ℝ} (hL : 0 < L) {w : Mom d} (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (EDartS M K → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDartS M K => κ x.1))
    (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hKM : K ⊆ M.atoms) {x₀ : D} (hx₀ : M.atom x₀ ∈ K)
    (hdpos : ∀ a ∈ K, 1 ≤ M.deg a) (htame : ∀ κ, Adm κ → TameLabelsS M K κ)
    (hfix : ∀ a ∈ K, M.deg a < 4 → ∃ k, ∀ κ, Adm κ → ∀ x ∈ M.dartsAt a, κ x = k)
    (hP : PinnedS M K) :
    M.countE L γ δ w Adm ≤ ((1 : ℕ) : ℕ∞) * (eraseSet M K).countE L γ δ w Adm' := by
  refine countE_eraseSet_le_of_vals Adm Adm' hAdm' hM4 _ fun c β k0 hp => ?_
  by_cases hex : ∃ κ, κ ∈ decSet M L γ δ w Adm c β k0
  · obtain ⟨κ₀, hκ₀⟩ := hex
    have hkey : ∀ κ ∈ decSet M L γ δ w Adm c β k0, κ x₀ = κ₀ x₀ := by
      intro κ hκ
      have hk1 : ∀ x, M.atom x ∈ K → κ x = κ x₀ := fun x hx => htame κ hκ.2.2 x x₀ hx hx₀
      have hk2 : ∀ x, M.atom x ∈ K → κ₀ x = κ₀ x₀ := fun x hx => htame κ₀ hκ₀.2.2 x x₀ hx hx₀
      rcases hP with ⟨a, haK, hne⟩ | ⟨a, ha, hsg⟩ | ⟨a, haK, hlt⟩
      · have e1 := unbalanced_label hκ.1 hk1 (hKM haK) haK
        have e2 := unbalanced_label hκ₀.1 hk2 (hKM haK) haK
        rw [e1] at e2
        have hne' : ((M.outdeg a : ℝ) - M.indeg a) ≠ 0 := by
          intro h; apply hne; exact_mod_cast (sub_eq_zero.1 h)
        have e3 := smul_right_injective (Mom d) hne' e2
        exact latticePoint_injective L hL (add_left_cancel e3)
      · have e1 := flux_identityS hκ.1 hk1 a
        have e2 := flux_identityS hκ₀.1 hk2 a
        rw [e1] at e2
        have e3 := smul_right_injective (Mom d) hsg e2
        exact latticePoint_injective L hL (add_left_cancel e3)
      · obtain ⟨k, hkf⟩ := hfix a haK hlt
        obtain ⟨y, hy⟩ := Finset.card_pos.1 (hdpos a haK)
        have hya : M.atom y = a := by simpa [Molecule.dartsAt] using hy
        have h1 := hkf κ hκ.2.2 y hy
        have h2 := hkf κ₀ hκ₀.2.2 y hy
        rw [hk1 y (hya ▸ haK)] at h1
        rw [hk2 y (hya ▸ haK)] at h2
        rw [h1, h2]
    exact ⟨{κ₀ x₀}, by simp, fun κ hκ => ⟨κ x₀, by simp [hkey κ hκ],
      fun x hx => htame κ hκ.2.2 x x₀ hx hx₀⟩⟩
  · exact ⟨∅, by simp, fun κ hκ => absurd ⟨κ, hκ⟩ hex⟩

end WaveTurbulence.FinalCountG3
