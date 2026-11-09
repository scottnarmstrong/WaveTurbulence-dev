/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.PairGainInput
public import WaveTurbulence.Foundations.CountLemmas.TripleCount
import Mathlib.Tactic

/-! # The `(3,3)` pair gain for every `γ ∈ (0, 1)` (packet L6-COUNT, item C; M2 Lemma 2.3(4), §5.1)

DH23 Lemma A.3(4), system `{(1,2,3),(1,4,5)}`, at `0 < γ ≤ 1/2` (M2 Lemma 2.3(4), REF-M2 C): the reparametrization of
main's `A23HalfReparam` (Lemma 2.1 forms (i)–(iv), `ncard_le_coupled_cyclic/mixed/anti`, all γ-free; M2
`reparam_check.py` (R1)) maps the solution set injectively into `coupledTripleSet`, and main's `coupledTriple_bound`
(TARGET Lemma A.8, all `γ ∈ (0,1)`, exponent `3(d−γ) − γ₀`; = M2 Lemma 2.2 at `γ ≤ 1/2`) counts it. This replaces the
`γ > 1/2` count `a23Half_bound` (exponent `3(d−γ) − γ₀ − κ(γ)`), which is the only `γ > 1/2` input of main's
`pairGain33` / `pairGainAt`.

* `system12345_bound_all`: `#{(1,2,3),(1,4,5)} ≤ C δ⁻² L^{3(d−γ) − γ₀}` for `γ ∈ (0,1)` (copy of main's
  `system12345_bound` with `coupledTriple_bound` in place of `a23Half_bound`).
* `pair33_count_bound_all`, `pairGain33_all`: main's `pair33_count_bound`, `pairGain33` for `γ ∈ (0,1)`.
* `pairGainAt_all`: main's `pairGainAt` (both branches: `(3,4)` double, `(3,3)` single) for `γ ∈ (0,1)`; in particular
  the provider of `PairGainAt` at `γ ≤ 1/2` (M2 §5.1).

Copied from main `CountLemmas/A23HalfReparam.lean`, `FinalCount/Pair33Count.lean`, `FinalCount/PairGain.lean`,
`FinalCount/PairGainInput.lean` (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas WaveTurbulence.FinalCountG8

/-- **DH23 Lemma A.3(4), `{(1,2,3),(1,4,5)}`, every `γ ∈ (0,1)`** (M2 Lemma 2.3(4)):
`#{(1,2,3),(1,4,5)} ≤ C δ⁻² L^{3(d−γ) − γ₀}` for every pair of sign patterns without three equal signs in a tuple, all
centers, right sides and energies. Main's `system12345_bound` with `coupledTriple_bound` (all γ) in place of the
`γ > 1/2` count `a23Half_bound`. -/
theorem system12345_bound_all :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ (a : Fin 5 → Mom d) (εA εB : Fin 3 → ℤˣ),
        ¬ (εA 0 = εA 1 ∧ εA 1 = εA 2) → ¬ (εB 0 = εB 1 ∧ εB 1 = εB 2) →
        ∀ (nA nB : Fin d → ℤ) (βA βB : ℝ),
          ((system12345Set L a εA εB nA nB βA βB (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤
            C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) := by
  intro d hd γ hγ
  obtain ⟨C, L₀', hC, hbound⟩ := coupledTriple_bound d hd γ hγ
  refine ⟨C, hC, fun δ hδ => ?_⟩
  have hL₁ : ∀ L ≥ L₀', ∀ (ax ay az : Mom d) (nv : Fin d → ℤ) (α β : ℝ) (ζsel : Fin 3),
      ((coupledTripleSet L ax ay az (latticePoint L nv) α β (δ⁻¹ * L ^ (-2 * γ)) ζsel).ncard : ℝ) ≤
        C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) :=
    fun L hL ax ay az nv α β ζsel => (hbound L hL δ hδ ax ay az nv ζsel α β).2
  refine ⟨max L₀' 1, fun L hL a εA εB hεA hεB nA nB βA βB => ?_⟩
  have hLp : 0 < L := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hL)
  have hLL : L ≥ L₀' := (le_max_left _ _).trans hL
  set τ := δ⁻¹ * L ^ (-2 * γ)
  set S := system12345Set L a εA εB nA nB βA βB τ
  obtain ⟨sA, pA, qA, oA, hshA, hnA⟩ := tupleEqn_normalize (d := d) εA hεA
  obtain ⟨sB, pB, qB, oB, hshB, hnB⟩ := tupleEqn_normalize (d := d) εB hεB
  have hS : ∀ n ∈ S, (∀ t, NearLattice L (a t) (n t)) ∧
      NormTuple L n (![0, 1, 2] pA) (![0, 1, 2] qA) (![0, 1, 2] oA) (sA • nA) (sA * βA) τ ∧
      NormTuple L n (![0, 3, 4] pB) (![0, 3, 4] qB) (![0, 3, 4] oB) (sB • nB) (sB * βB) τ :=
    fun n hn => ⟨hn.1, hnA L n _ nA βA τ hn.2.1, hnB L n _ nB βB τ hn.2.2⟩
  rcases hshA with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hshB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  -- the nine (odd entry of `A`, odd entry of `B`) cases: (i) cyclic, (ii)/(iii) mixed, (iv) anti-parallel
  · exact (Nat.cast_le.mpr (ncard_le_coupled_cyclic hLp a 1 2 3 4 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_mixed hLp a 1 2 4 3 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_mixed hLp a 1 2 3 4 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_mixed hLp a 3 4 2 1 (by decide) _ _ _ _ τ S
      fun n hn => ⟨(hS n hn).1, (hS n hn).2.2, (hS n hn).2.1⟩)).trans (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_anti hLp a 2 1 4 3 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_anti hLp a 2 1 3 4 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_mixed hLp a 3 4 1 2 (by decide) _ _ _ _ τ S
      fun n hn => ⟨(hS n hn).1, (hS n hn).2.2, (hS n hn).2.1⟩)).trans (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_anti hLp a 1 2 4 3 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_anti hLp a 1 2 3 4 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)

/-- **The `(3,3)` single-pair label count, every `γ ∈ (0,1)`**: main's `pair33_count_bound` with
`system12345_bound_all`. -/
theorem pair33_count_bound_all (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
      a ≠ b → M.deg a = 3 → M.deg b = 3 → M.bondsBetween a b = 1 →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {a, b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a, b} Adm) := by
  classical
  obtain ⟨C, hC, hB⟩ := system12345_bound_all d hd γ hγ
  refine ⟨C, hC, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hB δ hδ
  refine ⟨max L₀ 1, fun L hL V D _ _ _ M hM a ha b hb hab hda hdb hbb Adm => ?_⟩
  have hLR : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right _ _).trans hL)
  obtain ⟨m, e2, e3, f4, f5, h12, h13, h23, h45, h46, h56, hma, hmb, hA, hB'⟩ := stars33 M hab hda hdb hbb
  have hcapA := not_all_out_equal_of_triple_star M hM ha h12 h13 h23 hA
  have hcapB := not_all_out_equal_of_triple_star M hM hb h45 h46 h56 hB'
  let e : Fin 5 → D := ![m, e2, e3, f4, f5]
  have hcover : ∀ z : DeletedDart M {a, b}, ∃ i : Fin 5, z.val = e i ∨ z.val = M.mate (e i) := by
    apply deleted_cover_of_incident_cover
    intro z hz
    rcases mem_insert.mp hz with hz | hz
    · have hmem : z ∈ M.dartsAt a := (Mole.mem_dartsAt M a z).mpr hz
      rw [hA] at hmem
      rcases mem_insert.mp hmem with h | hmem
      · exact ⟨0, Or.inl h⟩
      · rcases mem_insert.mp hmem with h | h
        · exact ⟨1, Or.inl h⟩
        · exact ⟨2, Or.inl (mem_singleton.mp h)⟩
    · have hmem : z ∈ M.dartsAt b := (Mole.mem_dartsAt M b z).mpr (mem_singleton.mp hz)
      rw [hB'] at hmem
      rcases mem_insert.mp hmem with h | hmem
      · exact ⟨0, Or.inr h⟩
      · rcases mem_insert.mp hmem with h | h
        · exact ⟨3, Or.inl h⟩
        · exact ⟨4, Or.inl (mem_singleton.mp h)⟩
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hLp γ δ (0 : Mom d) β k0).subset (fun _ h => h.2.1)
  let F := hf.toFinset
  have hmem (κ) : κ ∈ F ↔ κ ∈ A := hf.mem_toFinset
  by_cases hne : A.Nonempty
  · obtain ⟨κ0, hκ0⟩ := hne
    set εA : Fin 3 → ℤˣ := ![sgn M m, sgn M e2, sgn M e3] with hεA
    set εB : Fin 3 → ℤˣ := ![sgn M (M.mate m), sgn M f4, sgn M f5] with hεB
    set nA : Fin d → ℤ := doubleSign (M.out m) • κ0 m + doubleSign (M.out e2) • κ0 e2 + doubleSign (M.out e3) • κ0 e3
    set nB : Fin d → ℤ := doubleSign (M.out (M.mate m)) • κ0 m + doubleSign (M.out f4) • κ0 f4 +
      doubleSign (M.out f5) • κ0 f5
    let a5 : Fin 5 → Mom d := ![k0 m, k0 e2, k0 e3, k0 f4, k0 f5]
    let Q := F.image (localLabels M e)
    have hQS : ∀ q ∈ Q, q ∈ system12345Set L a5 εA εB nA nB (β a) (β b) (δ⁻¹ * L ^ (-2 * γ)) := by
      intro q hq
      obtain ⟨κ, hκ, rfl⟩ := mem_image.mp hq
      have hκA := (hmem κ).mp hκ
      have hmA := momentum_of_dartsAt_triple M L ha h12 h13 h23 hA hκA.1
      have hm0A := momentum_of_dartsAt_triple M L ha h12 h13 h23 hA hκ0.1
      have hmB := momentum_of_dartsAt_triple M L hb h45 h46 h56 hB' hκA.1
      have hm0B := momentum_of_dartsAt_triple M L hb h45 h46 h56 hB' hκ0.1
      have hEA := energy_of_dartsAt_triple M L γ δ ha h12 h13 h23 hA hκA.2.1
      have hEB := energy_of_dartsAt_triple M L γ δ hb h45 h46 h56 hB' hκA.2.1
      refine ⟨fun t => ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · fin_cases t
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 m : ‖latticePoint L (κ m) - k0 m‖ ≤ 1)
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 e2 : ‖latticePoint L (κ e2) - k0 e2‖ ≤ 1)
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 e3 : ‖latticePoint L (κ e3) - k0 e3‖ ≤ 1)
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 f4 : ‖latticePoint L (κ f4) - k0 f4‖ ≤ 1)
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 f5 : ‖latticePoint L (κ f5) - k0 f5‖ ≤ 1)
      · have key : doubleSign (M.out m) • κ m + doubleSign (M.out e2) • κ e2 + doubleSign (M.out e3) • κ e3 = nA := by
          apply latticePointHom_injective hLp.ne'
          simp only [nA, map_add, map_zsmul, latticePointHom_apply, doubleSign_out_smul]
          exact hmA.trans hm0A.symm
        simpa [Fin.sum_univ_three, localLabels, e, hεA, sgn_cast] using key
      · simpa [Fin.sum_univ_three, localLabels, e, hεA, sgn_cast_real] using hEA
      · have key : doubleSign (M.out (M.mate m)) • κ m + doubleSign (M.out f4) • κ f4 + doubleSign (M.out f5) • κ f5 = nB := by
          apply latticePointHom_injective hLp.ne'
          simp only [nB, map_add, map_zsmul, latticePointHom_apply, doubleSign_out_smul]
          rw [hκA.1.1 m] at hmB
          rw [hκ0.1.1 m] at hm0B
          exact hmB.trans hm0B.symm
        simpa [Fin.sum_univ_three, localLabels, e, hεB, sgn_cast] using key
      · rw [hκA.1.1 m] at hEB
        simpa [Fin.sum_univ_three, localLabels, e, hεB, sgn_cast_real] using hEB
    have hcA : ¬ (εA 0 = εA 1 ∧ εA 1 = εA 2) := fun ⟨h1, h2⟩ =>
      hcapA ⟨(sgn_eq_iff M m e2).mp (by simpa [hεA] using h1), (sgn_eq_iff M e2 e3).mp (by simpa [hεA] using h2)⟩
    have hcB : ¬ (εB 0 = εB 1 ∧ εB 1 = εB 2) := fun ⟨h1, h2⟩ =>
      hcapB ⟨(sgn_eq_iff M (M.mate m) f4).mp (by simpa [hεB] using h1), (sgn_eq_iff M f4 f5).mp (by simpa [hεB] using h2)⟩
    have hbound := hL₀ L hLR a5 εA εB hcA hcB nA nB (β a) (β b)
    have hfin : (system12345Set L a5 εA εB nA nB (β a) (β b) (δ⁻¹ * L ^ (-2 * γ))).Finite := by
      refine (Set.Finite.pi (t := fun t => {n : Fin d → ℤ | NearLattice L (a5 t) n})
        (fun t => finite_nearLattice hLp (a5 t))).subset ?_
      intro n hn t _
      exact hn.1 t
    have hQcard : (Q.card : ℝ) ≤ C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) := by
      refine le_trans ?_ hbound
      have := Set.ncard_le_ncard (show (Q : Set (Fin 5 → Fin d → ℤ)) ⊆ _ from hQS) hfin
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    have hlocal := card_deletedLabels_image_le_localLabels_image M {a, b} e hcover F
      (fun κ hκ => ((hmem κ).mp hκ).1.1)
    have hImage : (deletedLabels M {a, b} '' A).ncard = (F.image (deletedLabels M {a, b})).card := by
      have he : deletedLabels M {a, b} '' A = (F.image (deletedLabels M {a, b}) : Set _) := by
        rw [Finset.coe_image, hf.coe_toFinset]
      rw [he, Set.ncard_coe_finset]
    have hreal : ((deletedLabels M {a, b} '' A).ncard : ℝ) ≤ C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) := by
      rw [hImage]
      have hh : ((F.image (deletedLabels M {a, b})).card : ℝ) ≤ Q.card := by exact_mod_cast hlocal
      exact hh.trans hQcard
    have hnat : (deletedLabels M {a, b} '' A).ncard ≤ ⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ := by
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    have hEN : ((deletedLabels M {a, b} '' A).ncard : ℕ∞) ≤
        (⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ : ℕ∞) := by exact_mod_cast hnat
    exact (encard_le_deletedImage_mul_post M {a, b} hLp γ δ (0 : Mom d) Adm c β k0 hk0).trans
      (mul_le_mul_of_nonneg_right hEN bot_le)
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change A.encard ≤ _
    rw [he, Set.encard_empty]
    exact bot_le

/-- **`PairGainAt`, the `(3,3)` single-bond branch, every `γ ∈ (0,1)`**: main's `pairGain33` with
`pair33_count_bound_all`. -/
theorem pairGain33_all {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ C1 > 0, ∀ L ≥ max R (Real.exp 1),
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (_ : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) (_ : ∀ z, M.atom z ≠ M.atom (M.mate z))
        (a b : V), a ∈ M.atoms → b ∈ M.atoms → a ≠ b → M.deg a = 3 → M.deg b = 3 → M.bondsBetween a b = 1 →
        (∀ p ∈ M.atoms, ∀ q ∈ M.atoms, M.SameComponent p q) →
        (∀ p ∈ (Degen.eraseAtoms M {a, b}).atoms, ∀ q ∈ (Degen.eraseAtoms M {a, b}).atoms,
          (Degen.eraseAtoms M {a, b}).SameComponent p q) →
        ∀ (η : ℝ) (P : Finset V → ℝ), (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
        MoleProp.countAFree M L γ δ C1 (0 : Mom d) (lgAdm M L γ η P) P ≤
          ENNReal.ofReal ((C * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * Real.log L ^ 8 *
            L ^ (-min γ (1 - γ))) * AFreeSup (Degen.eraseAtoms M {a, b}) d L γ δ η C1 := by
  obtain ⟨C, hC, hB⟩ := pair33_count_bound_all d hd γ hγ
  refine ⟨C, hC, fun δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := hB δ hδ
  refine ⟨R, fun C1 hC1 L hL V D _ _ _ M hcap hloop a b ha hb hab hda hdb hbb hconnM hconnP η P hP => ?_⟩
  classical
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4 := fun v hv => by
    have h := hcap v hv
    have hsum := Mole.outdeg_add_indeg M v
    omega
  have hmol : M.IsMolecule := isMolecule_of_connected M hcap hconnM ha (by omega)
  have hne : (Degen.eraseAtoms M {a, b}).atoms.Nonempty := erase_pair_nonempty M hloop hab (by omega)
  have hcount := hR L hLR M hmol a ha b hb hab hda hdb hbb (lgAdm M L γ η P)
  have hr : ((M.deg a + M.deg b - M.bondsBetween a b : ℤ) - 2) = ((3 : ℕ) : ℤ) := by rw [hda, hdb, hbb]; norm_num
  have hmain := countAFree_le_erase_pair M hloop hdeg hab ha hb hconnM hconnP hne (d := d) (η := η) (C1 := C1) hL1 hlog hδ.1 hC1
    P hP (lgAdm M L γ η P) (fun κ h => h) ⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ hr hcount
  refine hmain.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hce := ceil_mul_le (c := C * δ⁻¹ ^ 2) (e := 3 * ((d : ℝ) - γ) - min γ (1 - γ)) (by have := hδ.1; positivity) hL1
    (by have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith [hγ.2, min_le_right γ (1 - γ)])
  have hexp : L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) * L ^ (-((d : ℝ) - γ) * ((3 : ℕ) : ℝ)) = L ^ (-min γ (1 - γ)) := by
    rw [← Real.rpow_add hLp]; congr 1; push_cast; ring
  have hb0 : 0 ≤ (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 := by have := hδ.1; positivity
  have hlog8 : (Real.log L ^ 2) ^ 4 = Real.log L ^ 8 := by ring
  rw [hlog8]
  calc ((⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ : ℕ) : ℝ) *
        (L ^ (-((d : ℝ) - γ) * ((3 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * Real.log L ^ 8
      ≤ ((C * δ⁻¹ ^ 2 + 1) * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))) *
        (L ^ (-((d : ℝ) - γ) * ((3 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * Real.log L ^ 8 := by
        gcongr
    _ = _ := by
        rw [mul_assoc (C * δ⁻¹ ^ 2 + 1), mul_assoc, ← mul_assoc (L ^ _), hexp]; ring

/-- **`PairGainAt` for every `γ ∈ (0,1)`** (DH23 L1965, Lemma A.3(4); M2 §5.1): main's `pairGainAt` with
`pairGain33_all` in place of the `γ > 1/2` branch `pairGain33`. In particular the provider at `0 < γ ≤ 1/2`. -/
theorem pairGainAt_all {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : δ ∈ Ioc (0 : ℝ) 1)
    {C1 : ℝ} (hC1 : 0 < C1) (η : ℝ) :
    ∃ K B R : ℝ, ∀ L ≥ R, PairGainAt.{u, v} d L γ δ η C1 K B := by
  obtain ⟨C4, R4, hC4, h4⟩ := pairGain34.{u, v} hd hγ
  obtain ⟨C3, hC3, h3⟩ := pairGain33_all.{u, v} hd hγ
  obtain ⟨R3, h3'⟩ := h3 δ hδ
  refine ⟨max ((C4 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) ((C3 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3),
    8, max (max R4 R3) (Real.exp 1), fun L hL => ?_⟩
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hl8 : Real.log L ^ (8 : ℝ) = Real.log L ^ 8 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  intro V D _ _ _ M hcap hloop a ha b hb hab hda hcases hconnM hconnP P hP
  unfold AFree
  rw [hl8]
  have hnn : 0 ≤ Real.log L ^ 8 * L ^ (-min γ (1 - γ)) := by
    have := Real.rpow_nonneg hLp.le (-min γ (1 - γ)); positivity
  have h4L : max R4 (Real.exp 1) ≤ L := max_le ((le_max_left _ _).trans ((le_max_left _ _).trans hL)) hLe
  have h3L : max R3 (Real.exp 1) ≤ L := max_le ((le_max_right _ _).trans ((le_max_left _ _).trans hL)) hLe
  rcases hcases with ⟨hdb, hbb⟩ | ⟨hdb, hbb⟩
  · refine (h4 δ hδ C1 hC1 L h4L M hcap hloop a b ha hb hab hda hdb hbb hconnM hconnP η P hP).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    calc (C4 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * Real.log L ^ 8 * L ^ (-min γ (1 - γ))
        = ((C4 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * (Real.log L ^ 8 * L ^ (-min γ (1 - γ))) := by ring
      _ ≤ _ := by
        rw [mul_assoc _ (Real.log L ^ 8)]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
  · refine (h3' C1 hC1 L h3L M hcap hloop a b ha hb hab hda hdb hbb hconnM hconnP η P hP).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    calc (C3 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * Real.log L ^ 8 * L ^ (-min γ (1 - γ))
        = ((C3 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * (Real.log L ^ 8 * L ^ (-min γ (1 - γ))) := by ring
      _ ≤ _ := by
        rw [mul_assoc _ (Real.log L ^ 8)]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hnn

end WaveTurbulence.GammaLow.FinalCount.Count
