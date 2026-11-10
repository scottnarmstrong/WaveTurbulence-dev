/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3AncJoint
public import WaveTurbulence.Foundations.FinalCount.G3Rel
public import WaveTurbulence.Foundations.FinalCount.G3Run
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.FinalCount.VCAdm
/-! **FINALCOUNT-G3: ladders of a state are ladders of `M_sub`** (excessprop1 (1): ladder-scale heredity `hP`,
F-FC-3).

For a state `s` with `AncRel M₀ s a`, `DartRel M₀ s` in which every atom of degree `≥ 3` is an `ε`-atom, every ladder of
`s.M` (and its gap) is a ladder of `M₀` (with the same gap for the inherited decoration `k0 ∘ s.down`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V}

section lift
variable (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
include hA hD

theorem anc_eq_iff {c b : V} (hc : c ∈ s.M.atoms) (hb : b ∈ s.M.atoms) (hε : s.cls b = .eps) :
    a c = b ↔ c = b := by
  constructor
  · intro h; exact hA.uniq c hc b hb hε h
  · rintro rfl; exact hA.eps c hb hε

theorem dartsAt_eps_s {e : V} (he : e ∈ s.M.atoms) (hε : s.cls e = .eps) :
    M₀.dartsAt e = (s.M.dartsAt e).image s.down := by
  ext z
  simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := hA.surj e he hε z hz
    refine ⟨x, ?_, hx⟩
    exact hA.uniq _ (s.M.atom_mem x) e he hε (by rw [← hA.atom x, hx, hz])
  · rintro ⟨x, hx, rfl⟩
    rw [hA.atom x, hx]; exact hA.eps e he hε

theorem ends_down (x : s.D) : M₀.ends (s.down x) = Sym2.map a (s.M.ends x) := by
  unfold Molecule.ends
  rw [Sym2.map_mk, hD.mate, hA.atom, hA.atom]

/-- Bond multiplicities between two `ε`-atoms are those of `M_sub`. -/
theorem bondsBetween_lift {u v : V} (hu : u ∈ s.M.atoms) (hv : v ∈ s.M.atoms) (hue : s.cls u = .eps)
    (hve : s.cls v = .eps) (hne : u ≠ v) : s.M.bondsBetween u v = M₀.bondsBetween u v := by
  rw [Mole.bondsBetween_eq_card_darts s.M hne, Mole.bondsBetween_eq_card_darts M₀ hne,
    dartsAt_eps_s hA hD hu hue, Finset.filter_image, Finset.card_image_of_injective _ hA.inj]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  show s.M.atom (s.M.mate x) = v ↔ M₀.atom (M₀.mate (s.down x)) = v
  rw [hD.mate, hA.atom]
  exact (anc_eq_iff hA hD (s.M.atom_mem _) hv hve).symm

theorem directed_lift {u v : V} (hu : u ∈ s.M.atoms) (hv : v ∈ s.M.atoms) (hue : s.cls u = .eps)
    (hve : s.cls v = .eps) : s.M.Directed u v ↔ M₀.Directed u v := by
  constructor
  · rintro ⟨x, hx, hxa, hxb⟩
    refine ⟨s.down x, by rw [hD.out]; exact hx, ?_, ?_⟩
    · rw [hA.atom, hxa]; exact hA.eps u hu hue
    · rw [hD.mate, hA.atom, hxb]; exact hA.eps v hv hve
  · rintro ⟨z, hz, hza, hzb⟩
    have hzm : z ∈ M₀.dartsAt u := (mem_dartsAt M₀ u z).2 hza
    rw [dartsAt_eps_s hA hD hu hue, Finset.mem_image] at hzm
    obtain ⟨x, hx, rfl⟩ := hzm
    refine ⟨x, by rw [← hD.out]; exact hz, (mem_dartsAt s.M u x).1 hx, ?_⟩
    rw [hD.mate, hA.atom] at hzb
    exact (anc_eq_iff hA hD (s.M.atom_mem _) hv hve).1 hzb

end lift

section ladder
variable {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem deg_ge_two_nbrs {z b c : V} (hbc : b ≠ c) (hzb : z ≠ b) (hzc : z ≠ c) :
    M.bondsBetween z b + M.bondsBetween z c ≤ M.deg z := by
  rw [Mole.bondsBetween_eq_card_darts M hzb, Mole.bondsBetween_eq_card_darts M hzc]
  rw [← Finset.card_union_of_disjoint]
  · exact Finset.card_le_card (fun x hx => by
      rcases Finset.mem_union.1 hx with h | h <;> exact (Finset.mem_filter.1 h).1)
  · refine Finset.disjoint_left.2 fun x hx hx' => hbc ?_
    rw [← (Finset.mem_filter.1 hx).2, ← (Finset.mem_filter.1 hx').2]

theorem ladder_deg3 {m : ℕ} (x y : Fin (m + 1) → V) (hinj : Function.Injective (Sum.elim x y))
    (hrung : ∀ j, M.bondsBetween (x j) (y j) = 2)
    (hrail : ∀ j : Fin m, M.bondsBetween (x j.castSucc) (x j.succ) = 1) (hm : 1 ≤ m) (j : Fin (m + 1)) :
    3 ≤ M.deg (x j) := by
  have hxy : ∀ i k, x i ≠ y k := fun i k h => by
    have := @hinj (Sum.inl i) (Sum.inr k) h; cases this
  have hxx : ∀ i k, i ≠ k → x i ≠ x k := fun i k hik h => hik (by
    have := @hinj (Sum.inl i) (Sum.inl k) h; simpa using this)
  by_cases hj : (j : ℕ) < m
  · set k : Fin m := ⟨j, hj⟩ with hk
    have hjk : j = k.castSucc := Fin.ext rfl
    have h1 := deg_ge_two_nbrs M (z := x j) (b := y j) (c := x k.succ) (hxy _ _).symm (hxy _ _)
      (hxx _ _ (by rw [hjk]; exact (Fin.castSucc_lt_succ (i := k)).ne))
    rw [hrung j] at h1
    have h2 := hrail k
    rw [← hjk] at h2
    omega
  · have hjm : (j : ℕ) = m := by have := j.2; omega
    obtain ⟨k, hkj⟩ : ∃ k : Fin m, k.succ = j := ⟨⟨m - 1, by omega⟩, Fin.ext (by simp; omega)⟩
    have h1 := deg_ge_two_nbrs M (z := x j) (b := y j) (c := x k.castSucc) (hxy _ _).symm (hxy _ _)
      (hxx _ _ (by rw [← hkj]; exact (Fin.castSucc_lt_succ (i := k)).ne.symm))
    rw [hrung j] at h1
    have h2 := hrail k
    rw [hkj] at h2
    rw [Mole.bondsBetween_symm M] at h2
    omega

end ladder


section liftLadder
variable (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
  (hE : ∀ b ∈ s.M.atoms, 3 ≤ s.M.deg b → s.cls b = .eps)
include hA hD hE

theorem isLadder_lift {m : ℕ} {u v : Fin (m + 1) → V} (h : s.M.IsLadder u v) : M₀.IsLadder u v := by
  obtain ⟨hm, hinj, hat, hrung, hrail⟩ := h
  have hxy : ∀ i k, u i ≠ v k := fun i k hh => by
    have := @hinj (Sum.inl i) (Sum.inr k) hh; cases this
  have huu : ∀ i k, u i = u k → i = k := fun i k hh => by
    have := @hinj (Sum.inl i) (Sum.inl k) hh; simpa using this
  have hvv : ∀ i k, v i = v k → i = k := fun i k hh => by
    have := @hinj (Sum.inr i) (Sum.inr k) hh; simpa using this
  have hinj' : Function.Injective (Sum.elim v u) := by
    intro p q hpq
    rcases p with p | p <;> rcases q with q | q <;> simp only [Sum.elim_inl, Sum.elim_inr] at hpq
    · rw [hvv _ _ hpq]
    · exact absurd hpq.symm (hxy _ _)
    · exact absurd hpq (hxy _ _)
    · rw [huu _ _ hpq]
  have d3u := ladder_deg3 s.M u v hinj hrung (fun j => (hrail j).1) hm
  have d3v := ladder_deg3 s.M v u hinj'
    (fun j => by rw [Mole.bondsBetween_symm s.M]; exact hrung j)
    (fun j => (hrail j).2.1) hm
  have eu : ∀ j, s.cls (u j) = .eps := fun j => hE _ (hat j).1 (d3u j)
  have ev : ∀ j, s.cls (v j) = .eps := fun j => hE _ (hat j).2 (d3v j)
  have hcs : ∀ j : Fin m, j.castSucc ≠ j.succ := fun j => (Fin.castSucc_lt_succ (i := j)).ne
  refine ⟨hm, hinj, fun j => ⟨?_, ?_⟩, fun j => ?_, fun j => ⟨?_, ?_, ?_⟩⟩
  · have := hA.mem _ (hat j).1; rwa [hA.eps _ (hat j).1 (eu j)] at this
  · have := hA.mem _ (hat j).2; rwa [hA.eps _ (hat j).2 (ev j)] at this
  · rw [← bondsBetween_lift hA hD (hat j).1 (hat j).2 (eu j) (ev j) (hxy j j)]; exact hrung j
  · rw [← bondsBetween_lift hA hD (hat _).1 (hat _).1 (eu _) (eu _) (fun e => hcs j (huu _ _ e))]
    exact (hrail j).1
  · rw [← bondsBetween_lift hA hD (hat _).2 (hat _).2 (ev _) (ev _) (fun e => hcs j (hvv _ _ e))]
    exact (hrail j).2.1
  · rw [← directed_lift hA hD (hat _).1 (hat _).1 (eu _) (eu _),
      ← directed_lift hA hD (hat _).2 (hat _).2 (ev _) (ev _)]
    exact (hrail j).2.2

theorem isLadderSet_lift {S : Finset V} (h : s.M.IsLadderSet S) : M₀.IsLadderSet S := by
  obtain ⟨m, u, v, hl, rfl⟩ := h
  exact ⟨m, u, v, isLadder_lift hA hD hE hl, rfl⟩

theorem ladderGap_lift {k0 : D₀ → (Fin d → ℤ)} {L : ℝ} {w : Mom d} {m : ℕ} {u v : Fin (m + 1) → V}
    (h : s.M.IsLadder u v) {r : Mom d} :
    s.M.IsLadderGap L w (k0 ∘ s.down) u v h.1 r ↔ M₀.IsLadderGap L w k0 u v (isLadder_lift hA hD hE h).1 r := by
  have hat := h.2.2.1
  have hxy : ∀ i k, u i ≠ v k := fun i k hh => by
    have := @h.2.1 (Sum.inl i) (Sum.inr k) hh; cases this
  have huu : ∀ i k, u i = u k → i = k := fun i k hh => by
    have := @h.2.1 (Sum.inl i) (Sum.inl k) hh; simpa using this
  have hvv : ∀ i k, v i = v k → i = k := fun i k hh => by
    have := @h.2.1 (Sum.inr i) (Sum.inr k) hh; simpa using this
  have d3u := ladder_deg3 s.M u v h.2.1 h.2.2.2.1 (fun j => (h.2.2.2.2 j).1) h.1
  have hinj' : Function.Injective (Sum.elim v u) := by
    intro p q hpq
    rcases p with p | p <;> rcases q with q | q <;> simp only [Sum.elim_inl, Sum.elim_inr] at hpq
    · rw [hvv _ _ hpq]
    · exact absurd hpq.symm (hxy _ _)
    · exact absurd hpq (hxy _ _)
    · rw [huu _ _ hpq]
  have d3v := ladder_deg3 s.M v u hinj'
    (fun j => by rw [Mole.bondsBetween_symm s.M]; exact h.2.2.2.1 j)
    (fun j => (h.2.2.2.2 j).2.1) h.1
  have eu : ∀ j, s.cls (u j) = .eps := fun j => hE _ (hat j).1 (d3u j)
  have ev : ∀ j, s.cls (v j) = .eps := fun j => hE _ (hat j).2 (d3v j)
  have hm1 : 0 < m := h.1
  have hu1 : u ⟨1, by omega⟩ ∈ s.M.atoms := (hat _).1
  constructor
  · rintro ⟨x, y, hx, hy, hxa, hya, rfl⟩
    refine ⟨s.down x, s.down y, ?_, ?_, ?_, ?_, rfl⟩
    · rw [ends_down hA hD, hx, Sym2.map_mk, hA.eps _ (hat _).1 (eu _), hA.eps _ (hat _).1 (eu _)]
    · rw [ends_down hA hD, hy, Sym2.map_mk, hA.eps _ (hat _).2 (ev _), hA.eps _ (hat _).2 (ev _)]
    · rw [hA.atom, hxa, hA.eps _ (hat _).1 (eu _)]
    · rw [hA.atom, hya, hA.eps _ (hat _).2 (ev _)]
  · rintro ⟨x, y, hx, hy, hxa, hya, rfl⟩
    have hxm : x ∈ M₀.dartsAt (u 0) := (mem_dartsAt M₀ _ x).2 hxa
    have hym : y ∈ M₀.dartsAt (v 0) := (mem_dartsAt M₀ _ y).2 hya
    rw [dartsAt_eps_s hA hD (hat 0).1 (eu 0), Finset.mem_image] at hxm
    rw [dartsAt_eps_s hA hD (hat 0).2 (ev 0), Finset.mem_image] at hym
    obtain ⟨x', hx', rfl⟩ := hxm
    obtain ⟨y', hy', rfl⟩ := hym
    refine ⟨x', y', ?_, ?_, (mem_dartsAt s.M _ x').1 hx', (mem_dartsAt s.M _ y').1 hy', rfl⟩
    · have h1 := ends_down hA hD x'
      rw [hx] at h1
      have hxa' := (mem_dartsAt s.M _ x').1 hx'
      have h2 : Sym2.map a (s.M.ends x') = s(u 0, a (s.M.atom (s.M.mate x'))) := by
        unfold Molecule.ends; rw [Sym2.map_mk, hxa', hA.eps _ (hat _).1 (eu _)]
      rw [h2] at h1
      have h3 : a (s.M.atom (s.M.mate x')) = u ⟨1, by omega⟩ := Sym2.congr_right.1 h1.symm
      have h4 := (anc_eq_iff hA hD (s.M.atom_mem _) (hat _).1 (eu _)).1 h3
      unfold Molecule.ends; rw [hxa', h4]
    · have h1 := ends_down hA hD y'
      rw [hy] at h1
      have hya' := (mem_dartsAt s.M _ y').1 hy'
      have h2 : Sym2.map a (s.M.ends y') = s(v 0, a (s.M.atom (s.M.mate y'))) := by
        unfold Molecule.ends; rw [Sym2.map_mk, hya', hA.eps _ (hat _).2 (ev _)]
      rw [h2] at h1
      have h3 : a (s.M.atom (s.M.mate y')) = v ⟨1, by omega⟩ := Sym2.congr_right.1 h1.symm
      have h4 := (anc_eq_iff hA hD (s.M.atom_mem _) (hat _).2 (ev _)).1 h3
      unfold Molecule.ends; rw [hya', h4]

end liftLadder


/-- **Heredity of the ladder scale `P` at `M_sub`** (DH23 `kqmainest2`; named premise, discharged by the final assembly):
`P` is constant along inclusions of ladder atom sets of `M₀`. -/
def LadderHered (M₀ : Molecule V D₀) (P : Finset V → ℝ) : Prop :=
  ∀ S' S : Finset V, M₀.IsLadderSet S' → M₀.IsLadderSet S → S' ⊆ S → P S' = P S

section transfer
variable {D : Type*} [Fintype D] [DecidableEq D] {D' : Type*} [Fintype D'] [DecidableEq D']

theorem isLadderSet_sub_atoms {M : Molecule V D} {S : Finset V} (h : M.IsLadderSet S) : S ⊆ M.atoms := by
  obtain ⟨m, u, v, hl, rfl⟩ := h
  intro z hz
  unfold Molecule.ladderAtoms at hz
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hz
  rcases hz with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (hl.2.2.1 j).1
  · exact (hl.2.2.1 j).2

/-- every ladder atom set lies in a maximal one. -/
theorem exists_maximalLadder {M : Molecule V D} {S : Finset V} (h : M.IsLadderSet S) :
    ∃ S₁ ∈ M.maximalLadders, S ⊆ S₁ := by
  classical
  let F : Finset (Finset V) := M.atoms.powerset.filter fun T => M.IsLadderSet T ∧ S ⊆ T
  have hF : F.Nonempty := ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (isLadderSet_sub_atoms h), h, subset_rfl⟩⟩
  obtain ⟨S₁, hS₁, hmax⟩ := Finset.exists_max_image F Finset.card hF
  have hS₁' := Finset.mem_filter.1 hS₁
  obtain ⟨hp, hl, hsub⟩ : S₁ ∈ M.atoms.powerset ∧ M.IsLadderSet S₁ ∧ S ⊆ S₁ := ⟨hS₁'.1, hS₁'.2.1, hS₁'.2.2⟩
  refine ⟨S₁, Finset.mem_filter.2 ⟨hp, hl, fun S' hS' hsub' => ?_⟩, hsub⟩
  have hS'F : S' ∈ F := Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (isLadderSet_sub_atoms hS'), hS', hsub.trans hsub'⟩
  exact (Finset.eq_of_subset_of_card_le hsub' (hmax S' hS'F)).symm

variable (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
  (hE : ∀ b ∈ s.M.atoms, 3 ≤ s.M.deg b → s.cls b = .eps)
include hA hD hE

/-- the heredity hypothesis `hPinh` of the cut estimates, at every state (and its cut). -/
theorem hPinh_of_hered {P : Finset V → ℝ} (hP : LadderHered M₀ P)
    {s' : St.{u} V D₀} {a' : V → V} (hA' : AncRel M₀ s' a') (hD' : DartRel M₀ s')
    (hE' : ∀ b ∈ s'.M.atoms, 3 ≤ s'.M.deg b → s'.cls b = .eps) :
    ∀ S' ∈ s'.M.maximalLadders, ∀ S ∈ s.M.maximalLadders, S' ⊆ S → P S' = P S := by
  intro S' hS' S hS hsub
  have h1 := isLadderSet_lift hA' hD' hE' (Finset.mem_filter.1 hS').2.1
  have h2 := isLadderSet_lift hA hD hE (Finset.mem_filter.1 hS).2.1
  exact hP S' S h1 h2 hsub

end transfer

end WaveTurbulence.FinalCountG3
