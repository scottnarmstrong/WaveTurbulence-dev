/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Layervine.Bound
public import WaveTurbulence.Foundations.LayerCnt.HExit5
public import WaveTurbulence.Foundations.LayerCnt.ChainGarden
/-! # The layer range of a coherent (CL) T-vine (packet L5c, layervine′)

TARGET L1523–L1531 for T-vines (N3 Theorem 6 (ii), (iii); L3's `LayervineStatement`): for a coherent pre-layering
(every piece in one layer) satisfying the criterion `canonequiv` on the vine region, every atom has a layer between
those of the lower joint `b` and the upper joint `a`.
* spine pieces (pieces separating `a` from `b`): the parent chain from `b` to `a` (main's `chain_exists`) meets every
  spine piece, and layers do not decrease along it;
* pendant pieces `Y_k`: `H_k = Y_k ∪ ⋯ ∪ Y_s` has degree-four atoms and exactly two exits, single bonds ending in `Y_k`
  (Theorem 6 (iii)); main's generic `exit_lemma` gives `min(outer layers) ≤` the layer of `Y_k`, and the outer ends lie
  outside `H_k`, where the bound is already known (induction on `k`).
The upper half is main's `layer_le_upper` (any (CL) block). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.LayerCnt WaveTurbulence.Vine TTree

/-- **NAMED INPUT (N3 Theorem 6 (i)–(iii), both labellings; owner L3).** Exactly L3's
`TVine.Struct.LayervineStatement` (research-gamma-half-3/NOTES.txt L142–L174) at the universe of garden molecules. -/
def LayervineInput : Prop := TVine.Struct.LayervineStatement.{0, 0}

section general
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- A non-decreasing chain from `b` to `a` inside `S` meets every set separating `a` from `b`. -/
theorem stepF_chain_hits {S P : Finset V} {f : V → ℕ} {a b : V}
    (hch : Relation.ReflTransGen (StepF M S f) b a) (hP : ¬ TVine.Struct.ConnIn M (S \ P) a b) :
    ∃ z ∈ P, f b ≤ f z := by
  have key : ∀ c, Relation.ReflTransGen (StepF M S f) b c →
      (∃ z ∈ P, f b ≤ f z) ∨ (TVine.Struct.ConnIn M (S \ P) b c ∧ f b ≤ f c) := by
    intro c hc
    induction hc with
    | refl => exact Or.inr ⟨Relation.EqvGen.refl _, le_rfl⟩
    | @tail c d _ hst ih =>
      rcases ih with h | ⟨hconn, hle⟩
      · exact Or.inl h
      obtain ⟨hcS, hdS, hbond, hcd⟩ := hst
      by_cases hcP : c ∈ P
      · exact Or.inl ⟨c, hcP, hle⟩
      by_cases hdP : d ∈ P
      · exact Or.inl ⟨d, hdP, hle.trans hcd⟩
      refine Or.inr ⟨Relation.EqvGen.trans _ _ _ hconn ?_, hle.trans hcd⟩
      unfold Molecule.groupBonds at hbond
      obtain ⟨x, hx, hxe⟩ := Multiset.mem_map.mp hbond
      have hxg := (Finset.mem_filter.mp hx).2.2
      have hxe' : s(M.atom x, M.atom (M.mate x)) = s(c, d) := hxe
      have hcm : c ∈ S \ P := mem_sdiff.mpr ⟨hcS, hcP⟩
      have hdm : d ∈ S \ P := mem_sdiff.mpr ⟨hdS, hdP⟩
      rcases Sym2.eq_iff.mp hxe' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Relation.EqvGen.rel _ _ ⟨x, ⟨by rw [h1]; exact hcm, by rw [h2]; exact hdm⟩, h1, h2⟩
      · exact Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ ⟨x, ⟨by rw [h1]; exact hdm, by rw [h2]; exact hcm⟩, h1, h2⟩)
  rcases key a hch with h | ⟨hconn, _⟩
  · exact h
  · exact absurd (Relation.EqvGen.symm _ _ hconn) hP

/-- Index `0` means every piece is coherent. -/
theorem coherent_of_tvineIncoherency_zero {S : Finset V} {a b : V} {f : V → ℕ}
    (h : tvineIncoherency M S a b f = 0) : ∀ P ∈ M.tvineGroups S a b, ∀ x ∈ P, ∀ y ∈ P, f x = f y := by
  intro P hP
  unfold tvineIncoherency at h
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not] at h
  exact h hP

/-- Pieces lie in `S ∖ {a, b}`. -/
theorem mem_piece_interior {S : Finset V} {a b : V} {P : Finset V} (hP : P ∈ M.tvineGroups S a b) {x : V}
    (hx : x ∈ P) : x ∈ (S.erase a).erase b := by
  classical
  unfold Molecule.tvineGroups Molecule.pieces at hP
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hP
  exact (Finset.mem_filter.mp hx).1

end general

theorem mem_drop_iff_get {α : Type} {l : List α} {k : ℕ} {L : α} :
    L ∈ l.drop k ↔ ∃ j, ∃ hj : j < l.length, k ≤ j ∧ l.get ⟨j, hj⟩ = L := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_drop] at hi
    exact ⟨k + i, by omega, by omega, by simp [List.getElem_drop]⟩
  · rintro ⟨j, hj, hkj, rfl⟩
    refine ⟨j - k, by simp; omega, ?_⟩
    simp only [List.getElem_drop, List.get_eq_getElem]
    congr 1
    omega

section garden
variable {w : ℕ}

/-- Interior atoms of a block of a garden have degree four, all inside the block. -/
theorem block_interior_facts (G : Garden w) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) :
    ∀ x ∈ (S.erase a).erase b, G.molecule.deg x = 4 ∧
      ∀ d, G.molecule.atom d = x → G.molecule.atom (G.molecule.mate d) ∈ S := by
  intro x hx
  obtain ⟨hxb, hx'⟩ := mem_erase.mp hx
  obtain ⟨hxa, hxS⟩ := mem_erase.mp hx'
  have h4 := hB.2.2.2.2.2.2.2.2.1 x hxS hxa hxb
  have hle : G.molecule.deg x ≤ 4 := Mole.garden_molecule_deg_le_four G x
  have hdi : G.molecule.degIn S x ≤ G.molecule.deg x := Mole.degIn_le_deg G.molecule S x
  refine ⟨by omega, fun d hd => ?_⟩
  have heq : (G.molecule.dartsAt x).filter (fun y => G.molecule.InGroup S y) = G.molecule.dartsAt x :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by
      change G.molecule.deg x ≤ G.molecule.degIn S x; omega)
  have hdm : d ∈ G.molecule.dartsAt x := by simp [Molecule.dartsAt, hd]
  rw [← heq] at hdm
  exact (Finset.mem_filter.mp hdm).2.2

/-- A dart along a bond with given ends, at the second end. -/
theorem dart_at_end (G : Garden w) {e : GardenDart G} {u v : GBranch G.tree} (he : G.molecule.ends e = s(u, v)) :
    ∃ d, (d = e ∨ d = G.molecule.mate e) ∧ G.molecule.atom d = v ∧ G.molecule.atom (G.molecule.mate d) = u := by
  have he' : s(G.molecule.atom e, G.molecule.atom (G.molecule.mate e)) = s(u, v) := he
  rcases Sym2.eq_iff.mp he' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨G.molecule.mate e, Or.inr rfl, h2, by rw [G.molecule.mate_mate]; exact h1⟩
  · exact ⟨e, Or.inl rfl, h1, h2⟩

/-- Two single exits give main's `ExitData` (exactly two exit darts). -/
theorem exitData_of_two_exits (G : Garden w) {S H : Finset (GBranch G.tree)}
    (hint : ∀ x ∈ H, G.molecule.deg x = 4 ∧ ∀ d, G.molecule.atom d = x → G.molecule.atom (G.molecule.mate d) ∈ S)
    (hcross : TVine.Struct.crossBonds G.molecule H (S \ H) = 2) {x0 x0' y y' : GBranch G.tree}
    (hx0 : x0 ∈ S \ H) (hx0' : x0' ∈ S \ H) (hxx : x0 ≠ x0') (hyH : y ∈ H) (hy'H : y' ∈ H)
    (hb1 : G.molecule.bondsBetween x0 y = 1) (hb2 : G.molecule.bondsBetween x0' y' = 1) :
    ∃ d1 d2, ExitData G H d1 d2 ∧ G.molecule.atom d1 = y ∧ G.molecule.atom (G.molecule.mate d1) = x0 ∧
      G.molecule.atom d2 = y' ∧ G.molecule.atom (G.molecule.mate d2) = x0' := by
  obtain ⟨e1, he1b, he1⟩ := exists_bond_of_pos G.molecule (show 0 < G.molecule.bondsBetween x0 y by
    rw [hb1]; norm_num)
  obtain ⟨e2, he2b, he2⟩ := exists_bond_of_pos G.molecule (show 0 < G.molecule.bondsBetween x0' y' by
    rw [hb2]; norm_num)
  obtain ⟨d1, hd1e, hd1a, hd1m⟩ := dart_at_end G he1
  obtain ⟨d2, hd2e, hd2a, hd2m⟩ := dart_at_end G he2
  obtain ⟨-, hx0H⟩ := mem_sdiff.mp hx0
  obtain ⟨-, hx0'H⟩ := mem_sdiff.mp hx0'
  have hcrossing : ∀ {e : GardenDart G} {u v : GBranch G.tree}, e ∈ G.molecule.bonds →
      G.molecule.ends e = s(u, v) → u ∈ S \ H → v ∈ H →
      e ∈ G.molecule.bonds.filter (fun z => (G.molecule.atom z ∈ H ∧ G.molecule.atom (G.molecule.mate z) ∈ S \ H) ∨
        (G.molecule.atom z ∈ S \ H ∧ G.molecule.atom (G.molecule.mate z) ∈ H)) := by
    intro e u v heb he hu hv
    refine Finset.mem_filter.mpr ⟨heb, ?_⟩
    have he' : s(G.molecule.atom e, G.molecule.atom (G.molecule.mate e)) = s(u, v) := he
    rcases Sym2.eq_iff.mp he' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1 ▸ hu, h2 ▸ hv⟩
    · exact Or.inl ⟨h1 ▸ hv, h2 ▸ hu⟩
  have he12 : e1 ≠ e2 := by
    intro h
    rw [h, he2] at he1
    rcases Sym2.eq_iff.mp he1 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hxx h1.symm
    · exact hx0'H (by rw [h1]; exact hyH)
  have hXeq : G.molecule.bonds.filter (fun z => (G.molecule.atom z ∈ H ∧ G.molecule.atom (G.molecule.mate z) ∈ S \ H) ∨
      (G.molecule.atom z ∈ S \ H ∧ G.molecule.atom (G.molecule.mate z) ∈ H)) = {e1, e2} :=
    (Finset.eq_of_subset_of_card_le (by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hcrossing he1b he1 hx0 hyH
      · exact hcrossing he2b he2 hx0' hy'H) (by
      rw [card_pair he12]; exact hcross.le)).symm
  refine ⟨d1, d2, ⟨fun z hz => (hint z hz).1, ?_⟩, hd1a, hd1m, hd2a, hd2m⟩
  intro d hdH hdout
  have hdm : G.molecule.atom (G.molecule.mate d) ∈ S \ H := mem_sdiff.mpr ⟨(hint _ hdH).2 d rfl, hdout⟩
  have hbond : (d = e1 ∨ G.molecule.mate d = e1) ∨ (d = e2 ∨ G.molecule.mate d = e2) := by
    by_cases hod : G.molecule.out d = true
    · have hdX : d ∈ G.molecule.bonds.filter (fun z => (G.molecule.atom z ∈ H ∧
          G.molecule.atom (G.molecule.mate z) ∈ S \ H) ∨
          (G.molecule.atom z ∈ S \ H ∧ G.molecule.atom (G.molecule.mate z) ∈ H)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ d, hod⟩, Or.inl ⟨hdH, hdm⟩⟩
      rw [hXeq] at hdX
      rcases mem_insert.mp hdX with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl (mem_singleton.mp h))
    · have hom : G.molecule.out (G.molecule.mate d) = true := by rw [G.molecule.out_mate]; simpa using hod
      have hmd : G.molecule.atom (G.molecule.mate (G.molecule.mate d)) ∈ H := by rw [G.molecule.mate_mate]; exact hdH
      have hdX : G.molecule.mate d ∈ G.molecule.bonds.filter (fun z => (G.molecule.atom z ∈ H ∧
          G.molecule.atom (G.molecule.mate z) ∈ S \ H) ∨
          (G.molecule.atom z ∈ S \ H ∧ G.molecule.atom (G.molecule.mate z) ∈ H)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hom⟩, Or.inr ⟨hdm, hmd⟩⟩
      rw [hXeq] at hdX
      rcases mem_insert.mp hdX with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr (mem_singleton.mp h))
  have side : ∀ {e di : GardenDart G}, (di = e ∨ di = G.molecule.mate e) → G.molecule.atom di ∈ H →
      (d = e ∨ G.molecule.mate d = e) → d = di := by
    intro e di hdi hdiH hde
    rcases hde with rfl | rfl
    · rcases hdi with rfl | rfl
      · rfl
      · exact absurd hdiH hdout
    · rcases hdi with rfl | rfl
      · exact absurd hdiH hdout
      · rw [G.molecule.mate_mate]
  rcases hbond with h | h
  · exact Or.inl (side hd1e (hd1a ▸ hyH) h)
  · exact Or.inr (side hd2e (hd2a ▸ hy'H) h)

/-- **The pendant step**: if every atom of `S` outside `H` has layer at least `q`, the coherent inner ends of the two
exits of `H` have layer at least `q` (main's `exit_lemma`). -/
theorem pendant_step (G : Garden w) {S H : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hHint : ∀ z ∈ H, z ∈ (S.erase a).erase b)
    (hint : ∀ x ∈ H, G.molecule.deg x = 4 ∧ ∀ d, G.molecule.atom d = x → G.molecule.atom (G.molecule.mate d) ∈ S)
    {f : GBranch G.tree → ℕ} {p : ℕ} (hf : LFTwist.IsBranchPrelayering G f) (hC : CanonPairs G f p (RegV G S a))
    (hcross : TVine.Struct.crossBonds G.molecule H (S \ H) = 2) {x0 x0' y y' : GBranch G.tree}
    (hx0 : x0 ∈ S \ H) (hx0' : x0' ∈ S \ H) (hxx : x0 ≠ x0') (hyH : y ∈ H) (hy'H : y' ∈ H) (hyy : y ≠ y')
    (hb1 : G.molecule.bondsBetween x0 y = 1) (hb2 : G.molecule.bondsBetween x0' y' = 1)
    (hco : f y = f y') {q : ℕ} (hout : ∀ z ∈ S, z ∉ H → q ≤ f z) : q ≤ f y := by
  obtain ⟨d1, d2, hExit, hd1a, hd1m, hd2a, hd2m⟩ :=
    exitData_of_two_exits G hint hcross hx0 hx0' hxx hyH hy'H hb1 hb2
  have hHS : H ⊆ S := fun z hz => (mem_erase.mp (mem_erase.mp (hHint z hz)).2).2
  have hd12 : d1 ≠ d2 := fun h => hyy (by rw [← hd1a, ← hd2a, h])
  have hRegK : ∀ z ∈ H, RegV G S a z.toNode := by
    intro z hz
    have hz' := hHint z hz
    exact Or.inl ⟨z, (mem_erase.mp (mem_erase.mp hz').2).2, (mem_erase.mp (mem_erase.mp hz').2).1, rfl⟩
  have hRegLeafK : ∀ ℓ : GLeaf G.tree, ∀ hr : ℓ.1.2 ≠ [], GNode.parent ℓ.toNode hr ∈ H →
      RegV G S a (G.pair ℓ).toNode := by
    intro ℓ hr hp
    have hp' := hHint _ hp
    exact Or.inr ⟨ℓ, hr, (mem_erase.mp (mem_erase.mp hp').2).2, (mem_erase.mp (mem_erase.mp hp').2).1,
      Or.inr rfl⟩
  have hmin := exit_lemma hf hC hHS hExit hd12 (by rw [hd1a]; exact hyH)
    (by rw [hd1m]; exact (mem_sdiff.mp hx0).2) (by rw [hd2a]; exact hy'H) (by rw [hd2m]; exact (mem_sdiff.mp hx0').2)
    (by rw [hd1a, hd2a]; exact hco) (fun d hd => (hint _ hd).2 d rfl) hRegK hRegLeafK
  rw [hd1m, hd2m, hd1a] at hmin
  exact le_trans (le_min (hout x0 (mem_sdiff.mp hx0).1 (mem_sdiff.mp hx0).2)
    (hout x0' (mem_sdiff.mp hx0').1 (mem_sdiff.mp hx0').2)) hmin

/-- **The layer range of a coherent (CL) T-vine** (TARGET L1523–L1531 with groups := pieces). -/
theorem tvine_layer_range (hLV : LayervineInput) (G : Garden w) {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hT : G.molecule.IsTVine S a b) (hCL : Mole.CLParentPattern G S a b)
    {f : GBranch G.tree → ℕ} {p : ℕ} (hf : LFTwist.IsBranchPrelayering G f)
    (hcoh : tvineIncoherency G.molecule S a b f = 0) (hC : CanonPairs G f p (RegV G S a)) :
    ∀ x ∈ S, f b ≤ f x ∧ f x ≤ f a := by
  have hB := hT.1
  have hup : ∀ x ∈ S, f x ≤ f a := layer_le_upper G hB hCL hf
  have hcohP := coherent_of_tvineIncoherency_zero hcoh
  obtain ⟨sp, pd, -, hpcs, hspine, -, -, -, -, -, hpend⟩ := (hLV G.molecule S a b hT).1
  have hpieces : ∀ P, P ∈ G.molecule.tvineGroups S a b ↔ P ∈ sp ∨ P ∈ pd := by
    intro P
    show P ∈ G.molecule.pieces S a b ↔ _
    rw [← hpcs, List.mem_toFinset, List.mem_append]
  have hab : f b ≤ f a := hup b hB.2.2.1
  have hint := block_interior_facts G hB
  -- spine pieces
  have hch := chain_exists G hB hCL hf
  have hsp : ∀ P ∈ sp, ∀ x ∈ P, f b ≤ f x := by
    intro P hP x hx
    have hPg : P ∈ G.molecule.tvineGroups S a b := (hpieces P).mpr (Or.inl hP)
    obtain ⟨z, hz, hbz⟩ := stepF_chain_hits hch ((hspine P hPg).mp hP)
    rw [hcohP P hPg x hx z hz]
    exact hbz
  -- the exits of the pendant tails
  have hex : ∀ k : Fin pd.length, ∃ x x' : GBranch G.tree,
      TVine.Struct.TwoSingleExits G.molecule S (TVine.Struct.unionAll (pd.drop k.val)) (pd.get k) x x' := by
    rcases hpend with ⟨hpd0, -⟩ | ⟨Ys, C, -, -, -, -, -, hex⟩
    · intro k; exfalso; obtain ⟨kv, hkv⟩ := k; simp [hpd0] at hkv
    · intro k; obtain ⟨x, x', h, -⟩ := hex k; exact ⟨x, x', h⟩
  -- every non-joint atom lies in a spine piece or in a pendant piece
  have hloc : ∀ x ∈ S, x ≠ a → x ≠ b → (∃ P ∈ sp, x ∈ P) ∨ ∃ j, ∃ hj : j < pd.length, x ∈ pd.get ⟨j, hj⟩ := by
    intro x hx hxa hxb
    have hxI : x ∈ (S.erase a).erase b := mem_erase.mpr ⟨hxb, mem_erase.mpr ⟨hxa, hx⟩⟩
    obtain ⟨P, hP, hPmem⟩ := exists_piece_through (M := G.molecule) hxI
    have hxP : x ∈ P := (hPmem x).mpr ⟨hxI, fun F _ _ => Relation.EqvGen.refl _⟩
    rcases (hpieces P).mp hP with hPs | hPd
    · exact Or.inl ⟨P, hPs, hxP⟩
    · obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem hPd
      exact Or.inr ⟨j, hj, hxP⟩
  -- the pendant pieces, by induction along the list
  have hpd : ∀ k : ℕ, ∀ hk : k < pd.length, ∀ x ∈ pd.get ⟨k, hk⟩, f b ≤ f x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk x hx
    have hYg : pd.get ⟨k, hk⟩ ∈ G.molecule.tvineGroups S a b := (hpieces _).mpr (Or.inr (List.get_mem _ _))
    set H := TVine.Struct.unionAll (pd.drop k) with hH
    have hHmem : ∀ y, y ∈ H ↔ ∃ j, ∃ hj : j < pd.length, k ≤ j ∧ y ∈ pd.get ⟨j, hj⟩ := by
      intro y
      rw [hH, mem_unionAll]
      constructor
      · rintro ⟨L, hL, hyL⟩
        obtain ⟨j, hj, hkj, rfl⟩ := mem_drop_iff_get.mp hL
        exact ⟨j, hj, hkj, hyL⟩
      · rintro ⟨j, hj, hkj, hyj⟩
        exact ⟨_, mem_drop_iff_get.mpr ⟨j, hj, hkj, rfl⟩, hyj⟩
    have hHint : ∀ y ∈ H, y ∈ (S.erase a).erase b := by
      intro y hy
      obtain ⟨j, hj, -, hyj⟩ := (hHmem y).mp hy
      exact mem_piece_interior ((hpieces _).mpr (Or.inr (List.get_mem _ _))) hyj
    have hout : ∀ y ∈ S, y ∉ H → f b ≤ f y := by
      intro y hyS hyH
      by_cases hya : y = a
      · rw [hya]; exact hab
      by_cases hyb : y = b
      · rw [hyb]
      rcases hloc y hyS hya hyb with ⟨P, hPs, hyP⟩ | ⟨j, hj, hyj⟩
      · exact hsp P hPs y hyP
      · by_cases hjk : k ≤ j
        · exact absurd ((hHmem y).mpr ⟨j, hj, hjk, hyj⟩) hyH
        · exact ih j (by omega) hj y hyj
    obtain ⟨x0, x0', hcross, hxx, hx0, hx0', y, hy, y', hy', hyy, hb1, hb2⟩ := hex ⟨k, hk⟩
    have hyH : y ∈ H := (hHmem y).mpr ⟨k, hk, le_rfl, hy⟩
    have hy'H : y' ∈ H := (hHmem y').mpr ⟨k, hk, le_rfl, hy'⟩
    have hlow := pendant_step G hHint (fun z hz => hint z (hHint z hz)) hf hC hcross hx0 hx0' hxx hyH hy'H hyy
      hb1 hb2 (hcohP _ hYg y hy y' hy') hout
    rw [hcohP _ hYg x hx y hy]
    exact hlow
  intro x hx
  refine ⟨?_, hup x hx⟩
  by_cases hxa : x = a
  · rw [hxa]; exact hab
  by_cases hxb : x = b
  · rw [hxb]
  rcases hloc x hx hxa hxb with ⟨P, hPs, hxP⟩ | ⟨j, hj, hxj⟩
  · exact hsp P hPs x hxP
  · exact hpd j hj x hxj

end garden

end WaveTurbulence.GammaLow.Famc
