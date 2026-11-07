/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Compat
public import WaveTurbulence.Foundations.LayerCnt.ExitTranslate
public import WaveTurbulence.Foundations.LayerCnt.HExit
public import WaveTurbulence.Foundations.Molecule.MoleculeGroupIdentities
public import WaveTurbulence.Foundations.Molecule.GardenMoleculeAxioms
import Mathlib.Tactic

/-! # From a template cut with two single crossing bonds to a set with two exit darts (TARGET layervine, L1531)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine Finset TTree
variable {w : ℕ}

/-- `K` is a set of non-joint template atoms whose only crossing bond classes are the two single classes of `e₁, e₂`,
oriented with the first end inside `K`. -/
@[expose] def IsKCut (T : VineTemplate) (K : ℕ → Prop) (e1 e2 : ℕ × ℕ) : Prop :=
  (∀ e ∈ T.bonds, s(e.1, e.2) ≠ s(e1.1, e1.2) → s(e.1, e.2) ≠ s(e2.1, e2.2) → (K e.1 ↔ K e.2)) ∧
    (e1 ∈ T.bonds ∨ (e1.2, e1.1) ∈ T.bonds) ∧ (e2 ∈ T.bonds ∨ (e2.2, e2.1) ∈ T.bonds) ∧ SymSingle T e1 ∧ SymSingle T e2 ∧
    s(e1.1, e1.2) ≠ s(e2.1, e2.2) ∧ (K e1.1 ∧ ¬ K e1.2) ∧ (K e2.1 ∧ ¬ K e2.2) ∧
    ∀ v, K v → 2 ≤ v ∧ v < T.n

theorem exists_dart_of_bond {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b) {e : ℕ × ℕ}
    (he : e ∈ (X.expand R.k).bonds ∨ (e.2, e.1) ∈ (X.expand R.k).bonds) :
    ∃ d : D, M.InGroup S d ∧ R.f (M.atom d) = e.1 ∧ R.f (M.atom (M.mate d)) = e.2 := by
  have hm : s(e.1, e.2) ∈ ((X.expand R.k).bonds.map fun p => s(p.1, p.2) : Multiset (Sym2 ℕ)) := by
    rw [Multiset.mem_coe, List.mem_map]
    rcases he with he | he
    · exact ⟨e, he, rfl⟩
    · exact ⟨(e.2, e.1), he, Sym2.eq_swap⟩
  rw [← R.bonds_eq, Multiset.mem_map] at hm
  obtain ⟨β, hβ, hβe⟩ := hm
  obtain ⟨o, _, hio, rfl⟩ := (mem_groupBonds_iff_out (M := M) S β).mp hβ
  have hmp : Sym2.map R.f (M.ends o) = s(R.f (M.atom o), R.f (M.atom (M.mate o))) := rfl
  rw [hmp] at hβe
  rcases Sym2.eq_iff.mp hβe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨o, hio, h1, h2⟩
  · refine ⟨M.mate o, ?_, ?_, ?_⟩
    · unfold Molecule.InGroup at hio ⊢
      rw [M.mate_mate]; exact ⟨hio.2, hio.1⟩
    · rw [h2]
    · rw [M.mate_mate, h1]


/-- Orientation of an exit dart: it realizes the crossing class `e₁` or `e₂`, with the inside end first. -/
theorem orient_cross {T : VineTemplate} {K : ℕ → Prop} {e1 e2 : ℕ × ℕ} (hK : IsKCut T K e1 e2)
    {e : ℕ × ℕ} (he : e ∈ T.bonds) {x y : ℕ} (hxy : s(e.1, e.2) = s(x, y)) (hx : K x) (hy : ¬ K y) :
    (x = e1.1 ∧ y = e1.2) ∨ (x = e2.1 ∧ y = e2.2) := by
  obtain ⟨hc, _, _, _, _, _, ho1, ho2, _⟩ := hK
  by_cases h1 : s(e.1, e.2) = s(e1.1, e1.2)
  · left
    rw [h1] at hxy
    rcases Sym2.eq_iff.mp hxy with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact ⟨h2.symm, h3.symm⟩
    · exfalso; exact ho1.2 (by rw [h3]; exact hx)
  · by_cases h2 : s(e.1, e.2) = s(e2.1, e2.2)
    · right
      rw [h2] at hxy
      rcases Sym2.eq_iff.mp hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact ⟨h3.symm, h4.symm⟩
      · exfalso; exact ho2.2 (by rw [h4]; exact hx)
    · exfalso
      have := hc e he h1 h2
      rcases Sym2.eq_iff.mp hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h3, h4] at this; exact hy (this.mp hx)
      · rw [h3, h4] at this; exact hy (this.mpr hx)

open Classical in
/-- **Translation of a template cut into a set with two exit darts.** -/
theorem exit_of_kcut (G : Garden w) {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.DegreeBlock S a b) (R : VineRealization G.molecule X S a b)
    {K : ℕ → Prop} {e1 e2 : ℕ × ℕ} (hK : IsKCut (X.expand R.k) K e1 e2) :
    ∃ (d1 d2 : GardenDart G),
      ExitData G (S.filter fun z => K (R.f z)) d1 d2 ∧ d1 ≠ d2 ∧
      G.molecule.atom d1 ∈ (S.filter fun z => K (R.f z)) ∧
      G.molecule.atom (G.molecule.mate d1) ∉ (S.filter fun z => K (R.f z)) ∧
      G.molecule.atom d2 ∈ (S.filter fun z => K (R.f z)) ∧
      G.molecule.atom (G.molecule.mate d2) ∉ (S.filter fun z => K (R.f z)) ∧
      R.f (G.molecule.atom d1) = e1.1 ∧ R.f (G.molecule.atom (G.molecule.mate d1)) = e1.2 ∧
      R.f (G.molecule.atom d2) = e2.1 ∧ R.f (G.molecule.atom (G.molecule.mate d2)) = e2.2 ∧
      (∀ d, G.molecule.atom d ∈ (S.filter fun z => K (R.f z)) → G.molecule.atom (G.molecule.mate d) ∈ S) := by
  classical
  set Kf := S.filter fun z => K (R.f z) with hKf
  have hmemK : ∀ z, z ∈ Kf ↔ z ∈ S ∧ K (R.f z) := fun z => by simp [hKf]
  obtain ⟨hcr, hm1, hm2, hs1, hs2, hne, ho1, ho2, hnj⟩ := hK
  have hKS : ∀ z ∈ Kf, z ∈ S := fun z hz => ((hmemK z).mp hz).1
  have hjt := R.joints_eq
  have hfab : ∀ z, (z = a ∨ z = b) → R.f z < 2 := by
    intro z hz
    have : R.f z ∈ ({R.f a, R.f b} : Finset ℕ) := by rcases hz with rfl | rfl <;> simp
    rw [hjt] at this; simp at this; omega
  have hdeg : ∀ z ∈ Kf, G.molecule.deg z = 4 := by
    intro z hz
    obtain ⟨hzS, hzK⟩ := (hmemK z).mp hz
    have h2 := (hnj _ hzK).1
    have hza : z ≠ a := fun h => by have := hfab z (Or.inl h); omega
    have hzb : z ≠ b := fun h => by have := hfab z (Or.inr h); omega
    exact Mole.deg_eq_four_of_degIn G.molecule (Mole.garden_isMolecule G) (Finset.mem_univ _)
      (hB.2.2.2.2.2.2.2.2 z hzS hza hzb)
  have hdeg' : ∀ z ∈ Kf, G.molecule.degIn S z = 4 := by
    intro z hz
    obtain ⟨hzS, hzK⟩ := (hmemK z).mp hz
    have h2 := (hnj _ hzK).1
    have hza : z ≠ a := fun h => by have := hfab z (Or.inl h); omega
    have hzb : z ≠ b := fun h => by have := hfab z (Or.inr h); omega
    exact hB.2.2.2.2.2.2.2.2 z hzS hza hzb
  have hall : ∀ z ∈ Kf, ∀ d, G.molecule.atom d = z → G.molecule.InGroup S d := by
    intro z hz d hd
    have hsub : (G.molecule.dartsAt z).filter (G.molecule.InGroup S) = G.molecule.dartsAt z := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      have h1 : ((G.molecule.dartsAt z).filter (G.molecule.InGroup S)).card = 4 := hdeg' z hz
      have h2 : (G.molecule.dartsAt z).card = 4 := hdeg z hz
      omega
    have : d ∈ G.molecule.dartsAt z := (Mole.mem_dartsAt G.molecule z d).mpr hd
    rw [← hsub] at this
    exact (Finset.mem_filter.mp this).2
  have hSn : ∀ d, G.molecule.atom d ∈ Kf → G.molecule.atom (G.molecule.mate d) ∈ S := fun d hd =>
    (hall _ hd d rfl).2
  -- exits
  have hex : ∀ d, G.molecule.atom d ∈ Kf → G.molecule.atom (G.molecule.mate d) ∉ Kf →
      (R.f (G.molecule.atom d) = e1.1 ∧ R.f (G.molecule.atom (G.molecule.mate d)) = e1.2) ∨
      (R.f (G.molecule.atom d) = e2.1 ∧ R.f (G.molecule.atom (G.molecule.mate d)) = e2.2) := by
    intro d hd hmd
    have hig := hall _ hd d rfl
    have hin := mem_groupBonds_of_inGroup (M := G.molecule) S d hig
    have hm : Sym2.map R.f (G.molecule.ends d) ∈ (G.molecule.groupBonds S).map (Sym2.map R.f) :=
      Multiset.mem_map_of_mem _ hin
    rw [R.bonds_eq, Multiset.mem_coe, List.mem_map] at hm
    obtain ⟨e, he, hee⟩ := hm
    have hmp : Sym2.map R.f (G.molecule.ends d) =
        s(R.f (G.molecule.atom d), R.f (G.molecule.atom (G.molecule.mate d))) := rfl
    rw [hmp] at hee
    refine orient_cross ⟨hcr, hm1, hm2, hs1, hs2, hne, ho1, ho2, hnj⟩ he hee
      ((hmemK _).mp hd).2 ?_
    intro hK'
    exact hmd ((hmemK _).mpr ⟨(hSn d hd), hK'⟩)
  obtain ⟨d1, hd1i, hd1a, hd1b⟩ := exists_dart_of_bond R hm1
  obtain ⟨d2, hd2i, hd2a, hd2b⟩ := exists_dart_of_bond R hm2
  have hd1S : G.molecule.atom d1 ∈ S := hd1i.1
  have hd1S' : G.molecule.atom (G.molecule.mate d1) ∈ S := hd1i.2
  have hd2S : G.molecule.atom d2 ∈ S := hd2i.1
  have hd2S' : G.molecule.atom (G.molecule.mate d2) ∈ S := hd2i.2
  have hd1K : G.molecule.atom d1 ∈ Kf := (hmemK _).mpr ⟨hd1S, by rw [hd1a]; exact ho1.1⟩
  have hd1K' : G.molecule.atom (G.molecule.mate d1) ∉ Kf := fun h => ho1.2 (by
    have := ((hmemK _).mp h).2; rw [hd1b] at this; exact this)
  have hd2K : G.molecule.atom d2 ∈ Kf := (hmemK _).mpr ⟨hd2S, by rw [hd2a]; exact ho2.1⟩
  have hd2K' : G.molecule.atom (G.molecule.mate d2) ∉ Kf := fun h => ho2.2 (by
    have := ((hmemK _).mp h).2; rw [hd2b] at this; exact this)
  have hne12 : d1 ≠ d2 := by
    intro h
    rw [h] at hd1a hd1b
    apply hne
    rw [← hd2a.symm.trans hd1a, ← hd2b.symm.trans hd1b]
  have hinj : ∀ u v, u ∈ S → v ∈ S → R.f u = R.f v → u = v := fun u v hu hv h => R.injOn hu hv h
  refine ⟨d1, d2, ⟨hdeg, ?_⟩, hne12, hd1K, hd1K', hd2K, hd2K', hd1a, hd1b, hd2a, hd2b, hSn⟩
  intro d hd hmd
  have hdS : G.molecule.atom d ∈ S := hKS _ hd
  have hmdS : G.molecule.atom (G.molecule.mate d) ∈ S := hSn d hd
  rcases hex d hd hmd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hu : G.molecule.atom d = G.molecule.atom d1 := hinj _ _ hdS hd1S (h1.trans hd1a.symm)
    have hv : G.molecule.atom (G.molecule.mate d) = G.molecule.atom (G.molecule.mate d1) :=
      hinj _ _ hmdS hd1S' (h2.trans hd1b.symm)
    have hne' : G.molecule.atom d ≠ G.molecule.atom (G.molecule.mate d) := by
      intro h
      have : e1.1 = e1.2 := by rw [← h1, ← h2, h]
      exact ho1.2 (this ▸ ho1.1)
    have hc : SymSingle (X.expand R.k) (R.f (G.molecule.atom d), R.f (G.molecule.atom (G.molecule.mate d))) := by
      have : (R.f (G.molecule.atom d), R.f (G.molecule.atom (G.molecule.mate d))) = e1 := Prod.ext h1 h2
      rw [this]; exact hs1
    exact dart_unique R hdS hmdS hne' hc rfl rfl hu.symm hv.symm
  · right
    have hu : G.molecule.atom d = G.molecule.atom d2 := hinj _ _ hdS hd2S (h1.trans hd2a.symm)
    have hv : G.molecule.atom (G.molecule.mate d) = G.molecule.atom (G.molecule.mate d2) :=
      hinj _ _ hmdS hd2S' (h2.trans hd2b.symm)
    have hne' : G.molecule.atom d ≠ G.molecule.atom (G.molecule.mate d) := by
      intro h
      have : e2.1 = e2.2 := by rw [← h1, ← h2, h]
      exact ho2.2 (this ▸ ho2.1)
    have hc : SymSingle (X.expand R.k) (R.f (G.molecule.atom d), R.f (G.molecule.atom (G.molecule.mate d))) := by
      have : (R.f (G.molecule.atom d), R.f (G.molecule.atom (G.molecule.mate d))) = e2 := Prod.ext h1 h2
      rw [this]; exact hs2
    exact dart_unique R hdS hmdS hne' hc rfl rfl hu.symm hv.symm

end WaveTurbulence.LayerCnt
