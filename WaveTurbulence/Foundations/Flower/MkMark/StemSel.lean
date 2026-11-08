/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.Transport
public import WaveTurbulence.Foundations.Flower.MkMark.Decoded

/-! # B2b-2 MK-MARK: capped stems and selected vertices on addresses, and their transport

The capped stem of tree `j` (`MkDefs.stemSetCap`), its depth-`k` vertex (`MkDefs.stemAt`) and the selected set
(`MkDefs.selSetCap`) are read off addresses (`CapStemAt`, `mem_stemSetCap_iff`, `stemAt_eq_some_iff`, `SelAt`,
`selAt_iff`). `StemAvoid LG J R`: every root-to-capped-flower path avoids `R`.

**Stem transport** (`OutIso.stem_transport`): if a correspondence `I` of two gardens off `R, R'` has an inverse and
the capped stems of `LG` avoid `R`, then `I` fixes every capped-stem address, the two gardens have the same capped
flowers, the same capped stems (as address sets, tree by tree, hence with the same depths), the same depth-`k`
stem vertices and the same selected vertices, and the capped stems of `LG'` avoid `R'`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

section Addr
variable (LG : LayeredGarden w) (J : Finset (Fin w))

/-- `z` lies on the capped stem of tree `j` (address form of `stemSetCap`). -/
def CapStemAt (j : Fin w) (z : Address w) : Prop :=
  BranchAt LG z ∧ z.1 = j ∧ (∃ ℓ : Address w, CapFlowerAt LG J ℓ ∧ AddrBelow z ℓ) ∧ ¬ CapParentAt LG J z

/-- Every capped stem (every root-to-capped-flower path, flower included) avoids `R`. -/
def StemAvoid (R : Set (Address w)) : Prop :=
  ∀ ℓ : Address w, CapFlowerAt LG J ℓ → ∀ z : Address w, AddrBelow z ℓ → z ∉ R

/-- `σ` is a selected vertex (address form of `selSetCap`). -/
def SelAt (kSel : Fin w → Option ℕ) (σ : Address w) : Prop :=
  ∃ b ∈ selSetCap LG J kSel, b.1 = σ

theorem capFlowerAt_iff (ℓ : GLeaf LG.garden.tree) : CapFlowerAt LG J ℓ.1 ↔ IsCapFlower LG J ℓ :=
  ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨ℓ.2, h.1, h.2⟩⟩

theorem onCapStem_iff (a : GNode LG.garden.tree) :
    OnCapStem LG J a ↔ ∃ ℓ : Address w, CapFlowerAt LG J ℓ ∧ AddrBelow a.1 ℓ := by
  constructor
  · rintro ⟨ℓ, hℓ, hd⟩
    exact ⟨ℓ.1, (capFlowerAt_iff LG J ℓ).mpr hℓ, hd⟩
  · rintro ⟨ℓ, ⟨h, h1, h2⟩, hd⟩
    exact ⟨⟨ℓ, h⟩, ⟨h1, h2⟩, hd⟩

/-- **The capped stem on addresses.** -/
theorem mem_stemSetCap_iff (j : Fin w) (b : GBranch LG.garden.tree) :
    b ∈ stemSetCap LG J j ↔ CapStemAt LG J j b.1 := by
  unfold stemSetCap CapStemAt
  rw [Finset.mem_filter, onCapStem_iff, isCapFlowerParent_iff]
  simp only [Finset.mem_univ, true_and]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨b.2, h1, h2, h3⟩, fun ⟨_, h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- **The depth-`k` stem vertex on addresses**: it exists and sits at `z` iff `z` is the only capped-stem address
of tree `j` at depth `k`. -/
theorem stemAt_eq_some_iff (j : Fin w) (k : ℕ) (z : Address w) :
    (∃ b, stemAt LG J j k = some b ∧ b.1 = z) ↔
      CapStemAt LG J j z ∧ z.2.length = k ∧ ∀ z', CapStemAt LG J j z' → z'.2.length = k → z' = z := by
  have hF : ∀ c : GBranch LG.garden.tree,
      c ∈ (stemSetCap LG J j).filter (fun b => b.1.2.length = k) ↔ CapStemAt LG J j c.1 ∧ c.1.2.length = k := by
    intro c
    rw [Finset.mem_filter, mem_stemSetCap_iff]
  unfold stemAt
  constructor
  · rintro ⟨b, hb, rfl⟩
    by_cases h : ((stemSetCap LG J j).filter fun b => b.1.2.length = k).card = 1
    · rw [dite_eq_left h] at hb
      have hspec := Classical.choose_spec (Finset.card_eq_one.mp h)
      have hbe : Classical.choose (Finset.card_eq_one.mp h) = b := Option.some_injective _ hb
      rw [hbe] at hspec
      have hbm : b ∈ (stemSetCap LG J j).filter (fun b => b.1.2.length = k) := by
        rw [hspec]
        exact Finset.mem_singleton_self b
      obtain ⟨h1, h2⟩ := (hF b).mp hbm
      refine ⟨h1, h2, fun z' hz' hk => ?_⟩
      have hm : (⟨z', hz'.1⟩ : GBranch LG.garden.tree) ∈ (stemSetCap LG J j).filter (fun b => b.1.2.length = k) :=
        (hF _).mpr ⟨hz', hk⟩
      have hm' : (⟨z', hz'.1⟩ : GBranch LG.garden.tree) ∈ ({b} : Finset (GBranch LG.garden.tree)) := hspec ▸ hm
      have he : (⟨z', hz'.1⟩ : GBranch LG.garden.tree) = b := Finset.mem_singleton.mp hm'
      exact congrArg (fun c : GBranch LG.garden.tree => c.1) he
    · rw [dite_eq_right h] at hb
      exact absurd hb (by simp)
  · rintro ⟨hz, hk, huniq⟩
    set b0 : GBranch LG.garden.tree := ⟨z, hz.1⟩
    have hset : (stemSetCap LG J j).filter (fun b => b.1.2.length = k) = {b0} := by
      ext c
      rw [hF, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        exact Subtype.ext (huniq c.1 h1 h2)
      · rintro rfl
        exact ⟨hz, hk⟩
    have hcard : ((stemSetCap LG J j).filter fun b => b.1.2.length = k).card = 1 := by
      rw [hset, Finset.card_singleton]
    rw [dite_eq_left hcard]
    have hspec := Classical.choose_spec (Finset.card_eq_one.mp hcard)
    have e := Finset.singleton_inj.mp (hset.symm.trans hspec)
    exact ⟨_, rfl, by rw [← e]⟩

/-- **Selected vertices on addresses.** -/
theorem selAt_iff (kSel : Fin w → Option ℕ) (σ : Address w) :
    SelAt LG J kSel σ ↔ ∃ j k, kSel j = some k ∧ ∃ b, stemAt LG J j k = some b ∧ b.1 = σ := by
  unfold SelAt selSetCap selCap
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, ⟨j, hj⟩, rfl⟩
    cases hk : kSel j with
    | none => rw [hk] at hj; exact absurd hj (by simp)
    | some k => rw [hk] at hj; exact ⟨j, k, hk, b, hj, rfl⟩
  · rintro ⟨j, k, hk, b, hb, rfl⟩
    exact ⟨b, ⟨j, by rw [hk]; exact hb⟩, rfl⟩

theorem selAt_capStem {kSel : Fin w → Option ℕ} {σ : Address w} (h : SelAt LG J kSel σ) :
    ∃ j, CapStemAt LG J j σ := by
  obtain ⟨j, k, -, hb⟩ := (selAt_iff LG J kSel σ).mp h
  exact ⟨j, ((stemAt_eq_some_iff LG J j k σ).mp hb).1⟩

theorem nodeAt_of_selAt {kSel : Fin w → Option ℕ} {σ : Address w} (h : SelAt LG J kSel σ) : NodeAt LG σ := by
  obtain ⟨j, hj⟩ := selAt_capStem LG J h
  exact nodeAt_of_branchAt hj.1

end Addr

/-! ## Equal stem sets give equal depth-`k` vertices and selections -/

section Congr
variable {LG LG' : LayeredGarden w} {J : Finset (Fin w)}

theorem stemAt_congr (h : ∀ j z, CapStemAt LG' J j z ↔ CapStemAt LG J j z) (j : Fin w) (k : ℕ) (z : Address w) :
    (∃ b, stemAt LG' J j k = some b ∧ b.1 = z) ↔ (∃ b, stemAt LG J j k = some b ∧ b.1 = z) := by
  rw [stemAt_eq_some_iff, stemAt_eq_some_iff]
  simp only [h]

theorem selAt_congr (h : ∀ j z, CapStemAt LG' J j z ↔ CapStemAt LG J j z) (kSel : Fin w → Option ℕ)
    (σ : Address w) : SelAt LG' J kSel σ ↔ SelAt LG J kSel σ := by
  rw [selAt_iff, selAt_iff]
  simp only [stemAt_congr h]

end Congr

/-! ## Transport along a correspondence -/

theorem nodeAt_of_addrBelow {LG : LayeredGarden w} {z ℓ : Address w} (hℓ : NodeAt LG ℓ) (h : AddrBelow z ℓ) :
    NodeAt LG z := by
  obtain ⟨s, hs⟩ := h.2
  show z.2 ∈ (LG.garden.tree z.1).nodes
  rw [h.1]
  exact prefix_mem_nodes _ (s := s) (by rw [hs]; exact hℓ)

section One
variable {LG LG' : LayeredGarden w} {R R' : Set (Address w)} (I : OutIso LG LG' R R') {J : Finset (Fin w)}

/-- A correspondence fixes every root-connected path that avoids the region. -/
theorem OutIso.fix_path (ℓ : Address w) (hℓ : NodeAt LG ℓ) (hR : ∀ z, AddrBelow z ℓ → z ∉ R) :
    ∀ z, AddrBelow z ℓ → I.f z = z := by
  rintro ⟨j, p⟩ ⟨hj, hp⟩
  simp only at hj hp
  induction p using List.reverseRecOn with
  | nil =>
    have hz : AddrBelow ((j, []) : Address w) ℓ := ⟨hj, List.nil_prefix⟩
    have hn : NodeAt LG ((j, []) : Address w) := nodeAt_of_addrBelow hℓ hz
    have hzR := hR _ hz
    exact Prod.ext (I.tree _ hn hzR) ((I.root _ hn hzR).mpr rfl)
  | append_singleton p i ih =>
    have hp' : p <+: ℓ.2 := (List.prefix_append p [i]).trans hp
    have hz : AddrBelow ((j, p) : Address w) ℓ := ⟨hj, hp'⟩
    have hz' : AddrBelow ((j, p ++ [i]) : Address w) ℓ := ⟨hj, hp⟩
    have hn := nodeAt_of_addrBelow hℓ hz
    have hn' := nodeAt_of_addrBelow hℓ hz'
    have e : ((j, p ++ [i]) : Address w) = addrExt (j, p) [i] := rfl
    rw [e, I.child (j, p) i hn (hR _ hz) (e ▸ hn') (e ▸ hR _ hz'), ih hp']

/-- Under `StemAvoid`, the correspondence fixes every capped stem of `LG`. -/
theorem OutIso.stem_fix (hs : StemAvoid LG J R) {ℓ : Address w} (hℓ : CapFlowerAt LG J ℓ) :
    ∀ z, AddrBelow z ℓ → I.f z = z :=
  I.fix_path ℓ (nodeAt_of_leafAt hℓ.1) (hs ℓ hℓ)

include I in
/-- On a capped stem of `LG` avoiding `R`, branches and capped-flower parents correspond in place. -/
theorem OutIso.stem_local (hR : RegionOK LG R) (hR' : RegionOK LG' R') (hs : StemAvoid LG J R)
    {ℓ z : Address w} (hℓ : CapFlowerAt LG J ℓ) (hz : AddrBelow z ℓ) :
    (BranchAt LG' z ↔ BranchAt LG z) ∧ (CapParentAt LG' J z ↔ CapParentAt LG J z) ∧ CapFlowerAt LG' J ℓ := by
  have hn := nodeAt_of_addrBelow (nodeAt_of_leafAt hℓ.1) hz
  have hzR := hs ℓ hℓ z hz
  have e := I.stem_fix hs hℓ z hz
  have hb := I.branch hn hzR
  have hc := I.capParent hR hR' hn hzR (J := J)
  rw [e] at hb hc
  refine ⟨hb, hc, ?_⟩
  have hℓn := nodeAt_of_leafAt hℓ.1
  have hℓR := hs ℓ hℓ ℓ (addrBelow_refl ℓ)
  have h := (I.capFlower hℓn hℓR).mpr hℓ
  rwa [I.stem_fix hs hℓ ℓ (addrBelow_refl ℓ)] at h

end One

section Two
variable {LG LG' : LayeredGarden w} {R R' : Set (Address w)} {J : Finset (Fin w)}
  (I : OutIso LG LG' R R') (I' : OutIso LG' LG R' R)
  (hinv : ∀ z', NodeAt LG' z' → z' ∉ R' → I.f (I'.f z') = z')

include hinv in
/-- A capped flower of `LG'` is a capped flower of `LG` at the same address, fixed by `I'`. -/
theorem capFlower_bwd (hR' : RegionOK LG' R') (hs : StemAvoid LG J R) {ℓ' : Address w}
    (h : CapFlowerAt LG' J ℓ') : CapFlowerAt LG J ℓ' ∧ I'.f ℓ' = ℓ' := by
  have hn' := nodeAt_of_leafAt h.1
  have hR'ℓ : ℓ' ∉ R' := fun hm => not_capFlower_of_region hR' hm h
  obtain ⟨hn, -⟩ := I'.node ℓ' hn' hR'ℓ
  have hc : CapFlowerAt LG J (I'.f ℓ') := (I'.capFlower hn' hR'ℓ).mpr h
  have e1 := I.stem_fix hs hc _ (addrBelow_refl _)
  have e : I'.f ℓ' = ℓ' := e1.symm.trans (hinv ℓ' hn' hR'ℓ)
  rw [e] at hc
  exact ⟨hc, e⟩

include hinv in
/-- **Stem transport.** Under `StemAvoid LG J R`: the capped flowers and the capped stems of the two gardens coincide
as address sets, `I` fixes them, and the capped stems of `LG'` avoid `R'`. -/
theorem OutIso.stem_transport (hR : RegionOK LG R) (hR' : RegionOK LG' R') (hs : StemAvoid LG J R) :
    (∀ ℓ, CapFlowerAt LG' J ℓ ↔ CapFlowerAt LG J ℓ) ∧
      (∀ j z, CapStemAt LG' J j z ↔ CapStemAt LG J j z) ∧
      (∀ ℓ, CapFlowerAt LG J ℓ → ∀ z, AddrBelow z ℓ → z ∉ R ∧ I.f z = z) ∧
      StemAvoid LG' J R' := by
  refine ⟨fun ℓ => ⟨fun h => (capFlower_bwd I I' hinv hR' hs h).1,
    fun h => (I.stem_local hR hR' hs h (addrBelow_refl ℓ)).2.2⟩, fun j z => ⟨?_, ?_⟩,
    fun ℓ hℓ z hz => ⟨hs ℓ hℓ z hz, I.stem_fix hs hℓ z hz⟩, ?_⟩
  · rintro ⟨hb, hj, ⟨ℓ, hℓ, hz⟩, hcp⟩
    have hℓ0 := (capFlower_bwd I I' hinv hR' hs hℓ).1
    obtain ⟨e1, e2, -⟩ := I.stem_local hR hR' hs hℓ0 hz
    exact ⟨e1.mp hb, hj, ⟨ℓ, hℓ0, hz⟩, fun h => hcp (e2.mpr h)⟩
  · rintro ⟨hb, hj, ⟨ℓ, hℓ, hz⟩, hcp⟩
    obtain ⟨e1, e2, e3⟩ := I.stem_local hR hR' hs hℓ hz
    exact ⟨e1.mpr hb, hj, ⟨ℓ, e3, hz⟩, fun h => hcp (e2.mp h)⟩
  · intro ℓ' h z hz
    have hc := (capFlower_bwd I I' hinv hR' hs h).1
    have hzn : NodeAt LG z := nodeAt_of_addrBelow (nodeAt_of_leafAt hc.1) hz
    have hzR := hs ℓ' hc z hz
    have := (I.node z hzn hzR).2
    rwa [I.stem_fix hs hc z hz] at this

include hinv in
/-- **Depth-`k` stem vertices and selected vertices are carried over** (same addresses). -/
theorem OutIso.stemAt_transport (hR : RegionOK LG R) (hR' : RegionOK LG' R') (hs : StemAvoid LG J R)
    (j : Fin w) (k : ℕ) (z : Address w) :
    (∃ b, stemAt LG' J j k = some b ∧ b.1 = z) ↔ (∃ b, stemAt LG J j k = some b ∧ b.1 = z) :=
  stemAt_congr (I.stem_transport I' hinv hR hR' hs).2.1 j k z

include hinv in
theorem OutIso.selAt_transport (hR : RegionOK LG R) (hR' : RegionOK LG' R') (hs : StemAvoid LG J R)
    (kSel : Fin w → Option ℕ) (σ : Address w) : SelAt LG' J kSel σ ↔ SelAt LG J kSel σ :=
  selAt_congr (I.stem_transport I' hinv hR hR' hs).2.1 kSel σ

end Two

end WaveTurbulence.Flower.MkMark
