/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Leaves

/-! # D2c-3 PROT-CUT: relabelling the two trees of a couple leaves `kernelProt` unchanged

`swGarden G` has the trees and root signs of `G` in the other order (`t1sw`), the pairing and the marks transported;
`swLG LG` carries the same layers. The node, branch and leaf maps `ndB`, `brB`, `lfB` (swapped → original) are
bijections (`ndF`, `brF`, `lfF`). For a plain couple:

* `swDec`: decorations with root values `0` correspond (`κ ↦ κ ∘ ndB`);
* `epsDec`, `order`, `zeta`, `phaseProd`, the time domain and the input leaves are invariant;
* **`protSummand_sw`**, **`kernelProt_sw`**: the summands and the kernel agree, with the profiles, the multiplier,
  the clocks and the designations transported.

Main's `GlueData` glues a chain on tree `0` only; this transport moves a chain on tree `1` to tree `0`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The swapped forest. -/
abbrev swT (T : Fin 2 → TTree) : Fin 2 → TTree := fun j => T (t1sw j)

section Maps

variable {T : Fin 2 → TTree}

def ndB (a : GNode (swT T)) : GNode T := ⟨(t1sw a.1.1, a.1.2), a.2⟩
def ndF (a : GNode T) : GNode (swT T) :=
  ⟨(t1sw a.1.1, a.1.2), by show a.1.2 ∈ (T (t1sw (t1sw a.1.1))).nodes; rw [t1sw_t1sw]; exact a.2⟩
def brB (b : GBranch (swT T)) : GBranch T := ⟨(t1sw b.1.1, b.1.2), b.2⟩
def brF (b : GBranch T) : GBranch (swT T) :=
  ⟨(t1sw b.1.1, b.1.2), by show b.1.2 ∈ (T (t1sw (t1sw b.1.1))).branching; rw [t1sw_t1sw]; exact b.2⟩
def lfB (ℓ : GLeaf (swT T)) : GLeaf T := ⟨(t1sw ℓ.1.1, ℓ.1.2), ℓ.2⟩
def lfF (ℓ : GLeaf T) : GLeaf (swT T) :=
  ⟨(t1sw ℓ.1.1, ℓ.1.2), by show ℓ.1.2 ∈ (T (t1sw (t1sw ℓ.1.1))).leaves; rw [t1sw_t1sw]; exact ℓ.2⟩

theorem ndB_ndF (a : GNode T) : ndB (ndF a) = a := Subtype.ext (Prod.ext (t1sw_t1sw _) rfl)
theorem ndF_ndB (a : GNode (swT T)) : ndF (ndB a) = a := Subtype.ext (Prod.ext (t1sw_t1sw _) rfl)
theorem brB_brF (b : GBranch T) : brB (brF b) = b := Subtype.ext (Prod.ext (t1sw_t1sw _) rfl)
theorem brF_brB (b : GBranch (swT T)) : brF (brB b) = b := Subtype.ext (Prod.ext (t1sw_t1sw _) rfl)
theorem lfB_lfF (ℓ : GLeaf T) : lfB (lfF ℓ) = ℓ := Subtype.ext (Prod.ext (t1sw_t1sw _) rfl)
theorem lfF_lfB (ℓ : GLeaf (swT T)) : lfF (lfB ℓ) = ℓ := Subtype.ext (Prod.ext (t1sw_t1sw _) rfl)

def brEquiv : GBranch (swT T) ≃ GBranch T := ⟨brB, brF, brF_brB, brB_brF⟩
def lfEquiv : GLeaf (swT T) ≃ GLeaf T := ⟨lfB, lfF, lfF_lfB, lfB_lfF⟩

theorem brB_toNode (b : GBranch (swT T)) : (brB b).toNode = ndB b.toNode := rfl
theorem brB_child (b : GBranch (swT T)) (i : Fin 3) : (brB b).child i = ndB (b.child i) := rfl
theorem lfB_toNode (ℓ : GLeaf (swT T)) : (lfB ℓ).toNode = ndB ℓ.toNode := rfl
theorem ndB_lfF_toNode (ℓ : GLeaf T) : ndB (lfF ℓ).toNode = ℓ.toNode := Subtype.ext (Prod.ext (t1sw_t1sw _) rfl)

theorem brB_child_iff (b b' : GBranch (swT T)) : (brB b').IsChildOf (brB b) ↔ b'.IsChildOf b := by
  constructor
  · rintro ⟨h1, i, hi⟩
    exact ⟨t1sw_injective h1, i, hi⟩
  · rintro ⟨h1, i, hi⟩
    exact ⟨by simp [brB, h1], i, hi⟩

theorem forall_brB (P : GBranch T → Prop) : (∀ b, P b) ↔ ∀ b', P (brB b') :=
  ⟨fun h b' => h _, fun h b => by rw [← brB_brF b]; exact h _⟩

end Maps

/-- **The couple with its two trees in the other order.** -/
@[reducible] def swGarden (G : Garden 2) : Garden 2 where
  sig j := G.sig (t1sw j)
  tree := swT G.tree
  pair ℓ := lfF (G.pair (lfB ℓ))
  mark ℓ := G.mark (lfB ℓ)
  pair_pair ℓ := by
    show lfF (G.pair (lfB (lfF (G.pair (lfB ℓ))))) = ℓ
    rw [lfB_lfF, G.pair_pair, lfF_lfB]
  pair_eq_iff ℓ := by
    constructor
    · intro hp
      apply (G.pair_eq_iff (lfB ℓ)).1
      have := congrArg lfB hp
      rwa [lfB_lfF] at this
    · intro hm
      have := (G.pair_eq_iff (lfB ℓ)).2 hm
      show lfF (G.pair (lfB ℓ)) = ℓ
      rw [this, lfF_lfB]
  pair_sign ℓ hne := by
    have hne' : G.pair (lfB ℓ) ≠ lfB ℓ := fun hp => hne (by
      show lfF (G.pair (lfB ℓ)) = ℓ
      rw [hp, lfF_lfB])
    have := G.pair_sign _ hne'
    simp only [nodeSign, lfF, lfB, t1sw_t1sw] at this ⊢
    exact this

theorem swGarden_plain {G : Garden 2} (hp : G.IsPlain) : (swGarden G).IsPlain := fun ℓ => hp (lfB ℓ)

/-- **The layered couple with its two trees in the other order.** -/
@[reducible] def swLG (LG : LayeredGarden 2) : LayeredGarden 2 where
  garden := swGarden LG.garden
  layer a := LG.layer (ndB a)
  isLayering := ⟨fun b i => LG.isLayering.1 (brB b) i, fun ℓ => by
    show LG.layer (ndB ℓ.toNode) = LG.layer (ndB (lfF (LG.garden.pair (lfB ℓ))).toNode)
    rw [ndB_lfF_toNode]
    exact LG.isLayering.2 (lfB ℓ)⟩

section Invariance

variable {G : Garden 2}

theorem sign_ndB (a : GNode (swGarden G).tree) : G.sign (ndB a) = (swGarden G).sign a := rfl

theorem order_sw : (swGarden G).order = G.order := by
  unfold Garden.order
  simp only [Fin.sum_univ_two]
  show (G.tree (t1sw 0)).order + (G.tree (t1sw 1)).order = _
  simp only [t1sw]
  simp [add_comm]

theorem zeta_sw : (swGarden G).zeta = G.zeta := by
  unfold Garden.zeta
  exact Fintype.prod_equiv brEquiv _ _ (fun b => rfl)

theorem epsDec_sw {d : ℕ} (κ : GNode G.tree → (Fin d → ℤ)) : epsDec (swGarden G) (κ ∘ ndB) = epsDec G κ := by
  unfold epsDec
  exact Fintype.prod_equiv brEquiv _ _ (fun b => rfl)

theorem phaseProd_sw (L γ δ : ℝ) {d : ℕ} (K : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) :
    phaseProd L γ δ (swGarden G) (K ∘ ndB) (fun b => τ (brB b)) = phaseProd L γ δ G K τ := by
  unfold phaseProd
  exact Fintype.prod_equiv brEquiv _ _ (fun b => rfl)

theorem prod_inputLeaves_sw (hp : G.IsPlain) {M : Type*} [CommMonoid M] (f : GLeaf G.tree → M) :
    ∏ ℓ ∈ inputLeaves (swGarden G), f (lfB ℓ) = ∏ ℓ ∈ inputLeaves G, f ℓ := by
  rw [T1Data.prod_inputLeaves_plain (swGarden_plain hp), T1Data.prod_inputLeaves_plain hp]
  exact Fintype.prod_equiv lfEquiv _ _ (fun ℓ => rfl)

end Invariance

/-! ### Decorations -/

section Dec

variable {G : Garden 2} {V : Type*} [AddCommGroup V]

theorem isDecoration_sw {κ : GNode G.tree → V} (hκ : IsDecoration G κ) : IsDecoration (swGarden G) (κ ∘ ndB) := by
  refine ⟨fun b => hκ.1 (brB b), fun ℓ => ?_⟩
  show κ (ndB ℓ.toNode) = κ (ndB (lfF (G.pair (lfB ℓ))).toNode)
  rw [ndB_lfF_toNode]
  exact hκ.2 (lfB ℓ)

theorem isDecoration_of_sw {κ : GNode G.tree → V} (hκ : IsDecoration (swGarden G) (κ ∘ ndB)) :
    IsDecoration G κ := by
  refine ⟨fun b => ?_, fun ℓ => ?_⟩
  · have := hκ.1 (brF b)
    have hn : ndB (brF b).toNode = b.toNode := Subtype.ext (Prod.ext (t1sw_t1sw _) rfl)
    have hc : ∀ i, ndB ((brF b).child i) = b.child i := fun i => Subtype.ext (Prod.ext (t1sw_t1sw _) rfl)
    simp only [Function.comp_apply, hn, hc] at this
    exact this
  · have := hκ.2 (lfF ℓ)
    simp only [Function.comp_apply] at this
    rw [show ndB (lfF ℓ).toNode = ℓ.toNode from ndB_lfF_toNode ℓ] at this
    rw [this]
    show κ (ndB (lfF (G.pair (lfB (lfF ℓ)))).toNode) = _
    rw [lfB_lfF, ndB_lfF_toNode]

variable (d : ℕ)

/-- **Decorations of the relabelled couple.** -/
def swDec (hp : G.IsPlain) : GenDecoration G d (fun _ => 0) 0 ≃ GenDecoration (swGarden G) d (fun _ => 0) 0 where
  toFun κ := ⟨κ.1 ∘ ndB, isDecoration_sw κ.2.1, fun j => κ.2.2.1 (t1sw j),
    fun ℓ hℓ => absurd hℓ (not_flower_of_plain (swGarden_plain hp) ℓ)⟩
  invFun κ' := ⟨κ'.1 ∘ ndF, isDecoration_of_sw (by
      have h : (κ'.1 ∘ ndF) ∘ ndB = κ'.1 := funext fun a => congrArg κ'.1 (ndF_ndB a)
      rw [h]; exact κ'.2.1), fun j => by
      show κ'.1 (ndF (GNode.root G.tree j)) = 0
      exact κ'.2.2.1 (t1sw j),
    fun ℓ hℓ => absurd hℓ (not_flower_of_plain hp ℓ)⟩
  left_inv κ := Subtype.ext (funext fun a => congrArg κ.1 (ndB_ndF a))
  right_inv κ' := Subtype.ext (funext fun a => congrArg κ'.1 (ndF_ndB a))

theorem swDec_val (hp : G.IsPlain) (κ : GenDecoration G d (fun _ => 0) 0) : (swDec d hp κ).1 = κ.1 ∘ ndB := rfl

end Dec

/-! ### The time domain and the free-time integral -/

section Time

variable {LG : LayeredGarden 2}

theorem mem_protDom_sw (hp : LG.garden.IsPlain) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (τ : GBranch LG.garden.tree → ℝ) :
    τ ∈ protDom LG up s fix ↔
      (fun b => τ (brB b)) ∈ protDom (swLG LG) (fun b => up (brB b)) s (fun b => fix (brB b)) := by
  constructor
  · rintro ⟨hD, -⟩
    refine ⟨fun b => ⟨fun hb => (hD (brB b)).1 hb, fun b' hb' hor =>
      (hD (brB b)).2 (brB b') ((brB_child_iff b b').mpr hb') hor⟩, fun b hb _ =>
      absurd hb (not_loneParent_of_plain (swGarden_plain hp) b)⟩
  · rintro ⟨hD, -⟩
    refine ⟨(forall_brB _).mpr fun b => ⟨fun hb => (hD b).1 hb, fun c hc hor => ?_⟩, fun b hb _ =>
      absurd hb (not_loneParent_of_plain hp b)⟩
    rw [← brB_brF c] at hc hor ⊢
    exact (hD b).2 (brF c) ((brB_child_iff b (brF c)).mp hc) hor

/-- The free branches of the relabelled couple. -/
def swFree (fix : GBranch LG.garden.tree → Option ℝ) :
    {b : GBranch (swLG LG).garden.tree // fix (brB b) = none} ≃ {b : GBranch LG.garden.tree // fix b = none} :=
  brEquiv.subtypeEquiv (fun b => Iff.rfl)

theorem protTime_sw (hp : LG.garden.IsPlain) (L γ δ : ℝ) {d : ℕ} (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ (swLG LG) (fun b => up (brB b)) s (fun b => fix (brB b)) (K ∘ ndB) =
      protTime L γ δ LG up s fix K := by
  unfold protTime
  rw [← integral_arrow_equiv (swFree fix)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only
  have hext : (swLG LG).garden.extendFix (fun b => fix (brB b)) σ =
      fun b => LG.garden.extendFix fix (fun b => σ ((swFree fix).symm b)) (brB b) := by
    funext b
    cases hb : fix (brB b) with
    | some v =>
      rw [extendFix_some LG.garden fix _ hb]
      exact extendFix_some (swLG LG).garden (fun b => fix (brB b)) σ (show (fun b => fix (brB b)) b = some v from hb)
    | none =>
      rw [extendFix_free _ _ _ ⟨b, hb⟩, extendFix_free _ _ _ ⟨brB b, hb⟩]
      congr 1
      exact ((swFree fix).symm_apply_apply ⟨b, hb⟩).symm
  rw [hext]
  set τ := LG.garden.extendFix fix (fun b => σ ((swFree fix).symm b))
  by_cases hD : τ ∈ protDom LG up s fix
  · rw [Set.indicator_of_mem ((mem_protDom_sw hp up s fix τ).mp hD), Set.indicator_of_mem hD]
    exact phaseProd_sw L γ δ K τ
  · rw [Set.indicator_of_notMem (fun h => hD ((mem_protDom_sw hp up s fix τ).mpr h)),
      Set.indicator_of_notMem hD]

end Time

/-! ### The summand and the kernel -/

/-- The profiles of the relabelled couple. -/
def swH {d : ℕ} (H : LeafProfiles 2 d) : LeafProfiles 2 d := fun a => H (t1sw a.1, a.2)

/-- The multiplier of the relabelled couple. -/
def swM {d : ℕ} {G : Garden 2} (M : (GNode G.tree → Mom d) → ℂ) : (GNode (swGarden G).tree → Mom d) → ℂ :=
  fun K => M (K ∘ ndF)

/-- A branch-local multiplier stays branch-local under the relabelling. -/
theorem swM_local {G : Garden 2} {d : ℕ} (f : GBranch G.tree → (Fin 4 → Mom d) → ℂ) :
    swM (fun K => ∏ b, f b (bstar K b)) = fun K' => ∏ b', f (brB b') (bstar K' b') := by
  funext K'
  show ∏ b, f b (bstar (K' ∘ ndF) b) = _
  refine Fintype.prod_equiv brEquiv.symm _ _ (fun b => ?_)
  show f b (bstar (K' ∘ ndF) b) = f (brB (brF b)) (bstar K' (brF b))
  rw [brB_brF]
  congr 1

theorem protSummand_sw {LG : LayeredGarden 2} (hp : LG.garden.IsPlain) (L γ δ : ℝ) {d : ℕ}
    (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k : Mom d) (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
    protSummand L γ δ (swLG LG) (swH H) (swM M) (fun b => up (brB b)) s (fun b => fix (brB b)) k
        (swDec d hp κ) = protSummand L γ δ LG H M up s fix k κ := by
  unfold protSummand
  have hc : cosetDecoration (swLG LG).garden L k (swDec d hp κ).1 = cosetDecoration LG.garden L k κ.1 ∘ ndB := rfl
  have hm : swM M (cosetDecoration (swLG LG).garden L k (swDec d hp κ).1) = M (cosetDecoration LG.garden L k κ.1) := by
    rw [hc]
    show M ((cosetDecoration LG.garden L k κ.1 ∘ ndB) ∘ ndF) = _
    congr 1
    funext a
    exact congrArg (cosetDecoration LG.garden L k κ.1) (ndB_ndF a)
  have he : epsDec (swLG LG).garden (swDec d hp κ).1 = epsDec LG.garden κ.1 := epsDec_sw κ.1
  have ht := protTime_sw hp L γ δ up s fix (cosetDecoration LG.garden L k κ.1)
  have hl : ∏ ℓ ∈ inputLeaves (swLG LG).garden,
      (swH H ℓ.1 (cosetDecoration (swLG LG).garden L k (swDec d hp κ).1 ℓ.toNode) : ℂ) =
      ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) :=
    prod_inputLeaves_sw hp (fun ℓ => (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ))
  rw [hm, he, hc, ht, ← hc, hl]

/-- **Relabelling the two trees of a plain couple leaves `kernelProt` unchanged.** -/
theorem kernelProt_sw {LG : LayeredGarden 2} (hp : LG.garden.IsPlain) (L γ δ : ℝ) {d : ℕ}
    (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k : Mom d) :
    kernelProt L γ δ (swLG LG) (swH H) (swM M) (fun b => up (brB b)) s (fun b => fix (brB b)) k (fun _ => 0) 0 =
      kernelProt L γ δ LG H M up s fix k (fun _ => 0) 0 := by
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum, ← (swDec d hp).tsum_eq]
  simp only [protSummand_sw hp]
  rw [order_sw, zeta_sw]

end WaveTurbulence.Flower.ProtCut
