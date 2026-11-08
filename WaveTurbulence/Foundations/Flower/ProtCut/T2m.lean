/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Exist

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (c), time level — a type-2 couple with an empty chain

A couple `LG` decoded by `type2 Xp nil (type1 c Q₁ Q₂ Q₃)` (the `-` chain empty, `m_- = 0`; the lone-pair couple
`Q_lp` is of type 1, as it must be when its tree `1` root is branching). Its tree `1` is the tree `1` of `Q_lp`; its
tree `0` is the chain `Xp` with the tree `0` of `Q_lp` at the lone position `Xp.lonePath` (main's
`glueData_couple`, with `X₂ = nil`): `T2mData`, top `LGX` (code `Xp`), bottom `LGQ` (code `type1 c Q₁ Q₂ Q₃`).

The root `ρ = (1, [])` designated at `σ ≤ U 1` (`trFix 1 σ`); its partner `ρ' = (0, Xp.lonePath)` (the root of the
tree `0` of `Q_lp`, whose upper bound is the last chain node `n⁺_{2m}`) is integrated (`u = τ_{ρ'}`):
**`T2mData.protTime_t2m`**:

`protTime (trFix 1 σ) = ∫_{u ∈ t2mU} K_X(U 0, port u) · Q_lp(roots at (u, σ))`,

`t2mU = {𝔏_{ρ'} < u < 𝔏_{ρ'} + 1, 0 < u, u < U 0}`; the top chain carries the lone-port time `u` (its lone parent
is later than `u`), and `Q_lp` has both roots designated, so o104 (b) (`T1Data.protTime_t1`) cuts it. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- **A couple whose tree `0` is a chain `Xp` glued on a bottom couple `LGQ` at its root `0`** (o104 Prop 7.4 (c)):
the fields are what the cut uses (the gluing, plainness, the decoration split and glue, the layers). The decoded instance
(`type2 Xp nil (type1 c Q₁ Q₂ Q₃)`, `ε = -`) is `T2mData.of_decodes`; the relabelled instance (`ε = +`) is in
`T2p.lean`. -/
structure T2mData (LG : LayeredGarden 2) (Xp : RegChain) (LGX : LayeredGarden 1) (LGQ : LayeredGarden 2) : Prop where
  gd : GlueData LG.garden LGX.garden LGQ.garden Xp
  decX : Xp.DecodesTree LGX.garden
  plain : LG.garden.IsPlain
  plainQ : LGQ.garden.IsPlain
  rootQ : ([] : Path) ∈ (LGQ.garden.tree 0).branching
  hs : ∀ d : ℕ, gd.DecSplit (Fin d → ℤ)
  hg : ∀ d : ℕ, GlueData.DecGlue (G := LG.garden) (G₁ := LGX.garden) (G₂ := LGQ.garden) (X := Xp) (Fin d → ℤ)
  layX : ∀ z : GNode LGX.garden.tree, LGX.layer z = layerAt LG ((0 : Fin 2), z.1.2)
  layQ : ∀ z : GNode LGQ.garden.tree, LGQ.layer z = layerAt LG (botAddr Xp.lonePath z.1)

/-- The range of the partner time `u = τ_{ρ'}`. -/
def t2mU (LG : LayeredGarden 2) (Xp : RegChain) (T : ℝ) : Set ℝ :=
  {u | (layerAt LG ((0 : Fin 2), Xp.lonePath) : ℝ) < u ∧ u < layerAt LG ((0 : Fin 2), Xp.lonePath) + 1 ∧
    0 < u ∧ u < T}

theorem measurableSet_t2mU (LG : LayeredGarden 2) (Xp : RegChain) (T : ℝ) : MeasurableSet (t2mU LG Xp T) := by
  unfold t2mU
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter
      ((measurableSet_lt measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const)))

theorem volume_t2mU_ne_top (LG : LayeredGarden 2) (Xp : RegChain) (T : ℝ) : volume (t2mU LG Xp T) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := volume (Ioo (layerAt LG ((0 : Fin 2), Xp.lonePath) : ℝ)
    (layerAt LG ((0 : Fin 2), Xp.lonePath) + 1))) ?_ (measure_mono fun u hu => ⟨hu.1, hu.2.1⟩)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- Both roots of a couple designated, at `σ t`. -/
def rootsFix (σ : Fin 2 → ℝ) {T : Fin 2 → TTree} (y : GBranch T) : Option ℝ :=
  if y.1.2 = [] then some (σ y.1.1) else none

theorem botAddr_fst (lp : Path) (x : Fin 2 × Path) : (botAddr lp x).1 = x.1 := by
  obtain ⟨j, p⟩ := x
  unfold botAddr
  split_ifs with h
  · exact h.symm
  · rfl

theorem closeCouple_nil_nil (Q : RegCpl) : SourceApp.closeCouple .nil .nil Q = Q := by
  simp [SourceApp.closeCouple, RegChain.isNil]

/-- **The decoded instance** (`ε = -`): a couple decoded by `type2 Xp nil (type1 c Q₁ Q₂ Q₃)`. -/
theorem T2mData.of_decodes {LG : LayeredGarden 2} {Xp : RegChain} {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl}
    {LGX : LayeredGarden 1} {LGQ : LayeredGarden 2}
    (dec : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).Decodes LG.garden) (decX : Xp.DecodesTree LGX.garden)
    (sigX : LGX.garden.sig 0 = 1) (decQ : (RegCpl.type1 c Q₁ Q₂ Q₃).Decodes LGQ.garden)
    (layX : ∀ z : GNode LGX.garden.tree, LGX.layer z = layerAt LG ((0 : Fin 2), z.1.2))
    (layQ : ∀ z : GNode LGQ.garden.tree, LGQ.layer z = layerAt LG (botAddr Xp.lonePath z.1)) :
    T2mData LG Xp LGX LGQ :=
  have dec' : (RegCpl.type2 (appendChain Xp .nil) .nil (.type1 c Q₁ Q₂ Q₃)).Decodes LG.garden := by
    rw [appendChain_nil_right]; exact dec
  have decQ' : (SourceApp.closeCouple .nil .nil (.type1 c Q₁ Q₂ Q₃)).Decodes LGQ.garden := by
    rw [closeCouple_nil_nil]; exact decQ
  ⟨glueData_couple dec' decX sigX decQ', decX, dec.1.1, decQ.1.1, by
    rw [decQ.2.1]
    exact (mem_node3_nil ![_, _, _]).2.2, fun _ => decSplit_couple dec' decX sigX decQ',
    fun _ => decGlue_couple dec' decX sigX decQ', layX, layQ⟩

namespace T2mData

variable {LG : LayeredGarden 2} {Xp : RegChain}
  {LGX : LayeredGarden 1} {LGQ : LayeredGarden 2} (D : T2mData LG Xp LGX LGQ)
include D

/-- The root of tree `0` of `Q_lp`. -/
def r0 : GBranch LGQ.garden.tree := ⟨((0 : Fin 2), []), D.rootQ⟩

/-- The partner `ρ' = (0, Xp.lonePath)` in the couple. -/
def jB : GBranch LG.garden.tree := D.gd.ofSum (.inr D.r0)

theorem jB_val : D.jB.1 = ((0 : Fin 2), Xp.lonePath) := by
  show botAddr Xp.lonePath ((0 : Fin 2), ([] : Path)) = _
  simp [botAddr]

theorem ofSum_inl_val (x : GBranch LGX.garden.tree) : (D.gd.ofSum (.inl x)).1 = ((0 : Fin 2), x.1.2) := rfl

theorem ofSum_inr_val (y : GBranch LGQ.garden.tree) : (D.gd.ofSum (.inr y)).1 = botAddr Xp.lonePath y.1 := rfl

theorem trFix_jB (σ : ℝ) : trFix 1 σ D.jB = none := by
  unfold trFix
  rw [D.jB_val]
  simp

theorem not_loneParent (b : GBranch LG.garden.tree) : ¬ LG.garden.IsLoneParent b :=
  not_loneParent_of_plain D.plain b

theorem hlone (b : GBranch LG.garden.tree) :
    LG.garden.IsLoneParent b ↔ ∃ y, b = D.gd.ofSum (.inr y) ∧ LGQ.garden.IsLoneParent y := by
  constructor
  · intro hb; exact absurd hb (D.not_loneParent b)
  · rintro ⟨y, -, hy⟩; exact absurd hy (not_loneParent_of_plain D.plainQ y)

theorem hlone₁ (x : GBranch LGX.garden.tree) :
    LGX.garden.IsLoneParent x ↔ D.jB.IsChildOf (D.gd.ofSum (.inl x)) := by
  have key : LGX.garden.IsLoneParent x ↔ ∃ i : Fin 3, x.1.2 ++ [i] = Xp.lonePath := by
    constructor
    · rintro ⟨ℓ, hℓ, -, i, hi⟩
      have hpath : ℓ.1.2 = Xp.lonePath := by
        by_contra hne
        unfold Garden.IsLone at hℓ
        rw [D.decX.2.1 ℓ, ite_eq_right hne] at hℓ
        exact absurd hℓ (by simp)
      exact ⟨i, hi.symm.trans hpath⟩
    · rintro ⟨i, hi⟩
      have hmem : Xp.lonePath ∈ (LGX.garden.tree x.1.1).leaves := by
        rw [Subsingleton.elim x.1.1 0, D.decX.1]
        exact lonePath_mem_leaves _ _
      refine ⟨⟨(x.1.1, Xp.lonePath), hmem⟩, ?_, rfl, i, hi.symm⟩
      unfold Garden.IsLone
      exact (D.decX.2.1 _).trans (by simp)
  rw [key]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨?_, i, ?_⟩
    · show D.jB.1.1 = (D.gd.ofSum (.inl x)).1.1
      rw [D.jB_val, D.ofSum_inl_val]
    · show D.jB.1.2 = (D.gd.ofSum (.inl x)).1.2 ++ [i]
      rw [D.jB_val, D.ofSum_inl_val]
      exact hi.symm
  · rintro ⟨-, i, hi⟩
    have hi' : D.jB.1.2 = (D.gd.ofSum (.inl x)).1.2 ++ [i] := hi
    rw [D.jB_val, D.ofSum_inl_val] at hi'
    exact ⟨i, hi'.symm⟩

/-- The partner's constraints are exactly its own window and its upper clock. -/
theorem pinSet_jB (U : Fin 2 → ℝ) (s σ : ℝ) :
    pinSet LG (fun b => U b.1.1) s (trFix 1 σ) D.jB = t2mU LG Xp (U 0) := by
  ext u
  have hl : (LG.layer D.jB.toNode : ℝ) = layerAt LG ((0 : Fin 2), Xp.lonePath) := by
    rw [← D.jB_val, ← layerAt_node]; rfl
  have hU : U D.jB.1.1 = U 0 := by rw [D.jB_val]
  constructor
  · rintro ⟨h1, h2, h3, h4, -⟩
    rw [hl] at h1 h2
    exact ⟨h1, h2, h3, (show u < U D.jB.1.1 from h4).trans_eq hU⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by rw [hl]; exact h1, by rw [hl]; exact h2, h3, by show u < U D.jB.1.1; rw [hU]; exact h4,
      fun b' hb' v hv => ?_,
      fun b hb v hv => ?_, fun hl' => absurd hl' (D.not_loneParent _)⟩
    · obtain ⟨h0, i, hi⟩ := hb'
      have : b'.1.1 = 0 := by rw [h0, D.jB_val]
      unfold trFix at hv
      rw [if_neg (fun h => by rw [this] at h; exact absurd h.1 (by decide))] at hv
      simp at hv
    · obtain ⟨h0, i, hi⟩ := hb
      have : b.1.1 = 0 := by rw [← h0, D.jB_val]
      unfold trFix at hv
      rw [if_neg (fun h => by rw [this] at h; exact absurd h.1 (by decide))] at hv
      simp at hv

/-- The designations after the partner is designated at `u`. -/
theorem fix_inl (σ u : ℝ) (x : GBranch LGX.garden.tree) :
    Function.update (trFix 1 σ) D.jB (some u) (D.gd.ofSum (.inl x)) = none := by
  rw [Function.update_of_ne]
  · unfold trFix
    rw [if_neg]
    rw [D.ofSum_inl_val]
    simp
  · intro he
    have := D.gd.ofSum_injective he
    simp [jB] at this

theorem fix_inr (σ u : ℝ) (y : GBranch LGQ.garden.tree) :
    Function.update (trFix 1 σ) D.jB (some u) (D.gd.ofSum (.inr y)) = rootsFix (t1Clock 1 σ u) y := by
  by_cases hy : y = D.r0
  · subst hy
    rw [show D.gd.ofSum (.inr D.r0) = D.jB from rfl, Function.update_self]
    unfold rootsFix t1Clock
    simp [r0]
  · rw [Function.update_of_ne (fun he => hy (by
      have := D.gd.ofSum_injective he
      simpa [jB] using this))]
    unfold trFix rootsFix
    rw [D.ofSum_inr_val, botAddr_fst]
    obtain ⟨⟨t, p⟩, hp⟩ := y
    by_cases hp0 : p = []
    · subst hp0
      have ht : t = 1 := by
        fin_cases t
        · exact absurd rfl hy
        · rfl
      subst ht
      simp [botAddr, t1Clock]
    · have hb : (botAddr Xp.lonePath (t, p)).2 ≠ [] := by
        unfold botAddr; split_ifs <;> simp [hp0]
      simp only [hp0, if_false]
      rw [if_neg (fun h => hb h.2)]

/-- **The glue and pin step** (o104 (c)): the partner integrated, the chain split off. -/
theorem protTime_t2mGlue (L γ δ : ℝ) {d : ℕ} (U : Fin 2 → ℝ) (s σ : ℝ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun b => U b.1.1) s (trFix 1 σ) K =
      ∫ u in t2mU LG Xp (U 0), protTime L γ δ LGX (fun _ => U 0) u (fun _ => none) (K ∘ D.gd.ι₁) *
        protTime L γ δ LGQ (fun y => U y.1.1) s (rootsFix (t1Clock 1 σ u)) (K ∘ D.gd.ι₂) := by
  rw [protTime_pin L γ δ LG (fun b => U b.1.1) s (trFix 1 σ) K D.jB (D.trFix_jB σ), D.pinSet_jB U s σ,
    ← integral_indicator (measurableSet_t2mU LG Xp (U 0))]
  congr 1
  funext u
  by_cases hu : u ∈ t2mU LG Xp (U 0)
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    set fix := Function.update (trFix 1 σ) D.jB (some u)
    have hD := fun τ hτ => protDom_glue_pinned (LG₂ := LGQ) D.gd (fun b => U b.1.1) s fix D.r0 rfl u
      (Function.update_self _ _ _) (fun x => by rw [D.layX, ← layerAt_node]; rfl)
      (fun y => by rw [D.layQ, ← layerAt_node]; rfl) D.hlone D.hlone₁ τ hτ
    rw [protTime_glue L γ δ (LG₂ := LGQ) D.gd (fun b => U b.1.1) s fix (fun _ => U 0) u
      (fun y => U y.1.1) s K (fun τ hτ => by
        have hup₁ : ∀ x : GBranch LGX.garden.tree, U (D.gd.ofSum (.inl x)).1.1 = U 0 := fun x => rfl
        have hup₂ : ∀ y : GBranch LGQ.garden.tree, U (D.gd.ofSum (.inr y)).1.1 = U y.1.1 := fun y => by
          rw [D.ofSum_inr_val, botAddr_fst]
        simpa only [hup₁, hup₂] using hD τ hτ)]
    congr 2
    · funext x; exact D.fix_inl σ u x
    · funext y; exact D.fix_inr σ u y
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]

end T2mData

end WaveTurbulence.Flower.ProtCut
