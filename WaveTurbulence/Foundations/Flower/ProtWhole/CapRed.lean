/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CapKer
public import WaveTurbulence.Foundations.Flower.ProtGeo.Faith
public import WaveTurbulence.Foundations.Flower.ProtKer.Bridge

/-! # D6b: a width-2 cap couple, cap at either index, is its paired tree

D2c's `ProtCut.CapData` treats the normalized cap couple (cap = tree `1`, sign `+` on tree `0`). A wholly regular
capped component may have its cap at index `0` (the big tree then has sign `-1`). Here (`CapG`, adapted from
`ProtCut/Cap.lean`, `ProtCut/CapKer.lean`, see COPIED-SHA256SUMS) the big tree `j0` and the cap `c ≠ j0` are arbitrary,
the paired tree is D2b's `objTree` at the root of `j0` with its true sign, and the reduction starts from the frozen
`kernelKgen` with `F ≡ 1` (a component value `MkDefs.compValue`):

* **`CapG.kernelKgen_capG`**: `kernelKgen L γ δ 1 LG fix off wt up 0 roots 0 = [roots c = roots j0] ·
  kernelProt (objTree …) 1 (wt ∘ ext · offFactor ∘ ext) (up ∘ βc) 0 (fix ∘ βc) (latticePoint L (roots j0)) 0 0`,
  provided every removed phase (`off`) is at a pinned branch.
* the decoration shift `kernelKgen_shift` (any garden) and the removed-phase identity `phaseProdOff_extendFix`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtWhole

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtGeo

variable {d : ℕ}

/-! ### Decoration shift and removed phases (any garden) -/

section General

variable {w : ℕ}

theorem isDec_sub {G : Garden w} {κ : GNode G.tree → (Fin d → ℤ)} (h : IsDecoration G κ) (e : Fin d → ℤ) :
    IsDecoration G (fun a => κ a - e) := by
  refine ⟨fun b => ?_, fun ℓ => ?_⟩
  · show κ b.toNode - e = (κ (b.child 0) - e) - (κ (b.child 1) - e) + (κ (b.child 2) - e)
    rw [h.1 b]; abel
  · show κ ℓ.toNode - e = κ (G.pair ℓ).toNode - e
    rw [h.2 ℓ]

theorem isDec_add {G : Garden w} {κ : GNode G.tree → (Fin d → ℤ)} (h : IsDecoration G κ) (e : Fin d → ℤ) :
    IsDecoration G (fun a => κ a + e) := by
  refine ⟨fun b => ?_, fun ℓ => ?_⟩
  · show κ b.toNode + e = (κ (b.child 0) + e) - (κ (b.child 1) + e) + (κ (b.child 2) + e)
    rw [h.1 b]; abel
  · show κ ℓ.toNode + e = κ (G.pair ℓ).toNode + e
    rw [h.2 ℓ]

/-- Shifting an integer decoration by a constant. -/
def shiftDec (G : Garden w) (n : Fin w → (Fin d → ℤ)) (n' : Fin d → ℤ) (e : Fin d → ℤ) :
    GenDecoration G d n n' ≃ GenDecoration G d (fun j => n j - e) (n' - e) where
  toFun κ := ⟨fun a => κ.1 a - e, isDec_sub κ.2.1 e, fun j => congrArg (· - e) (κ.2.2.1 j),
    fun ℓ h => congrArg (· - e) (κ.2.2.2 ℓ h)⟩
  invFun κ := ⟨fun a => κ.1 a + e, isDec_add κ.2.1 e,
    fun j => (congrArg (· + e) (κ.2.2.1 j)).trans (sub_add_cancel _ _),
    fun ℓ h => (congrArg (· + e) (κ.2.2.2 ℓ h)).trans (sub_add_cancel _ _)⟩
  left_inv κ := Subtype.ext (funext fun a => sub_add_cancel (κ.1 a) e)
  right_inv κ := Subtype.ext (funext fun a => add_sub_cancel_right (κ.1 a) e)

theorem epsDec_shift (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ)) (e : Fin d → ℤ) :
    epsDec G (fun a => κ a - e) = epsDec G κ := by
  unfold epsDec epsCoef
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [ne_eq, sub_left_inj]

/-- **Decoration shift**: the root lattice values can be moved into the base momentum. -/
theorem kernelKgen_shift (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (n : Fin w → (Fin d → ℤ)) (n' : Fin d → ℤ) (e : Fin d → ℤ) :
    kernelKgen L γ δ F LG fix off wt up k₀ n n' =
      kernelKgen L γ δ F LG fix off wt up (k₀ + latticePoint L e) (fun j => n j - e) (n' - e) := by
  unfold kernelKgen
  congr 1
  rw [← (shiftDec LG.garden n n' e).tsum_eq]
  refine tsum_congr fun κ => ?_
  have hc : cosetDecoration LG.garden L (k₀ + latticePoint L e) (shiftDec LG.garden n n' e κ).1 =
      cosetDecoration LG.garden L k₀ κ.1 := by
    funext a
    show k₀ + latticePoint L e + latticePoint L (κ.1 a - e) = k₀ + latticePoint L (κ.1 a)
    rw [WaveTurbulence.Links.latticePoint_sub]
    abel
  have he : epsDec LG.garden (shiftDec LG.garden n n' e κ).1 = epsDec LG.garden κ.1 :=
    epsDec_shift LG.garden κ.1 e
  rw [hc, he]

/-- Without flowers the flower value is void. -/
def nflEquiv (G : Garden w) (hfl : ∀ ℓ, ¬ G.IsFlower ℓ) (n : Fin w → (Fin d → ℤ)) (n' n'' : Fin d → ℤ) :
    GenDecoration G d n n' ≃ GenDecoration G d n n'' where
  toFun κ := ⟨κ.1, κ.2.1, κ.2.2.1, fun ℓ h => absurd h (hfl ℓ)⟩
  invFun κ := ⟨κ.1, κ.2.1, κ.2.2.1, fun ℓ h => absurd h (hfl ℓ)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem kernelKgen_nfl (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (hfl : ∀ ℓ, ¬ LG.garden.IsFlower ℓ)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (n : Fin w → (Fin d → ℤ)) (n' n'' : Fin d → ℤ) :
    kernelKgen L γ δ F LG fix off wt up k₀ n n' = kernelKgen L γ δ F LG fix off wt up k₀ n n'' := by
  unfold kernelKgen
  congr 1
  rw [← (nflEquiv LG.garden hfl n n' n'').tsum_eq]
  rfl

/-- The removed-phase factor: the inverse phases of the `off` branches at their pinned times. -/
def offFactor (L γ δ : ℝ) (G : Garden w) (off : Finset (GBranch G.tree)) (fix : GBranch G.tree → Option ℝ)
    (K : GNode G.tree → Mom d) : ℂ :=
  ∏ b ∈ off, Complex.exp (-(((Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G K b *
    (fix b).getD 0 : ℝ) : ℂ) * Complex.I))

theorem norm_offFactor (L γ δ : ℝ) (G : Garden w) (off : Finset (GBranch G.tree)) (fix : GBranch G.tree → Option ℝ)
    (K : GNode G.tree → Mom d) : ‖offFactor L γ δ G off fix K‖ = 1 := by
  unfold offFactor
  rw [norm_prod]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← neg_mul, ← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

theorem prod_off_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (E N : ι → ℂ)
    (h : ∀ i ∈ s, E i * N i = 1) : ∏ i, (if i ∈ s then 1 else E i) = (∏ i, E i) * ∏ i ∈ s, N i := by
  have hpt : ∀ i, (if i ∈ s then (1 : ℂ) else E i) = E i * (if i ∈ s then N i else 1) := fun i => by
    split_ifs with hi
    · exact (h i hi).symm
    · ring
  rw [Finset.prod_congr rfl (fun i _ => hpt i), Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]

/-- **Removed phases at pinned branches** are a decoration factor. -/
theorem phaseProdOff_extendFix (L γ δ : ℝ) (G : Garden w) (off : Finset (GBranch G.tree))
    (fix : GBranch G.tree → Option ℝ) (hoff : ∀ b ∈ off, (fix b).isSome) (K : GNode G.tree → Mom d)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) :
    phaseProdOff L γ δ G off K (G.extendFix fix τ) =
      phaseProd L γ δ G K (G.extendFix fix τ) * offFactor L γ δ G off fix K := by
  unfold phaseProdOff phaseProd offFactor
  refine prod_off_aux off _ _ fun b hb => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hoff b hb)
  rw [extendFix_some G fix τ hv, hv, Option.getD_some, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem fin2_sum {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) (j0 c : Fin 2) (h : j0 ≠ c) :
    ∑ j, f j = f j0 + f c := by
  fin_cases j0 <;> fin_cases c <;> simp_all [Fin.sum_univ_two, add_comm]

end General

/-! ### The data -/

/-- **A width-2 cap couple**: tree `j0` is the paired tree of `X` with its root sign `ζ` (a chain embedding at the
root), its lone leaf is paired with the cap root `(c, [])`, and tree `c ≠ j0` is a leaf. -/
structure CapG (LG : LayeredGarden 2) (j0 c : Fin 2) (X : RegChain) (ζ : ℤˣ) : Prop where
  ne : j0 ≠ c
  emb : ChainEmb LG.garden X ζ (j0, []) .leaf
  cap : LG.garden.tree c = .leaf
  sig : LG.garden.sig j0 = ζ
  pair : ∀ ℓ : GLeaf LG.garden.tree, ℓ.1 = (j0, X.lonePath) → (LG.garden.pair ℓ).1 = (c, [])
  plain : LG.garden.IsPlain

namespace CapG

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ} (D : CapG LG j0 c X ζ)
include D

/-- The paired tree: D2b's `objTree` at the root of tree `j0`. -/
abbrev T1 : LayeredGarden 1 := objTree LG X ζ (j0, []) D.emb

theorem tree_j0 : LG.garden.tree j0 = X.plug ζ .leaf := D.emb.tree

theorem tree_eq : D.T1.garden.tree 0 = LG.garden.tree j0 := D.tree_j0.symm

set_option linter.unusedSectionVars false in
theorem fin1 (j : Fin 1) : j = 0 := Subsingleton.elim _ _

theorem idx (a : Fin 2) (h : a ≠ j0) : a = c := by
  have hn := D.ne
  simp only [ne_eq, Fin.ext_iff] at h hn ⊢
  omega

theorem branch_j0 (b : GBranch LG.garden.tree) : b.1.1 = j0 := by
  by_contra h
  have hb := b.2
  rw [D.idx _ h, D.cap] at hb
  simp [TTree.branching] at hb

theorem node_c (a : GNode LG.garden.tree) (h : a.1.1 ≠ j0) : a.1 = (c, []) := by
  have ha := a.2
  rw [D.idx _ h, D.cap] at ha
  simp [TTree.nodes] at ha
  exact Prod.ext (D.idx _ h) ha

/-- The placement of the paired tree in the couple. -/
def ι (a : GNode D.T1.garden.tree) : GNode LG.garden.tree :=
  ⟨(j0, a.1.2), by
    have h := a.2
    rw [D.fin1 a.1.1, D.tree_eq] at h
    exact h⟩

/-- The lone leaf of the paired tree. -/
def lone1 : GNode D.T1.garden.tree :=
  ⟨((0 : Fin 1), X.lonePath), lonePath_mem_plug X ζ .leaf⟩

/-- The projection of the couple on the paired tree (the cap goes to the lone leaf). -/
def ρ (a : GNode LG.garden.tree) : GNode D.T1.garden.tree :=
  ⟨((0 : Fin 1), if a.1.1 = j0 then a.1.2 else X.lonePath), by
    split_ifs with h
    · have h2 := a.2
      rw [h, ← D.tree_eq] at h2
      exact h2
    · exact lonePath_mem_plug X ζ .leaf⟩

theorem ρ_val (a : GNode LG.garden.tree) (h : a.1.1 = j0) : (D.ρ a).1 = ((0 : Fin 1), a.1.2) := by
  show ((0 : Fin 1), if a.1.1 = j0 then a.1.2 else X.lonePath) = _
  rw [if_pos h]

theorem ρ_ι (a : GNode D.T1.garden.tree) : D.ρ (D.ι a) = a :=
  Subtype.ext ((D.ρ_val _ rfl).trans (Prod.ext (D.fin1 _).symm rfl))

theorem ι_ρ (a : GNode LG.garden.tree) (h : a.1.1 = j0) : D.ι (D.ρ a) = a := by
  have e : (D.ρ a).1.2 = a.1.2 := congrArg Prod.snd (D.ρ_val a h)
  exact Subtype.ext (Prod.ext h.symm e)

theorem ρ_c (a : GNode LG.garden.tree) (h : a.1.1 ≠ j0) : D.ρ a = D.lone1 := by
  refine Subtype.ext ?_
  show ((0 : Fin 1), if a.1.1 = j0 then a.1.2 else X.lonePath) = _
  rw [if_neg h]
  rfl

/-- The branches of the couple are those of the paired tree. -/
def βc : GBranch D.T1.garden.tree ≃ GBranch LG.garden.tree where
  toFun b := ⟨(j0, b.1.2), by
    have h := b.2
    rw [D.fin1 b.1.1, D.tree_eq] at h
    exact h⟩
  invFun b := ⟨((0 : Fin 1), b.1.2), by
    have h := b.2
    rw [D.branch_j0 b, ← D.tree_eq] at h
    exact h⟩
  left_inv b := Subtype.ext (Prod.ext (D.fin1 _).symm rfl)
  right_inv b := Subtype.ext (Prod.ext (D.branch_j0 b).symm rfl)

theorem βc_toNode (b : GBranch D.T1.garden.tree) : (D.βc b).toNode = D.ι b.toNode := rfl

theorem βc_child (b : GBranch D.T1.garden.tree) (i : Fin 3) : (D.βc b).child i = D.ι (b.child i) := rfl

theorem ρ_βc_toNode (b : GBranch LG.garden.tree) : D.ρ b.toNode = (D.βc.symm b).toNode :=
  Subtype.ext (D.ρ_val _ (D.branch_j0 b))

theorem ρ_βc_child (b : GBranch LG.garden.tree) (i : Fin 3) : D.ρ (b.child i) = (D.βc.symm b).child i :=
  Subtype.ext (D.ρ_val _ (D.branch_j0 b))

theorem sign_ι (a : GNode D.T1.garden.tree) : LG.garden.sign (D.ι a) = D.T1.garden.sign a := by
  have hζ : ζ = nodeSign LG.garden.sig (j0, []) := by
    rw [← D.sig]; simp [nodeSign, TTree.pathSign]
  have h := objTree_nodeSign_of D.emb hζ a.1.2
  unfold Garden.sign
  have e : a.1 = ((0 : Fin 1), a.1.2) := Prod.ext (D.fin1 _) rfl
  rw [e]
  exact h

theorem layer_ι (a : GNode D.T1.garden.tree) : LG.layer (D.ι a) = D.T1.layer a := by
  rw [← layerAt_node LG (D.ι a)]
  rfl

/-! #### Leaves and pairs -/

/-- The leaves of the paired tree in the couple. -/
def ιL (ℓ : GLeaf D.T1.garden.tree) : GLeaf LG.garden.tree :=
  ⟨(j0, ℓ.1.2), by
    have h := ℓ.2
    rw [D.fin1 ℓ.1.1, D.tree_eq] at h
    exact h⟩

theorem ιL_injective : Function.Injective D.ιL := by
  intro ℓ ℓ' h
  have h2 := congrArg (fun z : GLeaf LG.garden.tree => z.1.2) h
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h2)

theorem ιL_toNode (ℓ : GLeaf D.T1.garden.tree) : (D.ιL ℓ).toNode = D.ι ℓ.toNode := rfl

/-- The lone leaf of `X` in the couple (the capped flower). -/
def ℓ0 : GLeaf LG.garden.tree :=
  ⟨(j0, X.lonePath), by rw [D.tree_j0]; exact lonePath_mem_leaves X ζ⟩

theorem pair_ℓ0 : (LG.garden.pair D.ℓ0).1 = (c, []) := D.pair D.ℓ0 rfl

theorem pair_ιL (ℓ : GLeaf D.T1.garden.tree) (hℓ : ℓ.1.2 ≠ X.lonePath) :
    LG.garden.pair (D.ιL ℓ) = D.ιL (D.T1.garden.pair ℓ) :=
  Subtype.ext (objTree_pair D.emb ℓ hℓ (D.ιL ℓ) rfl)

theorem leaf_cases (ℓ : GLeaf LG.garden.tree) :
    ℓ = D.ℓ0 ∨ ℓ.1 = (c, []) ∨ ∃ ℓ1 : GLeaf D.T1.garden.tree, ℓ1.1.2 ≠ X.lonePath ∧ ℓ = D.ιL ℓ1 := by
  by_cases h0 : ℓ.1.1 = j0
  · by_cases hl : ℓ.1.2 = X.lonePath
    · exact Or.inl (Subtype.ext (Prod.ext h0 hl))
    · right; right
      refine ⟨⟨((0 : Fin 1), ℓ.1.2), ?_⟩, hl, Subtype.ext (Prod.ext h0 rfl)⟩
      have h := ℓ.2
      rw [h0, ← D.tree_eq] at h
      exact h
  · right; left
    have h := TTree.leaves_subset_nodes _ ℓ.2
    exact D.node_c ⟨ℓ.1, h⟩ h0

theorem pair_c (ℓ : GLeaf LG.garden.tree) (h : ℓ.1 = (c, [])) : LG.garden.pair ℓ = D.ℓ0 := by
  have hp : LG.garden.pair D.ℓ0 = ℓ := Subtype.ext (D.pair_ℓ0.trans h.symm)
  rw [← hp, LG.garden.pair_pair]

theorem ρ_ℓ0 : D.ρ D.ℓ0.toNode = D.lone1 :=
  Subtype.ext (D.ρ_val _ rfl)

theorem ι_lone1 : D.ι D.lone1 = D.ℓ0.toNode := rfl

/-! #### Decorations -/

theorem lone1_eq_root {V : Type*} [AddCommGroup V] {κ : GNode D.T1.garden.tree → V}
    (hκ : IsDecoration D.T1.garden κ) : κ D.lone1 = κ (GNode.root D.T1.garden.tree 0) := by
  have hc := chainDec_of_decoration (decodedTree_decodes X ζ) hκ
  have h := chainDec_lone_eq _ X _ _ hc
  have e1 : extend κ ((0 : Fin 1), ([] : Path)) = κ (GNode.root D.T1.garden.tree 0) :=
    extend_node κ (GNode.root D.T1.garden.tree 0)
  have e2 : extend κ (addrExt ((0 : Fin 1), ([] : Path)) X.lonePath) = κ D.lone1 := by
    have : addrExt ((0 : Fin 1), ([] : Path)) X.lonePath = D.lone1.1 := by simp [addrExt, lone1]
    rw [this]
    exact extend_node κ D.lone1
  rw [← e1, ← e2]
  exact h.symm

theorem not_flower1 (ℓ : GLeaf D.T1.garden.tree) : ¬ D.T1.garden.IsFlower ℓ := by
  unfold Garden.IsFlower
  have hm := (decodedTree_decodes X ζ).2.1 ℓ
  change D.T1.garden.mark ℓ = _ at hm
  rw [hm]
  split_ifs <;> simp

theorem not_flower (ℓ : GLeaf LG.garden.tree) : ¬ LG.garden.IsFlower ℓ := by
  unfold Garden.IsFlower
  rw [D.plain ℓ]
  simp

theorem isDec_fwd {V : Type*} [AddCommGroup V] {κ : GNode LG.garden.tree → V} (hκ : IsDecoration LG.garden κ) :
    IsDecoration D.T1.garden (κ ∘ D.ι) := by
  refine ⟨fun b => ?_, fun ℓ => ?_⟩
  · have := hκ.1 (D.βc b)
    simpa only [Function.comp_apply, D.βc_toNode, D.βc_child] using this
  · by_cases hl : ℓ.1.2 = X.lonePath
    · have hm : D.T1.garden.mark ℓ ≠ none := by
        have hm0 := (decodedTree_decodes X ζ).2.1 ℓ
        change D.T1.garden.mark ℓ = _ at hm0
        rw [hm0, if_pos hl]; simp
      rw [(D.T1.garden.pair_eq_iff ℓ).2 hm]
    · have := hκ.2 (D.ιL ℓ)
      rw [D.pair_ιL ℓ hl, D.ιL_toNode, D.ιL_toNode] at this
      simpa only [Function.comp_apply] using this

theorem root_ι : D.ι (GNode.root D.T1.garden.tree 0) = GNode.root LG.garden.tree j0 := rfl

/-- In every decoration of the couple the cap root carries the value of the root of `j0`. -/
theorem cap_eq_root {V : Type*} [AddCommGroup V] {κ : GNode LG.garden.tree → V} (hκ : IsDecoration LG.garden κ) :
    κ (GNode.root LG.garden.tree c) = κ (GNode.root LG.garden.tree j0) := by
  have h1 := D.lone1_eq_root (D.isDec_fwd hκ)
  simp only [Function.comp_apply, D.ι_lone1, D.root_ι] at h1
  rw [← h1, hκ.2 D.ℓ0]
  congr 1
  exact Subtype.ext D.pair_ℓ0.symm

/-- Restriction of a couple decoration to the paired tree. -/
def decFwd (κ : GenDecoration LG.garden d (fun _ => 0) 0) : GenDecoration D.T1.garden d (fun _ => 0) 0 :=
  ⟨κ.1 ∘ D.ι, D.isDec_fwd κ.2.1, fun j => by
    rw [D.fin1 j]
    show κ.1 (D.ι (GNode.root D.T1.garden.tree 0)) = 0
    rw [D.root_ι]
    exact κ.2.2.1 j0, fun ℓ h => absurd h (D.not_flower1 ℓ)⟩

/-- Extension of a paired-tree decoration to the couple. -/
def decBwd (κ : GenDecoration D.T1.garden d (fun _ => 0) 0) : GenDecoration LG.garden d (fun _ => 0) 0 :=
  ⟨κ.1 ∘ D.ρ, by
    refine ⟨⟨fun b => ?_, fun ℓ => ?_⟩, fun j => ?_, fun ℓ h => absurd h (D.not_flower ℓ)⟩
    · have := κ.2.1.1 (D.βc.symm b)
      simp only [Function.comp_apply, D.ρ_βc_toNode, D.ρ_βc_child]
      exact this
    · simp only [Function.comp_apply]
      rcases D.leaf_cases ℓ with h | h | ⟨ℓ1, hne, rfl⟩
      · subst h
        have h1 : (LG.garden.pair D.ℓ0).toNode.1.1 ≠ j0 := by
          rw [show (LG.garden.pair D.ℓ0).toNode.1 = (LG.garden.pair D.ℓ0).1 from rfl, D.pair_ℓ0]
          exact fun h => D.ne h.symm
        rw [D.ρ_c _ h1, D.ρ_ℓ0]
      · have h1 : ℓ.toNode.1.1 ≠ j0 := by
          rw [show ℓ.toNode.1 = ℓ.1 from rfl, h]
          exact fun h => D.ne h.symm
        rw [D.ρ_c _ h1, D.pair_c ℓ h, D.ρ_ℓ0]
      · rw [D.pair_ιL ℓ1 hne, D.ιL_toNode, D.ιL_toNode, D.ρ_ι, D.ρ_ι]
        exact κ.2.1.2 ℓ1
    · by_cases hj : j = j0
      · subst hj
        have : D.ρ (GNode.root LG.garden.tree j) = GNode.root D.T1.garden.tree 0 :=
          Subtype.ext (D.ρ_val _ rfl)
        simp only [Function.comp_apply, this]
        exact κ.2.2.1 0
      · simp only [Function.comp_apply]
        rw [D.ρ_c (GNode.root LG.garden.tree j) hj, D.lone1_eq_root κ.2.1]
        exact κ.2.2.1 0⟩

theorem decBwd_fwd (κ : GenDecoration LG.garden d (fun _ => 0) 0) : D.decBwd (D.decFwd κ) = κ := by
  apply Subtype.ext
  funext a
  show κ.1 (D.ι (D.ρ a)) = κ.1 a
  by_cases h : a.1.1 = j0
  · rw [D.ι_ρ a h]
  · rw [D.ρ_c a h, D.ι_lone1]
    have e2 : a = (LG.garden.pair D.ℓ0).toNode := Subtype.ext ((D.node_c a h).trans D.pair_ℓ0.symm)
    rw [e2]
    exact κ.2.1.2 D.ℓ0

theorem decFwd_bwd (κ : GenDecoration D.T1.garden d (fun _ => 0) 0) : D.decFwd (D.decBwd κ) = κ := by
  apply Subtype.ext
  funext a
  show κ.1 (D.ρ (D.ι a)) = κ.1 a
  rw [D.ρ_ι]

/-- **Decorations of the couple are decorations of the paired tree.** -/
def decEquiv (d : ℕ) : GenDecoration LG.garden d (fun _ => 0) 0 ≃ GenDecoration D.T1.garden d (fun _ => 0) 0 :=
  ⟨D.decFwd, D.decBwd, D.decBwd_fwd, D.decFwd_bwd⟩

theorem coset_ρ (L : ℝ) (k : Mom d) (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
    cosetDecoration LG.garden L k κ.1 = fun a => cosetDecoration D.T1.garden L k (D.decFwd κ).1 (D.ρ a) := by
  funext a
  unfold cosetDecoration
  congr 2
  exact (congrArg (fun κ' : GenDecoration LG.garden d (fun _ => 0) 0 => κ'.1 a) (D.decBwd_fwd κ)).symm

theorem order_eq : LG.garden.order = D.T1.garden.order := by
  unfold Garden.order
  rw [fin2_sum _ j0 c D.ne, D.cap, Fin.sum_univ_one, D.tree_eq]
  simp [TTree.order]

theorem zeta_eq : LG.garden.zeta = D.T1.garden.zeta := by
  unfold Garden.zeta
  rw [← D.βc.prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [D.βc_toNode, D.sign_ι]

theorem epsDec_eq (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
    epsDec LG.garden κ.1 = epsDec D.T1.garden (D.decFwd κ).1 :=
  (Equiv.prod_comp D.βc _).symm

theorem phaseProd_eq (L γ δ : ℝ) (K : GNode LG.garden.tree → Mom d) (τ : GBranch LG.garden.tree → ℝ) :
    phaseProd L γ δ LG.garden K τ =
      phaseProd L γ δ D.T1.garden (fun a => K (D.ι a)) (fun b => τ (D.βc b)) := by
  unfold phaseProd
  rw [← D.βc.prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [D.βc_toNode, D.sign_ι]
  rfl

theorem isChild_iff (b' b : GBranch D.T1.garden.tree) : (D.βc b').IsChildOf (D.βc b) ↔ b'.IsChildOf b :=
  ⟨fun h => ⟨Subsingleton.elim _ _, h.2⟩, fun h => ⟨rfl, h.2⟩⟩

theorem not_loneParent (b : GBranch LG.garden.tree) : ¬ LG.garden.IsLoneParent b := by
  rintro ⟨ℓ, hl, -⟩
  unfold Garden.IsLone at hl
  rw [D.plain ℓ] at hl
  exact absurd hl (by simp)

theorem protTime_capG (L γ δ : ℝ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG up s fix K =
      protTime L γ δ D.T1 (fun b => up (D.βc b)) 0 (fun b => fix (D.βc b)) (fun a => K (D.ι a)) := by
  refine protTime_transport L γ δ D.βc (fun _ => rfl) (fun τ => ?_) (fun τ => D.phaseProd_eq L γ δ K τ)
  constructor
  · rintro ⟨hk, -⟩
    refine ⟨fun b => ⟨fun hf => ?_, fun b' hc hor => ?_⟩, fun b _ hf => ?_⟩
    · have := (hk (D.βc b)).1 hf
      simpa only [D.βc_toNode, D.layer_ι] using this
    · exact (hk (D.βc b)).2 (D.βc b') ((D.isChild_iff b' b).2 hc) hor
    · exact ((hk (D.βc b)).1 hf).2.2.1
  · rintro ⟨hk, -⟩
    refine ⟨fun b => ⟨fun hf => ?_, fun b' hc hor => ?_⟩, fun b hl _ => absurd hl (D.not_loneParent b)⟩
    · obtain ⟨b1, rfl⟩ := D.βc.surjective b
      have := (hk b1).1 hf
      simpa only [D.βc_toNode, D.layer_ι] using this
    · obtain ⟨b1, rfl⟩ := D.βc.surjective b
      obtain ⟨b1', rfl⟩ := D.βc.surjective b'
      exact (hk b1).2 b1' ((D.isChild_iff b1' b1).1 hc) hor

/-! ### The kernel -/

/-- The multiplier of the paired tree: the component weight and removed phases read through `ρ`. -/
def capWt (L γ δ : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) : (GNode D.T1.garden.tree → Mom d) → ℂ :=
  fun K => (wt (fun a => K (D.ρ a)) : ℂ) * offFactor L γ δ LG.garden off fix (fun a => K (D.ρ a))

theorem integral_kgen (L γ δ : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (hoff : ∀ b ∈ off, (fix b).isSome) (up : GBranch LG.garden.tree → ℝ) (K : GNode LG.garden.tree → Mom d) :
    (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
      (kDomainFix LG up fix).indicator (phaseProdOff L γ δ LG.garden off K) (LG.garden.extendFix fix τ)) =
    protTime L γ δ D.T1 (fun b => up (D.βc b)) 0 (fun b => fix (D.βc b)) (fun a => K (D.ι a)) *
      offFactor L γ δ LG.garden off fix K := by
  rw [← D.protTime_capG L γ δ up 0 fix K]
  unfold protTime protDom
  rw [loneConstraint_vacuous LG up 0 fix D.not_loneParent, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hm : LG.garden.extendFix fix τ ∈ kDomainFix LG up fix
  · simp only [indicator_of_mem hm]
    exact phaseProdOff_extendFix L γ δ LG.garden off fix hoff K τ
  · simp only [indicator_of_notMem hm, zero_mul]

/-- **The general cap reduction** from a component value: with `F ≡ 1`, removed phases only at pinned branches. -/
theorem kernelKgen_capG (L γ δ : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (off : Finset (GBranch LG.garden.tree)) (hoff : ∀ b ∈ off, (fix b).isSome)
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (roots : Fin 2 → (Fin d → ℤ)) :
    kernelKgen L γ δ (fun _ _ => 1) LG fix off wt up 0 roots 0 =
      if roots c = roots j0 then
        kernelProt L γ δ D.T1 (fun _ _ => 1) (D.capWt L γ δ fix off wt) (fun b => up (D.βc b)) 0
          (fun b => fix (D.βc b)) (latticePoint L (roots j0)) (fun _ => 0) 0
      else 0 := by
  rw [kernelKgen_shift L γ δ _ LG fix off wt up 0 roots 0 (roots j0), zero_add]
  split_ifs with hr
  · have hn : (fun j => roots j - roots j0) = fun _ => (0 : Fin d → ℤ) := by
      funext j
      by_cases hj : j = j0
      · rw [hj, sub_self]
      · rw [D.idx j hj, hr, sub_self]
    rw [hn, kernelKgen_nfl L γ δ _ LG D.not_flower fix off wt up _ _ _ 0, kernelProt_eq_tsum]
    unfold kernelKgen
    rw [D.order_eq, D.zeta_eq]
    congr 1
    rw [← (D.decEquiv d).tsum_eq]
    refine tsum_congr fun κ => ?_
    unfold protSummand
    have he : D.decEquiv d κ = D.decFwd κ := rfl
    rw [he, D.integral_kgen L γ δ fix off hoff up, D.epsDec_eq κ]
    simp only [Complex.ofReal_one, Finset.prod_const_one, mul_one]
    unfold capWt
    rw [← D.coset_ρ L (latticePoint L (roots j0)) κ]
    have hι : (fun a => cosetDecoration LG.garden L (latticePoint L (roots j0)) κ.1 (D.ι a)) =
        cosetDecoration D.T1.garden L (latticePoint L (roots j0)) (D.decFwd κ).1 := rfl
    rw [hι]
    ring
  · have hE : IsEmpty (GenDecoration LG.garden d (fun j => roots j - roots j0) (0 - roots j0)) := by
      refine ⟨fun κ => hr ?_⟩
      have h := D.cap_eq_root κ.2.1
      rw [κ.2.2.1 c, κ.2.2.1 j0] at h
      beta_reduce at h
      rw [sub_self] at h
      exact sub_eq_zero.1 h
    unfold kernelKgen
    rw [tsum_empty, mul_zero]

end CapG

end WaveTurbulence.Flower.ProtWhole
