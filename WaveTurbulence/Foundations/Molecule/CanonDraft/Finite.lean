/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CanonDraft.Trunc

/-!
# Finiteness and enumeration of canonical layered gardens (packet D3 CANON, pre-freeze)

For the counting packets (`T.layerreg2`, M8) and the `finsum`s of the gates:

* `finite_layeredGardens`: layered gardens of width `w`, order `≤ n` and depth `≤ p` form a finite set
  (moved here from the B1 probes, so that it can land without them);
* `layer_le_of_isCanonGC` etc. and `finite_canonG`, `finite_canonC`, `finite_canonH`,
  `finite_canonGC`: the classes `𝒢_q`, `𝒞_q`, `ℋ_q` of bounded order are finite, with the explicit
  enumerations `canonGFinset` etc. (`Finset`s with membership lemmas);
* `truncSum_eq_sum`, `truncSumC_eq_sum`: the shared truncated sums as `Finset` sums over these
  enumerations;
* `ncard_layerings_le`: a fixed garden has at most `(p+1)^{#nodes}` layerings of depth `≤ p`.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.Canon

open TTree

/-! ### Layered gardens of bounded order and depth -/

theorem finite_order_le : ∀ n : ℕ, {T : TTree | T.order ≤ n}.Finite
  | 0 => by
    refine (Set.finite_singleton TTree.leaf).subset ?_
    intro T hT
    cases T with
    | leaf => rfl
    | node l m r => simp [order] at hT
  | n + 1 => by
    have ih := finite_order_le n
    refine ((Set.finite_singleton TTree.leaf).union
      (((ih.prod (ih.prod ih)).image fun x => TTree.node x.1 x.2.1 x.2.2))).subset ?_
    intro T hT
    cases T with
    | leaf => exact Or.inl rfl
    | node l m r =>
      simp only [Set.mem_ofPred_eq, order] at hT
      refine Or.inr ⟨(l, m, r), ⟨?_, ?_, ?_⟩, rfl⟩ <;> simp only [Set.mem_ofPred_eq] <;> omega

/-- The garden data with layers bounded by `p`, before imposing the axioms. -/
def RawData {w : ℕ} (p : ℕ) (t : Fin w → TTree) : Type :=
  (Fin w → ℤˣ) × (GLeaf t → GLeaf t) × (GLeaf t → Option MarkTag) × (GNode t → Fin (p + 1))

instance {w : ℕ} (p : ℕ) (t : Fin w → TTree) : Finite (RawData p t) := by
  unfold RawData
  infer_instance

/-- The axioms of a layered garden on raw data. -/
def RawOK {w : ℕ} (p : ℕ) (t : Fin w → TTree) (x : RawData p t) : Prop :=
  (∀ ℓ, x.2.1 (x.2.1 ℓ) = ℓ) ∧ (∀ ℓ, x.2.1 ℓ = ℓ ↔ x.2.2.1 ℓ ≠ none) ∧
    (∀ ℓ, x.2.1 ℓ ≠ ℓ → nodeSign x.1 (x.2.1 ℓ).1 = -nodeSign x.1 ℓ.1) ∧
    (∀ b : GBranch t, ∀ i : Fin 3, ((x.2.2.2 (b.child i) : Fin (p + 1)) : ℕ) ≤ x.2.2.2 b.toNode) ∧
    ∀ ℓ : GLeaf t, ((x.2.2.2 ℓ.toNode : Fin (p + 1)) : ℕ) = x.2.2.2 (x.2.1 ℓ).toNode

/-- Assemble a layered garden from raw data satisfying the axioms. -/
def assemble {w : ℕ} (p : ℕ) (t : Fin w → TTree) (x : {x : RawData p t // RawOK p t x}) :
    LayeredGarden w where
  garden := ⟨x.1.1, t, x.1.2.1, x.1.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1⟩
  layer a := x.1.2.2.2 a
  isLayering := ⟨x.2.2.2.2.1, x.2.2.2.2.2⟩

/-- **Finiteness**: for every width `w`, order bound `n` and depth `p`, there are finitely many
layered gardens of order `≤ n` with all layers `≤ p`. -/
theorem finite_layeredGardens (w n p : ℕ) :
    {LG : LayeredGarden w | LG.garden.order ≤ n ∧ ∀ a, LG.layer a ≤ p}.Finite := by
  let B : Set (Fin w → TTree) := Set.pi Set.univ fun _ => {T : TTree | T.order ≤ n}
  have hB : B.Finite := Set.Finite.pi fun _ => finite_order_le n
  have : Finite B := hB.to_subtype
  let g : (Σ t : B, {x : RawData p t.1 // RawOK p t.1 x}) → LayeredGarden w :=
    fun y => assemble p y.1.1 y.2
  refine (Set.finite_range g).subset ?_
  rintro ⟨⟨sig, t, pair, mk, h1, h2, h3⟩, layer, hlay⟩ ⟨hord, hp⟩
  have ht : t ∈ B := by
    intro j _
    have : (t j).order ≤ ∑ j, (t j).order :=
      Finset.single_le_sum (f := fun j => (t j).order) (fun _ _ => Nat.zero_le _) (mem_univ j)
    exact this.trans hord
  refine ⟨⟨⟨t, ht⟩, ⟨(sig, pair, mk, fun a => ⟨layer a, Nat.lt_succ_of_le (hp a)⟩),
    ⟨h1, h2, h3, hlay.1, hlay.2⟩⟩⟩, rfl⟩

/-! ### The canonical classes of bounded order -/

theorem layer_le_of_isCanonG {w p : ℕ} {LG : LayeredGarden w} (h : IsCanonG (p + 1) LG)
    (a : GNode LG.garden.tree) : LG.layer a ≤ p := h.2.2.2.1 a

theorem layer_le_of_isCanonC {p : ℕ} {LG : LayeredGarden 2} (h : IsCanonC (p + 1) LG)
    (a : GNode LG.garden.tree) : LG.layer a ≤ p := h.2.1 a

theorem layer_le_of_isCanonH {w p : ℕ} {LG : LayeredGarden w} (h : IsCanonH (p + 1) LG)
    (a : GNode LG.garden.tree) : LG.layer a ≤ p := h.2.2.1 a

theorem layer_le_of_isCanonGC {w p : ℕ} {LG : LayeredGarden w} (h : IsCanonGC (p + 1) LG)
    (a : GNode LG.garden.tree) : LG.layer a ≤ p := h.2.2.1 a

theorem finite_canonG (q n w : ℕ) :
    {LG : LayeredGarden w | IsCanonG q LG ∧ LG.garden.order ≤ n}.Finite := by
  rcases q with _ | p
  · simp [IsCanonG]
  · exact (finite_layeredGardens w n p).subset fun LG h => ⟨h.2, layer_le_of_isCanonG h.1⟩

theorem finite_canonC (q n : ℕ) :
    {LG : LayeredGarden 2 | IsCanonC q LG ∧ LG.garden.order ≤ n}.Finite := by
  rcases q with _ | p
  · simp [IsCanonC]
  · exact (finite_layeredGardens 2 n p).subset fun LG h => ⟨h.2, layer_le_of_isCanonC h.1⟩

theorem finite_canonH (q n w : ℕ) :
    {LG : LayeredGarden w | IsCanonH q LG ∧ LG.garden.order ≤ n}.Finite := by
  rcases q with _ | p
  · simp [IsCanonH]
  · exact (finite_layeredGardens w n p).subset fun LG h => ⟨h.2, layer_le_of_isCanonH h.1⟩

theorem finite_canonGC (q n w : ℕ) :
    {LG : LayeredGarden w | IsCanonGC q LG ∧ LG.garden.order ≤ n}.Finite := by
  rcases q with _ | p
  · simp [IsCanonGC]
  · exact (finite_layeredGardens w n p).subset fun LG h => ⟨h.2, layer_le_of_isCanonGC h.1⟩

/-! ### The shared sums as finite sums -/

theorem finite_truncSum_support (P : WTParams) (q N w : ℕ) (ζ : Fin w → ℤˣ) :
    {LG : LayeredGarden w | IsCanonGC q LG ∧ LG.IsTrunc (q - 1) (P.N q) (P.N (q - 1)) ∧
      LG.garden.sig = ζ ∧ LG.garden.order = N}.Finite :=
  (finite_canonGC q N w).subset fun _ h => ⟨h.1, h.2.2.2.le⟩

theorem finite_truncSumC_support (P : WTParams) (q N : ℕ) :
    {LG : LayeredGarden 2 | IsCanonC q LG ∧ LG.IsTrunc (q - 1) (P.N q) (P.N (q - 1)) ∧
      LG.garden.order = N}.Finite :=
  (finite_canonC q N).subset fun _ h => ⟨h.1, h.2.2.le⟩

/-- `truncSum` as a `Finset` sum over the enumeration of its support. -/
theorem truncSum_eq_sum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (q N : ℕ) {w : ℕ} (t : ℝ)
    (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
    truncSum P F q N t ζ n =
      ∑ LG ∈ (finite_truncSum_support P q N w ζ).toFinset, KG P.L P.γ P.δ F LG t n := by
  unfold truncSum
  rw [← finsum_mem_eq_finite_toFinset_sum]
  rfl

/-- `truncSumC` as a `Finset` sum over the enumeration of its support. -/
theorem truncSumC_eq_sum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (q N : ℕ) (t : ℝ) (k : Mom P.d) :
    truncSumC P F q N t k =
      ∑ LG ∈ (finite_truncSumC_support P q N).toFinset, KQ P.L P.γ P.δ F LG t k := by
  unfold truncSumC
  rw [← finsum_mem_eq_finite_toFinset_sum]
  rfl

/-! ### Counting layerings -/

end WaveTurbulence.Canon
