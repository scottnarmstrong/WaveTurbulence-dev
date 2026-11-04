/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Param

/-!
# Node values are fixed integer combinations of the link parameters (packet C2)

TARGET (incohproof1), L985–L988: "each `k_ℓ - k` is a fixed integer linear combination of
`(x_𝔫, y_𝔫)`". The construction `cplVal` is additive in `(θ, r)` (`cplVal_add`) and natural under
additive maps (`cplVal_map`); hence on a couple carrier every node value of the decoration with root
value `r` and parameters `θ` is `r + ∑_j (A_j x_j + B_j y_j)` with integer `A_j, B_j` independent of
the group and of `(r, θ)` (`node_linear`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W] {w : ℕ}

theorem childVals_add (u₁ u₂ : V) (t₁ t₂ : V × V) (i : Fin 3) :
    childVals (u₁ + u₂) (t₁ + t₂) i = childVals u₁ t₁ i + childVals u₂ t₂ i := by
  fin_cases i <;> simp [childVals] <;> abel

theorem childVals_map (φ : V →+ W) (u : V) (t : V × V) (i : Fin 3) :
    φ (childVals u t i) = childVals (φ u) (φ t.1, φ t.2) i := by
  fin_cases i <;> simp [childVals]

mutual
/-- **Additivity** of the constructed decoration in `(θ, r)`. -/
theorem cplVal_add (θ₁ θ₂ : Fin w × Path → V × V) (Q : RegCpl) (a b : Fin w × Path) (r₁ r₂ : V)
    (z : Fin w × Path) :
    cplVal (θ₁ + θ₂) Q a b (r₁ + r₂) z = cplVal θ₁ Q a b r₁ z + cplVal θ₂ Q a b r₂ z := by
  cases Q with
  | triv => simp only [cplVal]; split_ifs <;> simp
  | type1 c Q₁ Q₂ Q₃ =>
    simp only [cplVal, Pi.add_apply]
    split_ifs
    · rfl
    · rw [childVals_add, cplVal_add]
    · rw [childVals_add, cplVal_add]
    · rw [childVals_add, cplVal_add]
  | type2 Xp Xm Qlp =>
    have hQ : cplVal (θ₁ + θ₂) Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) (r₁ + r₂) =
        cplVal θ₁ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r₁ +
          cplVal θ₂ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r₂ :=
      funext fun z => cplVal_add θ₁ θ₂ Qlp _ _ r₁ r₂ z
    simp only [cplVal, hQ]
    split_ifs <;> exact chainVal_add _ _ _ _ _ _ _ _ _ _
termination_by structural Q

/-- Additivity of the chain construction. -/
theorem chainVal_add (θ₁ θ₂ : Fin w × Path → V × V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (u₁ u₂ : V) (c₁ c₂ : (Fin w × Path) → V) (z : Fin w × Path) :
    chainVal (θ₁ + θ₂) X ζ a (u₁ + u₂) (c₁ + c₂) z =
      chainVal θ₁ X ζ a u₁ c₁ z + chainVal θ₂ X ζ a u₂ c₂ z := by
  cases X with
  | nil => rfl
  | pair m Qr Qg inner rest =>
    simp only [chainVal, Pi.add_apply]
    have hc : (fun _ : Fin w × Path => childVals (u₁ + u₂) (θ₁ a + θ₂ a) m.c) =
        (fun _ => childVals u₁ (θ₁ a) m.c) + (fun _ => childVals u₂ (θ₂ a) m.c) := by
      funext _; simp only [Pi.add_apply, childVals_add]
    split_ifs
    · rfl
    · rw [childVals_add, cplVal_add]
    · rw [childVals_add, cplVal_add]
    · rw [childVals_add, cplVal_add]
    · rw [childVals_add, cplVal_add]
    · exact chainVal_add _ _ _ _ _ _ _ _ _ _
    · rw [hc, childVals_add]; exact chainVal_add _ _ _ _ _ _ _ _ _ _
termination_by structural X
end

mutual
/-- **Naturality** of the constructed decoration under additive maps. -/
theorem cplVal_map (φ : V →+ W) (θ : Fin w × Path → V × V) (Q : RegCpl) (a b : Fin w × Path)
    (r : V) (z : Fin w × Path) :
    φ (cplVal θ Q a b r z) = cplVal (fun x => (φ (θ x).1, φ (θ x).2)) Q a b (φ r) z := by
  cases Q with
  | triv => simp only [cplVal]; split_ifs <;> simp
  | type1 c Q₁ Q₂ Q₃ =>
    simp only [cplVal]
    split_ifs
    · rfl
    · rw [cplVal_map, childVals_map]
    · rw [cplVal_map, childVals_map]
    · rw [cplVal_map, childVals_map]
  | type2 Xp Xm Qlp =>
    have hQ : (fun z => φ (cplVal θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r z)) =
        cplVal (fun x => (φ (θ x).1, φ (θ x).2)) Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)
          (φ r) := funext fun z => cplVal_map φ θ Qlp _ _ r z
    simp only [cplVal]
    split_ifs
    · rw [chainVal_map, hQ]
    · rw [chainVal_map, hQ]
termination_by structural Q

/-- Naturality of the chain construction. -/
theorem chainVal_map (φ : V →+ W) (θ : Fin w × Path → V × V) (X : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (u : V) (c : (Fin w × Path) → V) (z : Fin w × Path) :
    φ (chainVal θ X ζ a u c z) =
      chainVal (fun x => (φ (θ x).1, φ (θ x).2)) X ζ a (φ u) (fun x => φ (c x)) z := by
  cases X with
  | nil => rfl
  | pair m Qr Qg inner rest =>
    simp only [chainVal]
    split_ifs
    · rfl
    · rw [cplVal_map, childVals_map]
    · rw [cplVal_map, childVals_map]
    · rw [cplVal_map, childVals_map]
    · rw [cplVal_map, childVals_map]
    · exact chainVal_map φ θ rest _ _ u c z
    · rw [chainVal_map φ θ inner _ _ _ _ z, childVals_map]
termination_by structural X
end

theorem cplVal_zero (Q : RegCpl) (a b : Fin w × Path) (z : Fin w × Path) :
    cplVal (0 : Fin w × Path → V × V) Q a b 0 z = 0 := by
  have h := cplVal_add (V := V) 0 0 Q a b 0 0 z
  rw [add_zero, add_zero] at h
  calc cplVal (0 : Fin w × Path → V × V) Q a b 0 z
      = cplVal (0 : Fin w × Path → V × V) Q a b 0 z + cplVal 0 Q a b 0 z -
          cplVal (0 : Fin w × Path → V × V) Q a b 0 z := by abel
    _ = 0 := by rw [← h, sub_self]

/-- The constructed decoration as an additive map of the parameters (root value `0`). -/
def cplValHom (Q : RegCpl) (a b : Fin w × Path) (z : Fin w × Path) : (Fin w × Path → V × V) →+ V where
  toFun θ := cplVal θ Q a b 0 z
  map_zero' := cplVal_zero Q a b z
  map_add' θ₁ θ₂ := by
    have := cplVal_add θ₁ θ₂ Q a b 0 0 z
    rwa [add_zero] at this

/-- With zero parameters the constructed decoration is constant on the code. -/
theorem cplVal_const (Q : RegCpl) (a b : Fin w × Path) (r : V) (h : Indep a b) :
    ∀ z ∈ pairEndpoints (Q.linksAt a b) ∪ pairEndpoints (Q.pairsAt a b),
      cplVal (0 : Fin w × Path → V × V) Q a b r z = r := by
  intro z hz
  have hd : CplDec (fun _ => r) Q a b :=
    cplDec_of_lists _ Q a b (fun x _ => by unfold NodeRel; abel) (fun _ _ => rfl)
  exact (cplDec_determined 0 Q a b r h (fun _ => r) hd rfl
    (fun l _ => by simp [xv, yv]) z hz).symm

variable {G : Garden 2} {Q : RegCpl}

/-- `paramFun` as an additive map. -/
def paramFunHom (Q : RegCpl) : (Fin Q.links.length → V × V) →+ (Fin 2 × Path → V × V) where
  toFun := paramFun Q
  map_zero' := by funext z; unfold paramFun; split_ifs <;> rfl
  map_add' θ₁ θ₂ := by
    funext z; unfold paramFun
    by_cases h : (Q.links.map Prod.fst).idxOf z < Q.links.length
    · simp only [dif_pos h, Pi.add_apply]
    · simp only [dif_neg h, Pi.add_apply, add_zero]

theorem paramFun_map (φ : V →+ W) (θ : Fin Q.links.length → V × V) (z : Fin 2 × Path) :
    paramFun Q (fun j => (φ (θ j).1, φ (θ j).2)) z =
      (φ (paramFun Q θ z).1, φ (paramFun Q θ z).2) := by
  unfold paramFun; split_ifs
  · rfl
  · simp only [map_zero, Prod.fst_zero, Prod.snd_zero]; rfl

/-- **Node values are fixed integer linear combinations of the link parameters** (TARGET
(incohproof1)): for every node `𝔫` of a couple carrier there are integers `A_j, B_j` such that, in
every additive group, the decoration with root value `r` and parameters `(x_j, y_j)_j` has
`κ_𝔫 = r + ∑_j (A_j x_j + B_j y_j)`. -/
theorem node_linear (hQ : Q.Decodes G) (a : GNode G.tree) :
    ∃ A B : Fin Q.links.length → ℤ, ∀ (V : Type) [AddCommGroup V] (r : V)
      (θ : Fin Q.links.length → V × V),
      (decOfParams hQ r θ).1 a = r + ∑ j, (A j • (θ j).1 + B j • (θ j).2) := by
  refine ⟨fun j => cplVal (paramFun Q (Pi.single j ((1 : ℤ), (0 : ℤ)))) Q (0, []) (1, []) 0 a.1,
    fun j => cplVal (paramFun Q (Pi.single j ((0 : ℤ), (1 : ℤ)))) Q (0, []) (1, []) 0 a.1,
    fun V _ r θ => ?_⟩
  have ha : a.1 ∈ pairEndpoints (Q.linksAt (0, []) (1, [])) ∪ pairEndpoints (Q.pairsAt (0, []) (1, [])) :=
    (mem_nodes_iff_endpoints hQ a.1).1 a.2
  show cplVal (paramFun Q θ) Q (0, []) (1, []) r a.1 = _
  have e1 := cplVal_add (paramFun Q θ) 0 Q (0, []) (1, []) 0 r a.1
  rw [add_zero, zero_add] at e1
  rw [e1, cplVal_const Q _ _ r indep_roots _ ha, add_comm]
  congr 1
  -- decompose `θ` into single entries
  have hθ : θ = ∑ j : Fin Q.links.length, (Pi.single j ((θ j).1, 0) + Pi.single j (0, (θ j).2)) := by
    rw [← Finset.univ_sum_single θ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_add]; simp
  have key : cplVal (paramFun Q θ) Q (0, []) (1, []) 0 a.1 =
      cplValHom Q (0, []) (1, []) a.1 (paramFunHom Q θ) := rfl
  rw [key]
  conv_lhs => rw [hθ]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, map_add]
  -- naturality: `x • (coefficient over ℤ)`
  have c1 := cplVal_map (zmultiplesHom V (θ j).1) (paramFun Q (Pi.single j ((1 : ℤ), (0 : ℤ))))
    Q (0, []) (1, []) 0 a.1
  have c2 := cplVal_map (zmultiplesHom V (θ j).2) (paramFun Q (Pi.single j ((0 : ℤ), (1 : ℤ))))
    Q (0, []) (1, []) 0 a.1
  have p1 : (fun x => ((zmultiplesHom V (θ j).1) (paramFun Q (Pi.single j ((1 : ℤ), (0 : ℤ))) x).1,
      (zmultiplesHom V (θ j).1) (paramFun Q (Pi.single j ((1 : ℤ), (0 : ℤ))) x).2)) =
      paramFunHom Q (Pi.single j ((θ j).1, 0)) := by
    funext x
    rw [← paramFun_map]
    show paramFun Q _ x = paramFun Q _ x
    congr 1
    funext j'
    by_cases hj : j' = j
    · subst hj; simp [zmultiplesHom_apply]
    · simp [hj, zmultiplesHom_apply]
  have p2 : (fun x => ((zmultiplesHom V (θ j).2) (paramFun Q (Pi.single j ((0 : ℤ), (1 : ℤ))) x).1,
      (zmultiplesHom V (θ j).2) (paramFun Q (Pi.single j ((0 : ℤ), (1 : ℤ))) x).2)) =
      paramFunHom Q (Pi.single j (0, (θ j).2)) := by
    funext x
    rw [← paramFun_map]
    show paramFun Q _ x = paramFun Q _ x
    congr 1
    funext j'
    by_cases hj : j' = j
    · subst hj; simp [zmultiplesHom_apply]
    · simp [hj, zmultiplesHom_apply]
  rw [p1, map_zero] at c1
  rw [p2, map_zero] at c2
  show cplVal (paramFunHom Q (Pi.single j ((θ j).1, 0))) Q (0, []) (1, []) 0 a.1 +
    cplVal (paramFunHom Q (Pi.single j (0, (θ j).2))) Q (0, []) (1, []) 0 a.1 = _
  rw [← c1, ← c2]
  simp [zmultiplesHom_apply]

end WaveTurbulence.Links
