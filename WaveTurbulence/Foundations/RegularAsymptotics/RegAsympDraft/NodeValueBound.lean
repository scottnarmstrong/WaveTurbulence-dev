/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.NodeCoordinateRows

/-! # Uniform source node-coordinate bounds without determinants -/

public section
namespace WaveTurbulence.RegAsymp
open Links
variable {V : Type} [NormedAddCommGroup V] {w : ℕ}

/-- Each literal child update uses at most one x and one y. -/
theorem norm_childVals_le (u : V) (t : V × V) (i : Fin 3) :
    ‖childVals u t i‖ ≤ ‖u‖+‖t.1‖+‖t.2‖ := by
  fin_cases i
  · change ‖u+t.1‖ ≤ _
    exact (norm_add_le _ _).trans (le_add_of_nonneg_right (norm_nonneg _))
  · change ‖u+t.1-t.2‖ ≤ _
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  · change ‖u-t.2‖ ≤ _
    have hh := norm_sub_le u t.2
    have h0 := norm_nonneg t.1
    linarith

mutual
/-- The actual recursive decoration grows at most linearly in source order. -/
theorem norm_cplVal_le (θ : Fin w × TTree.Path → V × V) (D : ℝ) (hD : 0 ≤ D)
    (hθ : ∀ z, ‖(θ z).1‖ ≤ D ∧ ‖(θ z).2‖ ≤ D)
    (Q : RegCpl) (a b : Fin w × TTree.Path) (r : V) (z : Fin w × TTree.Path) :
    ‖cplVal θ Q a b r z‖ ≤ ‖r‖+(Q.size : ℝ)*D := by
  cases Q with
  | triv =>
    simp only [cplVal,RegCpl.size,Nat.cast_zero,zero_mul,add_zero]
    split <;> simp
  | type1 c q₁ q₂ q₃ =>
    have hc (i : Fin 3) : ‖childVals r (θ a) i‖ ≤ ‖r‖+2*D := by
      have hh := norm_childVals_le r (θ a) i
      obtain ⟨h1,h2⟩ := hθ a
      linarith
    have hh₁ := norm_cplVal_le θ D hD hθ q₁ (addrExt a [0]) (addrExt b [c.partner 0]) (childVals r (θ a) 0) z
    have hh₂ := norm_cplVal_le θ D hD hθ q₂ (addrExt b [1]) (addrExt a [1]) (childVals r (θ a) 1) z
    have hh₃ := norm_cplVal_le θ D hD hθ q₃ (addrExt a [2]) (addrExt b [c.partner 2]) (childVals r (θ a) 2) z
    simp only [cplVal,RegCpl.size,Nat.cast_add,Nat.cast_ofNat]
    split_ifs <;> nlinarith [hc 0,hc 1,hc 2,(show (0:ℝ) ≤ (q₁.size:ℝ) from Nat.cast_nonneg _),(show (0:ℝ) ≤ (q₂.size:ℝ) from Nat.cast_nonneg _),(show (0:ℝ) ≤ (q₃.size:ℝ) from Nat.cast_nonneg _)]
  | type2 xp xm q =>
    have hc (p) : ‖cplVal θ q (addrExt a xp.lonePath) (addrExt b xm.lonePath) r p‖ ≤ ‖r‖+(q.size:ℝ)*D :=
      norm_cplVal_le θ D hD hθ q _ _ r p
    have hp := norm_chainVal_le θ D hD hθ xp 1 a r ((q.size:ℝ)*D) (by positivity) _ hc z
    have hm := norm_chainVal_le θ D hD hθ xm (-1) b r ((q.size:ℝ)*D) (by positivity) _ hc z
    simp only [cplVal,RegCpl.size,Nat.cast_add]
    split <;> nlinarith [(show (0:ℝ) ≤ (xp.size:ℝ) from Nat.cast_nonneg _),(show (0:ℝ) ≤ (xm.size:ℝ) from Nat.cast_nonneg _)]
termination_by structural Q

/-- A chain adds at most its order times the uniform coordinate bound. -/
theorem norm_chainVal_le (θ : Fin w × TTree.Path → V × V) (D : ℝ) (hD : 0 ≤ D)
    (hθ : ∀ z, ‖(θ z).1‖ ≤ D ∧ ‖(θ z).2‖ ≤ D)
    (X : RegChain) (ζ : ℤˣ) (a : Fin w × TTree.Path) (u : V)
    (H : ℝ) (hH : 0 ≤ H) (cont : (Fin w × TTree.Path) → V)
    (hcont : ∀ p, ‖cont p‖ ≤ ‖u‖+H) (z : Fin w × TTree.Path) :
    ‖chainVal θ X ζ a u cont z‖ ≤ ‖u‖+(X.size:ℝ)*D+H := by
  cases X with
  | nil => simpa only [chainVal,RegChain.size,Nat.cast_zero,zero_mul,add_zero] using hcont z
  | pair m qr qg inner rest =>
    have hc (i : Fin 3) : ‖childVals u (θ a) i‖ ≤ ‖u‖+2*D := by
      have hh := norm_childVals_le u (θ a) i
      obtain ⟨h1,h2⟩ := hθ a
      linarith
    have hr (a' b') := norm_cplVal_le θ D hD hθ qr a' b' (childVals u (θ a) m.red.1) z
    have hg (a' b') := norm_cplVal_le θ D hD hθ qg a' b' (childVals u (θ a) m.green.1) z
    have hi := norm_chainVal_le θ D hD hθ inner (slotSign ζ m.c) (addrExt a [m.c])
      (childVals u (θ a) m.c) 0 (le_refl 0) (fun _ => childVals u (θ a) m.c)
      (fun _ => by simp) z
    have hs := norm_chainVal_le θ D hD hθ rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c]++inner.lonePath++[m.lone])) u H hH cont hcont z
    simp only [chainVal,RegChain.size,Nat.cast_add,Nat.cast_ofNat]
    split_ifs <;>
      nlinarith [hc m.red.1,hc m.green.1,hc m.c,
                hr (addrExt a [m.red.1]) (addrExt a ([m.c]++inner.lonePath++[m.red.2])),
                hr (addrExt a ([m.c]++inner.lonePath++[m.red.2])) (addrExt a [m.red.1]),
                hg (addrExt a [m.green.1]) (addrExt a ([m.c]++inner.lonePath++[m.green.2])),
                hg (addrExt a ([m.c]++inner.lonePath++[m.green.2])) (addrExt a [m.green.1]),
                (show (0:ℝ) ≤ (qr.size:ℝ) from Nat.cast_nonneg _),(show (0:ℝ) ≤ (qg.size:ℝ) from Nat.cast_nonneg _),(show (0:ℝ) ≤ (inner.size:ℝ) from Nat.cast_nonneg _),(show (0:ℝ) ≤ (rest.size:ℝ) from Nat.cast_nonneg _)]
termination_by structural X
end

end WaveTurbulence.RegAsymp
