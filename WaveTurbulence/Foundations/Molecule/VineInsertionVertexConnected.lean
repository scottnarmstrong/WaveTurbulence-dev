/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSubdivisionAvoidPaths
public import WaveTurbulence.Foundations.Molecule.VineEndpointBounds
public import WaveTurbulence.Foundations.Molecule.VineInsertionPaths
import Mathlib.Tactic

/-! # Arbitrary simultaneous rail subdivision and rung insertion preserve vertex connectivity -/

public section
namespace WaveTurbulence.Vine

/-- A single subdivision keeps every endpoint in the enlarged atom range. -/
theorem subdivide_endpoints {n : ℕ} {es : List (ℕ×ℕ)} (hb : EdgeBounded n es)
    (a b k : ℕ) (ha : a<n) (hbn : b<n) :
    EdgeBounded (n+k) (subdivideBonds n es a b k) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · have hh := hb e (List.mem_of_mem_erase he)
    constructor <;> omega
  · apply railBonds_endpoints a b (n+k) _ (by omega) (by omega) _ he
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    omega

/-- Rung insertion contains the graph obtained by subdividing each old
rail bond separately. Extra doubled rungs can only improve connectivity. -/
theorem double_subdivision_mem_insertRungs (T : VineTemplate)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) {k : ℕ} (hk : k ≠ 0)
    (h2 : s.2 ∈ T.bonds.erase s.1) :
    ∀ e ∈ subdivideBonds (T.n+k) (subdivideBonds T.n T.bonds s.1.1 s.1.2 k)
      s.2.1 s.2.2 k,e ∈ (insertRungs T s k).bonds := by
  intro e he
  unfold subdivideBonds at he
  rw [List.erase_append_left _ h2] at he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · simp only [insertRungs,hk,ite_false,List.mem_append]
      exact Or.inl (Or.inl (Or.inl he))
    · exact first_rail_mem T s hk he
  · exact second_rail_mem T s hk he

/-- Subdividing the two distinct nonloop rail bonds preserves connectivity
after removal of any one old or fresh atom, at every rung count. -/
theorem insertRungs_vertexConnected (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hn : 3 ≤ T.n) (hb : EdgeBounded T.n T.bonds)
    (hc : VertexConnected T.n T.bonds)
    (hs : s.1.1<T.n ∧ s.1.2<T.n ∧ s.2.1<T.n ∧ s.2.2<T.n)
    (h1 : s.1.1 ≠ s.1.2) (h2 : s.2.1 ≠ s.2.2)
    (hmem2 : s.2 ∈ T.bonds.erase s.1) :
    VertexConnected (insertRungs T s k).n (insertRungs T s k).bonds := by
  by_cases hk : k=0
  · simpa only [hk,insertRungs_zero] using hc
  have hfirst := subdivide_vertexConnected hc hb hn s.1.1 s.1.2 k hs.1 hs.2.1 h1
  have hbfirst := subdivide_endpoints hb s.1.1 s.1.2 k hs.1 hs.2.1
  have hsecond := subdivide_vertexConnected hfirst hbfirst (by omega)
    s.2.1 s.2.2 k (by omega) (by omega) h2
  intro z u v hu hv huz hvz
  rw [insertRungs_atoms] at hu hv
  have hp := hsecond z u v (by omega) (by omega) huz hvz
  exact avoidPath_mono (double_subdivision_mem_insertRungs T s hk hmem2) hp

end WaveTurbulence.Vine
