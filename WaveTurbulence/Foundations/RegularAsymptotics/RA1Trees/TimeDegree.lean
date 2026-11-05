/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-! # Literal time degrees of the recursive source leading factors -/

@[expose] public section
namespace WaveTurbulence.RegAsymp

mutual
/-- Degree of the actual source couple time factor under positive simultaneous scaling. -/
def coupleTimeDegree : RegCpl → ℕ
  | .triv => 0
  | .type1 _ a b c => 1 + coupleTimeDegree a + coupleTimeDegree b + coupleTimeDegree c
  | .type2 p m q => chainTimeDegree p + chainTimeDegree m + coupleTimeDegree q

/-- Degree contributed by the actual chain time integrations. The inner chain does not occur
in JBchain; source dominant chains have trivial inner chains. -/
def chainTimeDegree : RegChain → ℕ
  | .nil => 0
  | .pair _ r g _ rest => 1 + coupleTimeDegree r + coupleTimeDegree g + chainTimeDegree rest
end

mutual
/-- The literal source time degree is at most half the source couple order. -/
theorem twice_coupleTimeDegree_le_size : ∀ Q : RegCpl, 2 * coupleTimeDegree Q ≤ Q.size
  | .triv => by simp [coupleTimeDegree, RegCpl.size]
  | .type1 _ a b c => by
    have ha := twice_coupleTimeDegree_le_size a
    have hb := twice_coupleTimeDegree_le_size b
    have hc := twice_coupleTimeDegree_le_size c
    simp only [coupleTimeDegree, RegCpl.size]
    omega
  | .type2 p m q => by
    have hp := twice_chainTimeDegree_le_size p
    have hm := twice_chainTimeDegree_le_size m
    have hq := twice_coupleTimeDegree_le_size q
    simp only [coupleTimeDegree, RegCpl.size]
    omega

/-- The literal source time degree is at most half the source tree order. -/
theorem twice_chainTimeDegree_le_size : ∀ X : RegChain, 2 * chainTimeDegree X ≤ X.size
  | .nil => by simp [chainTimeDegree, RegChain.size]
  | .pair _ r g _ rest => by
    have hr := twice_coupleTimeDegree_le_size r
    have hg := twice_coupleTimeDegree_le_size g
    have ht := twice_chainTimeDegree_le_size rest
    simp only [chainTimeDegree, RegChain.size]
    omega
end

end WaveTurbulence.RegAsymp
