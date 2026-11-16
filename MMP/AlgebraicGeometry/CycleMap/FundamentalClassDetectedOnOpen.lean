module

public import MMP.AlgebraicGeometry.CycleMap.TopClassComponentBasis
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVarietyUnique

/-!
# A fundamental class is detected on one open subset of the regular part

## Main results

* `MMP.pushforward_map_id_apply`: the push-forward along the complex points of the
  identity is the identity.
* `MMP.IsVarietyFundamentalClass.eq_of_restrict_eq`,
  `MMP.IsVarietyFundamentalClass.of_restrict_eq`: a top-degree class of a complex
  variety which agrees with a fundamental class on one non-empty open subset of the regular part
  is that fundamental class (Fulton, proof of Lemma 19.2(d): "restriction
  `H_{2v} V → H_{2v} V_0` is injective").

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, Lemma 19.2(d).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MMP.UnderlyingSpace

namespace MMP

open MMP.Intersection.Scheme (dimension)
open MMP

variable {R : Type} [CommRing R] {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V]

/-- The push-forward along the complex points of the identity of `V` is the identity. -/
lemma pushforward_map_id_apply (j : ℤ)
    (c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) j) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) (𝟙 V)))
      (isClosedEmbedding_map_of_isClosedImmersion (𝟙 V)).isProperMap j c = c := by
  have e : TopCat.ofHom (map (K := ℂ) (𝟙 V)) = 𝟙 (TopCat.of (UnderlyingSpace ℂ V)) := by
    rw [map_id]; rfl
  have h : borelMooreHomology.pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (map (K := ℂ) (𝟙 V)))
      (isClosedEmbedding_map_of_isClosedImmersion (𝟙 V)).isProperMap j = 𝟙 _ := by
    rw [← borelMooreHomology.pushforward_id R (ModuleCat.of R R) j]
    congr 1
  rw [h]
  rfl

variable [IsIntegral V]

/-- **A fundamental class is detected on one open subset of the regular part.** Let `V` be a
complex variety of dimension `n`, `c'` a fundamental class of `V` and `W ⊆ V(ℂ)` a non-empty open
subset of the regular part `V_reg(ℂ)`. If `c ∈ H_{2n} V` agrees with `c'` on `W`, then `c = c'`;
in particular `c` is a fundamental class of `V`. -/
theorem IsVarietyFundamentalClass.eq_of_restrict_eq {n : ℕ}
    {hn : (n : WithBot ℕ∞) = dimension V}
    {c c' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ)}
    (hc' : IsVarietyFundamentalClass R hn c') (W : Opens (UnderlyingSpace ℂ V))
    (hW : (W : Set (UnderlyingSpace ℂ V)) ⊆ regularPart ℂ V)
    (hne : (W : Set (UnderlyingSpace ℂ V)).Nonempty)
    (h : borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
        W (2 * n : ℕ) c =
      borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
        W (2 * n : ℕ) c') :
    c = c' := by
  obtain ⟨r, hr⟩ := hc'.bijective_smul.2 c
  simp only at hr
  subst hr
  have hW' : (W : Set (UnderlyingSpace ℂ V)) ⊆ mapFun (K := ℂ) (𝟙 V) '' regularPart ℂ V := by
    intro p hp
    refine ⟨p, hW hp, ?_⟩
    change map (K := ℂ) (𝟙 V) p = p
    rw [map_id]; rfl
  have h1 : (r - 1) • borelMooreHomology.restrict R (ModuleCat.of R R)
      (Y := TopCat.of (UnderlyingSpace ℂ V)) W (2 * n : ℕ)
      (borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) (𝟙 V)))
        (isClosedEmbedding_map_of_isClosedImmersion (𝟙 V)).isProperMap (2 * n : ℕ) c') = 0 := by
    rw [pushforward_map_id_apply, sub_smul, one_smul, ← map_smul, h, sub_self]
  have := eq_zero_of_smul_restrict_pushforward_eq_zero R (𝟙 V) hc' W hW' hne h1
  rw [sub_eq_zero.1 this, one_smul]

/-- **A fundamental class is detected on one open subset of the regular part.** A class
`c ∈ H_{2n} V` of a complex variety of dimension `n` which agrees with a fundamental class on a
non-empty open subset `W` of `V_reg(ℂ)` is a fundamental class of `V`. -/
theorem IsVarietyFundamentalClass.of_restrict_eq {n : ℕ}
    {hn : (n : WithBot ℕ∞) = dimension V}
    {c c' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * n : ℕ)}
    (hc' : IsVarietyFundamentalClass R hn c') (W : Opens (UnderlyingSpace ℂ V))
    (hW : (W : Set (UnderlyingSpace ℂ V)) ⊆ regularPart ℂ V)
    (hne : (W : Set (UnderlyingSpace ℂ V)).Nonempty)
    (h : borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
        W (2 * n : ℕ) c =
      borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ V))
        W (2 * n : ℕ) c') :
    IsVarietyFundamentalClass R hn c :=
  hc'.eq_of_restrict_eq W hW hne h ▸ hc'

end MMP
