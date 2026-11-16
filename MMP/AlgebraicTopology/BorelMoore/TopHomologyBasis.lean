module

public import MMP.AlgebraicTopology.FundamentalClass.Restriction
public import MMP.AlgebraicTopology.PoincareDuality.TopDegree
/-!
# The top Borel–Moore homology of a manifold with finitely many components (Fulton, §19.1)

Let `M` be an oriented real `n`-manifold (for instance a complex manifold of complex dimension
`m`, with `n = 2m`) which is the disjoint union of finitely many non-empty connected open subsets
`M_1, …, M_r`, with inclusions `ι_l`. By Poincaré duality each `H_n M_l` is free of rank one on
the fundamental class `μ_{M_l}`, and the Borel–Moore homology of a finite disjoint union is the
direct sum, `(a_l)_l ↦ ∑_l ι_{l*} a_l` being an isomorphism `⨁_l H_n M_l ≅ H_n M` with inverse
`a ↦ (a|_{M_l})_l`. Hence `H_n M` is free with basis `ι_{1*} μ_{M_1}, …, ι_{r*} μ_{M_r}`.
Since `μ_M|_{M_l} = μ_{M_l}`, the fundamental class of `M` is `μ_M = ∑_l ι_{l*} μ_{M_l}`.

## Main definitions

* `MMP.borelMooreHomology.topHomologyBasis`: the basis
  `ι_{1*} μ_1, …, ι_{r*} μ_r` of `H_n M`, for fundamental classes `μ_l` of the pieces `M_l`.

## Main results

* `MMP.borelMooreHomology.topHomologyBasis_apply`: the `l`-th basis vector is
  `ι_{l*} μ_l`.
* `MMP.borelMooreHomology.eq_sum_pushforward_restrict`: every class
  `a ∈ H_j M` is `∑_l ι_{l*} (a|_{M_l})`.
* `MMP.IsFundamentalClass.eq_sum_topHomologyBasis`: `μ_M = ∑_l ι_{l*} μ_{M_l}`,
  with `μ_{M_l} = μ_M|_{M_l}`, the sum of the basis vectors.

## Implementation notes

The statement is made for an oriented real `n`-manifold, modelled on a real vector space `H`
with orientation basis `b` as in `MMP.IsFundamentalClass`; a complex manifold of
complex dimension `m` is the case `H = ℂ^m`, `n = 2m`, `b = complexOrientationBasis m`
(`MMP.IsComplexFundamentalClass`). The pieces `M_l` are given as a finite family
of pairwise disjoint open subsets covering `M`.

Poincaré duality is used only in top degree, at the pieces `M_l`: each `μ_l` freely generates
`H_n M_l` for non-empty connected `M_l`
(`MMP.PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold`). The
manifold is Hausdorff and second countable, the standard convention.

The fundamental class `μ_{M_l}` of `M_l` is taken to be `μ_M|_{M_l}`, a fundamental class of
`M_l` by `MMP.IsFundamentalClass.restrict`; with Fulton's reading of "the class
`μ_{M_l}`" as the unique fundamental class (Iversen, IX.4.7) this is the fundamental class of
`M_l`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.1.
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][bott1982], 4.1.3.
* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Function

universe u v

namespace MMP

namespace borelMooreHomology

variable (R : Type u) [CommRing R] {H : Type v} [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace H M] {ι : Type} [Fintype ι] (U : ι → TopologicalSpace.Opens M)
  (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set M))) (hcover : ∀ x, ∃ l, x ∈ U l)

include hdisj hcover in
/-- Every class `a ∈ H_j M` of a finite disjoint union of open subsets `U l` is
`∑_l ι_{l*} (a|_{U l})`. -/
theorem eq_sum_pushforward_restrict (j : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) j) :
    a = ∑ l, pushforward R (ModuleCat.of R R) (clopenInclusion (Y := TopCat.of M) (U l))
      (isProperMap_clopenInclusion (Y := TopCat.of M) U hdisj hcover l) j
      (restrict R (ModuleCat.of R R) (Y := TopCat.of M) (U l) j a) := by
  have h := congrArg (fun f ↦ f a) (sum_restrict_pushforward R (ModuleCat.of R R)
    (Y := TopCat.of M) U hdisj hcover (isProperMap_clopenInclusion (Y := TopCat.of M) U hdisj
      hcover) j)
  simpa [ModuleCat.hom_sum, LinearMap.sum_apply] using h.symm

variable {n : ℕ}
  (μ : ∀ l, borelMooreHomology R (ModuleCat.of R R) (TopCat.of (U l)) n)
  (hμ : ∀ l, Function.Bijective fun r : R ↦ r • μ l)

/-- The linear equivalence `R ≃ H_n (U l)`, `r ↦ r • μ_l`, for a free generator `μ_l`. -/
def generatorEquiv (l : ι) :
    R ≃ₗ[R] borelMooreHomology R (ModuleCat.of R R) (TopCat.of (U l)) n :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _ (μ l)) (hμ l)

/-- The coordinates `H_n M ≃ (ι → R)`: `a ↦ (r_l)_l` with `a|_{U l} = r_l • μ_l`. -/
def topHomologyEquivFun :
    borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n ≃ₗ[R] (ι → R) where
  toFun a l := (generatorEquiv R U μ hμ l).symm
    (restrict R (ModuleCat.of R R) (Y := TopCat.of M) (U l) n a)
  map_add' a a' := by ext l; simp
  map_smul' r a := by ext l; simp
  invFun c := ∑ l, c l • pushforward R (ModuleCat.of R R) (clopenInclusion (Y := TopCat.of M) (U l))
    (isProperMap_clopenInclusion (Y := TopCat.of M) U hdisj hcover l) n (μ l)
  left_inv a := by
    conv_rhs => rw [eq_sum_pushforward_restrict R U hdisj hcover n a]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← map_smul]
    congr 1
    exact (generatorEquiv R U μ hμ l).apply_symm_apply _
  right_inv c := by
    classical
    ext m
    simp only [map_sum, map_smul]
    rw [Finset.sum_eq_single m]
    · rw [← ConcreteCategory.comp_apply, pushforward_restrict_self R (ModuleCat.of R R)
        (Y := TopCat.of M) (U m) (isClopen_of_disjoint_cover (Y := TopCat.of M) U hdisj hcover m)]
      rw [ConcreteCategory.id_apply, ← map_smul]
      have : c m • μ m = generatorEquiv R U μ hμ m (c m) := rfl
      rw [this, LinearEquiv.symm_apply_apply]
    · intro l _ hlm
      rw [← ConcreteCategory.comp_apply, pushforward_restrict_of_disjoint R (ModuleCat.of R R)
        (Y := TopCat.of M) (U l) (U m)
        (isClopen_of_disjoint_cover (Y := TopCat.of M) U hdisj hcover m) (hdisj hlm)]
      simp
    · simp

/-- **The top Borel–Moore homology of a manifold with finitely many components** (Fulton, §19.1,
proof of Lemma 19.1.1). Let the real `n`-manifold `M` be the disjoint union of finitely many open
subsets `U l`, with inclusions `ι_l`, and let `μ_l ∈ H_n (U l)` freely generate `H_n (U l)`
(e.g. the fundamental class of a non-empty connected `U l`, by Poincaré duality). Then
`ι_{1*} μ_1, …, ι_{r*} μ_r` is a basis of `H_n M`. -/
def topHomologyBasis :
    Module.Basis ι R (borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n) :=
  Module.Basis.ofEquivFun (topHomologyEquivFun R U hdisj hcover μ hμ)

/-- The `l`-th vector of `topHomologyBasis` is `ι_{l*} μ_l`. -/
theorem topHomologyBasis_apply (l : ι) :
    topHomologyBasis R U hdisj hcover μ hμ l =
      pushforward R (ModuleCat.of R R) (clopenInclusion (Y := TopCat.of M) (U l))
        (isProperMap_clopenInclusion (Y := TopCat.of M) U hdisj hcover l) n (μ l) := by
  classical
  simp [topHomologyBasis, topHomologyEquivFun, Pi.single_apply]

end borelMooreHomology

open borelMooreHomology

section Fundamental

variable {R : Type u} [CommRing R] {H : Type v} [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] {M : Type u} [TopologicalSpace M]
  [T2Space H] [T2Space M] [SecondCountableTopology M] [ChartedSpace H M] {ι : Type} [Fintype ι]
  {U : ι → TopologicalSpace.Opens M} {n : ℕ} {b : Module.Basis (Fin n) ℝ H}

/-- Each non-empty connected open piece of a Hausdorff second countable manifold satisfies
Poincaré duality in top degree. -/
theorem topHomologyFreeOnFundamentalClass_of_connected (hconn : ∀ l, ConnectedSpace (U l))
    (l : ι) : TopHomologyFreeOnFundamentalClass R (U l) b :=
  haveI := hconn l
  PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold b

/-- The basis `ι_{1*} μ_{M_1}, …, ι_{r*} μ_{M_r}` of `H_n M` built from the fundamental class
`μ_M`, with `μ_{M_l} = μ_M|_{M_l}`, for non-empty connected pieces `M_l` (by Poincaré duality in
top degree each `μ_{M_l}` freely generates `H_n M_l`). -/
def IsFundamentalClass.topHomologyBasis
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n} (hμ : IsFundamentalClass R b μ)
    (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set M))) (hcover : ∀ x, ∃ l, x ∈ U l)
    (hconn : ∀ l, ConnectedSpace (U l)) :
    Module.Basis ι R (borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n) :=
  borelMooreHomology.topHomologyBasis R U hdisj hcover
    (fun l ↦ borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of M) (U l) n μ)
    fun l ↦ topHomologyFreeOnFundamentalClass_of_connected hconn l _ (hμ.restrict (U l))

/-- The `l`-th vector of `IsFundamentalClass.topHomologyBasis` is `ι_{l*} μ_{M_l}`, with
`μ_{M_l} = μ_M|_{M_l}` a fundamental class of `M_l`. -/
theorem IsFundamentalClass.topHomologyBasis_apply
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n} (hμ : IsFundamentalClass R b μ)
    (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set M))) (hcover : ∀ x, ∃ l, x ∈ U l)
    (hconn : ∀ l, ConnectedSpace (U l)) (l : ι) :
    hμ.topHomologyBasis hdisj hcover hconn l =
      pushforward R (ModuleCat.of R R) (clopenInclusion (Y := TopCat.of M) (U l))
        (isProperMap_clopenInclusion (Y := TopCat.of M) U hdisj hcover l) n
        (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of M) (U l) n μ) ∧
      IsFundamentalClass R b
        (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of M) (U l) n μ) :=
  ⟨borelMooreHomology.topHomologyBasis_apply R U hdisj hcover _ _ l, hμ.restrict (U l)⟩

/-- **`μ_M = ∑_l ι_{l*} μ_{M_l}`** (Fulton, §19.1, proof of Lemma 19.1.1): the fundamental class
of `M` is the sum of the vectors of the basis `IsFundamentalClass.topHomologyBasis`. -/
theorem IsFundamentalClass.eq_sum_topHomologyBasis
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n} (hμ : IsFundamentalClass R b μ)
    (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set M))) (hcover : ∀ x, ∃ l, x ∈ U l)
    (hconn : ∀ l, ConnectedSpace (U l)) :
    μ = ∑ l, hμ.topHomologyBasis hdisj hcover hconn l := by
  simp only [IsFundamentalClass.topHomologyBasis, borelMooreHomology.topHomologyBasis_apply]
  exact eq_sum_pushforward_restrict R U hdisj hcover n μ

end Fundamental

end MMP
