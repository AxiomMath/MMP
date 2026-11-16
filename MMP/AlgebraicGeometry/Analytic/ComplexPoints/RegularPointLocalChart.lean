module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BasicOpenPointsLevelSet
public import MMP.AlgebraicGeometry.Variety.RegularClosedPointStandardSmooth
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPointsUnderlyingSpace

/-!
# Near a regular point, the `ℂ`-points of an affine scheme are a submersion level set

Let `X` be an affine scheme of finite type over an algebraically closed field `K`, with ring of
global sections `A`. A `K`-point `p` of `X` corresponds to the maximal ideal
`𝔪_p = {a ∈ A | a(p) = 0}`, the kernel of evaluation at `p`, and the local ring of `X` at the
image of `p` is the localization `A_{𝔪_p}`.

If `p` is a regular point, so `A_{𝔪_p}` is a regular local ring, then there is `g ∈ A` with
`g(p) ≠ 0` such that `A_g` has a submersive presentation `K[x_i]_{i ∈ ι} / (f_j)_{j ∈ σ}` of
relative dimension `dim A_{𝔪_p}`. For `K = ℂ`, the classically open neighbourhood
`{q ∈ X(ℂ) | g(q) ≠ 0}` of `p` is then homeomorphic to the zero set of the polynomial map
`(f_j) : ℂ^ι → ℂ^σ`, whose derivative is surjective at every zero: a complex manifold of
dimension `|ι| - |σ| = dim A_{𝔪_p}`.

## Main results

* `MMP.UnderlyingSpace.mem_primeIdealOf_iff_evalTop_eq_zero`: the prime ideal of
  the image of `p` in `A` is the kernel of evaluation at `p`.
* `MMP.UnderlyingSpace.isRegularLocalRing_localization_ker_evalTopRingHom`: at a
  regular `K`-point `p`, the localization of `A` at the kernel of evaluation is regular.
* `MMP.UnderlyingSpace.exists_nonvanishingLocus_homeomorph_levelSet`: a regular
  `ℂ`-point has a classically open neighbourhood homeomorphic to the level set of a polynomial
  submersion of relative dimension `dim A_{𝔪_p}`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace MMP

namespace UnderlyingSpace

section Ideal

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsAffine X]
  [Algebra K Γ(X, ⊤)]

/-- The prime ideal of `Γ(X, X)` at the image of a `K`-point `p` of an affine scheme is the
kernel of evaluation at `p`. -/
theorem mem_primeIdealOf_iff_evalTop_eq_zero (p : UnderlyingSpace K X) (a : Γ(X, ⊤)) :
    a ∈ ((isAffineOpen_top X).primeIdealOf
      ⟨p.toHom (IsLocalRing.closedPoint K), trivial⟩).asIdeal ↔ evalTop p a = 0 := by
  rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  change a ∈ (PrimeSpectrum.comap (X.presheaf.germ ⊤ _ trivial).hom
    (IsLocalRing.closedPoint _)).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change _ ∈ IsLocalRing.maximalIdeal _ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← Scheme.mem_basicOpen_top, ← top_le_preimage_iff, evalTop,
    top_le_preimage_basicOpen_iff p (Scheme.Hom.preimage_top _).ge, not_not]

/-- The prime ideal of `Γ(X, X)` at the image of a `K`-point `p` of an affine scheme equals the
kernel of the evaluation ring homomorphism at `p`. -/
theorem primeIdealOf_eq_ker_evalTopRingHom (p : UnderlyingSpace K X) :
    ((isAffineOpen_top X).primeIdealOf
      ⟨p.toHom (IsLocalRing.closedPoint K), trivial⟩).asIdeal = RingHom.ker (evalTopRingHom p) := by
  ext a
  rw [mem_primeIdealOf_iff_evalTop_eq_zero, RingHom.mem_ker, evalTopRingHom_apply]

/-- The kernel of evaluation at a `K`-point `p` is a prime ideal of `Γ(X, X)`. -/
instance isPrime_ker_evalTopRingHom (p : UnderlyingSpace K X) :
    (RingHom.ker (evalTopRingHom p)).IsPrime :=
  RingHom.ker_isPrime _

/-- The local ring of `X` at the image of a `K`-point `p` is the localization of `Γ(X, X)` at the
kernel of evaluation at `p`. -/
theorem isLocalization_stalk_ker_evalTopRingHom (p : UnderlyingSpace K X) :
    letI := X.presheaf.algebra_section_stalk
      (⟨p.toHom (IsLocalRing.closedPoint K), trivial⟩ : (⊤ : X.Opens))
    IsLocalization.AtPrime (X.presheaf.stalk
      ((⟨p.toHom (IsLocalRing.closedPoint K), trivial⟩ : (⊤ : X.Opens)) : X))
      (RingHom.ker (evalTopRingHom p)) := by
  letI := X.presheaf.algebra_section_stalk
    (⟨p.toHom (IsLocalRing.closedPoint K), trivial⟩ : (⊤ : X.Opens))
  have h := (isAffineOpen_top X).isLocalization_stalk
    ⟨p.toHom (IsLocalRing.closedPoint K), trivial⟩
  unfold IsLocalization.AtPrime at h ⊢
  simpa only [primeIdealOf_eq_ker_evalTopRingHom] using h

/-- At a `K`-point `p` of an affine scheme whose image is a regular point, the localization of
`Γ(X, X)` at the kernel of evaluation at `p` is a regular local ring. -/
theorem isRegularLocalRing_localization_ker_evalTopRingHom (p : UnderlyingSpace K X)
    (hp : p.toHom (IsLocalRing.closedPoint K) ∈ regularLocus X) :
    IsRegularLocalRing (Localization.AtPrime (RingHom.ker (evalTopRingHom p))) := by
  letI := X.presheaf.algebra_section_stalk
    (⟨p.toHom (IsLocalRing.closedPoint K), trivial⟩ : (⊤ : X.Opens))
  have := isLocalization_stalk_ker_evalTopRingHom p
  have : IsRegularLocalRing (X.presheaf.stalk
      ((⟨p.toHom (IsLocalRing.closedPoint K), trivial⟩ : (⊤ : X.Opens)) : X)) := hp
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv
    (RingHom.ker (evalTopRingHom p)).primeCompl (X.presheaf.stalk
      ((⟨p.toHom (IsLocalRing.closedPoint K), trivial⟩ : (⊤ : X.Opens)) : X))
    (Localization.AtPrime (RingHom.ker (evalTopRingHom p)))).toRingEquiv

/-- The kernel of evaluation at a `K`-point is a maximal ideal. -/
theorem isMaximal_ker_evalTopRingHom (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (p : UnderlyingSpace K X) : (RingHom.ker (evalTopRingHom p)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦
    ⟨algebraMap K Γ(X, ⊤) c, by rw [evalTopRingHom_apply, hK, evalTop_structureRingHom]⟩

end Ideal

section Chart

variable {𝕜 : Type u} [RCLike 𝕜] [IsAlgClosed 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]
  [IsAffine X] [Algebra 𝕜 Γ(X, ⊤)] [Algebra.FiniteType 𝕜 Γ(X, ⊤)]

/-- **Local charts at a regular point.** Let `X` be an affine scheme of finite type over `ℂ` (an
algebraically closed `RCLike` field) and `p ∈ X(ℂ)` a point whose image is regular. Then there
are `g ∈ Γ(X, X)` with `g(p) ≠ 0` and a submersive presentation `P` of `Γ(X, X)_g` of relative
dimension `dim 𝒪_{X,p}`, and the neighbourhood `{g ≠ 0}` of `p` in `X(ℂ)` is homeomorphic to
the zero set of the relation map of `P`, a submersion on `ℂ^ι`. -/
theorem exists_nonvanishingLocus_homeomorph_levelSet
    (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X) (p : UnderlyingSpace 𝕜 X)
    (hp : p.toHom (IsLocalRing.closedPoint 𝕜) ∈ regularLocus X) :
    ∃ g : Γ(X, ⊤), p ∈ nonvanishingLocus 𝕜 g ∧
      ∃ (ι σ : Type) (_ : Fintype ι) (_ : Fintype σ) (_ : DecidableEq σ)
        (P : Algebra.SubmersivePresentation 𝕜 (Localization.Away g) ι σ),
        (P.dimension : WithBot ℕ∞) =
          ringKrullDim (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜))) ∧
        SmoothLevelSet.IsSubmersionOn (𝕜 := 𝕜) ⊤ Set.univ
          (SubmersivePresentationLevelSet.relMap P.toPresentation) ∧
        Nonempty (nonvanishingLocus 𝕜 g ≃ₜ SmoothLevelSet.levelSet Set.univ
          (SubmersivePresentationLevelSet.relMap P.toPresentation)) := by
  classical
  have := isRegularLocalRing_localization_ker_evalTopRingHom p hp
  have := isMaximal_ker_evalTopRingHom hK p
  obtain ⟨g, hg, ι, σ, _, _, P, hP⟩ :=
    exists_submersivePresentation_away_of_isRegularLocalRing (K := 𝕜)
      (RingHom.ker (evalTopRingHom p))
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite σ
  refine ⟨g, fun h ↦ hg (by rwa [RingHom.mem_ker, evalTopRingHom_apply]), ι, σ, inferInstance,
    inferInstance, inferInstance, P, ?_, SubmersivePresentationLevelSet.isSubmersionOn_relMap P
      le_top, ⟨nonvanishingLocusHomeomorphLevelSet hK P.toPresentation⟩⟩
  rw [hP]
  letI := X.presheaf.algebra_section_stalk
    (⟨p.toHom (IsLocalRing.closedPoint 𝕜), trivial⟩ : (⊤ : X.Opens))
  have := isLocalization_stalk_ker_evalTopRingHom p
  exact ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv
    (RingHom.ker (evalTopRingHom p)).primeCompl _ (X.presheaf.stalk
      ((⟨p.toHom (IsLocalRing.closedPoint 𝕜), trivial⟩ : (⊤ : X.Opens)) : X))).toRingEquiv

end Chart

end UnderlyingSpace

end MMP
