module
import MMP.AlgebraicGeometry.Singularities.Semismooth.BranchLocus
public import MMP.AlgebraicGeometry.Singularities.Semismooth.DoubleCoverRank
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import MMP.AlgebraicGeometry.Morphisms.Etale.DoubleCoverInvolution
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFlat

/-!
# The double locus of a semismooth `n`-fold and the gluing of a double normal crossing `n`-fold

Let `X` be a semismooth `n`-fold over a field `k`, `ν : X^ν ⟶ X` its normalization, `D_X` the
singular locus of `X` with its reduced structure and `D_ν = ν⁻¹(D_X)_red`. The restriction
`D_ν ⟶ D_X` of `ν` is a finite flat double cover; it is étale over a closed point `x` of `D_X`
exactly when `x` is not a pinch point of `X`, that is, it is ramified exactly along the pinch
locus.

When every closed point of an `n`-fold `U` is smooth or a double normal crossing point, the
cover `D_μ ⟶ D` of the double intersection locus `D` is finite étale with a covering involution
`τ`, and `𝒪_U = {h ∈ μ_*𝒪_{U^μ} : h|_{D_μ} is τ-invariant}`: `U` is glued from its
normalization along `τ`.

## Main results

* `MMP.Flips.IsSemismooth.etale_restrict_doubleLocus_iff_not_isPinchPoint`: the double cover
  `D_ν ⟶ D_X` is étale exactly over the closed points that are not pinch points.
* `MMP.Flips.IsSemismooth.isFinite_flat_finrank_subschemeMap_normalization`: the restriction
  `ν|_{D_ν} : D_ν ⟶ D_X` is finite, flat and of degree `2`.
* `MMP.Flips.exists_involution_and_range_app_normalization_eq`: an `n`-fold with only smooth and
  double normal crossing points is glued from its normalization.

## Implementation notes

`D_X` is `MMP.Resolution.reducedSingularLocus sX` and `D_ν` is the reduced closed subscheme
on the preimage of the singular locus. In the branch-locus statement the restriction of `ν` is
any morphism `φ : D_ν ⟶ D_X` with `φ ≫ ι_{D_X} = ι_{D_ν} ≫ ν`; since `ι_{D_X}` is a
monomorphism there is exactly one, namely `Scheme.IdealSheafData.subschemeMap`. "Étale over `x`"
is read as: the restriction of `φ` over some open neighbourhood of `x` in `D_X` is étale.

The degree of a finite flat morphism is `AlgebraicGeometry.Scheme.Hom.finrank`, the rank of
`f_* 𝒪` at each point of the target; "of degree `2`" is the statement that this function is
constantly `2`. Flatness is miracle flatness at closed points, both `𝒪_{D_X}` and `𝒪_{D_ν}`
being regular of dimension `n - 1` there, read on the completed local models.

The source states the gluing for surfaces over `ℂ`; the argument (completion at the closed points
of `D`, where `𝒪̂_{U,x} ≅ k[[x₀, …, xₙ]]/(x₀x₁)`) works for `n`-folds over any field, and that is
the form stated here. "Finite étale of degree two with covering involution `τ`" is stated as a
`ℤ/2`-torsor: `(id, τ) : D_μ ⨿ D_μ ⟶ D_μ ×_D D_μ` is an isomorphism. The equality of sheaves is
stated on sections over every open `W ⊆ U`. A section `h` of `μ_*𝒪_{U^μ}` with `τ`-invariant
restriction to `D_μ` is a pull-back near every closed point `x`: its restriction descends to `D`,
lifts to `U` near `x`, and the difference vanishes on `D_μ`; its germ comes from `𝒪_{U,x}` by
faithfully flat descent along the completion, since `x₀` and `x₁` multiply the integral closure
of `k[[x]]/(x₀x₁)` into it.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.1, 12.2.3
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

variable {k : Type u} [Field k]

section DoubleLocus

variable {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

open BranchLocus in
/-- **The double cover `D_ν → D_X` is ramified exactly over the pinch points** (FA 12.2.1(2)).
Let `X` be a semismooth `n`-fold with normalization `ν : X^ν ⟶ X`, let `D_X` be its reduced
singular locus and `D_ν` the reduced preimage of `D_X` in `X^ν`, and let `φ : D_ν ⟶ D_X` be the
restriction of `ν`. For a closed point `z` of `D_X`, `φ` is étale over a neighbourhood of `z` if
and only if `z` is not a pinch point of `X`. -/
@[mmp "lem_fa12a_semismooth_double_cover_branch_locus"]
public theorem IsSemismooth.etale_restrict_doubleLocus_iff_not_isPinchPoint {n : ℕ}
    (h : IsSemismooth sX n)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (φ : (Scheme.IdealSheafData.vanishingIdeal
        ((MMP.Mori.singularLocus sX).preimage
          (Stacks.AlgebraicGeometry.Normalization.normalization X hX).continuous)).subscheme ⟶
      (MMP.Resolution.reducedSingularLocus sX).subscheme)
    (hφ : φ ≫ (MMP.Resolution.reducedSingularLocus sX).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        ((MMP.Mori.singularLocus sX).preimage
          (Stacks.AlgebraicGeometry.Normalization.normalization X hX).continuous)).subschemeι ≫
        Stacks.AlgebraicGeometry.Normalization.normalization X hX)
    (z : (MMP.Resolution.reducedSingularLocus sX).subscheme) (hz : IsClosed ({z} : Set _)) :
    (∃ U : (MMP.Resolution.reducedSingularLocus sX).subscheme.Opens, z ∈ U ∧ Etale (φ ∣_ U)) ↔
      ¬ IsPinchPoint sX n ((MMP.Resolution.reducedSingularLocus sX).subschemeι z) := by
  refine ⟨fun ⟨U, hzU, hU⟩ hp ↦ not_etale_of_isPinchPoint h hX φ hφ z hp U hzU hU, fun hp ↦ ?_⟩
  have hcl : IsClosed ({(MMP.Resolution.reducedSingularLocus sX).subschemeι z} : Set X) := by
    rw [← Set.image_singleton]
    exact (MMP.Resolution.reducedSingularLocus sX).subschemeι.isClosedEmbedding.isClosedMap _ hz
  rcases h.2 _ hcl with hs | hdnc | hp'
  · exact absurd hs (subschemeι_notMem_smoothLocus z)
  · exact exists_etale_of_isDoubleNormalCrossingPoint h hX φ hφ z hdnc
  · exact absurd hp' hp

/-! ### The double cover `D_ν ⟶ D_X` -/

namespace SemismoothDoubleCover

/-- The stalks of a scheme locally of finite type over a field are excellent. -/
private theorem isExcellent_stalk_of_field {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] (y : Y) : IsExcellent (Y.presheaf.stalk y) :=
  AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent k
    ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) sY y

/-- The restriction of a finite morphism to closed subschemes is finite. -/
private theorem isFinite_subschemeMap {Y : Scheme.{u}} (I : X.IdealSheafData)
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsFinite f] (H : J ≤ I.map f) :
    IsFinite (Scheme.IdealSheafData.subschemeMap I J f H) := by
  have : IsFinite (Scheme.IdealSheafData.subschemeMap I J f H ≫ J.subschemeι) := by
    rw [Scheme.IdealSheafData.subschemeMap_subschemeι]; infer_instance
  exact IsFinite.of_comp _ J.subschemeι

/-- A double normal crossing point of a reduced scheme of finite type over `k` has `n ≥ 1`: for
`n = 0` the model `k[[x₀]]/(x₀²)` is not reduced, while the completion of `𝒪_{X,x}` is. -/
private theorem exists_eq_add_one_of_dnc [IsReduced X] [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {x : X} {n : ℕ}
    (hmod : HasCompletedLocalModel sX x
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (n + 1)) k)) :
    ∃ m, n = m + 1 := by
  rcases n with _ | m
  · exfalso
    have hred := (MMP.Resolution.isReduced_adicCompletion_stalk_and_normalization_completion
      X sX hX x).1
    let := (stalkStructureMap sX x).toAlgebra
    obtain ⟨e⟩ := hmod
    have h10 : (1 : Fin 1) = 0 := Subsingleton.elim _ _
    have hsq : (MvPowerSeries.X 0 * MvPowerSeries.X 0 : MvPowerSeries (Fin (0 + 1)) k) =
        MvPowerSeries.X 0 * MvPowerSeries.X 1 := by rw [h10]
    set u := e.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 0))
    have hu : u ^ 2 = 0 := by
      rw [← map_pow, ← map_pow, pow_two, hsq,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
    have hu0 : u = 0 := IsReduced.eq_zero u ⟨2, hu⟩
    have hmk : Ideal.Quotient.mk (Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin (0 + 1)) k)}) (MvPowerSeries.X 0) = 0 := by
      have := congrArg e hu0
      rwa [AlgEquiv.apply_symm_apply, map_zero] at this
    have hdvd := (Ideal.Quotient.eq_zero_iff_dvd _ _).mp hmk
    rw [← hsq, ← pow_two, MvPowerSeries.X_pow_dvd_iff] at hdvd
    have := hdvd (Finsupp.single 0 1) (by simp)
    simp [MvPowerSeries.coeff_X] at this
  · exact ⟨m, rfl⟩

/-- Regularity of the localization at equal primes. -/
private theorem isRegularLocalRing_localization_congr {R : Type*} [CommRing R] {I J : Ideal R}
    [I.IsPrime] [J.IsPrime] (h : I = J) :
    IsRegularLocalRing (Localization.AtPrime I) ↔ IsRegularLocalRing (Localization.AtPrime J) := by
  subst h; rfl

/-- **The local ring of the singular locus at a point over a model point.** Let `z ∈ D_X` lie
over `x` with `𝒪̂_{X,x} ≅ M`, the non-regular primes of `M` being those containing a prime `I`.
Then `𝒪_{D,z}` is regular exactly when `M ⧸ I` is, of the same dimension. -/
private theorem isRegularLocalRing_and_ringKrullDim_stalk_of_model [LocallyOfFiniteType sX]
    (hsing : ∀ w : X, w ∈ MMP.Mori.smoothLocus sX ↔ IsRegularLocalRing (X.presheaf.stalk w))
    (D : X.IdealSheafData) [IsReduced D.subscheme]
    (hD : ∀ w, w ∈ Set.range D.subschemeι ↔ w ∉ MMP.Mori.smoothLocus sX)
    (z : D.subscheme) {M : Type u} [CommRing M]
    (e : CompletedLocalRing X (D.subschemeι z) ≃+* M) (I : Ideal M) (d : WithBot ℕ∞)
    (hM : ∀ (q : Ideal M) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q) ↔ ¬ I ≤ q)
    (hMI : IsRegularLocalRing (M ⧸ I) ∧ ringKrullDim (M ⧸ I) = d) :
    IsRegularLocalRing (D.subscheme.presheaf.stalk z) ∧
      ringKrullDim (D.subscheme.presheaf.stalk z) = d := by
  have hexc : IsExcellent (X.presheaf.stalk (D.subschemeι z)) :=
    isExcellent_stalk_of_field sX _
  have : IsNoetherianRing (X.presheaf.stalk (D.subschemeι z)) := hexc.1.1
  have hG : IsGRing (X.presheaf.stalk (D.subschemeι z)) := hexc.1.2.1
  have : IsReduced (D.subscheme.presheaf.stalk z) := isReduced_stalk_of_isReduced _ z
  have : IsDomain (M ⧸ I) := @IsRegularLocalRing.isDomain _ _ hMI.1
  have hI : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp this
  set Q₀ := I.comap e
  have : Q₀.IsPrime := Ideal.IsPrime.comap _
  let eQ : (CompletedLocalRing X (D.subschemeι z) ⧸ Q₀) ≃+* (M ⧸ I) :=
    Ideal.quotientEquiv Q₀ I e (Ideal.map_comap_of_surjective _ e.surjective I).symm
  obtain ⟨hreg, hdim⟩ := isRegularLocalRing_iff_and_ringKrullDim_eq_of_forall_le_comap_iff hG
    (D.subschemeι.stalkMap z).hom (D.subschemeι.stalkMap_surjective z) Q₀ (fun Q hQ => by
      obtain ⟨q, hq, rfl⟩ : ∃ q : Ideal M, q.IsPrime ∧ q.comap e = Q :=
        ⟨Q.map e, Ideal.map_isPrime_of_equiv _, Ideal.comap_map_of_bijective _ e.bijective⟩
      rw [ker_stalkMap_le_iff_mem_range, hD, hsing, isRegularLocalRing_stalk_fromSpecStalk_iff,
        ← SingLoc.isRegularLocalRing_localization_adicCompletion_iff hG (q.comap e),
        SingLoc.isRegularLocalRing_localization_comap_iff e q, hM, not_not,
        Ideal.comap_le_comap_iff_of_surjective _ e.surjective])
  have := hMI.1
  refine ⟨hreg.mpr (IsRegularLocalRing.of_ringEquiv eQ.symm), ?_⟩
  rw [hdim, ringKrullDim_eq_of_ringEquiv eQ, hMI.2]

open IsLocalRing in
/-- **The primes of `𝒪̂_{X^ν,w}` over the double locus of the normalization.** Let `y ∈ D_ν` lie
over `x` with `𝒪̂_{X,x} ≅ M`, the non-regular primes of `M` being those containing `I`, and let
`ψ₀ : 𝒪̂_{X,x} → 𝒪̂_{X^ν,w}` be compatible with the stalk map of `ν`. A prime `Q` of `𝒪̂_{X^ν,w}`
lies over `D_ν` exactly when it contains `I 𝒪̂_{X^ν,w}`. -/
private theorem ker_stalkMap_le_comap_iff_of_model [IsReduced X] [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hsing : ∀ w : X, w ∈ MMP.Mori.smoothLocus sX ↔ IsRegularLocalRing (X.presheaf.stalk w))
    (E : (X.normalizationScheme hX).IdealSheafData)
    (hE : ∀ w, w ∈ Set.range E.subschemeι ↔ X.normalization hX w ∉ MMP.Mori.smoothLocus sX)
    (y : E.subscheme) {M : Type u} [CommRing M]
    (e : CompletedLocalRing X (X.normalization hX (E.subschemeι y)) ≃+* M) (I : Ideal M)
    (hM : ∀ (q : Ideal M) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q) ↔ ¬ I ≤ q)
    (ψ₀ : CompletedLocalRing X (X.normalization hX (E.subschemeι y)) →+*
        AdicCompletion (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk (E.subschemeι y)))
          ((X.normalizationScheme hX).presheaf.stalk (E.subschemeι y)))
    (hψ₀alg : ∀ a : X.presheaf.stalk (X.normalization hX (E.subschemeι y)),
        ψ₀ (algebraMap _ _ a) = algebraMap _ _ (((X.normalization hX).stalkMap
          (E.subschemeι y)).hom a))
    (Q : Ideal (AdicCompletion
      (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk (E.subschemeι y)))
      ((X.normalizationScheme hX).presheaf.stalk (E.subschemeι y)))) (hQ : Q.IsPrime) :
    RingHom.ker (E.subschemeι.stalkMap y).hom ≤ Q.comap (algebraMap _ _) ↔
      I.map (ψ₀.comp e.symm.toRingHom) ≤ Q := by
  let w := E.subschemeι y
  have hexcX := isExcellent_stalk_of_field sX (X.normalization hX w)
  have : IsNoetherianRing (X.presheaf.stalk (X.normalization hX w)) := hexcX.1.1
  set q := Q.comap (algebraMap ((X.normalizationScheme hX).presheaf.stalk w)
    (AdicCompletion (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk w))
      ((X.normalizationScheme hX).presheaf.stalk w)))
  have : q.IsPrime := hQ.comap _
  have hν : X.normalization hX ((X.normalizationScheme hX).fromSpecStalk w
      (⟨q, inferInstance⟩ : PrimeSpectrum _)) = X.fromSpecStalk (X.normalization hX w)
        (⟨q.comap ((X.normalization hX).stalkMap w).hom, inferInstance⟩ : PrimeSpectrum _) :=
    (congrArg (fun t => t (⟨q, inferInstance⟩ : PrimeSpectrum _))
      (Scheme.SpecMap_stalkMap_fromSpecStalk (f := X.normalization hX) (x := w))).symm
  have hcq : q.comap ((X.normalization hX).stalkMap w).hom = (Q.comap ψ₀).comap
      (algebraMap (X.presheaf.stalk (X.normalization hX w))
        (CompletedLocalRing X (X.normalization hX w))) := by
    rw [Ideal.comap_comap, Ideal.comap_comap]
    congr 1
    exact RingHom.ext fun a => (hψ₀alg a).symm
  have hce : Q.comap ψ₀ = (Q.comap (ψ₀.comp e.symm.toRingHom)).comap e := by
    ext a
    simp
  rw [ker_stalkMap_le_iff_mem_range, hE, hν, hsing, isRegularLocalRing_stalk_fromSpecStalk_iff,
    isRegularLocalRing_localization_congr hcq,
    ← SingLoc.isRegularLocalRing_localization_adicCompletion_iff hexcX.1.2.1 (Q.comap ψ₀),
    isRegularLocalRing_localization_congr hce,
    SingLoc.isRegularLocalRing_localization_comap_iff e _, hM, not_not,
    Ideal.map_le_iff_le_comap]

open IsLocalRing in
/-- **The completed ideal of the double locus of the normalization.** Let `y ∈ D_ν` lie over `x`
with `𝒪̂_{X,x} ≅ M`, the non-regular primes of `M` being those containing `I`. If for every factor
`ψ : M → L` of the normalization of `M` the ring `L ⧸ I L` is regular of dimension `d`, then for
the factor map `ψ₀ : 𝒪̂_{X,x} → L = 𝒪̂_{X^ν,w}` compatible with the stalk map, the kernel of
`𝒪_{X^ν,w} → 𝒪_{D_ν,y}` extends to `I L`, and `𝒪_{D_ν,y}` is regular of dimension `d`. -/
private theorem exists_completion_data_normalization_of_model [IsReduced X]
    [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hsing : ∀ w : X, w ∈ MMP.Mori.smoothLocus sX ↔ IsRegularLocalRing (X.presheaf.stalk w))
    (E : (X.normalizationScheme hX).IdealSheafData) (hEred : IsReduced E.subscheme)
    (hE : ∀ w, w ∈ Set.range E.subschemeι ↔ X.normalization hX w ∉ MMP.Mori.smoothLocus sX)
    (y : E.subscheme) {M : Type u} [CommRing M]
    (e : CompletedLocalRing X (X.normalization hX (E.subschemeι y)) ≃+* M) (I : Ideal M)
    (d : WithBot ℕ∞)
    (hM : ∀ (q : Ideal M) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q) ↔ ¬ I ≤ q)
    (hL : ∀ {L : Type u} [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
      (ψ : M →+* L), (∀ l, ψ.IsIntegralElem l) →
        (∀ l, ∃ r s, s ∈ nonZeroDivisors M ∧ ψ s * l = ψ r) →
        (∀ s ∈ nonZeroDivisors M, ψ s ≠ 0) →
        IsRegularLocalRing (L ⧸ I.map ψ) ∧ ringKrullDim (L ⧸ I.map ψ) = d) :
    ∃ ψ₀ : CompletedLocalRing X (X.normalization hX (E.subschemeι y)) →+*
        AdicCompletion (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk (E.subschemeι y)))
          ((X.normalizationScheme hX).presheaf.stalk (E.subschemeι y)),
      ((∀ l, ψ₀.IsIntegralElem l) ∧ (∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ₀ s * l = ψ₀ r) ∧
        (∀ s ∈ nonZeroDivisors _, ψ₀ s ≠ 0)) ∧
      (∀ a : X.presheaf.stalk (X.normalization hX (E.subschemeι y)),
        ψ₀ (algebraMap _ _ a) = algebraMap _ _ (((X.normalization hX).stalkMap
          (E.subschemeι y)).hom a)) ∧
      (RingHom.ker (E.subschemeι.stalkMap y).hom).map (algebraMap _ (AdicCompletion
          (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk (E.subschemeι y)))
          ((X.normalizationScheme hX).presheaf.stalk (E.subschemeι y)))) =
        I.map (ψ₀.comp e.symm.toRingHom) ∧
      IsRegularLocalRing (E.subscheme.presheaf.stalk y) ∧
        ringKrullDim (E.subscheme.presheaf.stalk y) = d := by
  let w := E.subschemeι y
  have : IsFinite (X.normalization hX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have hexc := isExcellent_stalk_of_field (X.normalization hX ≫ sX) w
  have : IsNoetherianRing ((X.normalizationScheme hX).presheaf.stalk w) := hexc.1.1
  have : IsReduced (E.subscheme.presheaf.stalk y) := isReduced_stalk_of_isReduced _ y
  obtain ⟨hND, ψ₀, hint, hbir, hnz, hψ₀alg⟩ :=
    exists_completion_factor_normalization (sX := sX) hX w
  have hloc : IsLocalRing (AdicCompletion
      (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk w))
      ((X.normalizationScheme hX).presheaf.stalk w)) :=
    AdicCompletion.isLocalRing_of_fg (IsNoetherian.noetherian _)
  obtain ⟨h₁, h₂, h₃⟩ := props_comp_symm_of_ringEquiv ψ₀ e hint hbir hnz
  obtain ⟨hLreg, hLdim⟩ := @hL _ _ hloc hND.isDomain hND.isIntegrallyClosed _ h₁ h₂ h₃
  have : IsDomain (_ ⧸ I.map (ψ₀.comp e.symm.toRingHom)) :=
    @IsRegularLocalRing.isDomain _ _ hLreg
  have : (I.map (ψ₀.comp e.symm.toRingHom)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hV := ker_stalkMap_le_comap_iff_of_model hX hsing E hE y e I hM ψ₀ hψ₀alg
  obtain ⟨hreg, hdim⟩ := isRegularLocalRing_iff_and_ringKrullDim_eq_of_forall_le_comap_iff
    hexc.1.2.1 _ (E.subschemeι.stalkMap_surjective y) _ hV
  set eq := RingHom.quotientKerEquivOfSurjective (E.subschemeι.stalkMap_surjective y)
  have : Nontrivial (_ ⧸ RingHom.ker (E.subschemeι.stalkMap y).hom) := eq.toEquiv.nontrivial
  have : IsLocalRing (_ ⧸ RingHom.ker (E.subschemeι.stalkMap y).hom) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsReduced (_ ⧸ RingHom.ker (E.subschemeι.stalkMap y).hom) :=
    isReduced_of_injective eq.toRingHom eq.injective
  exact ⟨ψ₀, ⟨hint, hbir, hnz⟩, hψ₀alg, map_eq_of_forall_le_comap_iff hexc.1.2.1 _ _ hV,
    hreg.mpr hLreg, hdim.trans hLdim⟩

open IsLocalRing in
/-- **Rational residue fields of `D_ν`.** Let `y ∈ D_ν` lie over `x` with `𝒪̂_{X,x} ≅ M` as
`k`-algebras. If every factor of the normalization of `M` has residue field `k`, then so does
`𝒪_{D_ν,y}`. -/
private theorem exists_sub_mem_maximalIdeal_stalk_of_model [IsReduced X] [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (E : (X.normalizationScheme hX).IdealSheafData) (y : E.subscheme)
    {M : Type u} [CommRing M] [Algebra k M]
    (e : CompletedLocalRing X (X.normalization hX (E.subschemeι y)) ≃+* M)
    (he : ∀ c : k, e (algebraMap _ _ (stalkStructureMap sX (X.normalization hX (E.subschemeι y)) c))
      = algebraMap k M c)
    (hres : ∀ {L : Type u} [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
      (ψ : M →+* L), (∀ l, ψ.IsIntegralElem l) →
        (∀ l, ∃ r s, s ∈ nonZeroDivisors M ∧ ψ s * l = ψ r) →
        (∀ s ∈ nonZeroDivisors M, ψ s ≠ 0) →
        ∀ l : L, ∃ c : k, l - ψ (algebraMap k M c) ∈ maximalIdeal L)
    (b : E.subscheme.presheaf.stalk y) : ∃ c : k,
      b - stalkStructureMap (E.subschemeι ≫ X.normalization hX ≫ sX) y c ∈
        maximalIdeal (E.subscheme.presheaf.stalk y) := by
  let w := E.subschemeι y
  obtain ⟨hND, ψ₀, hint, hbir, hnz, hψ₀alg⟩ :=
    exists_completion_factor_normalization (sX := sX) hX w
  obtain ⟨hLloc, -⟩ := isLocalRing_and_isNormalDomain_adicCompletion_normalization
    (sX := sX) hX w
  obtain ⟨h₁, h₂, h₃⟩ := props_comp_symm_of_ringEquiv ψ₀ e hint hbir hnz
  obtain ⟨a, rfl⟩ := E.subschemeι.stalkMap_surjective y b
  obtain ⟨c, hc⟩ := @hres _ _ hLloc hND.isDomain hND.isIntegrallyClosed _ h₁ h₂ h₃
    (algebraMap _ _ a)
  refine ⟨c, ?_⟩
  have hψc : (ψ₀.comp e.symm.toRingHom) (algebraMap k M c) = algebraMap _ (AdicCompletion
      (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk w))
      ((X.normalizationScheme hX).presheaf.stalk w))
      (stalkStructureMap (X.normalization hX ≫ sX) w c) := by
    rw [RingHom.comp_apply, ← he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, hψ₀alg, stalkMap_stalkStructureMap]
  rw [hψc, ← map_sub] at hc
  have hmem : a - stalkStructureMap (X.normalization hX ≫ sX) w c ∈
      maximalIdeal ((X.normalizationScheme hX).presheaf.stalk w) := by
    by_contra hm
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hm
    rw [mem_maximalIdeal, mem_nonunits_iff] at hc
    exact hc (hm.map _)
  have := map_nonunit (E.subschemeι.stalkMap y).hom _ hmem
  rwa [map_sub, stalkMap_stalkStructureMap] at this

open IsLocalRing in
/-- **The length of a fibre ring of `ν|_{D_ν}` over a model point.** Let `y ∈ D_ν` lie over
`z ∈ D_X`, with `𝒪̂_{X,x} ≅ M` as in `exists_completion_data_normalization_of_model`, `I ≤ 𝔪_M`.
If for every factor `ψ : M → L` of the normalization of `M` the fibre `L ⧸ 𝔪_M L` has length `ℓ`,
then so does the fibre ring `𝒪_{D_ν,y} ⧸ 𝔪_z 𝒪_{D_ν,y}`. -/
private theorem length_fibre_of_model [IsReduced X] [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hsing : ∀ w : X, w ∈ MMP.Mori.smoothLocus sX ↔ IsRegularLocalRing (X.presheaf.stalk w))
    (D : X.IdealSheafData) (E : (X.normalizationScheme hX).IdealSheafData)
    (hEred : IsReduced E.subscheme)
    (hE : ∀ w, w ∈ Set.range E.subschemeι ↔ X.normalization hX w ∉ MMP.Mori.smoothLocus sX)
    (φ : E.subscheme ⟶ D.subscheme) (hφ : φ ≫ D.subschemeι = E.subschemeι ≫ X.normalization hX)
    (hfin : IsFinite φ) (y : E.subscheme) {M : Type u} [CommRing M] [IsLocalRing M]
    (e : CompletedLocalRing X (X.normalization hX (E.subschemeι y)) ≃+* M) (I : Ideal M)
    (d : WithBot ℕ∞)
    (hM : ∀ (q : Ideal M) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q) ↔ ¬ I ≤ q)
    (hL : ∀ {L : Type u} [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
      (ψ : M →+* L), (∀ l, ψ.IsIntegralElem l) →
        (∀ l, ∃ r s, s ∈ nonZeroDivisors M ∧ ψ s * l = ψ r) →
        (∀ s ∈ nonZeroDivisors M, ψ s ≠ 0) →
        IsRegularLocalRing (L ⧸ I.map ψ) ∧ ringKrullDim (L ⧸ I.map ψ) = d)
    (hIm : I ≤ maximalIdeal M) (ℓ : ℕ∞)
    (hℓ : ∀ {L : Type u} [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
      (ψ : M →+* L), (∀ l, ψ.IsIntegralElem l) →
        (∀ l, ∃ r s, s ∈ nonZeroDivisors M ∧ ψ s * l = ψ r) →
        (∀ s ∈ nonZeroDivisors M, ψ s ≠ 0) →
        Module.length (L ⧸ (maximalIdeal M).map ψ) (L ⧸ (maximalIdeal M).map ψ) = ℓ) :
    Module.length (E.subscheme.presheaf.stalk y ⧸
        (maximalIdeal (D.subscheme.presheaf.stalk (φ y))).map (φ.stalkMap y).hom)
      (E.subscheme.presheaf.stalk y ⧸
        (maximalIdeal (D.subscheme.presheaf.stalk (φ y))).map (φ.stalkMap y).hom) = ℓ := by
  obtain ⟨ψ₀, ⟨hint, hbir, hnz⟩, hψ₀alg, hK, -⟩ :=
    exists_completion_data_normalization_of_model hX hsing E hEred hE y e I d hM hL
  let w := E.subschemeι y
  have : IsFinite (X.normalization hX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have : LocallyOfFiniteType (X.normalization hX ≫ sX) := inferInstance
  have hexc : IsExcellent ((X.normalizationScheme hX).presheaf.stalk w) :=
    isExcellent_stalk_of_field (X.normalization hX ≫ sX) w
  have : IsNoetherianRing ((X.normalizationScheme hX).presheaf.stalk w) := hexc.1.1
  have hexcE : IsExcellent (E.subscheme.presheaf.stalk y) :=
    isExcellent_stalk_of_field (E.subschemeι ≫ X.normalization hX ≫ sX) y
  have : IsNoetherianRing (E.subscheme.presheaf.stalk y) := hexcE.1.1
  obtain ⟨hLloc, hND⟩ := isLocalRing_and_isNormalDomain_adicCompletion_normalization
    (sX := sX) hX w
  set ψ := ψ₀.comp e.symm.toRingHom
  have hℓψ := @hℓ _ _ hLloc hND.isDomain hND.isIntegrallyClosed ψ
    ((props_comp_symm_of_ringEquiv ψ₀ e hint hbir hnz).1)
    ((props_comp_symm_of_ringEquiv ψ₀ e hint hbir hnz).2.1)
    ((props_comp_symm_of_ringEquiv ψ₀ e hint hbir hnz).2.2)
  -- the rings of the square
  set g := ((X.normalization hX).stalkMap w).hom
  set πB := (E.subschemeι.stalkMap y).hom
  set f := (φ.stalkMap y).hom
  have hpt : X.normalization hX w = D.subschemeι (φ y) := by
    rw [← Scheme.Hom.comp_apply, ← hφ, Scheme.Hom.comp_apply]
  set c := (X.presheaf.stalkCongr (.of_eq hpt.symm)).commRingCatIsoToRingEquiv
  set πA := (D.subschemeι.stalkMap (φ y)).hom.comp c.symm.toRingHom
  have h5 : f.comp (D.subschemeι.stalkMap (φ y)).hom =
      (πB.comp g).comp (X.presheaf.stalkCongr (.of_eq hpt.symm)).hom.hom := by
    have h2 := Scheme.Hom.stalkMap_comp φ D.subschemeι y
    have h3 := Scheme.Hom.stalkMap_congr_hom (φ ≫ D.subschemeι)
      (E.subschemeι ≫ X.normalization hX) hφ y
    have h4 := Scheme.Hom.stalkMap_comp E.subschemeι (X.normalization hX) y
    rw [h2, h4] at h3
    rw [← CommRingCat.hom_comp, h3]
    rfl
  have hsq : f.comp πA = πB.comp g := by
    refine RingHom.ext fun r => ?_
    have := RingHom.congr_fun h5 (c.symm r)
    simp only [RingHom.comp_apply] at this ⊢
    change f ((D.subschemeι.stalkMap (φ y)).hom (c.symm r)) = _
    rw [this]
    congr 2
    exact c.apply_symm_apply r
  have hπA : Function.Surjective πA :=
    (D.subschemeι.stalkMap_surjective (φ y)).comp c.symm.surjective
  have hπB : Function.Surjective πB := E.subschemeι.stalkMap_surjective y
  -- the fibre ring as a quotient of `𝒪_{X^ν,w}`
  set J := RingHom.ker πB ⊔ (maximalIdeal (X.presheaf.stalk (X.normalization hX w))).map g
  have hJm : (maximalIdeal (D.subscheme.presheaf.stalk (φ y))).map f = J.map πB := by
    rw [Ideal.map_sup, Ideal.map_map, ← hsq, ← Ideal.map_map,
      IsLocalRing.map_maximalIdeal_of_surjective πA hπA,
      (Ideal.map_eq_bot_iff_le_ker πB).mpr le_rfl, bot_sup_eq]
  obtain ⟨eJ⟩ := nonempty_ringEquiv_quotient_map_of_surjective πB hπB J le_sup_left
  rw [hJm, ← length_self_eq_of_ringEquiv eJ]
  have hJne : J ≠ ⊤ := by
    intro hJ
    have h := IsLocalRing.map_maximalIdeal_le f
    rw [hJm, hJ, Ideal.map_top] at h
    exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h)
  have : LocallyQuasiFinite φ := inferInstance
  have hdim0 := ringKrullDim_quotient_stalk_eq_zero_of_locallyQuasiFinite φ y
  have : Nontrivial (E.subscheme.presheaf.stalk y ⧸
      (maximalIdeal (D.subscheme.presheaf.stalk (φ y))).map f) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [hJm]; exact fun h => hJne (by
      have := congrArg (Ideal.comap πB) h
      rwa [Ideal.comap_map_of_surjective' πB hπB, sup_eq_left.mpr le_sup_left, Ideal.comap_top]
        at this))
  have : IsArtinianRing (E.subscheme.presheaf.stalk y ⧸
      (maximalIdeal (D.subscheme.presheaf.stalk (φ y))).map f) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr
      ⟨inferInstance, ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0⟩
  rw [hJm] at this
  have : IsArtinianRing ((X.normalizationScheme hX).presheaf.stalk w ⧸ J) :=
    eJ.symm.isArtinianRing
  rw [length_quotient_eq_length_quotient_map_adicCompletion J hJne]
  have hexcX : IsExcellent (X.presheaf.stalk (X.normalization hX w)) :=
    isExcellent_stalk_of_field sX _
  have : IsNoetherianRing (X.presheaf.stalk (X.normalization hX w)) := hexcX.1.1
  have : IsLocalRing (CompletedLocalRing X (X.normalization hX w)) :=
    AdicCompletion.isLocalRing_of_fg (IsNoetherian.noetherian _)
  have hmapJ : J.map (algebraMap _ (AdicCompletion
      (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk w))
      ((X.normalizationScheme hX).presheaf.stalk w))) = (maximalIdeal M).map ψ := by
    rw [Ideal.map_sup, hK, Ideal.map_map]
    have hcomp : (algebraMap ((X.normalizationScheme hX).presheaf.stalk w) (AdicCompletion
        (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk w))
        ((X.normalizationScheme hX).presheaf.stalk w))).comp g =
        ψ₀.comp (algebraMap _ (CompletedLocalRing X (X.normalization hX w))) :=
      RingHom.ext fun a => (hψ₀alg a).symm
    rw [hcomp, ← Ideal.map_map (algebraMap (X.presheaf.stalk (X.normalization hX w))
        (CompletedLocalRing X (X.normalization hX w))) ψ₀,
      ← AdicCompletion.maximalIdeal_eq_map,
      ← IsLocalRing.map_maximalIdeal_of_surjective e.symm.toRingHom e.symm.surjective,
      Ideal.map_map]
    exact sup_eq_right.mpr (Ideal.map_mono hIm)
  rw [hmapJ]
  exact hℓψ

open Stacks.AlgebraicGeometry.Normalization in
/-- **`ν|_{D_ν}` is flat at the closed points of `D_ν`.** At a closed point `y` over `x` both
`𝒪_{D_X,φ y}` and `𝒪_{D_ν,y}` are regular local rings of dimension `n - 1`, read on the completed
models, and `φ` is finite; miracle flatness applies. -/
private theorem flat_stalkMap_of_isClosed {n : ℕ} (h : MMP.Flips.IsSemismooth sX n)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (D : X.IdealSheafData) (E : (normalizationScheme X hX).IdealSheafData)
    [IsReduced D.subscheme] [IsReduced E.subscheme]
    (hD : ∀ w, w ∈ Set.range D.subschemeι ↔ w ∉ MMP.Mori.smoothLocus sX)
    (hE : ∀ w, w ∈ Set.range E.subschemeι ↔ normalization X hX w ∉ MMP.Mori.smoothLocus sX)
    (φ : E.subscheme ⟶ D.subscheme) (hφ : φ ≫ D.subschemeι = E.subschemeι ≫ normalization X hX)
    (y : E.subscheme) (hy : IsClosed ({y} : Set E.subscheme)) :
    (φ.stalkMap y).hom.Flat := by
  obtain ⟨⟨⟨-, hlft, -⟩, hred, -⟩, hpts⟩ := h
  have : LocallyOfFiniteType sX := hlft
  have hsing := mem_smoothLocus_iff_isRegularLocalRing hpts
  have : IsFinite (normalization X hX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have : IsFinite (φ ≫ D.subschemeι) := by rw [hφ]; infer_instance
  have : IsFinite φ := IsFinite.of_comp φ D.subschemeι
  have hpt : normalization X hX (E.subschemeι y) = D.subschemeι (φ y) := by
    rw [← Scheme.Hom.comp_apply, ← hφ, Scheme.Hom.comp_apply]
  have hcl : IsClosed ({D.subschemeι (φ y)} : Set X) := by
    rw [← Set.image_singleton, ← Set.image_singleton]
    exact D.subschemeι.isClosedEmbedding.isClosedMap _ (φ.isClosedMap _ hy)
  have hns : D.subschemeι (φ y) ∉ MMP.Mori.smoothLocus sX := (hD _).mp ⟨_, rfl⟩
  have key : ∀ d : WithBot ℕ∞,
      IsRegularLocalRing (D.subscheme.presheaf.stalk (φ y)) ∧
        ringKrullDim (D.subscheme.presheaf.stalk (φ y)) = d →
      IsRegularLocalRing (E.subscheme.presheaf.stalk y) ∧
        ringKrullDim (E.subscheme.presheaf.stalk y) = d → (φ.stalkMap y).hom.Flat := by
    rintro d ⟨h1, h2⟩ ⟨h3, h4⟩
    exact flat_stalkMap_of_ringKrullDim_quotient_eq_zero φ y
      (ringKrullDim_quotient_stalk_eq_zero_of_locallyQuasiFinite φ y) (h4.trans h2.symm)
  rcases hpts _ hcl with hs | hdnc | hp
  · exact absurd hs hns
  · obtain ⟨m, rfl⟩ := exists_eq_add_one_of_dnc (sX := sX) hX hdnc.2.2
    have hmodE := hdnc.2.2
    rw [← hpt] at hmodE
    let := (stalkStructureMap sX (D.subschemeι (φ y))).toAlgebra
    obtain ⟨e⟩ := hdnc.2.2
    let := (stalkStructureMap sX (normalization X hX (E.subschemeι y))).toAlgebra
    obtain ⟨e'⟩ := hmodE
    exact key m
      (isRegularLocalRing_and_ringKrullDim_stalk_of_model hsing D hD (φ y) e.toRingEquiv _ m
        (fun q _ => isRegularLocalRing_localization_dnc_iff_not_le q)
        isRegularLocalRing_and_ringKrullDim_quotient_dnc)
      (exists_completion_data_normalization_of_model hX hsing E ‹_› hE y
        e'.toRingEquiv _ m (fun q _ => isRegularLocalRing_localization_dnc_iff_not_le q)
        (fun ψ h1 h2 h3 => isRegularLocalRing_and_ringKrullDim_quotient_map_of_dnc ψ h1 h2 h3)
        ).choose_spec.2.2.2
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hp.1; omega⟩
    have hmodE := hp.2.2.2
    rw [← hpt] at hmodE
    let := (stalkStructureMap sX (D.subschemeι (φ y))).toAlgebra
    obtain ⟨e⟩ := hp.2.2.2
    let := (stalkStructureMap sX (normalization X hX (E.subschemeι y))).toAlgebra
    obtain ⟨e'⟩ := hmodE
    exact key ((m + 1 : ℕ) : WithBot ℕ∞)
      (isRegularLocalRing_and_ringKrullDim_stalk_of_model hsing D hD (φ y)
        (M := MvPowerSeries (Fin (m + 3)) k ⧸ Ideal.span
          {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
            MvPowerSeries (Fin (m + 3)) k)}) e.toRingEquiv _ _
        (fun q _ => isRegularLocalRing_localization_pinch_iff_not_le q)
        isRegularLocalRing_and_ringKrullDim_quotient_pinch)
      (exists_completion_data_normalization_of_model hX hsing E ‹_› hE y
        (M := MvPowerSeries (Fin (m + 3)) k ⧸ Ideal.span
          {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
            MvPowerSeries (Fin (m + 3)) k)})
        e'.toRingEquiv _ _ (fun q _ => isRegularLocalRing_localization_pinch_iff_not_le q)
        (fun ψ h1 h2 h3 => isRegularLocalRing_and_ringKrullDim_quotient_map_of_pinch ψ h1 h2 h3)
        ).choose_spec.2.2.2

open Stacks.AlgebraicGeometry.Normalization IsLocalRing in
/-- **The rank of `ν|_{D_ν}` at a point of `D_X`** is the number of points of `X^ν` over it times
the common length of the fibre rings, when the residue fields of `D_ν` over it are `k`. -/
private theorem finrank_eq_mul_of_forall [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (D : X.IdealSheafData) (E : (normalizationScheme X hX).IdealSheafData)
    (hE : ∀ w, w ∈ Set.range E.subschemeι ↔ normalization X hX w ∉ MMP.Mori.smoothLocus sX)
    (φ : E.subscheme ⟶ D.subscheme) (hφ : φ ≫ D.subschemeι = E.subschemeι ≫ normalization X hX)
    [Flat φ] [IsFinite φ] (z : D.subscheme)
    (hns : D.subschemeι z ∉ MMP.Mori.smoothLocus sX) (c ℓ : ℕ) (hcpos : 0 < c)
    (hc : Nat.card ((normalization X hX).base ⁻¹' {D.subschemeι z}) = c)
    (hlen : ∀ y : E.subscheme, φ y = z →
      Module.length (E.subscheme.presheaf.stalk y ⧸
          (maximalIdeal (D.subscheme.presheaf.stalk (φ y))).map (φ.stalkMap y).hom)
        (E.subscheme.presheaf.stalk y ⧸
          (maximalIdeal (D.subscheme.presheaf.stalk (φ y))).map (φ.stalkMap y).hom) = ℓ)
    (hres : ∀ y : E.subscheme, φ y = z → ∀ b : E.subscheme.presheaf.stalk y, ∃ c : k,
      b - stalkStructureMap (E.subschemeι ≫ normalization X hX ≫ sX) y c ∈
        maximalIdeal (E.subscheme.presheaf.stalk y)) :
    φ.finrank z = c * ℓ := by
  have hcomp : φ ≫ D.subschemeι ≫ sX = E.subschemeι ≫ normalization X hX ≫ sX := by
    rw [← Category.assoc, hφ, Category.assoc]
  rw [finrank_eq_finsum_length_quotient (D.subschemeι ≫ sX) φ z (fun y hy b => by
    rw [hcomp]; exact hres y hy b)]
  -- the fibre of `φ` over `z` is the fibre of `ν` over `x`
  let F : φ ⁻¹' {z} → (normalization X hX).base ⁻¹' {D.subschemeι z} := fun y =>
    ⟨E.subschemeι y.1, by
      change normalization X hX (E.subschemeι y.1) = D.subschemeι z
      rw [← Scheme.Hom.comp_apply, ← hφ, Scheme.Hom.comp_apply]
      exact congrArg _ y.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun a b hab => Subtype.ext (E.subschemeι.isEmbedding.injective
      (congrArg Subtype.val hab :)), fun ⟨w, hw⟩ => ?_⟩
    have hw' : normalization X hX w = D.subschemeι z := hw
    obtain ⟨y, rfl⟩ := (hE w).mpr (by rw [hw']; exact hns)
    refine ⟨⟨y, ?_⟩, rfl⟩
    change φ y = z
    refine D.subschemeι.isEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply]
    exact hw'
  have hcard : Nat.card (φ ⁻¹' {z}) = c := (Nat.card_congr (Equiv.ofBijective F hF)).trans hc
  have hterm : ∀ y : φ ⁻¹' {z}, (Module.length (E.subscheme.presheaf.stalk y.1 ⧸
      (maximalIdeal (D.subscheme.presheaf.stalk (φ y.1))).map (φ.stalkMap y.1).hom)
      (E.subscheme.presheaf.stalk y.1 ⧸
      (maximalIdeal (D.subscheme.presheaf.stalk (φ y.1))).map (φ.stalkMap y.1).hom)).toNat = ℓ :=
    fun y => by rw [hlen y.1 y.2]; rfl
  rw [finsum_congr hterm]
  have : Finite (φ ⁻¹' {z}) := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite (φ ⁻¹' {z})
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, hcard]

open Stacks.AlgebraicGeometry.Normalization IsLocalRing in
/-- **`ν|_{D_ν}` has rank `2` at the closed points of `D_X`**: over a double normal crossing
point there are two points of `X^ν`, with fibre rings of length `1`; over a pinch point there is
one, with fibre ring `k[u] ⧸ (u²)` of length `2`. All residue fields are `k`. -/
private theorem finrank_of_isClosed {n : ℕ} (h : MMP.Flips.IsSemismooth sX n)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (D : X.IdealSheafData) (E : (normalizationScheme X hX).IdealSheafData)
    [IsReduced D.subscheme] [IsReduced E.subscheme]
    (hD : ∀ w, w ∈ Set.range D.subschemeι ↔ w ∉ MMP.Mori.smoothLocus sX)
    (hE : ∀ w, w ∈ Set.range E.subschemeι ↔ normalization X hX w ∉ MMP.Mori.smoothLocus sX)
    (φ : E.subscheme ⟶ D.subscheme) (hφ : φ ≫ D.subschemeι = E.subschemeι ≫ normalization X hX)
    [Flat φ] [IsFinite φ] (z : D.subscheme) (hz : IsClosed ({z} : Set D.subscheme)) :
    φ.finrank z = 2 := by
  obtain ⟨⟨⟨-, hlft, -⟩, hred, -⟩, hpts⟩ := h
  have : LocallyOfFiniteType sX := hlft
  have hsing := mem_smoothLocus_iff_isRegularLocalRing hpts
  have hcl : IsClosed ({D.subschemeι z} : Set X) := by
    rw [← Set.image_singleton]
    exact D.subschemeι.isClosedEmbedding.isClosedMap _ hz
  have hns : D.subschemeι z ∉ MMP.Mori.smoothLocus sX := (hD _).mp ⟨_, rfl⟩
  have hpt : ∀ y, φ y = z → normalization X hX (E.subschemeι y) = D.subschemeι z := fun y hy => by
    rw [← Scheme.Hom.comp_apply, ← hφ, Scheme.Hom.comp_apply, hy]
  have hlocM : ∀ {M : Type u} [CommRing M] (x : X), (CompletedLocalRing X x ≃+* M) →
      IsLocalRing M := fun {M} _ x e => by
    have hexc : IsExcellent (X.presheaf.stalk x) :=
      isExcellent_stalk_of_field sX _
    have : IsNoetherianRing (X.presheaf.stalk x) := hexc.1.1
    have : IsLocalRing (CompletedLocalRing X x) :=
      AdicCompletion.isLocalRing_of_fg (IsNoetherian.noetherian _)
    have : Nontrivial M := e.symm.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' e.toRingHom e.surjective
  rcases hpts _ hcl with hs | hdnc | hp
  · exact absurd hs hns
  · obtain ⟨m, rfl⟩ := exists_eq_add_one_of_dnc (sX := sX) hX hdnc.2.2
    have hIm : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1 + 1)) k),
        MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span
          {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)})) ≠ ⊤ := by
      have := (isRegularLocalRing_and_ringKrullDim_quotient_dnc (k := k) (m := m)).1
      exact Ideal.Quotient.nontrivial_iff.mp inferInstance
    have := finrank_eq_mul_of_forall hX D E hE φ hφ z hns 2 1 two_pos
      (natCard_preimage_normalization_of_dnc (sX := sX) hX hdnc.2.2)
      (fun y hy => by
        have hmod := hdnc.2.2
        rw [← hpt y hy] at hmod
        let := (stalkStructureMap sX (normalization X hX (E.subschemeι y))).toAlgebra
        obtain ⟨e⟩ := hmod
        have := hlocM _ e.toRingEquiv
        exact length_fibre_of_model hX hsing D E ‹_› hE φ hφ ‹_› y e.toRingEquiv _ m
          (fun q _ => isRegularLocalRing_localization_dnc_iff_not_le q)
          (fun ψ h1 h2 h3 => isRegularLocalRing_and_ringKrullDim_quotient_map_of_dnc ψ h1 h2 h3)
          (IsLocalRing.le_maximalIdeal hIm) 1
          (fun ψ h1 h2 h3 => length_quotient_map_maximalIdeal_of_dnc ψ h1 h2 h3))
      (fun y hy b => by
        have hmod := hdnc.2.2
        rw [← hpt y hy] at hmod
        let := (stalkStructureMap sX (normalization X hX (E.subschemeι y))).toAlgebra
        obtain ⟨e⟩ := hmod
        have := hlocM _ e.toRingEquiv
        exact exists_sub_mem_maximalIdeal_stalk_of_model hX E y e.toRingEquiv
          e.commutes
          (fun ψ h1 h2 h3 l => exists_sub_mem_maximalIdeal_of_dnc ψ h1 h2 h3 l) b)
    rw [this]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hp.1; omega⟩
    have hIm : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 3)) k),
        MvPowerSeries.X 2}).map (Ideal.Quotient.mk (Ideal.span
          {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
            MvPowerSeries (Fin (m + 3)) k)})) ≠ ⊤ := by
      have := (isRegularLocalRing_and_ringKrullDim_quotient_pinch (k := k) (m := m)).1
      exact Ideal.Quotient.nontrivial_iff.mp inferInstance
    have := finrank_eq_mul_of_forall hX D E hE φ hφ z hns 1 2 one_pos
      (natCard_preimage_normalization_of_pinch (sX := sX) hX hp.2.2.2)
      (fun y hy => by
        have hmod := hp.2.2.2
        rw [← hpt y hy] at hmod
        let := (stalkStructureMap sX (normalization X hX (E.subschemeι y))).toAlgebra
        obtain ⟨e⟩ := hmod
        have := hlocM _ e.toRingEquiv
        exact length_fibre_of_model hX hsing D E ‹_› hE φ hφ ‹_› y
          (M := MvPowerSeries (Fin (m + 3)) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
              MvPowerSeries (Fin (m + 3)) k)}) e.toRingEquiv _ _
          (fun q _ => isRegularLocalRing_localization_pinch_iff_not_le q)
          (fun ψ h1 h2 h3 => isRegularLocalRing_and_ringKrullDim_quotient_map_of_pinch ψ h1 h2 h3)
          (IsLocalRing.le_maximalIdeal hIm) 2
          (fun ψ h1 h2 h3 => length_quotient_map_maximalIdeal_of_pinch ψ h1 h2 h3))
      (fun y hy b => by
        have hmod := hp.2.2.2
        rw [← hpt y hy] at hmod
        let := (stalkStructureMap sX (normalization X hX (E.subschemeι y))).toAlgebra
        obtain ⟨e⟩ := hmod
        exact exists_sub_mem_maximalIdeal_stalk_of_model hX E y e.toRingEquiv
          e.commutes
          (fun ψ h1 h2 h3 l => exists_sub_mem_maximalIdeal_of_pinch ψ h1 h2 h3 l) b)
    rw [this]

/-- Flatness and degree `2` of `ν|_{D_ν} : D_ν ⟶ D_X`: both are read at closed points. -/
private theorem flat_and_finrank_subschemeMap_normalization {n : ℕ}
    (h : MMP.Flips.IsSemismooth sX n)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Flat (Scheme.IdealSheafData.subschemeMap
        (Scheme.IdealSheafData.vanishingIdeal
          ((MMP.Resolution.reducedSingularLocus sX).comap
            (Stacks.AlgebraicGeometry.Normalization.normalization X hX)).support)
        (MMP.Resolution.reducedSingularLocus sX)
        (Stacks.AlgebraicGeometry.Normalization.normalization X hX)
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl))) ∧
      Scheme.Hom.finrank (Scheme.IdealSheafData.subschemeMap
        (Scheme.IdealSheafData.vanishingIdeal
          ((MMP.Resolution.reducedSingularLocus sX).comap
            (Stacks.AlgebraicGeometry.Normalization.normalization X hX)).support)
        (MMP.Resolution.reducedSingularLocus sX)
        (Stacks.AlgebraicGeometry.Normalization.normalization X hX)
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl))) = 2 := by
  have : LocallyOfFiniteType sX := h.1.1.2.1
  set ν := Stacks.AlgebraicGeometry.Normalization.normalization X hX
  set D := MMP.Resolution.reducedSingularLocus sX
  set E := Scheme.IdealSheafData.vanishingIdeal (D.comap ν).support
  set φ := Scheme.IdealSheafData.subschemeMap E D ν
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl))
  have hφ : φ ≫ D.subschemeι = E.subschemeι ≫ ν :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have : IsFinite ν :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have : IsFinite φ := isFinite_subschemeMap _ _ _ _
  have : IsReduced D.subscheme := by
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme
    infer_instance
  have : IsReduced E.subscheme := by
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme
    infer_instance
  have hD : ∀ w, w ∈ Set.range D.subschemeι ↔ w ∉ MMP.Mori.smoothLocus sX := fun w => by
    rw [Scheme.IdealSheafData.range_subschemeι, MMP.Resolution.support_reducedSingularLocus]
    rfl
  have hE : ∀ w, w ∈ Set.range E.subschemeι ↔ ν w ∉ MMP.Mori.smoothLocus sX := fun w => by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.support_comap, ← hD, Scheme.IdealSheafData.range_subschemeι]
    rfl
  have : JacobsonSpace E.subscheme := LocallyOfFiniteType.jacobsonSpace (E.subschemeι ≫ ν ≫ sX)
  have : JacobsonSpace D.subscheme := LocallyOfFiniteType.jacobsonSpace (D.subschemeι ≫ sX)
  have : IsLocallyNoetherian D.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ sX)
  have hflat : Flat φ := MMP.Flips.flat_of_flat_stalkMap_of_isClosed φ fun y hy =>
    flat_stalkMap_of_isClosed h hX D E hD hE φ hφ y hy
  refine ⟨hflat, ?_⟩
  exact MMP.Flips.finrank_eq_of_finrank_eq_of_isClosed φ 2 fun z hz =>
    finrank_of_isClosed h hX D E hD hE φ hφ z hz

end SemismoothDoubleCover

/-- **The double locus of the normalization is a double cover** (FA 12.2.1(2)). Let `X` be a
semismooth `n`-fold over `k` and `ν : X^ν ⟶ X` its normalization. Then the restriction of `ν` to
the reduced preimage `D_ν = ν⁻¹(D_X)_red` of the reduced singular locus `D_X` of `X` is a finite
flat morphism `D_ν ⟶ D_X` of degree `2`. -/
@[mmp "lem_fa12a_semismooth_double_cover_pinch"]
public theorem IsSemismooth.isFinite_flat_finrank_subschemeMap_normalization {n : ℕ}
    (h : IsSemismooth sX n)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsFinite (Scheme.IdealSheafData.subschemeMap
        (Scheme.IdealSheafData.vanishingIdeal
          ((MMP.Resolution.reducedSingularLocus sX).comap
            (Stacks.AlgebraicGeometry.Normalization.normalization X hX)).support)
        (MMP.Resolution.reducedSingularLocus sX)
        (Stacks.AlgebraicGeometry.Normalization.normalization X hX)
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl))) ∧
      Flat (Scheme.IdealSheafData.subschemeMap
        (Scheme.IdealSheafData.vanishingIdeal
          ((MMP.Resolution.reducedSingularLocus sX).comap
            (Stacks.AlgebraicGeometry.Normalization.normalization X hX)).support)
        (MMP.Resolution.reducedSingularLocus sX)
        (Stacks.AlgebraicGeometry.Normalization.normalization X hX)
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl))) ∧
      Scheme.Hom.finrank (Scheme.IdealSheafData.subschemeMap
        (Scheme.IdealSheafData.vanishingIdeal
          ((MMP.Resolution.reducedSingularLocus sX).comap
            (Stacks.AlgebraicGeometry.Normalization.normalization X hX)).support)
        (MMP.Resolution.reducedSingularLocus sX)
        (Stacks.AlgebraicGeometry.Normalization.normalization X hX)
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl))) = 2 := by
  have : LocallyOfFiniteType sX := h.1.1.2.1
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization X hX) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  exact ⟨SemismoothDoubleCover.isFinite_subschemeMap _ _ _ _,
    SemismoothDoubleCover.flat_and_finrank_subschemeMap_normalization h hX⟩

end DoubleLocus

/-! ### Gluing an `n`-fold with double normal crossings from its normalization -/

variable {U : Scheme.{u}}

namespace DncGluing

open MMP.Mori Stacks.AlgebraicGeometry.Normalization

/-- An `n`-fold all of whose closed points are smooth or double normal crossing points is
semismooth. -/
private theorem isSemismooth_of_forall_smooth_or_dnc (sU : U ⟶ Spec (.of k)) {n : ℕ}
    (hU : IsNFold sU n)
    (hpts : ∀ x : U, IsClosed ({x} : Set U) →
      x ∈ smoothLocus sU ∨ IsDoubleNormalCrossingPoint sU n x) :
    IsSemismooth sU n :=
  ⟨hU, fun x hx => (hpts x hx).imp_right Or.inl⟩

/-! ### Dimension bounds -/

/-- `ht 𝔭 + dim R/𝔭 ≤ dim R` for a prime `𝔭`. -/
private theorem height_add_ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R)
    [I.IsPrime] : (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I) ≤ ringKrullDim R := by
  let p : PrimeSpectrum R := ⟨I, inferInstance⟩
  have : Nonempty (PrimeSpectrum R) := ⟨p⟩
  have hz : PrimeSpectrum.zeroLocus (I : Set R) = Set.Ici p := by
    ext q
    exact Iff.rfl
  rw [ringKrullDim_quotient, hz, ← Order.coheight_eq_krullDim_Ici,
    show I.height = Order.height p from PrimeSpectrum.height_eq_orderHeight p, ← WithBot.coe_add]
  change _ ≤ Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr
    (le_iSup (fun x : PrimeSpectrum R => Order.height x + Order.coheight x) p)

private theorem le_one_of_add_le_natCast_add_one {a : ℕ∞} {m : ℕ}
    (h : (a : WithBot ℕ∞) + (m : WithBot ℕ∞) ≤ ((m + 1 : ℕ) : WithBot ℕ∞)) :
    (a : WithBot ℕ∞) ≤ 1 := by
  induction a using ENat.recTopCoe with
  | top =>
    exfalso
    have h' : ((⊤ + m : ℕ∞) : WithBot ℕ∞) ≤ ((m + 1 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
    rw [WithBot.coe_le_coe, top_add] at h'
    exact absurd h' (by simpa using (ENat.coe_ne_top (m + 1)).symm)
  | coe a =>
    have : a + m ≤ m + 1 := by exact_mod_cast h
    exact_mod_cast (by omega : a ≤ 1)

private theorem le_natCast_of_add_one_le {d : WithBot ℕ∞} {n : ℕ}
    (h : d + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) : d ≤ n := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((n + 1 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_le_coe, top_add] at h'
      exact absurd h' (by simpa using (ENat.coe_ne_top (n + 1)).symm)
    | coe a =>
      have : a + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : a ≤ n)

/-- A reduced Noetherian local ring of dimension at most zero is a field, hence regular. -/
private theorem isRegularLocalRing_of_ringKrullDim_le_zero (A : Type*) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsReduced A] (h : ringKrullDim A ≤ 0) :
    IsRegularLocalRing A := by
  have : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr (by simpa using h)
  have hf : IsField A := Ring.KrullDimLE.isField_of_isReduced
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hf]
  simpa using ringKrullDim_nonneg_of_nontrivial (R := A)

/-- The local ring at a double normal crossing point of an `n`-fold has dimension at most `n`:
its completion is `k[[x₀, …, xₙ]]/(x₀x₁)`. -/
private theorem ringKrullDim_stalk_le_of_isDoubleNormalCrossingPoint (sU : U ⟶ Spec (.of k))
    {n : ℕ} [LocallyOfFiniteType sU] (x : U) (hd : IsDoubleNormalCrossingPoint sU n x) :
    ringKrullDim (U.presheaf.stalk x) ≤ n := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian sU
  letI := (stalkStructureMap sU x).toAlgebra
  obtain ⟨e⟩ := hd.2.2
  have : IsRegularLocalRing (MvPowerSeries (Fin (n + 1)) k) := MvPowerSeries.isRegularLocalRing k _
  have : IsDomain (MvPowerSeries (Fin (n + 1)) k) := IsRegularLocalRing.isDomain _
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mul_mem (MvPowerSeries.X_mem_nonzeroDivisors (R := k) (σ := Fin (n + 1)) (i := 0))
      (MvPowerSeries.X_mem_nonzeroDivisors (i := 1)))
  rw [MvPowerSeries.ringKrullDim_eq] at h1
  rw [_root_.ringKrullDim_adicCompletion_maximalIdeal (A := U.presheaf.stalk x),
    ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  exact le_natCast_of_add_one_le h1

/-- The double intersection locus of an `n`-fold whose closed points are smooth or double normal
crossing points is its singular locus (at a double normal crossing point the singular locus is
of codimension one). -/
private theorem doubleIntersectionLocusIdeal_eq_reducedSingularLocus (sU : U ⟶ Spec (.of k))
    {n : ℕ} (hU : IsNFold sU n)
    (hpts : ∀ x : U, IsClosed ({x} : Set U) →
      x ∈ smoothLocus sU ∨ IsDoubleNormalCrossingPoint sU n x) :
    doubleIntersectionLocusIdeal U = MMP.Resolution.reducedSingularLocus sU := by
  have hss := isSemismooth_of_forall_smooth_or_dnc sU hU hpts
  have hlft : LocallyOfFiniteType sU := hU.1.2.1
  have hqc : QuasiCompact sU := hU.1.2.2
  have : IsReduced U := hU.2.1
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian sU
  have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace sU
  have hsing := mem_smoothLocus_iff_isRegularLocalRing (sX := sU) hss.2
  have hclosed : ∀ x : U, IsClosed ({x} : Set U) → x ∉ smoothLocus sU →
      ringKrullDim (U.presheaf.stalk x) ≤ n := fun x hx hns =>
    ringKrullDim_stalk_le_of_isDoubleNormalCrossingPoint sU x ((hpts x hx).resolve_left hns)
  have key : (doubleIntersectionLocus U : Set U) = (singularLocus sU : Set U) := by
    apply Set.Subset.antisymm
    · refine closure_minimal ?_ (singularLocus sU).isClosed
      rintro η ⟨-, hη⟩ hs
      exact hη ((hsing η).mp hs)
    intro y (hy : y ∉ smoothLocus sU)
    rcases n with _ | m
    · exfalso
      obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints (Z := closure {y})
        ⟨y, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
      have hws : w ∉ smoothLocus sU :=
        closure_minimal (Set.singleton_subset_iff.mpr hy) (singularLocus sU).isClosed hw
      exact hws ((hsing w).mpr (isRegularLocalRing_of_ringKrullDim_le_zero _
        (by exact_mod_cast hclosed w hwc hws)))
    set D := MMP.Resolution.reducedSingularLocus sU
    obtain ⟨hDsm, hDdim⟩ := hss.singularLocus_smooth (Nat.succ_pos m)
    have hD : ∀ v : U, v ∈ (D.support : Set U) ↔ v ∉ smoothLocus sU := fun v => by
      rw [MMP.Resolution.support_reducedSingularLocus]
      rfl
    have : IsLocallyNoetherian D.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ sU)
    have : CompactSpace D.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (D.subschemeι ≫ sU)
    have : IsNoetherian D.subscheme := {}
    have : JacobsonSpace D.subscheme := LocallyOfFiniteType.jacobsonSpace (D.subschemeι ≫ sU)
    obtain ⟨z₀, rfl⟩ : y ∈ Set.range D.subschemeι := by
      rw [D.range_subschemeι, hD]
      exact hy
    obtain ⟨Z, hZ, hz₀Z⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {z₀} isIrreducible_singleton
    obtain ⟨w, hwc, hwZ, huniq⟩ := exists_closed_point_mem_unique_irreducibleComponent k
      D.subscheme (D.subschemeι ≫ sU) Z hZ
    have hAdim : ringKrullDim (D.subscheme.presheaf.stalk w) = m := by
      rw [← topologicalKrullDim_eq_ringKrullDim_stalk_of_unique_irreducibleComponent k
        D.subscheme (D.subschemeι ≫ sU) Z hZ w hwZ hwc huniq, hDdim Z hZ]
      simp
    have : Smooth (D.subschemeι ≫ sU) := MMP.Mori.IsSmoothScheme.smooth hDsm
    have : IsRegularLocalRing (D.subscheme.presheaf.stalk w) :=
      isRegularLocalRing_stalk_of_smooth_over_field (D.subschemeι ≫ sU) w
    have : IsDomain (D.subscheme.presheaf.stalk w) := IsRegularLocalRing.isDomain _
    -- the generic point `ξ` of `Z` and the generic point `g` of `Spec 𝒪_{D,w}`
    have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hξ : IsGenericPoint hZ.1.genericPoint Z :=
      hZ.1.isGenericPoint_genericPoint_closure.trans hZc.closure_eq
    have hξz₀ : hZ.1.genericPoint ⤳ z₀ := hξ.specializes (hz₀Z (Set.mem_singleton z₀))
    have hξw : hZ.1.genericPoint ⤳ w := hξ.specializes hwZ
    let g : D.subscheme := D.subscheme.fromSpecStalk w ⟨⊥, Ideal.isPrime_bot⟩
    have hgξ : g ⤳ hZ.1.genericPoint := by
      obtain ⟨P, hP⟩ : hZ.1.genericPoint ∈ Set.range (D.subscheme.fromSpecStalk w) := by
        rw [Scheme.range_fromSpecStalk]
        exact hξw
      rw [← hP]
      have hle : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (D.subscheme.presheaf.stalk w)) ≤ P :=
        bot_le (a := P.asIdeal)
      exact ((PrimeSpectrum.le_iff_specializes _ P).mp hle).map
        (D.subscheme.fromSpecStalk w).continuous
    -- `ι g` is the point of `Spec 𝒪_{U,ι w}` at the kernel `I` of `𝒪_{U,ι w} → 𝒪_{D,w}`
    let ι := D.subschemeι
    let R := U.presheaf.stalk (ι w)
    let φ := (ι.stalkMap w).hom
    have hφ : Function.Surjective φ := ι.stalkMap_surjective w
    let I : Ideal R := RingHom.ker φ
    have : I.IsPrime := RingHom.ker_isPrime φ
    have hη : U.fromSpecStalk (ι w) ⟨I, inferInstance⟩ = ι g := by
      have hsq := Scheme.SpecMap_stalkMap_fromSpecStalk (f := ι) (x := w)
      have h2 := congrArg (fun f => f (⟨⊥, Ideal.isPrime_bot⟩ :
        PrimeSpectrum (D.subscheme.presheaf.stalk w))) hsq
      refine Eq.trans ?_ h2
      rfl
    have hyx : ι g ⤳ ι w := by
      have : U.fromSpecStalk (ι w) ⟨I, inferInstance⟩ ∈ Set.range (U.fromSpecStalk (ι w)) :=
        ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecStalk, hη] at this
    have hdimη : ringKrullDim (U.presheaf.stalk (ι g)) = I.height := by
      letI : Algebra R (U.presheaf.stalk (ι g)) :=
        (U.presheaf.stalkSpecializes hyx).hom.toAlgebra
      have hloc := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hyx
      have hp' : (IsLocalRing.maximalIdeal (U.presheaf.stalk (ι g))).under R = I := by
        have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hyx
        have h2 := congrArg (fun f => f (IsLocalRing.closedPoint (U.presheaf.stalk (ι g)))) h1
        simp only [Scheme.fromSpecStalk_closedPoint] at h2
        have := (U.fromSpecStalk (ι w)).isEmbedding.injective (h2.trans hη.symm)
        exact congrArg PrimeSpectrum.asIdeal this
      have := Stacks.StalkSpecialization.isLocalization_atPrime_of_eq hp' hloc
      exact IsLocalization.AtPrime.ringKrullDim_eq_height I _
    have hmemD : ∀ v : D.subscheme, ι v ∈ (D.support : Set U) := fun v => by
      rw [← D.range_subschemeι]
      exact ⟨v, rfl⟩
    have hηs : ι g ∉ smoothLocus sU := (hD _).mp (hmemD g)
    have hηreg : ¬ IsRegularLocalRing (U.presheaf.stalk (ι g)) := fun h => hηs ((hsing _).mpr h)
    have hιwc : IsClosed ({ι w} : Set U) := by
      rw [← Set.image_singleton]
      exact ι.isClosedEmbedding.isClosedMap _ hwc
    have hR : ringKrullDim R ≤ (m + 1 : ℕ) :=
      hclosed (ι w) hιwc ((hD _).mp (hmemD w))
    have hRI : ringKrullDim (R ⧸ I) = m := by
      rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφ)]
      exact hAdim
    have hle := height_add_ringKrullDim_quotient_le I
    rw [hRI] at hle
    have hle1 : ringKrullDim (U.presheaf.stalk (ι g)) ≤ 1 := by
      rw [hdimη]
      exact le_one_of_add_le_natCast_add_one (hle.trans hR)
    have hcoh : Order.coheight (ι g) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight] at hle1
      have hc1 : Order.coheight (ι g) ≤ 1 := by exact_mod_cast hle1
      have hc0 : Order.coheight (ι g) ≠ 0 := by
        intro h0
        refine hηreg (isRegularLocalRing_of_ringKrullDim_le_zero _ ?_)
        rw [ringKrullDim_stalk_eq_coheight, h0]
        rfl
      exact le_antisymm hc1 (ENat.one_le_iff_ne_zero.mpr hc0)
    show ι z₀ ∈ closure {η : U | Order.coheight η = 1 ∧ ¬ IsRegularLocalRing (U.presheaf.stalk η)}
    exact closure_mono (Set.singleton_subset_iff.mpr (show ι g ∈ {η : U | Order.coheight η = 1 ∧
        ¬ IsRegularLocalRing (U.presheaf.stalk η)} from ⟨hcoh, hηreg⟩))
      (specializes_iff_mem_closure.mp ((hgξ.trans hξz₀).map ι.continuous))
  unfold doubleIntersectionLocusIdeal MMP.Resolution.reducedSingularLocus
  congr 1
  exact TopologicalSpace.Closeds.ext key

/-- The restriction of the normalization to closed subschemes `I`, `J` with `I ≤ J.map μ` is
finite. -/
private theorem isFinite_subschemeMap (sU : U ⟶ Spec (.of k)) [LocallyOfFiniteType sU]
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (I : U.IdealSheafData) (J : (normalizationScheme U hX).IdealSheafData)
    (hIJ : I ≤ J.map (normalization U hX)) :
    IsFinite (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ) := by
  have : IsFinite (normalization U hX) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sU) hX
  exact SemismoothDoubleCover.isFinite_subschemeMap J I _ hIJ

/-! ### The completed local rings of a double normal crossing point and of a pinch point -/

section PowerSeries

open MvPowerSeries IsLocalRing Stacks.MvPowerSeries.RegularParameters

variable {m : ℕ}

private theorem eq_zero_or_eq_single_of_sum_lt_two (d : Fin m →₀ ℕ) (hd : ∑ i, d i < 2) :
    d = 0 ∨ ∃ i, d = Finsupp.single i 1 := by
  classical
  by_cases h0 : d = 0
  · exact Or.inl h0
  right
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h; push Not at h; exact h0 (Finsupp.ext h)
  refine ⟨i, ?_⟩
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]; omega
  obtain ⟨d', rfl⟩ : ∃ d' : Fin m →₀ ℕ, d = Finsupp.single i 1 + d' :=
    ⟨d - Finsupp.single i 1, (add_tsub_cancel_of_le hle).symm⟩
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hd
  have : ∑ j, d' j = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at this
  rw [show d' = 0 from Finsupp.ext fun j => this j (Finset.mem_univ j), add_zero]

private theorem coeff_single_two_mul_self {f : MvPowerSeries (Fin m) k} (hf : constantCoeff f = 0)
    (i : Fin m) : coeff (Finsupp.single i 2) (f * f) = coeff (Finsupp.single i 1) f ^ 2 := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, hf, pow_two]

private theorem span_range_X_eq_maximalIdeal :
    Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) k)) = maximalIdeal _ := by
  rw [MvPowerSeries.span_X_eq_ker_constantCoeff,
    IsLocalRing.ker_eq_maximalIdeal (constantCoeff : MvPowerSeries (Fin m) k →+* k)
      fun c => ⟨C c, by simp⟩]

private theorem isLocalRing_quotient_span_singleton {h : MvPowerSeries (Fin m) k}
    (hh : h ∈ maximalIdeal (MvPowerSeries (Fin m) k)) :
    IsLocalRing (MvPowerSeries (Fin m) k ⧸ Ideal.span {h}) := by
  have : Nontrivial (MvPowerSeries (Fin m) k ⧸ Ideal.span {h}) :=
    Ideal.Quotient.nontrivial_iff.mpr fun ht =>
      (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (ht ▸ Ideal.span_le.mpr (by simpa)))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private theorem mk_mem_maximalIdeal_pow_iff {h : MvPowerSeries (Fin m) k}
    [IsLocalRing (MvPowerSeries (Fin m) k ⧸ Ideal.span {h})] (t : ℕ) (f : MvPowerSeries (Fin m) k) :
    Ideal.Quotient.mk _ f ∈ maximalIdeal (MvPowerSeries (Fin m) k ⧸ Ideal.span {h}) ^ t ↔
      f ∈ Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) k)) ^ t ⊔ Ideal.span {h} := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
    ← span_range_X_eq_maximalIdeal, ← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

private theorem ringEquiv_preserves {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) {ℓ : R} (h1 : ℓ ∈ maximalIdeal R) (h2 : ℓ ∉ maximalIdeal R ^ 2)
    (h3 : ℓ ^ 2 ∈ maximalIdeal R ^ 3) :
    e ℓ ∈ maximalIdeal S ∧ e ℓ ∉ maximalIdeal S ^ 2 ∧ e ℓ ^ 2 ∈ maximalIdeal S ^ 3 := by
  have he := IsLocalRing.map_maximalIdeal_of_surjective (e : R →+* S) e.surjective
  have hs := IsLocalRing.map_maximalIdeal_of_surjective (e.symm : S →+* R) e.symm.surjective
  refine ⟨he ▸ Ideal.mem_map_of_mem _ h1, fun h => h2 ?_, ?_⟩
  · have := Ideal.mem_map_of_mem (e.symm : S →+* R) h
    rwa [Ideal.map_pow, hs, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this
  · have := Ideal.mem_map_of_mem (e : R →+* S) h3
    rwa [Ideal.map_pow, he, RingEquiv.coe_toRingHom, map_pow] at this

private theorem X_mul_X_mem_pow_two (i j : Fin m) :
    (X i * X j : MvPowerSeries (Fin m) k) ∈
      Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) k)) ^ 2 := by
  rw [pow_two]
  exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (Ideal.subset_span ⟨j, rfl⟩)

/-- In `k[[x₀, …, xₙ]]/(x₀² - x₁x₂²)` the class of `x₀` lies in `𝔪 ∖ 𝔪²` and its square in `𝔪³`. -/
private theorem pinch_witness {n : ℕ}
    [IsLocalRing (MvPowerSeries (Fin (n + 1)) k ⧸ Ideal.span {(X 0 ^ 2 - X 1 * X 2 ^ 2 :
      MvPowerSeries (Fin (n + 1)) k)})] :
    ∃ ℓ ∈ maximalIdeal (MvPowerSeries (Fin (n + 1)) k ⧸ Ideal.span {(X 0 ^ 2 - X 1 * X 2 ^ 2 :
      MvPowerSeries (Fin (n + 1)) k)}),
      ℓ ∉ maximalIdeal (MvPowerSeries (Fin (n + 1)) k ⧸ Ideal.span {(X 0 ^ 2 - X 1 * X 2 ^ 2 :
        MvPowerSeries (Fin (n + 1)) k)}) ^ 2 ∧
      ℓ ^ 2 ∈ maximalIdeal (MvPowerSeries (Fin (n + 1)) k ⧸ Ideal.span {(X 0 ^ 2 - X 1 * X 2 ^ 2 :
        MvPowerSeries (Fin (n + 1)) k)}) ^ 3 := by
  set P := Ideal.span (Set.range (X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) k))
  have hh : (X 0 ^ 2 - X 1 * X 2 ^ 2 : MvPowerSeries (Fin (n + 1)) k) ∈ P ^ 2 := by
    rw [pow_two (X 0), pow_two (X 2), ← mul_assoc]
    refine sub_mem (X_mul_X_mem_pow_two 0 0) ?_
    exact Ideal.mul_mem_right _ _ (X_mul_X_mem_pow_two 1 2)
  refine ⟨Ideal.Quotient.mk _ (X 0), ?_, ?_, ?_⟩
  · rw [← pow_one (maximalIdeal _), mk_mem_maximalIdeal_pow_iff, pow_one]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨0, rfl⟩)
  · rw [mk_mem_maximalIdeal_pow_iff, sup_eq_left.mpr (Ideal.span_le.mpr (by simpa)),
      mem_pow_span_range_X_iff]
    intro h
    have := h (Finsupp.single 0 1) (by rw [Finsupp.univ_sum_single_apply]; norm_num)
    simp at this
  · rw [← map_pow, mk_mem_maximalIdeal_pow_iff, Submodule.mem_sup]
    refine ⟨X 1 * X 2 ^ 2, ?_, X 0 ^ 2 - X 1 * X 2 ^ 2, Ideal.mem_span_singleton_self _, by ring⟩
    rw [pow_succ, pow_two (X 2), ← mul_assoc]
    exact Ideal.mul_mem_mul (X_mul_X_mem_pow_two 1 2) (Ideal.subset_span ⟨2, rfl⟩)

/-- In `k[[x₀, …, xₙ]]/(x₀x₁)`, `n ≥ 1`, no element of `𝔪 ∖ 𝔪²` has its square in `𝔪³`. -/
private theorem dnc_no_witness {n : ℕ} (hn : 1 ≤ n)
    [IsLocalRing (MvPowerSeries (Fin (n + 1)) k ⧸ Ideal.span {(X 0 * X 1 :
      MvPowerSeries (Fin (n + 1)) k)})]
    (ℓ : MvPowerSeries (Fin (n + 1)) k ⧸ Ideal.span {(X 0 * X 1 : MvPowerSeries (Fin (n + 1)) k)})
    (h1 : ℓ ∈ maximalIdeal _) (h3 : ℓ ^ 2 ∈ maximalIdeal _ ^ 3) : ℓ ∈ maximalIdeal _ ^ 2 := by
  classical
  set P := Ideal.span (Set.range (X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) k))
  have hh : (X 0 * X 1 : MvPowerSeries (Fin (n + 1)) k) ∈ P ^ 2 := X_mul_X_mem_pow_two 0 1
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective ℓ
  have hP1 : Ideal.span {(X 0 * X 1 : MvPowerSeries (Fin (n + 1)) k)} ≤ P ^ 1 := by
    rw [pow_one, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_le_self two_ne_zero hh
  rw [← pow_one (maximalIdeal _), mk_mem_maximalIdeal_pow_iff, sup_eq_left.mpr hP1] at h1
  rw [← map_pow, mk_mem_maximalIdeal_pow_iff, Submodule.mem_sup] at h3
  obtain ⟨g, hg, c, hc, hgc⟩ := h3
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  rw [mk_mem_maximalIdeal_pow_iff]
  refine Ideal.mem_sup_left ?_
  rw [mem_pow_span_range_X_iff] at hg h1 ⊢
  have hf0 : constantCoeff f = 0 := by
    simpa using h1 0 (by simp)
  have hlin : ∀ i, coeff (Finsupp.single i 1) f = 0 := by
    intro i
    have h := congrArg (coeff (Finsupp.single i 2)) hgc
    rw [map_add, hg _ (by rw [Finsupp.univ_sum_single_apply]; norm_num), zero_add, pow_two,
      coeff_single_two_mul_self hf0, MvPowerSeries.X, MvPowerSeries.X, monomial_mul_monomial,
      mul_one, coeff_mul_monomial] at h
    split_ifs at h with hle
    · exfalso
      have h0 := hle 0
      have h1' := hle 1
      have h01 : (0 : Fin (n + 1)) ≠ 1 := by
        rw [Ne, Fin.ext_iff]; simp; omega
      simp only [Finsupp.add_apply, Finsupp.single_apply] at h0 h1'
      split_ifs at h0 h1' <;> simp_all
    · exact pow_eq_zero_iff two_ne_zero |>.mp h.symm
  intro d hd
  rcases eq_zero_or_eq_single_of_sum_lt_two d hd with rfl | ⟨i, rfl⟩
  · simpa using hf0
  · exact hlin i

end PowerSeries

/-- Cutting `k[[x]]` by one variable gives a regular local ring. -/
private theorem isRegularLocalRing_quotient_X {m : ℕ} (i : Fin m) :
    IsRegularLocalRing (MvPowerSeries (Fin m) k ⧸
      Ideal.span {(MvPowerSeries.X i : MvPowerSeries (Fin m) k)}) := by
  have : IsRegularLocalRing (MvPowerSeries (Fin m) k) := MvPowerSeries.isRegularLocalRing k _
  refine Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton
    ?_ ?_
  · rw [← span_range_X_eq_maximalIdeal]
    exact Ideal.subset_span ⟨i, rfl⟩
  · rw [← span_range_X_eq_maximalIdeal,
      Stacks.MvPowerSeries.RegularParameters.mem_pow_span_range_X_iff]
    intro h
    have := h (Finsupp.single i 1) (by rw [Finsupp.univ_sum_single_apply]; norm_num)
    simp at this

/-- A double normal crossing point is not a pinch point: `k[[x₀, …, xₙ]]/(x₀x₁)` and
`k[[x₀, …, xₙ]]/(x₀² - x₁x₂²)` are not isomorphic as `k`-algebras. -/
private theorem not_isPinchPoint_of_isDoubleNormalCrossingPoint (sU : U ⟶ Spec (.of k)) {n : ℕ}
    (x : U) (hd : IsDoubleNormalCrossingPoint sU n x) : ¬ IsPinchPoint sU n x := by
  intro hp
  letI := (stalkStructureMap sU x).toAlgebra
  obtain ⟨e₁⟩ := hd.2.2
  obtain ⟨e₂⟩ := hp.2.2.2
  have hmem : ∀ h : MvPowerSeries (Fin (n + 1)) k,
      h ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin (n + 1) → _)) ^ 2 →
        h ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin (n + 1)) k) := fun h hh =>
    span_range_X_eq_maximalIdeal (k := k) ▸ Ideal.pow_le_self two_ne_zero hh
  have := isLocalRing_quotient_span_singleton (hmem _ (X_mul_X_mem_pow_two (k := k) 0 1))
  have hpinch : (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
      MvPowerSeries (Fin (n + 1)) k) ∈
        Ideal.span (Set.range (MvPowerSeries.X : Fin (n + 1) → _)) ^ 2 := by
    rw [pow_two (MvPowerSeries.X 0), pow_two (MvPowerSeries.X 2), ← mul_assoc]
    exact sub_mem (X_mul_X_mem_pow_two 0 0) (Ideal.mul_mem_right _ _ (X_mul_X_mem_pow_two 1 2))
  have := isLocalRing_quotient_span_singleton (hmem _ hpinch)
  obtain ⟨ℓ, h1, h2, h3⟩ := pinch_witness (k := k) (n := n)
  obtain ⟨h1', h2', h3'⟩ :=
    ringEquiv_preserves (e₂.symm.toRingEquiv.trans e₁.toRingEquiv) h1 h2 h3
  exact h2' (dnc_no_witness (by have := hp.1; omega) _ h1' h3')

/-- No point of a reduced scheme locally of finite type over `k` is a double normal crossing
point of dimension `0`: the model `k[[x₀]]/(x₀²)` is not reduced, while the completion of
`𝒪_{U,x}` is. -/
private theorem not_isDoubleNormalCrossingPoint_zero (sU : U ⟶ Spec (.of k)) [IsReduced U]
    [LocallyOfFiniteType sU]
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite) (x : U) :
    ¬ IsDoubleNormalCrossingPoint sU 0 x := fun hd => by
  obtain ⟨m, hm⟩ := SemismoothDoubleCover.exists_eq_add_one_of_dnc (sX := sU) hX hd.2.2
  omega

/-- A closed point of the reduced singular locus `D` is a closed singular point of `U`. -/
private theorem isClosed_and_notMem_smoothLocus_of_reducedSingularLocus (sU : U ⟶ Spec (.of k))
    (z : (MMP.Resolution.reducedSingularLocus sU).subscheme) (hz : IsClosed ({z} : Set _)) :
    IsClosed ({(MMP.Resolution.reducedSingularLocus sU).subschemeι z} : Set U) ∧
      (MMP.Resolution.reducedSingularLocus sU).subschemeι z ∉ smoothLocus sU := by
  refine ⟨?_, ?_⟩
  · rw [← Set.image_singleton]
    exact Scheme.Hom.isClosedEmbedding _ |>.isClosedMap _ hz
  · have : (MMP.Resolution.reducedSingularLocus sU).subschemeι z ∈
        ((MMP.Resolution.reducedSingularLocus sU).support : Set U) :=
      (MMP.Resolution.reducedSingularLocus sU).range_subschemeι ▸ ⟨z, rfl⟩
    rw [MMP.Resolution.support_reducedSingularLocus] at this
    exact this

/-- A semismooth `0`-fold has empty, hence smooth, singular locus: at a closed singular point
the completed local ring would be `k[[x₀]]/(x₀²)`, which is not reduced, whereas the completion
of a local ring of a reduced scheme of finite type over `k` is reduced. -/
private theorem isSmoothScheme_reducedSingularLocus_of_eq_zero (sU : U ⟶ Spec (.of k))
    (h : IsSemismooth sU 0)
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite) :
    IsSmoothScheme ((MMP.Resolution.reducedSingularLocus sU).subschemeι ≫ sU) := by
  obtain ⟨⟨⟨-, hlft, -⟩, hred, -⟩, hpts⟩ := h
  set D := MMP.Resolution.reducedSingularLocus sU
  rw [IsSmoothScheme, eq_top_iff]
  intro z _
  exfalso
  have : JacobsonSpace D.subscheme := LocallyOfFiniteType.jacobsonSpace (D.subschemeι ≫ sU)
  obtain ⟨w, -, hwc⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨z, trivial⟩
    isClosed_univ.isLocallyClosed
  obtain ⟨hx, hsing⟩ := isClosed_and_notMem_smoothLocus_of_reducedSingularLocus sU w hwc
  rcases hpts _ hx with hs | hd | hp
  · exact hsing hs
  · exact not_isDoubleNormalCrossingPoint_zero sU hX _ hd
  · exact absurd hp.1 (by norm_num)

/-- The normalization of a scheme with locally finitely many irreducible components is
surjective: it is integral, hence closed, and dominant. -/
private theorem surjective_normalization
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite) :
    Surjective (normalization U hX) := by
  letI := quasiCompact_fromGenericPointResidueFields U hX
  have : IsDominant (normalization U hX) := by
    have h := isDominant_fromGenericPointResidueFields U
    rw [← (fromGenericPointResidueFields U).toNormalization_fromNormalization] at h
    exact IsDominant.of_comp ((fromGenericPointResidueFields U).toNormalization)
      (normalization U hX)
  exact surjective_of_isDominant_of_isClosed_range _
    (normalization U hX).isClosedMap.isClosed_range

/-- The restriction `D_μ ⟶ D` of the normalization to `D_μ = μ⁻¹(D)_red` is surjective. -/
private theorem surjective_subschemeMap
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (I : U.IdealSheafData)
    (J : (normalizationScheme U hX).IdealSheafData)
    (hJ : J = (I.comap (normalization U hX)).radical)
    (hIJ : I ≤ J.map (normalization U hX)) :
    Surjective (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ) := by
  subst hJ
  have hφ := Scheme.IdealSheafData.subschemeMap_subschemeι _ I (normalization U hX) hIJ
  refine ⟨fun w => ?_⟩
  obtain ⟨y, hy⟩ := (surjective_normalization hX).surj (I.subschemeι w)
  have hyJ : y ∈ Set.range ((I.comap (normalization U hX)).radical.subschemeι) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_radical,
      Scheme.IdealSheafData.support_comap]
    change normalization U hX y ∈ (I.support : Set U)
    rw [hy, ← I.range_subschemeι]
    exact ⟨w, rfl⟩
  obtain ⟨y', rfl⟩ := hyJ
  refine ⟨y', I.subschemeι.isEmbedding.injective ?_⟩
  rw [← hy, ← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply]

/-- `D_μ ⟶ D` is étale, for `D` the reduced singular locus: it is étale over a neighbourhood of
every closed point, none of which is a pinch point. -/
private theorem etale_subschemeMap (sU : U ⟶ Spec (.of k)) {n : ℕ} (hU : IsNFold sU n)
    (hpts : ∀ x : U, IsClosed ({x} : Set U) →
      x ∈ smoothLocus sU ∨ IsDoubleNormalCrossingPoint sU n x)
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (I : U.IdealSheafData) (hI : I = MMP.Resolution.reducedSingularLocus sU)
    (J : (normalizationScheme U hX).IdealSheafData)
    (hJ : J = (I.comap (normalization U hX)).radical)
    (hIJ : I ≤ J.map (normalization U hX)) :
    Etale (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ) := by
  have hss := isSemismooth_of_forall_smooth_or_dnc sU hU hpts
  subst hI
  rw [← Scheme.IdealSheafData.vanishingIdeal_support, Scheme.IdealSheafData.support_comap,
    MMP.Resolution.support_reducedSingularLocus] at hJ
  subst hJ
  set D := MMP.Resolution.reducedSingularLocus sU
  set φ := Scheme.IdealSheafData.subschemeMap _ D (normalization U hX) hIJ
  have hφ := Scheme.IdealSheafData.subschemeMap_subschemeι _ D (normalization U hX) hIJ
  have hlft : LocallyOfFiniteType sU := hU.1.2.1
  have : JacobsonSpace D.subscheme := LocallyOfFiniteType.jacobsonSpace (D.subschemeι ≫ sU)
  have key : ∀ z : D.subscheme, IsClosed ({z} : Set _) →
      ∃ V : D.subscheme.Opens, z ∈ V ∧ Etale (φ ∣_ V) := by
    intro z hz
    refine (hss.etale_restrict_doubleLocus_iff_not_isPinchPoint hX φ hφ z hz).mpr ?_
    obtain ⟨hx, hsing⟩ := isClosed_and_notMem_smoothLocus_of_reducedSingularLocus sU z hz
    exact not_isPinchPoint_of_isDoubleNormalCrossingPoint sU _
      ((hpts _ hx).resolve_left hsing)
  choose! V hzV hV using key
  have : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @Etale (Q := @RingHom.Etale)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun z : {z : D.subscheme // IsClosed ({z} : Set _)} => V z) ?_ (fun z => hV z z.2)
  rw [eq_top_iff]
  intro w _
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure {w}) ⟨w, subset_closure rfl⟩
    isClosed_closure.isLocallyClosed
  rw [TopologicalSpace.Opens.mem_iSup]
  exact ⟨⟨z, hzc⟩, (specializes_iff_mem_closure.mpr hz).mem_open (V z).isOpen (hzV z hzc)⟩

/-- `D_μ` is smooth and `D_μ ⟶ D` is étale and surjective, for `D` the reduced singular locus. -/
private theorem smooth_etale_surjective (sU : U ⟶ Spec (.of k)) {n : ℕ} (hU : IsNFold sU n)
    (hpts : ∀ x : U, IsClosed ({x} : Set U) →
      x ∈ smoothLocus sU ∨ IsDoubleNormalCrossingPoint sU n x)
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (I : U.IdealSheafData) (hI : I = MMP.Resolution.reducedSingularLocus sU)
    (J : (normalizationScheme U hX).IdealSheafData)
    (hJ : J = (I.comap (normalization U hX)).radical)
    (hIJ : I ≤ J.map (normalization U hX)) :
    IsSmoothScheme (J.subschemeι ≫ normalization U hX ≫ sU) ∧
      Etale (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ) ∧
      Surjective (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ) := by
  have het := etale_subschemeMap sU hU hpts hX I hI J hJ hIJ
  refine ⟨?_, het, surjective_subschemeMap hX I J hJ hIJ⟩
  have hss := isSemismooth_of_forall_smooth_or_dnc sU hU hpts
  have hD : IsSmoothScheme (I.subschemeι ≫ sU) := by
    subst hI
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact isSmoothScheme_reducedSingularLocus_of_eq_zero sU hss hX
    · exact (hss.singularLocus_smooth hn).1
  have : Smooth (I.subschemeι ≫ sU) := MMP.Mori.IsSmoothScheme.smooth hD
  have : Smooth (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ) := inferInstance
  have hsm : Smooth (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ ≫
      I.subschemeι ≫ sU) := inferInstance
  have : LocallyOfFinitePresentation (Scheme.IdealSheafData.subschemeMap J I
      (normalization U hX) hIJ ≫ I.subschemeι ≫ sU) :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth _
  rw [← Category.assoc, ← Scheme.IdealSheafData.subschemeMap_subschemeι J I _ hIJ,
    Category.assoc]
  exact (isSmoothScheme_iff _).mpr hsm

/-! ### The conductor of the double normal crossing model -/

section Conductor

open MvPowerSeries TensorProduct

/-- **The conductor of a ring with two branches.** Let `u, v ∈ B` with `uv = 0`, `(u) ∩ (v) = 0`
and `B ⧸ (v)` a normal domain. Then `u` multiplies every element of the total ring of fractions of
`B` integral over `B` into `B`. -/
private theorem exists_algebraMap_eq_mul_of_isIntegral {B : Type*} [CommRing B] {u v : B}
    (huv : u * v = 0) (hinter : ∀ b, u ∣ b → v ∣ b → b = 0)
    [IsDomain (B ⧸ Ideal.span {v})] [IsIntegrallyClosed (B ⧸ Ideal.span {v})]
    (y : FractionRing B) (hy : IsIntegral B y) :
    ∃ c : B, algebraMap B _ c = algebraMap B _ u * y := by
  by_cases hu : u = 0
  · exact ⟨0, by simp [hu]⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) y
  set π := Ideal.Quotient.mk (Ideal.span {v})
  have hπs : ∀ t ∈ nonZeroDivisors B, π t ≠ 0 := by
    intro t ht h0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
    obtain ⟨d, rfl⟩ := h0
    exact hu ((mem_nonZeroDivisors_iff.mp ht).1 u (by linear_combination d * huv))
  let K₁ := FractionRing (B ⧸ Ideal.span {v})
  let φ : FractionRing B →+* K₁ := IsLocalization.lift (M := nonZeroDivisors B)
    (g := (algebraMap (B ⧸ Ideal.span {v}) K₁).comp π) (fun t => by
      simp only [RingHom.comp_apply]
      exact IsUnit.mk0 _ (fun h => hπs t t.2
        (IsFractionRing.injective _ K₁ (by rw [h, map_zero]))))
  have hφ : φ.comp (algebraMap B (FractionRing B)) = (algebraMap _ K₁).comp π :=
    IsLocalization.lift_comp _
  have hint : IsIntegral (B ⧸ Ideal.span {v}) (φ (IsLocalization.mk' _ a s)) :=
    IsIntegral.map_of_comp_eq π φ hφ.symm hy
  obtain ⟨d₁, hd₁⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K₁)).mp hint
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d₁
  refine ⟨u * d, ?_⟩
  have key : u * (d * s - a) = 0 := by
    refine hinter _ (dvd_mul_right _ _) (dvd_mul_of_dvd_right ?_ _)
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective (B ⧸ Ideal.span {v}) K₁
    simp only [map_sub, map_mul, map_zero]
    change algebraMap _ K₁ (π d) * algebraMap _ K₁ (π s) - algebraMap _ K₁ (π a) = 0
    rw [hd₁, ← RingHom.comp_apply _ π, ← RingHom.comp_apply _ π, ← hφ, RingHom.comp_apply,
      RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec, sub_self]
  rw [mul_sub, sub_eq_zero] at key
  rw [← IsLocalization.mk'_one (M := nonZeroDivisors B),
    ← IsLocalization.mk'_one (M := nonZeroDivisors B) (FractionRing B) u,
    ← IsLocalization.mk'_mul, one_mul, IsLocalization.mk'_eq_iff_eq]
  simp only [Submonoid.coe_one, one_mul, mul_one]
  rw [← key]; congr 1; ring

/-- Faithfully flat descent of an element: if `s ⊗ 1 = 1 ⊗ r` in `A' ⊗_A C` with `C` faithfully
flat over `A`, then `s` comes from `A`. -/
private theorem exists_algebraMap_eq_of_tmul {A A' C : Type*} [CommRing A] [CommRing A']
    [CommRing C] [Algebra A A'] [Algebra A C] [Module.FaithfullyFlat A C] (s : A')
    (h : ∃ r : C, (1 : A') ⊗ₜ[A] r = s ⊗ₜ[A] (1 : C)) : ∃ a : A, algebraMap A A' a = s := by
  obtain ⟨r, hr⟩ := h
  set N := LinearMap.range (Algebra.linearMap A A')
  have h1 : N.mkQ 1 = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨1, by simp⟩
  have h2 := congrArg (LinearMap.rTensor C N.mkQ) hr
  rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, h1, zero_tmul] at h2
  have h3 := congrArg (TensorProduct.comm A _ C) h2
  rw [map_zero, TensorProduct.comm_tmul, eq_comm, Module.FaithfullyFlat.one_tmul_eq_zero_iff,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h3
  obtain ⟨a, ha⟩ := h3
  exact ⟨a, ha⟩

variable {m : ℕ}

/-- If `a` divides `f` modulo `ab`, then `a` divides `f`. -/
private theorem dvd_of_mk_dvd_mk {R : Type*} [CommRing R] {a b f : R}
    (h : Ideal.Quotient.mk (Ideal.span {a * b}) a ∣ Ideal.Quotient.mk _ f) : a ∣ f := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
  obtain ⟨d, hd⟩ := hc
  exact ⟨c + b * d, by linear_combination hd⟩

/-- In `k[[x₀, …, x_{m+1}]] ⧸ (x₀x₁)` the ideals `(x₀)` and `(x₁)` meet in `0`. -/
private theorem eq_zero_of_dvd_of_dvd_dnc
    (b : MvPowerSeries (Fin (m + 1 + 1)) k ⧸
      Ideal.span {(X 0 * X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)})
    (h0 : Ideal.Quotient.mk _ (X 0) ∣ b) (h1 : Ideal.Quotient.mk _ (X 1) ∣ b) : b = 0 := by
  have hreg := isRegularLocalRing_quotient_X (k := k) (1 : Fin (m + 1 + 1))
  have : IsDomain (MvPowerSeries (Fin (m + 1 + 1)) k ⧸
      Ideal.span {(X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}) := IsRegularLocalRing.isDomain _
  have hX1 : (X 1 : MvPowerSeries (Fin (m + 1 + 1)) k) ≠ 0 :=
    nonZeroDivisors.ne_zero MvPowerSeries.X_mem_nonzeroDivisors
  have hp : Prime (X 1 : MvPowerSeries (Fin (m + 1 + 1)) k) :=
    (Ideal.span_singleton_prime hX1).mp ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance)
  have h10 : ¬ (X 1 : MvPowerSeries (Fin (m + 1 + 1)) k) ∣ X 0 := by
    rw [MvPowerSeries.X_dvd_iff]
    intro h
    have := h (Finsupp.single 0 1) (by simp [Finsupp.single_apply])
    simp [MvPowerSeries.coeff_X] at this
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hdvd1 : (X 1 : MvPowerSeries (Fin (m + 1 + 1)) k) ∣ f :=
    dvd_of_mk_dvd_mk (b := X 0) (by rw [mul_comm (X 1)]; exact h1)
  obtain ⟨c, rfl⟩ := dvd_of_mk_dvd_mk h0
  rcases hp.2.2 _ _ hdvd1 with h | h
  · exact absurd h h10
  · obtain ⟨d, rfl⟩ := h
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨d, by ring⟩

/-- `k[[x₀, …, x_{m+1}]] ⧸ (x₀x₁)` modulo `x₀` or `x₁` is a regular, hence normal, domain. -/
private theorem isDomain_and_isIntegrallyClosed_quotient_dnc (i : Fin (m + 1 + 1))
    (hi : i = 0 ∨ i = 1) :
    IsDomain ((MvPowerSeries (Fin (m + 1 + 1)) k ⧸
      Ideal.span {(X 0 * X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}) ⧸
        Ideal.span {Ideal.Quotient.mk _ (X i : MvPowerSeries (Fin (m + 1 + 1)) k)}) ∧
    IsIntegrallyClosed ((MvPowerSeries (Fin (m + 1 + 1)) k ⧸
      Ideal.span {(X 0 * X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}) ⧸
        Ideal.span {Ideal.Quotient.mk _ (X i : MvPowerSeries (Fin (m + 1 + 1)) k)}) := by
  have hreg := isRegularLocalRing_quotient_X (k := k) i
  have : IsDomain (MvPowerSeries (Fin (m + 1 + 1)) k ⧸
      Ideal.span {(X i : MvPowerSeries (Fin (m + 1 + 1)) k)}) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (MvPowerSeries (Fin (m + 1 + 1)) k ⧸
      Ideal.span {(X i : MvPowerSeries (Fin (m + 1 + 1)) k)}) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have hle : Ideal.span {(X 0 * X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)} ≤ Ideal.span {X i} := by
    rw [Ideal.span_singleton_le_span_singleton]
    rcases hi with rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  let E := (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {(X 0 * X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)})
      (Ideal.span {(X i : MvPowerSeries (Fin (m + 1 + 1)) k)})).trans
        (Ideal.quotEquivOfEq (sup_eq_right.mpr hle)))
  exact ⟨Function.Injective.isDomain E.toRingHom E.injective, IsIntegrallyClosed.of_equiv E.symm⟩

end Conductor

/-! ### Sections of the normalization -/

/-- Pulling back sections along `μ` commutes with restriction. -/
private theorem app_map_apply {X Y : Scheme.{u}} (μ : Y ⟶ X) {V V' : X.Opens} (i : V' ⟶ V)
    (a : Γ(X, V)) :
    μ.app V' (X.presheaf.map i.op a) =
      Y.presheaf.map (homOfLE (μ.preimage_mono (leOfHom i))).op (μ.app V a) := by
  rw [← CommRingCat.comp_apply, μ.naturality, CommRingCat.comp_apply]
  rfl

/-- If `μ^♯` is injective on sections, a section of `μ_*𝒪_Y` which is locally a pull-back is a
pull-back. -/
private theorem mem_range_app_of_locally {X Y : Scheme.{u}} (μ : Y ⟶ X)
    (hinj : ∀ V : X.Opens, Function.Injective (μ.app V)) (W : X.Opens) (h : Γ(Y, μ ⁻¹ᵁ W))
    (hloc : ∀ x ∈ W, ∃ (V : X.Opens) (hVW : V ≤ W), x ∈ V ∧ ∃ a : Γ(X, V),
      μ.app V a = Y.presheaf.map (homOfLE (μ.preimage_mono hVW)).op h) :
    h ∈ Set.range (μ.app W) := by
  choose V hVW hxV a ha using hloc
  let ι := {x : X // x ∈ W}
  have hcover : W ≤ ⨆ i : ι, V i.1 i.2 := fun x hx =>
    Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun i : ι => V i.1 i.2) W
    (fun i => homOfLE (hVW i.1 i.2)) hcover (fun i => a i.1 i.2) (by
      intro i j
      apply hinj
      change μ.app _ (X.presheaf.map (homOfLE inf_le_left).op _) =
        μ.app _ (X.presheaf.map (homOfLE inf_le_right).op _)
      rw [app_map_apply, app_map_apply, ha, ha, ← CommRingCat.comp_apply,
        ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl)
  refine ⟨b, ?_⟩
  apply Y.sheaf.eq_of_locally_eq' (fun i : ι => μ ⁻¹ᵁ V i.1 i.2) (μ ⁻¹ᵁ W)
    (fun i => homOfLE (μ.preimage_mono (hVW i.1 i.2)))
  · intro y hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover hy)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    have e := app_map_apply μ (homOfLE (hVW i.1 i.2)) b
    change Y.presheaf.map _ (μ.app W b) = Y.presheaf.map _ h
    rw [← ha, ← hb i]
    exact e.symm

/-- A section of `μ_*𝒪_Y` whose germ at `x` comes from `𝒪_{X,x}` is a pull-back near `x`. -/
private theorem exists_app_eq_of_germ {X Y : Scheme.{u}} (μ : Y ⟶ X) {V : X.Opens} {x : X}
    (hx : x ∈ V) (s : Γ(Y, μ ⁻¹ᵁ V)) (c : X.presheaf.stalk x)
    (hc : ((TopCat.Presheaf.stalkFunctor CommRingCat x).map μ.c).hom c =
      (μ.base _* Y.presheaf).germ V x hx s) :
    ∃ (V' : X.Opens) (hV' : V' ≤ V), x ∈ V' ∧ ∃ a : Γ(X, V'),
      μ.app V' a = Y.presheaf.map (homOfLE (μ.preimage_mono hV')).op s := by
  obtain ⟨W, hxW, b, rfl⟩ := X.presheaf.germ_exist c
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hc
  obtain ⟨V', hxV', iW, iV, he⟩ := TopCat.Presheaf.germ_eq _ x hxW hx _ _ hc
  refine ⟨V', leOfHom iV, hxV', X.presheaf.map iW.op b, ?_⟩
  rw [app_map_apply]
  exact he

private theorem appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (V : Y.Opens)
    (V' : X.Opens) (e : V' ≤ f ⁻¹ᵁ V) (e' : V' ≤ g ⁻¹ᵁ V) : f.appLE V V' e = g.appLE V V' e' := by
  subst hfg; rfl

/-! ### The double cover `D_μ ⟶ D` -/

/-- The restriction `D_μ ⟶ D` of the normalization has degree `2`
(`MMP.Flips.IsSemismooth.isFinite_flat_finrank_subschemeMap_normalization`, FA 12.2.1(2)). -/
private theorem finrank_subschemeMap (sU : U ⟶ Spec (.of k)) {n : ℕ}
    (h : IsSemismooth sU n)
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (I : U.IdealSheafData) (hI : I = MMP.Resolution.reducedSingularLocus sU)
    (J : (normalizationScheme U hX).IdealSheafData)
    (hJ : J = (I.comap (normalization U hX)).radical)
    (hIJ : I ≤ J.map (normalization U hX)) :
    (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ).finrank = 2 := by
  subst hI
  rw [← Scheme.IdealSheafData.vanishingIdeal_support] at hJ
  subst hJ
  exact (h.isFinite_flat_finrank_subschemeMap_normalization hX).2.2

/-! ### The local ring at a closed point -/

/-- A point of `Spec 𝒪_{U^μ,y}` whose image in `U` is not regular lies on `D_μ`. -/
private theorem fromSpecStalk_mem_range_of_not_isRegularLocalRing (sU : U ⟶ Spec (.of k))
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (hsing : ∀ y : U, y ∈ smoothLocus sU ↔ IsRegularLocalRing (U.presheaf.stalk y))
    (J : (normalizationScheme U hX).IdealSheafData)
    (hE : ∀ w, w ∈ Set.range J.subschemeι ↔ normalization U hX w ∉ smoothLocus sU)
    (y : normalizationScheme U hX) (𝔮 : Ideal ((normalizationScheme U hX).presheaf.stalk y))
    [𝔮.IsPrime] [(𝔮.comap ((normalization U hX).stalkMap y).hom).IsPrime]
    (h : ¬ IsRegularLocalRing (Localization.AtPrime
      (𝔮.comap ((normalization U hX).stalkMap y).hom))) :
    (normalizationScheme U hX).fromSpecStalk y (⟨𝔮, inferInstance⟩ : PrimeSpectrum _) ∈
      Set.range J.subschemeι := by
  rw [hE]
  intro hsmooth
  have hpt := congrArg (fun f => f (⟨𝔮, inferInstance⟩ : PrimeSpectrum _))
    (Scheme.SpecMap_stalkMap_fromSpecStalk (f := normalization U hX) (x := y))
  have h1 : U.fromSpecStalk (normalization U hX y)
      (⟨𝔮.comap ((normalization U hX).stalkMap y).hom, inferInstance⟩ : PrimeSpectrum _) ∈
        smoothLocus sU := by
    convert hsmooth using 1
    exact hpt
  rw [hsing, MMP.Flips.isRegularLocalRing_stalk_fromSpecStalk_iff] at h1
  exact h h1

/-- **A branch of the normalization at a double normal crossing point.** Let `y ∈ U^μ` lie over
a double normal crossing point, `E : 𝒪̂_{U,μ y} ≅ k[[x]]/(x₀x₁)`, and `ψ : 𝒪̂_{U,μ y} → 𝒪̂_{U^μ,y}`
integral, birational, without non-zero-divisors in its kernel and compatible with the stalk map.
A germ at `y` lying in every prime over `D_μ` maps into the ideal generated by `ψ(x₀), ψ(x₁)`. -/
private theorem exists_eq_mul_add_mul_of_dnc (sU : U ⟶ Spec (.of k))
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (hsing : ∀ y : U, y ∈ smoothLocus sU ↔ IsRegularLocalRing (U.presheaf.stalk y))
    (J : (normalizationScheme U hX).IdealSheafData)
    (hE : ∀ w, w ∈ Set.range J.subschemeι ↔ normalization U hX w ∉ smoothLocus sU)
    {m : ℕ} (y : normalizationScheme U hX)
    (hG : IsGRing (U.presheaf.stalk (normalization U hX y)))
    [IsNoetherianRing (U.presheaf.stalk (normalization U hX y))]
    [IsNoetherianRing ((normalizationScheme U hX).presheaf.stalk y)]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal
      ((normalizationScheme U hX).presheaf.stalk y)) ((normalizationScheme U hX).presheaf.stalk y))]
    [IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal
      ((normalizationScheme U hX).presheaf.stalk y)) ((normalizationScheme U hX).presheaf.stalk y))]
    (E : CompletedLocalRing U (normalization U hX y) ≃+* (MvPowerSeries (Fin (m + 1 + 1)) k ⧸
      Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}))
    (ψ : CompletedLocalRing U (normalization U hX y) →+* AdicCompletion (IsLocalRing.maximalIdeal
      ((normalizationScheme U hX).presheaf.stalk y)) ((normalizationScheme U hX).presheaf.stalk y))
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0)
    (hψalg : ψ.comp (algebraMap _ _) = (algebraMap _ _).comp
      ((normalization U hX).stalkMap y).hom)
    (T : (normalizationScheme U hX).presheaf.stalk y)
    (hT : ∀ (p : Ideal ((normalizationScheme U hX).presheaf.stalk y)) [p.IsPrime],
      (normalizationScheme U hX).fromSpecStalk y (⟨p, inferInstance⟩ : PrimeSpectrum _) ∈
        Set.range J.subschemeι → T ∈ p) :
    ∃ c d : CompletedLocalRing U (normalization U hX y),
      algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal
        ((normalizationScheme U hX).presheaf.stalk y))
          ((normalizationScheme U hX).presheaf.stalk y)) T =
        ψ c * ψ (E.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 0))) +
          ψ d * ψ (E.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 1))) := by
  have hloc : IsLocalRing (AdicCompletion
      (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk y))
      ((normalizationScheme U hX).presheaf.stalk y)) :=
    AdicCompletion.isLocalRing_of_fg (IsNoetherian.noetherian _)
  obtain ⟨h₁, h₂, h₃⟩ := props_comp_symm_of_ringEquiv ψ E hint hbir hnz
  obtain ⟨hsurj, Q, hQ, hQc⟩ := surjective_and_comap_of_dnc (k := k) (m := m)
    (ψ.comp E.symm.toRingHom) h₁ h₂ h₃
  have hc1 : Q.comap ψ = ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1 + 1)) k),
      MvPowerSeries.X 1}).map (Ideal.Quotient.mk _)).comap E := by
    rw [← hQc]
    ext r
    simp [Ideal.mem_comap]
  have hcomap : Q.comap ψ = Ideal.span {E.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 0)),
      E.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 1))} := by
    rw [hc1, Ideal.map_span, Set.image_pair, ← Ideal.map_symm, Ideal.map_span, Set.image_pair]
  have hsurjψ : Function.Surjective ψ := fun l => by
    obtain ⟨r, hr⟩ := hsurj l
    exact ⟨E.symm r, hr⟩
  set 𝔮 := Q.comap (algebraMap ((normalizationScheme U hX).presheaf.stalk y) (AdicCompletion
    (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk y))
    ((normalizationScheme U hX).presheaf.stalk y))) with h𝔮
  have hp : 𝔮.comap ((normalization U hX).stalkMap y).hom =
      (Q.comap ψ).comap (algebraMap _ _) := by
    rw [h𝔮, Ideal.comap_comap, Ideal.comap_comap, hψalg]
  have : (Q.comap ψ).IsPrime := Ideal.IsPrime.comap _
  have h𝔞₀ : ((Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1 + 1)) k),
      MvPowerSeries.X 1}).map (Ideal.Quotient.mk (Ideal.span {(MvPowerSeries.X 0 *
        MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}))).IsPrime := by
    rw [← hQc]; exact Ideal.IsPrime.comap _
  have : (𝔮.comap ((normalization U hX).stalkMap y).hom).IsPrime := Ideal.IsPrime.comap _
  have hnotreg : ¬ IsRegularLocalRing (Localization.AtPrime
      (𝔮.comap ((normalization U hX).stalkMap y).hom)) := by
    rw [SemismoothDoubleCover.isRegularLocalRing_localization_congr hp,
      ← SingLoc.isRegularLocalRing_localization_adicCompletion_iff hG,
      SemismoothDoubleCover.isRegularLocalRing_localization_congr hc1,
      SingLoc.isRegularLocalRing_localization_comap_iff E,
      isRegularLocalRing_localization_dnc_iff_not_le, not_not]
  have hq := hT 𝔮 (fromSpecStalk_mem_range_of_not_isRegularLocalRing sU hX hsing J hE y 𝔮
    hnotreg)
  rw [h𝔮, Ideal.mem_comap] at hq
  obtain ⟨t', ht'⟩ := hsurjψ (algebraMap _ _ T)
  have ht'Q : t' ∈ Q.comap ψ := by
    rw [Ideal.mem_comap, ht']
    exact hq
  rw [hcomap, Ideal.mem_span_pair] at ht'Q
  obtain ⟨c, d, hcd⟩ := ht'Q
  exact ⟨c, d, by rw [← ht', ← hcd, map_add, map_mul, map_mul]⟩

open scoped TensorProduct in
/-- **The gluing on one branch.** Over a double normal crossing point `μ y`, a germ `s` of
`μ_*𝒪_{U^μ}` whose germ `T` at `y` lies in every prime over `D_μ` has image in `𝒪̂_{U^μ,y}` in the
ideal generated by the images of `x₀` and `x₁`. -/
private theorem exists_tmul_eq_of_dnc (sU : U ⟶ Spec (.of k)) [LocallyOfFiniteType sU]
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (hsing : ∀ y : U, y ∈ smoothLocus sU ↔ IsRegularLocalRing (U.presheaf.stalk y))
    (J : (normalizationScheme U hX).IdealSheafData)
    (hE : ∀ w, w ∈ Set.range J.subschemeι ↔ normalization U hX w ∉ smoothLocus sU)
    {m : ℕ} (y : normalizationScheme U hX)
    (hyx : y ∈ (normalization U hX).base ⁻¹' {normalization U hX y})
    (E : CompletedLocalRing U (normalization U hX y) ≃+* (MvPowerSeries (Fin (m + 1 + 1)) k ⧸
      Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (m + 1 + 1)) k)}))
    (T : (normalizationScheme U hX).presheaf.stalk y)
    (hker : ∀ (p : Ideal ((normalizationScheme U hX).presheaf.stalk y)) [p.IsPrime],
      (normalizationScheme U hX).fromSpecStalk y (⟨p, inferInstance⟩ : PrimeSpectrum _) ∈
        Set.range J.subschemeι → T ∈ p) :
    letI := Scheme.normalizationPushforwardStalkAlgebra U hX (normalization U hX y)
    ∀ (s : Scheme.normalizationPushforwardStalk U hX (normalization U hX y))
      (_ : T = (TopCat.Presheaf.stalkSpecializes
        ((normalization U hX).base _* (normalizationScheme U hX).presheaf)
        (specializes_of_eq rfl) ≫ TopCat.Presheaf.stalkPushforward _ (normalization U hX).base
          (normalizationScheme U hX).presheaf y).hom s)
      (e : Scheme.normalizationPushforwardStalk U hX (normalization U hX y) ⊗[U.presheaf.stalk
          (normalization U hX y)] AdicCompletion (IsLocalRing.maximalIdeal
            (U.presheaf.stalk (normalization U hX y))) (U.presheaf.stalk (normalization U hX y)) ≃+*
          ((x' : (normalization U hX).base ⁻¹' {normalization U hX y}) →
            AdicCompletion (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk x'))
              ((normalizationScheme U hX).presheaf.stalk x')))
      (_ : ∀ (a' : Scheme.normalizationPushforwardStalk U hX (normalization U hX y))
          (x' : (normalization U hX).base ⁻¹' {normalization U hX y}),
          e (a' ⊗ₜ 1) x' =
            algebraMap ((normalizationScheme U hX).presheaf.stalk x')
              (AdicCompletion
                (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk x'))
                ((normalizationScheme U hX).presheaf.stalk x'))
              ((TopCat.Presheaf.stalkSpecializes ((normalization U hX).base _*
                  (normalizationScheme U hX).presheaf)
                  (specializes_of_eq (Set.mem_singleton_iff.mp x'.2)) ≫
                TopCat.Presheaf.stalkPushforward _ (normalization U hX).base
                  (normalizationScheme U hX).presheaf x').hom a'))
      (g : Scheme.normalizationPushforwardStalk U hX (normalization U hX y) ⊗[U.presheaf.stalk
          (normalization U hX y)] AdicCompletion (IsLocalRing.maximalIdeal
            (U.presheaf.stalk (normalization U hX y))) (U.presheaf.stalk (normalization U hX y)) →+*
          FractionRing (AdicCompletion (IsLocalRing.maximalIdeal
            (U.presheaf.stalk (normalization U hX y))) (U.presheaf.stalk (normalization U hX y))))
      (_ : Function.Injective g)
      (_ : g.range = (integralClosure (AdicCompletion (IsLocalRing.maximalIdeal
          (U.presheaf.stalk (normalization U hX y))) (U.presheaf.stalk (normalization U hX y)))
          (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal
            (U.presheaf.stalk (normalization U hX y)))
              (U.presheaf.stalk (normalization U hX y))))).toSubring)
      (_ : ∀ z, g (1 ⊗ₜ z) = algebraMap _ (FractionRing (AdicCompletion
          (IsLocalRing.maximalIdeal (U.presheaf.stalk (normalization U hX y)))
            (U.presheaf.stalk (normalization U hX y)))) z),
      ∃ a b, e (s ⊗ₜ 1) ⟨y, hyx⟩ =
        a * e (1 ⊗ₜ E.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 0))) ⟨y, hyx⟩ +
          b * e (1 ⊗ₜ E.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 1))) ⟨y, hyx⟩ := by
  obtain ⟨ι₀, hι₀⟩ : ∃ f : U.presheaf.stalk (normalization U hX y) →+* AdicCompletion
      (IsLocalRing.maximalIdeal (U.presheaf.stalk (normalization U hX y)))
        (U.presheaf.stalk (normalization U hX y)), f = algebraMap _ _ :=
    ⟨_, rfl⟩
  obtain ⟨ιN, hιN⟩ : ∃ f : ∀ y : normalizationScheme U hX,
      (normalizationScheme U hX).presheaf.stalk y →+* AdicCompletion
        (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk y))
        ((normalizationScheme U hX).presheaf.stalk y), f = fun y => algebraMap _ _ :=
    ⟨_, rfl⟩
  have hexc : IsExcellent (U.presheaf.stalk (normalization U hX y)) :=
    AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent k
      ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) sU _
  have : IsNoetherianRing (U.presheaf.stalk (normalization U hX y)) := hexc.1.1
  intro s hT e he g hg hrange hgy
  letI := Scheme.normalizationPushforwardStalkAlgebra U hX (normalization U hX y)
  have heT : e (s ⊗ₜ 1) ⟨y, hyx⟩ = ιN y T := by
    rw [he, hT, hιN]
  -- the completed local ring of `U^μ` at `y` and `ψ : 𝒪̂_{U,x} → 𝒪̂_{U^μ,y}`
  have : IsFinite (normalization U hX) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sU) hX
  have hexcy : IsExcellent ((normalizationScheme U hX).presheaf.stalk y) :=
    AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent k
      ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) (normalization U hX ≫ sU) _
  have : IsNoetherianRing ((normalizationScheme U hX).presheaf.stalk y) := hexcy.1.1
  have hNormal : IsNormal (normalizationScheme U hX) := Scheme.isNormal_normalizationScheme U hX
  have hn : IsNormalRing ((normalizationScheme U hX).presheaf.stalk y) := by
    let : IsDomain ((normalizationScheme U hX).presheaf.stalk y) :=
      hNormal.stalk_isDomain _
    let : IsIntegrallyClosed ((normalizationScheme U hX).presheaf.stalk y) :=
      hNormal.stalk_normal _
    exact IsNormalRing.of_isIntegrallyClosed _
  have hND := AlgebraicGeometry.isNormalDomain_adicCompletion_of_isExcellent _ hexcy hn
  obtain ⟨hint, hbir, hnz⟩ := factor_props_of_normalization
    Algebra.TensorProduct.includeRight.toRingHom e g hg hrange hgy
    ⟨y, hyx⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal
        (U.presheaf.stalk (normalization U hX y)))
        (U.presheaf.stalk (normalization U hX y)) →+*
      AdicCompletion
        (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk y))
        ((normalizationScheme U hX).presheaf.stalk y),
      ψ = (Pi.evalRingHom _ ⟨y, hyx⟩).comp
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) := ⟨_, rfl⟩
  rw [← hψ] at hint hbir hnz
  have hD : IsDomain (AdicCompletion
      (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk y))
      ((normalizationScheme U hX).presheaf.stalk y)) := hND.isDomain
  have hIC : IsIntegrallyClosed (AdicCompletion
      (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk y))
      ((normalizationScheme U hX).presheaf.stalk y)) := hND.isIntegrallyClosed
  clear hND
  have hψalg : ψ.comp ι₀ = (ιN y).comp ((normalization U hX).stalkMap y).hom := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have ht : (1 : Scheme.normalizationPushforwardStalk U hX (normalization U hX y)) ⊗ₜ[
        U.presheaf.stalk (normalization U hX y)] (ι₀ a) =
        algebraMap _ (Scheme.normalizationPushforwardStalk U hX
          (normalization U hX y)) a ⊗ₜ 1 := by
      rw [hι₀, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one a,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have h1 : ψ (ι₀ a) = e ((1 : Scheme.normalizationPushforwardStalk U hX (normalization U hX
          y)) ⊗ₜ (ι₀ a)) ⟨y, hyx⟩ := by
      rw [hψ]; rfl
    rw [h1, ht, he, hιN]
    congr 1
    simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
    rfl
  rw [hι₀, hιN] at hψalg
  obtain ⟨c, d, hcd⟩ := exists_eq_mul_add_mul_of_dnc sU hX hsing J hE y hexc.1.2.1 E ψ hint
    hbir hnz hψalg T hker
  refine ⟨ψ c, ψ d, ?_⟩
  rw [heT, hιN]
  refine hcd.trans ?_
  rw [hψ]
  rfl

open scoped TensorProduct in
/-- **The gluing at a closed point.** A germ of `μ_*𝒪_{U^μ}` at a closed point `x` vanishing on
`D_μ` comes from `𝒪_{U,x}`. -/
private theorem exists_stalkFunctor_map_eq (sU : U ⟶ Spec (.of k)) {n : ℕ} (hU : IsNFold sU n)
    (hpts : ∀ x : U, IsClosed ({x} : Set U) →
      x ∈ smoothLocus sU ∨ IsDoubleNormalCrossingPoint sU n x)
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (I : U.IdealSheafData) (hI : I = MMP.Resolution.reducedSingularLocus sU)
    (J : (normalizationScheme U hX).IdealSheafData)
    (hJ : J = (I.comap (normalization U hX)).radical)
    (x : U) (hx : IsClosed ({x} : Set U))
    (s : Scheme.normalizationPushforwardStalk U hX x)
    (hs : ∀ (z : J.subscheme) (hz : normalization U hX (J.subschemeι z) = x),
      (J.subschemeι.stalkMap z).hom
        ((TopCat.Presheaf.stalkSpecializes _ (specializes_of_eq hz) ≫
          TopCat.Presheaf.stalkPushforward _ (normalization U hX).base
            (normalizationScheme U hX).presheaf (J.subschemeι z)).hom s) = 0) :
    ∃ c : U.presheaf.stalk x,
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (normalization U hX).c).hom c = s := by
  classical
  have hlft : LocallyOfFiniteType sU := hU.1.2.1
  have : IsReduced U := hU.2.1
  have hss := isSemismooth_of_forall_smooth_or_dnc sU hU hpts
  have hsing := mem_smoothLocus_iff_isRegularLocalRing (sX := sU) hss.2
  have hE : ∀ w, w ∈ Set.range J.subschemeι ↔ normalization U hX w ∉ smoothLocus sU := by
    intro w
    subst hJ hI
    rw [Scheme.IdealSheafData.range_subschemeι, ← Scheme.IdealSheafData.vanishingIdeal_support,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.IdealSheafData.support_comap,
      MMP.Resolution.support_reducedSingularLocus]
    rfl
  -- the structure maps of the completions, named before the algebra structure on the
  -- pushforward stalk enters the context
  obtain ⟨ι₀, hι₀⟩ : ∃ f : U.presheaf.stalk x →+* AdicCompletion
      (IsLocalRing.maximalIdeal (U.presheaf.stalk x)) (U.presheaf.stalk x), f = algebraMap _ _ :=
    ⟨_, rfl⟩
  obtain ⟨ιN, hιN⟩ : ∃ f : ∀ y : normalizationScheme U hX,
      (normalizationScheme U hX).presheaf.stalk y →+* AdicCompletion
        (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk y))
        ((normalizationScheme U hX).presheaf.stalk y), f = fun y => algebraMap _ _ :=
    ⟨_, rfl⟩
  letI : Algebra (U.presheaf.stalk x) (Scheme.normalizationPushforwardStalk U hX x) :=
    Scheme.normalizationPushforwardStalkAlgebra U hX x
  obtain ⟨-, ⟨e, he⟩, g, hg, hrange, hgy⟩ : _root_.IsReduced
      (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk x)) (U.presheaf.stalk x)) ∧
      (∃ e : Scheme.normalizationPushforwardStalk U hX x ⊗[U.presheaf.stalk x]
          AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk x)) (U.presheaf.stalk x) ≃+*
          ((x' : (normalization U hX).base ⁻¹' {x}) →
            AdicCompletion (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk x'))
              ((normalizationScheme U hX).presheaf.stalk x')),
        ∀ (a' : Scheme.normalizationPushforwardStalk U hX x)
          (x' : (normalization U hX).base ⁻¹' {x}),
          e (a' ⊗ₜ 1) x' =
            algebraMap ((normalizationScheme U hX).presheaf.stalk x')
              (AdicCompletion
                (IsLocalRing.maximalIdeal ((normalizationScheme U hX).presheaf.stalk x'))
                ((normalizationScheme U hX).presheaf.stalk x'))
              ((TopCat.Presheaf.stalkSpecializes ((normalization U hX).base _*
                  (normalizationScheme U hX).presheaf)
                  (specializes_of_eq (Set.mem_singleton_iff.mp x'.2)) ≫
                TopCat.Presheaf.stalkPushforward _ (normalization U hX).base
                  (normalizationScheme U hX).presheaf x').hom a')) ∧
      ∃ g : Scheme.normalizationPushforwardStalk U hX x ⊗[U.presheaf.stalk x]
          AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk x)) (U.presheaf.stalk x) →+*
          FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk x))
            (U.presheaf.stalk x)),
        Function.Injective g ∧
        g.range = (integralClosure (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk x))
          (U.presheaf.stalk x)) (FractionRing (AdicCompletion
            (IsLocalRing.maximalIdeal (U.presheaf.stalk x)) (U.presheaf.stalk x)))).toSubring ∧
        ∀ y, g (1 ⊗ₜ y) = algebraMap _ (FractionRing (AdicCompletion
          (IsLocalRing.maximalIdeal (U.presheaf.stalk x)) (U.presheaf.stalk x))) y :=
    MMP.Resolution.isReduced_adicCompletion_stalk_and_normalization_completion U sU hX x
  have hexc : IsExcellent (U.presheaf.stalk x) :=
    AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent k
      ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) sU x
  have : IsNoetherianRing (U.presheaf.stalk x) := hexc.1.1
  have hff : Module.FaithfullyFlat (U.presheaf.stalk x)
      (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk x)) (U.presheaf.stalk x)) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  suffices H : ∃ r, g (1 ⊗ₜ r) = g (s ⊗ₜ 1) by
    obtain ⟨r, hr⟩ := H
    exact exists_algebraMap_eq_of_tmul (A' := Scheme.normalizationPushforwardStalk U hX x) s
      ⟨r, hg hr⟩
  have hgint : ∀ t, IsIntegral _ (g t) := fun t => by
    have : g t ∈ g.range := ⟨t, rfl⟩
    rw [hrange] at this
    exact this
  by_cases hsm : x ∈ smoothLocus sU
  · -- at a smooth point the completion is a normal domain
    have hreg : IsRegularLocalRing (U.presheaf.stalk x) := (hsing x).mp hsm
    have : IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk x))
        (U.presheaf.stalk x)) := isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp hreg
    have : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk x))
        (U.presheaf.stalk x)) := IsRegularLocalRing.isDomain _
    have : UniqueFactorizationMonoid (AdicCompletion (IsLocalRing.maximalIdeal
        (U.presheaf.stalk x)) (U.presheaf.stalk x)) :=
      IsRegularLocalRing.uniqueFactorizationMonoid _
    obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (K := FractionRing (AdicCompletion
      (IsLocalRing.maximalIdeal (U.presheaf.stalk x)) (U.presheaf.stalk x)))).mp (hgint (s ⊗ₜ 1))
    exact ⟨r, by rw [hgy, hr]⟩
  -- at a double normal crossing point
  have hd : IsDoubleNormalCrossingPoint sU n x := (hpts x hx).resolve_left hsm
  obtain ⟨m, rfl⟩ := SemismoothDoubleCover.exists_eq_add_one_of_dnc (sX := sU) hX hd.2.2
  obtain ⟨E⟩ : Nonempty (CompletedLocalRing U x ≃+* (MvPowerSeries (Fin (m + 1 + 1)) k ⧸
      Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin (m + 1 + 1)) k)})) := by
    letI := (stalkStructureMap sU x).toAlgebra
    obtain ⟨e₀⟩ := hd.2.2
    exact ⟨e₀.toRingEquiv⟩
  set u := E.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) with hu
  set v := E.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) with hv
  have hquot : ∀ i : Fin (m + 1 + 1), Ideal.span {(Ideal.Quotient.mk
      (Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin (m + 1 + 1)) k)}) (MvPowerSeries.X i))} =
      (Ideal.span {E.symm (Ideal.Quotient.mk _ (MvPowerSeries.X i))}).map E := fun i => by
    rw [Ideal.map_span, Set.image_singleton, RingEquiv.apply_symm_apply]
  obtain ⟨hD0, hI0⟩ := isDomain_and_isIntegrallyClosed_quotient_dnc (k := k) (m := m) 0
    (Or.inl rfl)
  obtain ⟨hD1, hI1⟩ := isDomain_and_isIntegrallyClosed_quotient_dnc (k := k) (m := m) 1
    (Or.inr rfl)
  haveI : IsDomain (_ ⧸ Ideal.span {u}) :=
    Function.Injective.isDomain (Ideal.quotientEquiv _ _ E (hquot 0)).toRingHom
      (Ideal.quotientEquiv _ _ E (hquot 0)).injective
  haveI : IsIntegrallyClosed (_ ⧸ Ideal.span {u}) :=
    IsIntegrallyClosed.of_equiv (Ideal.quotientEquiv _ _ E (hquot 0)).symm
  haveI : IsDomain (_ ⧸ Ideal.span {v}) :=
    Function.Injective.isDomain (Ideal.quotientEquiv _ _ E (hquot 1)).toRingHom
      (Ideal.quotientEquiv _ _ E (hquot 1)).injective
  haveI : IsIntegrallyClosed (_ ⧸ Ideal.span {v}) :=
    IsIntegrallyClosed.of_equiv (Ideal.quotientEquiv _ _ E (hquot 1)).symm
  have huv : u * v = 0 := by
    rw [hu, hv, ← map_mul, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  have hinter : ∀ b, u ∣ b → v ∣ b → b = 0 := by
    intro b hub hvb
    apply E.injective
    rw [map_zero]
    refine eq_zero_of_dvd_of_dvd_dnc (E b) ?_ ?_
    · simpa [u] using map_dvd E hub
    · simpa [v] using map_dvd E hvb
  -- on every branch, `s ⊗ 1` lies in the ideal generated by `u` and `v`
  have key : ∀ y, ∃ a b,
      e (s ⊗ₜ 1) y = a * e (1 ⊗ₜ u) y + b * e (1 ⊗ₜ v) y := by
    rintro ⟨y, hyx⟩
    have hyx' : normalization U hX y = x := hyx
    obtain ⟨z, hz⟩ : y ∈ Set.range J.subschemeι := (hE y).mpr (by rw [hyx']; exact hsm)
    subst hyx'
    -- the germ of `s` at `y` vanishes on `D_μ`
    obtain ⟨T, hT⟩ : ∃ T, T = (TopCat.Presheaf.stalkSpecializes
        ((normalization U hX).base _* (normalizationScheme U hX).presheaf)
        (specializes_of_eq rfl) ≫ TopCat.Presheaf.stalkPushforward _ (normalization U hX).base
          (normalizationScheme U hX).presheaf y).hom s := ⟨_, rfl⟩
    have hker : ∀ (p : Ideal ((normalizationScheme U hX).presheaf.stalk y)) [p.IsPrime],
        (normalizationScheme U hX).fromSpecStalk y (⟨p, inferInstance⟩ : PrimeSpectrum _) ∈
          Set.range J.subschemeι → T ∈ p := by
      subst hz hT
      intro p _ hp
      exact (ker_stalkMap_le_iff_mem_range J.subschemeι z p).mpr hp
        (RingHom.mem_ker.mpr (hs z rfl))
    exact exists_tmul_eq_of_dnc sU hX hsing J hE y hyx E T hker s hT e he g hg hrange hgy
  choose a b hab using key
  have hst : s ⊗ₜ 1 = e.symm a * (1 ⊗ₜ u) + e.symm b * (1 ⊗ₜ v) := by
    apply e.injective
    funext y
    simp only [map_add, map_mul, RingEquiv.apply_symm_apply, Pi.add_apply, Pi.mul_apply]
    exact hab y
  obtain ⟨c₁, hc₁⟩ := exists_algebraMap_eq_mul_of_isIntegral huv hinter (g (e.symm a)) (hgint _)
  obtain ⟨c₂, hc₂⟩ := exists_algebraMap_eq_mul_of_isIntegral (u := v) (v := u)
    (by rw [mul_comm, huv]) (fun b h1 h2 => hinter b h2 h1) (g (e.symm b)) (hgint _)
  refine ⟨c₁ + c₂, ?_⟩
  rw [hgy, map_add, hc₁, hc₂, hst, map_add, map_mul, map_mul]
  erw [hgy u, hgy v]
  ring

/-- **The gluing near a closed point.** A section of `μ_*𝒪_{U^μ}` whose restriction to `D_μ` is
`τ`-invariant is a pull-back near every closed point. -/
private theorem exists_app_eq_near (sU : U ⟶ Spec (.of k)) {n : ℕ} (hU : IsNFold sU n)
    (hpts : ∀ x : U, IsClosed ({x} : Set U) →
      x ∈ smoothLocus sU ∨ IsDoubleNormalCrossingPoint sU n x)
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (I : U.IdealSheafData) (hI : I = MMP.Resolution.reducedSingularLocus sU)
    (J : (normalizationScheme U hX).IdealSheafData)
    (hJ : J = (I.comap (normalization U hX)).radical)
    (hIJ : I ≤ J.map (normalization U hX))
    [Flat (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ)]
    [Surjective (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ)]
    [IsFinite (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ)]
    (τ : J.subscheme ≅ J.subscheme)
    (hτ : τ.hom ≫ Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ =
      Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ)
    (hΦ : IsIso (coprod.desc (pullback.lift (𝟙 _) (𝟙 _) rfl)
      (pullback.lift (𝟙 _) τ.hom (by rw [hτ, Category.id_comp])) :
        J.subscheme ⨿ J.subscheme ⟶ pullback
          (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ)
          (Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ)))
    (W : U.Opens) (h : Γ(normalizationScheme U hX, normalization U hX ⁻¹ᵁ W))
    (hh : ∀ (V : J.subscheme.Opens) (e₁ : V ≤ J.subschemeι ⁻¹ᵁ (normalization U hX ⁻¹ᵁ W))
      (e₂ : V ≤ (τ.hom ≫ J.subschemeι) ⁻¹ᵁ (normalization U hX ⁻¹ᵁ W)),
      J.subschemeι.appLE (normalization U hX ⁻¹ᵁ W) V e₁ h =
        (τ.hom ≫ J.subschemeι).appLE (normalization U hX ⁻¹ᵁ W) V e₂ h)
    (x : U) (hxW : x ∈ W) (hx : IsClosed ({x} : Set U)) :
    ∃ (V : U.Opens) (hVW : V ≤ W), x ∈ V ∧ ∃ a : Γ(U, V),
      (normalization U hX).app V a =
        (normalizationScheme U hX).presheaf.map
          (homOfLE ((normalization U hX).preimage_mono hVW)).op h := by
  have : LocallyOfFiniteType sU := hU.1.2.1
  have hφ : Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ ≫ I.subschemeι =
      J.subschemeι ≫ normalization U hX :=
    Scheme.IdealSheafData.subschemeMap_subschemeι J I _ hIJ
  generalize Scheme.IdealSheafData.subschemeMap J I (normalization U hX) hIJ = p at *
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
  replace hVW : V ≤ W := hVW
  set VD := I.subschemeι ⁻¹ᵁ V
  have hVD : IsAffineOpen VD := hV.preimage _
  have hpre : p ⁻¹ᵁ VD = J.subschemeι ⁻¹ᵁ (normalization U hX ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hφ]
  have hτpre : p ⁻¹ᵁ VD ≤ τ.hom ⁻¹ᵁ (p ⁻¹ᵁ VD) := by
    have : (τ.hom ≫ p) ⁻¹ᵁ VD = p ⁻¹ᵁ VD := by rw [hτ]
    rw [Scheme.Hom.comp_preimage] at this
    exact this.ge
  have e₀ : p ⁻¹ᵁ VD ≤ J.subschemeι ⁻¹ᵁ (normalization U hX ⁻¹ᵁ V) := hpre.le
  have e₁ : p ⁻¹ᵁ VD ≤ J.subschemeι ⁻¹ᵁ (normalization U hX ⁻¹ᵁ W) :=
    e₀.trans (J.subschemeι.preimage_mono ((normalization U hX).preimage_mono hVW))
  have e₂ : p ⁻¹ᵁ VD ≤ (τ.hom ≫ J.subschemeι) ⁻¹ᵁ (normalization U hX ⁻¹ᵁ W) := by
    rw [Scheme.Hom.comp_preimage]
    exact hτpre.trans (τ.hom.preimage_mono e₁)
  have hb : τ.hom.appLE (p ⁻¹ᵁ VD) (p ⁻¹ᵁ VD) hτpre
      (J.subschemeι.appLE (normalization U hX ⁻¹ᵁ W) (p ⁻¹ᵁ VD) e₁ h) =
      J.subschemeι.appLE (normalization U hX ⁻¹ᵁ W) (p ⁻¹ᵁ VD) e₁ h := by
    conv_rhs => rw [hh (p ⁻¹ᵁ VD) e₁ e₂]
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE _ _ _ (p ⁻¹ᵁ VD) _ e₁ hτpre]
  obtain ⟨ā, hā⟩ := MMP.Flips.exists_app_eq_of_involution p τ hτ hΦ hVD _ hb
  obtain ⟨a₀, ha₀⟩ := I.subschemeι.app_surjective V hV ā
  have hs0 : J.subschemeι.appLE (normalization U hX ⁻¹ᵁ V) (p ⁻¹ᵁ VD) e₀
      ((normalizationScheme U hX).presheaf.map
        (homOfLE ((normalization U hX).preimage_mono hVW)).op h -
          (normalization U hX).app V a₀) = 0 := by
    have h1 : J.subschemeι.appLE (normalization U hX ⁻¹ᵁ V) (p ⁻¹ᵁ VD) e₀
        ((normalizationScheme U hX).presheaf.map
          (homOfLE ((normalization U hX).preimage_mono hVW)).op h) =
        J.subschemeι.appLE (normalization U hX ⁻¹ᵁ W) (p ⁻¹ᵁ VD) e₁ h := by
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    have h2 : J.subschemeι.appLE (normalization U hX ⁻¹ᵁ V) (p ⁻¹ᵁ VD) e₀
        ((normalization U hX).app V a₀) =
        J.subschemeι.appLE (normalization U hX ⁻¹ᵁ W) (p ⁻¹ᵁ VD) e₁ h := by
      have c1 := Scheme.Hom.comp_appLE J.subschemeι (normalization U hX) V (p ⁻¹ᵁ VD) e₀
      have c2 := Scheme.Hom.comp_appLE p I.subschemeι V (p ⁻¹ᵁ VD) le_rfl
      rw [← CommRingCat.comp_apply, ← c1, ← appLE_eq_of_eq hφ V (p ⁻¹ᵁ VD) le_rfl e₀, c2,
        CommRingCat.comp_apply, ha₀, ← hā, Scheme.Hom.app_eq_appLE]
    rw [map_sub, h1, h2, sub_self]
  -- the germ of `s` at `x` comes from `𝒪_{U,x}`
  obtain ⟨c, hc⟩ := exists_stalkFunctor_map_eq sU hU hpts hX I hI J hJ x hx
    (((normalization U hX).base _* (normalizationScheme U hX).presheaf).germ V x hxV
      ((normalizationScheme U hX).presheaf.map
        (homOfLE ((normalization U hX).preimage_mono hVW)).op h -
          (normalization U hX).app V a₀)) (by
      intro z hz
      subst hz
      have hzV : z ∈ p ⁻¹ᵁ VD := by
        show I.subschemeι (p z) ∈ V
        rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply]
        exact hxV
      simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
      have key : ((normalization U hX).base _* (normalizationScheme U hX).presheaf).germ V _ hxV ≫
          (TopCat.Presheaf.stalkPushforward CommRingCat (normalization U hX).base
            (normalizationScheme U hX).presheaf (J.subschemeι z) ≫ J.subschemeι.stalkMap z) =
          J.subschemeι.app _ ≫ J.subscheme.presheaf.germ
            (J.subschemeι ⁻¹ᵁ (normalization U hX ⁻¹ᵁ V)) z (e₀ hzV) := by
        rw [← Category.assoc]
        erw [TopCat.Presheaf.stalkPushforward_germ]
        exact Scheme.Hom.germ_stalkMap _ _ _ _
      refine (congrArg (fun f => f.hom ((normalizationScheme U hX).presheaf.map
        (homOfLE ((normalization U hX).preimage_mono hVW)).op h -
          (normalization U hX).app V a₀)) key).trans ?_
      rw [CommRingCat.comp_apply,
        ← TopCat.Presheaf.germ_res_apply _ (homOfLE e₀) z hzV, ← CommRingCat.comp_apply
          (J.subschemeι.app _), ← Scheme.Hom.appLE, hs0, map_zero])
  obtain ⟨V', hV', hxV', a₁, ha₁⟩ := exists_app_eq_of_germ (normalization U hX) hxV _ c hc
  refine ⟨V', hV'.trans hVW, hxV', U.presheaf.map (homOfLE hV').op a₀ + a₁, ?_⟩
  rw [map_add, ha₁, app_map_apply, map_sub, add_sub_cancel, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  rfl

/-- The finite étale double cover `p : D_μ ⟶ D` has a covering involution `τ` making it a
`ℤ/2`-torsor, and `𝒪_U` is the `τ`-invariant part of `μ_*𝒪_{U^μ}`. -/
private theorem exists_involution_and_gluing (sU : U ⟶ Spec (.of k)) {n : ℕ} (hU : IsNFold sU n)
    (hpts : ∀ x : U, IsClosed ({x} : Set U) →
      x ∈ smoothLocus sU ∨ IsDoubleNormalCrossingPoint sU n x)
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite)
    (I : U.IdealSheafData) (hI : I = MMP.Resolution.reducedSingularLocus sU)
    (J : (normalizationScheme U hX).IdealSheafData)
    (hJ : J = (I.comap (normalization U hX)).radical)
    (hIJ : I ≤ J.map (normalization U hX)) :
    let μ := normalization U hX
    let p : J.subscheme ⟶ I.subscheme := Scheme.IdealSheafData.subschemeMap J I μ hIJ
      ∃ τ : J.subscheme ≅ J.subscheme, ∃ hτ : τ.hom ≫ p = p,
        IsIso (coprod.desc (pullback.lift (𝟙 _) (𝟙 _) rfl)
          (pullback.lift (𝟙 _) τ.hom (by rw [hτ, Category.id_comp])) :
            J.subscheme ⨿ J.subscheme ⟶ pullback p p) ∧
        ∀ W : U.Opens, Function.Injective (μ.app W) ∧
          Set.range (μ.app W) = {h : Γ(normalizationScheme U hX, μ ⁻¹ᵁ W) |
            ∀ (V : J.subscheme.Opens) (e₁ : V ≤ J.subschemeι ⁻¹ᵁ (μ ⁻¹ᵁ W))
              (e₂ : V ≤ (τ.hom ≫ J.subschemeι) ⁻¹ᵁ (μ ⁻¹ᵁ W)),
              J.subschemeι.appLE (μ ⁻¹ᵁ W) V e₁ h =
                (τ.hom ≫ J.subschemeι).appLE (μ ⁻¹ᵁ W) V e₂ h} := by
  intro μ p
  have hss := isSemismooth_of_forall_smooth_or_dnc sU hU hpts
  obtain ⟨-, het, hsurj⟩ := smooth_etale_surjective sU hU hpts hX I hI J hJ hIJ
  have : LocallyOfFiniteType sU := hU.1.2.1
  have hfin : IsFinite p := isFinite_subschemeMap sU hX I J hIJ
  have h2 := finrank_subschemeMap sU hss hX I hI J hJ hIJ
  have hφ : p ≫ I.subschemeι = J.subschemeι ≫ μ :=
    Scheme.IdealSheafData.subschemeMap_subschemeι J I μ hIJ
  obtain ⟨τ, hτ, hΦ⟩ := MMP.Flips.exists_involution_of_finrank_eq_two p h2
  have : IsReduced U := hU.2.1
  have hinj : ∀ W : U.Opens, Function.Injective (μ.app W) := fun W => by
    letI := quasiCompact_fromGenericPointResidueFields U hX
    have : IsDominant (fromGenericPointResidueFields U) :=
      isDominant_fromGenericPointResidueFields U
    exact injective_fromNormalization_app (fromGenericPointResidueFields U) W
  refine ⟨τ, hτ, hΦ, fun W => ⟨hinj W, ?_⟩⟩
  ext h
  constructor
  · rintro ⟨a, rfl⟩ V e₁ e₂
    have c1 := Scheme.Hom.comp_appLE J.subschemeι μ W V e₁
    have c2 := Scheme.Hom.comp_appLE (τ.hom ≫ J.subschemeι) μ W V e₂
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← c1, ← c2]
    congr 2
    exact appLE_eq_of_eq (by rw [Category.assoc, ← hφ, ← Category.assoc, hτ]) _ _ _ _
  · intro hh
    refine mem_range_app_of_locally μ hinj W h fun x hxW => ?_
    have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace sU
    obtain ⟨x₀, hx₀, hx₀c⟩ := nonempty_inter_closedPoints (Z := closure {x} ∩ W)
      ⟨x, subset_closure rfl, hxW⟩ (isClosed_closure.isLocallyClosed.inter W.isOpen.isLocallyClosed)
    obtain ⟨V, hVW, hx₀V, a, ha⟩ := exists_app_eq_near sU hU hpts hX I hI J hJ hIJ τ hτ hΦ W h hh
      x₀ hx₀.2 hx₀c
    exact ⟨V, hVW, (specializes_iff_mem_closure.mpr hx₀.1).mem_open V.isOpen hx₀V, a, ha⟩

end DncGluing

open MMP.Mori Stacks.AlgebraicGeometry.Normalization in
/-- **An `n`-fold with only smooth and double normal crossing points is glued from its
normalization.** Let `U` be an `n`-fold over `k` every closed point of which is a smooth point
or a double normal crossing point, `μ : U^μ ⟶ U` its normalization, `D` the double intersection
locus and `D_μ = μ⁻¹(D)_red`. Then `U^μ` and `D_μ` are smooth over `k`, the map
`p : D_μ ⟶ D` induced by `μ` is finite, étale and surjective, and there is an automorphism `τ`
of `D_μ` over `D` with `(id, τ) : D_μ ⨿ D_μ ≅ D_μ ×_D D_μ` (so `p` is a double cover with covering
involution `τ`), such that for every open `W ⊆ U` the map `μ^♯ : Γ(U, W) ⟶ Γ(U^μ, μ⁻¹W)` is
injective with image the sections whose restriction to `D_μ` is `τ`-invariant. -/
@[mmp "lem_fa12a_dnc_surface_is_gluing"]
public theorem exists_involution_and_range_app_normalization_eq
    (sU : U ⟶ Spec (.of k)) {n : ℕ} (hU : IsNFold sU n)
    (hpts : ∀ x : U, IsClosed ({x} : Set U) →
      x ∈ smoothLocus sU ∨ IsDoubleNormalCrossingPoint sU n x)
    (hX : ∀ W : U.Opens, IsCompact (W : Set U) → (irreducibleComponents W).Finite) :
    let μ := normalization U hX
    let I := doubleIntersectionLocusIdeal U
    let J := (I.comap μ).radical
    let p : J.subscheme ⟶ I.subscheme :=
      Scheme.IdealSheafData.subschemeMap J I μ
        ((I.le_map_comap μ).trans (Scheme.IdealSheafData.map_mono μ (I.comap μ).le_radical))
    IsSmoothScheme (μ ≫ sU) ∧ IsSmoothScheme (J.subschemeι ≫ μ ≫ sU) ∧
      IsFinite p ∧ Etale p ∧ Surjective p ∧
      ∃ τ : J.subscheme ≅ J.subscheme, ∃ hτ : τ.hom ≫ p = p,
        IsIso (coprod.desc (pullback.lift (𝟙 _) (𝟙 _) rfl)
          (pullback.lift (𝟙 _) τ.hom (by rw [hτ, Category.id_comp])) :
            J.subscheme ⨿ J.subscheme ⟶ pullback p p) ∧
        ∀ W : U.Opens, Function.Injective (μ.app W) ∧
          Set.range (μ.app W) = {h : Γ(normalizationScheme U hX, μ ⁻¹ᵁ W) |
            ∀ (V : J.subscheme.Opens) (e₁ : V ≤ J.subschemeι ⁻¹ᵁ (μ ⁻¹ᵁ W))
              (e₂ : V ≤ (τ.hom ≫ J.subschemeι) ⁻¹ᵁ (μ ⁻¹ᵁ W)),
              J.subschemeι.appLE (μ ⁻¹ᵁ W) V e₁ h =
                (τ.hom ≫ J.subschemeι).appLE (μ ⁻¹ᵁ W) V e₂ h} := by
  intro μ I J p
  have hss := DncGluing.isSemismooth_of_forall_smooth_or_dnc sU hU hpts
  have hI := DncGluing.doubleIntersectionLocusIdeal_eq_reducedSingularLocus sU hU hpts
  obtain ⟨hsm, het, hsurj⟩ := DncGluing.smooth_etale_surjective sU hU hpts hX I hI J rfl _
  have : LocallyOfFiniteType sU := hU.1.2.1
  exact ⟨hss.isSmoothScheme_normalization hX, hsm,
    DncGluing.isFinite_subschemeMap sU hX I J _, het, hsurj,
    DncGluing.exists_involution_and_gluing sU hU hpts hX I hI J rfl _⟩

end MMP.Flips

end
