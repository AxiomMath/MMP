module
public import MMP.AlgebraicGeometry.Normalization.IntegralScheme
public import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
public import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafSmoothCurve
public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.CurveVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Properties.CodimensionLocalRing
public import StacksFrontier.RingTheory.NodalChart.Regularity

/-!
# Normalization of curves, fixed coefficients, bad loci and echoes

Six results used in the fourfold step of the minimal model program.

* **Normalization of a curve.** Let `C` be an integral projective curve over a perfect field `k`
  and `ν : Cᵛ ⟶ C` its normalization. Every invertible sheaf on `Cᵛ` is `ν^* L` for an
  invertible sheaf `L` on `C` (conductor square); in particular `ω_{Cᵛ} = Ω_{Cᵛ/k}` is such a
  pullback, and every such `L` has `H¹(C, L) ≠ 0`, since `H¹(C, L) ⟶ H¹(Cᵛ, ν^* L)` is
  surjective and `H¹(Cᵛ, ω_{Cᵛ}) ≠ 0` by duality.
* **Persistence of strict fixed coefficients.** For proper birational `p : T ⟶ X`, `q : T ⟶ Y`
  over `Z` and affine families `D_t`, `D'_t` of real Cartier divisors with
  `q_*(p^*D_t - q^*D'_t) = 0`, a prime divisor with positive coefficient in `p_*E_δ` lies in the
  relative divisorial stable base locus of `D_t` for all `t` near `δ`, uniformly in the divisor:
  the coefficients of `E_t` are affine, hence continuous, in `t`.
* **Bad loci of threefold step diagrams.** In `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, every closed point of
  the bad locus `Σ` has a positive-dimensional fibre under `f⁻` or `f⁺`, and a prime divisor
  of `X⁻` whose valuation is exceptional over `X⁺` lies in `W⁻ = (f⁻)⁻¹(Σ)`.
* **Echoes.** On a normal threefold with labels `L`, for `S ∈ L` and a curve `V ⊆ S` whose
  generic point lies in the one-label smooth locus, the echo of order `j ≥ 1` of `S` at `V`
  exists, is unique, and takes the value `j` on a local equation of `S`. It is the monomial
  valuation `v_{x,t;j}`, equivalently a monomial valuation of weight `(j, 1)` for the snc
  divisor `(S ∩ U) + {t = 0}` on a suitable neighbourhood `U` of `η_V`.

## Main results

* `MMP.Fourfold.liftsInvertible_normalization`
* `MMP.Fourfold.eventually_isInRelativeDivisorialStableBase_of_coeff_pos`
* `MMP.Fourfold.IsThreefoldStepDiagram.pos_dim_fibre_of_mem_badLocusBase`
* `MMP.Fourfold.IsThreefoldStepDiagram.support_subset_badLocusMinus`
* `MMP.Fourfold.isEcho_tfae_isMonomialValuationOfWeight_isWeightedMonomialValuation`
* `MMP.Fourfold.existsUnique_isEcho`

## Implementation notes

* The normalization is `AlgebraicGeometry.Scheme.normalization`, and `H¹(C, L)` is
  `AlgebraicGeometry.cohomologyOverField k f L 1`. A perfect base field makes `Cᵛ` smooth.
* The strict-transform coefficient of `G` in `E_δ` is the coefficient of `G` in
  `MMP.Mori.RationalMap.transformDivisor p.toRationalMap E_δ`; the pullbacks are families
  satisfying `MMP.Flips.IsRCartierPullback`.
* Valuations of `k(X⁻)` and `k(X⁺)` are compared through `k(Z)` along `functionFieldMap`.
* Valuations are multiplicative, in `ℤᵐ⁰`, so `ξ(x) = j` reads `ξ x = WithZero.exp (-j)`. The
  neighbourhood `U` is an open subscheme carrying sections `x_U, t_U` whose germs at `η_V` are
  `x` and `t`, and `ξ` is read on `k(U)` through `functionFieldMap U.ι`.
-/

universe u

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Proofs.lem_fourfold_curve_normalization_pic_surjective

/-- A finite locally free module of nonzero constant rank on a nonempty scheme is not zero. -/
private theorem not_isZero_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}} [Nonempty X]
    (F : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (hr : r ≠ 0) : ¬ IsZero F := by
  intro hz
  obtain ⟨x⟩ := ‹Nonempty X›
  refine hr ?_
  rw [← Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank F r x]
  refine Scheme.Modules.fiberRank_eq_zero_of_subsingleton_stalk F x ⟨fun a b => ?_⟩
  obtain ⟨U, -, ta, rfl⟩ := TopCat.Presheaf.germ_exist _ a
  obtain ⟨V, -, tb, rfl⟩ := TopCat.Presheaf.germ_exist _ b
  have hU := ModuleCat.subsingleton_of_isZero
    ((SheafOfModules.evaluation _ (Opposite.op U)).map_isZero hz)
  have hV := ModuleCat.subsingleton_of_isZero
    ((SheafOfModules.evaluation _ (Opposite.op V)).map_isZero hz)
  rw [@Subsingleton.elim _ hU ta 0, @Subsingleton.elim _ hV tb 0]
  exact (map_zero _).trans (map_zero _).symm

/-- `H¹(Cᵛ, Ω_{Cᵛ/k}) ≠ 0` on the normalization of a projective curve over a perfect field. -/
private theorem nontrivial_cohomologyOverField_one_relativeDifferentials_normalization
    {k : Type u} [Field k] [PerfectField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProjectiveVariety k f]
    (hC : topologicalKrullDim C = 1) :
    Nontrivial (cohomologyOverField k (C.normalization
          (MMP.finite_irreducibleComponents_of_isIntegral C) ≫ f)
        (Scheme.Hom.relativeDifferentials (C.normalization
          (MMP.finite_irreducibleComponents_of_isIntegral C) ≫ f))
        1) := by
  set ν := C.normalization
    (MMP.finite_irreducibleComponents_of_isIntegral C)
  haveI : IsCurve k f := { topologicalKrullDim_eq_one := hC }
  haveI hcur : IsCurve k (ν ≫ f) := (AlgebraicGeometry.normalizationModel' k f).isCurve
  haveI : Smooth (ν ≫ f) := (AlgebraicGeometry.normalizationModel' k f).smooth_structureMap
  haveI : IsFinite ν := isFinite_normalizationOverField k f
  haveI : SmoothOfRelativeDimension 1 (ν ≫ f) := smoothOfRelativeDimension_one_of_isCurve _ _
  haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials (ν ≫ f) 1
  haveI : Stacks.Ample.IsInvertibleModule _ (Scheme.Hom.relativeDifferentials (ν ≫ f)) :=
    MMP.Fourfold.isInvertible_relativeDifferentials_normalization_comp f _
  have hq := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule
    (Scheme.Hom.relativeDifferentials (ν ≫ f))
  obtain ⟨eω⟩ := Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials (ν ≫ f)
  obtain ⟨e, -⟩ := Stacks.Duality.exists_natural_addEquiv_hom_dualizingSheafOverField (ν ≫ f)
    hcur.topologicalKrullDim_eq_one.le
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have hdual : Subsingleton (cohomologyOverField k (ν ≫ f)
      (Scheme.Hom.relativeDifferentials (ν ≫ f)) 1 →ₗ[k] k) :=
    ⟨fun a b => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  have hhom := (e _ hq).toEquiv.subsingleton
  haveI : Nonempty (C.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral C)) :=
    ν.surjective.nonempty
  refine not_isZero_of_isFiniteLocallyFreeOfRank (Scheme.Hom.relativeDifferentials (ν ≫ f)) 1
    one_ne_zero ?_
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  have : eω.inv = 0 := Subsingleton.elim _ _
  simpa [this] using eω.inv_hom_id.symm

open Stacks.AlgebraicGeometry in
/-- The cokernel of the unit `L ⟶ ν_* ν^* L` vanishes at the generic point of `C`, over which
the normalization is an isomorphism. -/
private theorem notMem_supp_cokernel_unit {k : Type u} [Field k] [PerfectField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProjectiveVariety k f]
    (hC : topologicalKrullDim C = 1) (L : C.Modules) :
    ∀ y ∈ Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne C,
      y ∉ _root_.SheafOfModules.supp (cokernel
        ((Scheme.Modules.pullbackPushforwardAdjunction (C.normalization
          (MMP.finite_irreducibleComponents_of_isIntegral C))).unit.app
            L)) := by
  intro y hy
  set h := MMP.finite_irreducibleComponents_of_isIntegral C
  have hNagata : IsNagataScheme C := isNagataScheme_of_locallyOfFiniteType_over_field k f
  let U : C.Opens := ⟨regularLocus C, isOpen_regularLocus_of_isNagataScheme C hNagata hC.le⟩
  haveI hU : IsIso (C.normalization h ∣_ U) :=
    isIso_morphismRestrict_normalization_of_subset_regularLocus h U le_rfl
  have hyU : y ∈ U := by
    by_contra hyU
    exact notMem_genericPointsOne_of_isClosed_singleton
      (NormalizationQuotientDirectSum.isClosed_singleton_of_not_mem_regularLocus C hC.le y hyU) hy
  exact Stacks.AlgebraicGeometry.ConfinedDevissage.notMem_supp_cokernel_of_isIso_restrict _ U
    (Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit _ U hU L)
    y hyU

/-- `H¹(C, L) ≠ 0` whenever `ν^* L ≅ ω_{Cᵛ}`. -/
private theorem nontrivial_cohomologyOverField_one {k : Type u} [Field k] [PerfectField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProjectiveVariety k f]
    (hC : topologicalKrullDim C = 1) (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L]
    (hL : Nonempty ((Scheme.Modules.pullback (C.normalization
      (MMP.finite_irreducibleComponents_of_isIntegral C))).obj L ≅
        Scheme.Hom.relativeDifferentials (C.normalization
          (MMP.finite_irreducibleComponents_of_isIntegral C) ≫ f))) :
    Nontrivial (cohomologyOverField k f L 1) := by
  set ν := C.normalization
    (MMP.finite_irreducibleComponents_of_isIntegral C)
  obtain ⟨e⟩ := hL
  haveI : IsCurve k f := { topologicalKrullDim_eq_one := hC }
  haveI : IsFinite ν := isFinite_normalizationOverField k f
  haveI : Stacks.Ample.IsInvertibleModule _ (Scheme.Hom.relativeDifferentials (ν ≫ f)) :=
    MMP.Fourfold.isInvertible_relativeDifferentials_normalization_comp f _
  haveI := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule
    (Scheme.Hom.relativeDifferentials (ν ≫ f))
  let η := (Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L
  have hT : Nontrivial (cohomologyOverField k f
      ((Scheme.Modules.pushforward ν).obj ((Scheme.Modules.pullback ν).obj L)) 1) := by
    have e1 := cohomologyOverFieldPushforwardIsoOfIsAffineHom k ν f
      (Scheme.Hom.relativeDifferentials (ν ≫ f)) 1
    have e2 := cohomologyOverFieldIso k f ((Scheme.Modules.pushforward ν).mapIso e) 1
    have := nontrivial_cohomologyOverField_one_relativeDifferentials_normalization f hC
    exact (e1 ≪≫ e2.symm).symm.toLinearEquiv.toEquiv.nontrivial
  have hcoker : IsZero (cohomologyOverField k f (cokernel η) 1) := by
    haveI : IsLocallyNoetherian C :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k f
    haveI := Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule C L
    haveI hcur : IsCurve k (ν ≫ f) := (AlgebraicGeometry.normalizationModel' k f).isCurve
    haveI : Smooth (ν ≫ f) := (AlgebraicGeometry.normalizationModel' k f).smooth_structureMap
    haveI : SmoothOfRelativeDimension 1 (ν ≫ f) := smoothOfRelativeDimension_one_of_isCurve _ _
    haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials (ν ≫ f) 1
    haveI : L.IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f L 1
    have hΩ : (Scheme.Hom.relativeDifferentials (ν ≫ f)).IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k (ν ≫ f)
        _ 1
    haveI : ((Scheme.Modules.pullback ν).obj L).IsCoherent :=
      Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso e.symm hΩ
    haveI : ((Scheme.Modules.pushforward ν).obj ((Scheme.Modules.pullback ν).obj L)).IsCoherent :=
      Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite ν _
    haveI : ((𝟭 C.Modules).obj L).IsCoherent := ‹L.IsCoherent›
    haveI : ((Scheme.Modules.pullback ν ⋙ Scheme.Modules.pushforward ν).obj L).IsCoherent :=
      ‹((Scheme.Modules.pushforward ν).obj ((Scheme.Modules.pullback ν).obj L)).IsCoherent›
    haveI : (cokernel ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L)).IsCoherent :=
      isCoherent_cokernel _
    exact isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k f
      (cokernel ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L))
      (topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hC.le _ inferInstance
        (notMem_supp_cokernel_unit f hC L)) 1 one_pos
  have hsurj := surjective_cohomologyOverFieldMap_one_of_isZero_cokernel k f η
    (fun G => isZero_cohomologyOverField_of_topologicalKrullDim_le k f G (d := 1)
      hC.le (by norm_num)) hcoker
  exact @Function.Surjective.nontrivial _ _ hT _ hsurj

end MMP.Proofs.lem_fourfold_curve_normalization_pic_surjective

namespace MMP.Fourfold

open MMP.Proofs.lem_fourfold_curve_normalization_pic_surjective in
/-- **Invertible sheaves lift from the normalization of a curve.** Let `C` be an integral
projective curve over a perfect field `k`, with structure morphism `f`, and let
`ν : Cᵛ ⟶ C` be its normalization. Then every invertible sheaf on `Cᵛ` is the pullback along `ν`
of an invertible sheaf on `C`; there is an invertible sheaf `L` on `C` with
`ν^* L ≅ Ω_{Cᵛ/k} = ω_{Cᵛ}`; and every invertible `L` on `C` with `ν^* L ≅ ω_{Cᵛ}` has
`H¹(C, L) ≠ 0`. -/
@[mmp "lem_fourfold_curve_normalization_pic_surjective"]
public theorem liftsInvertible_normalization {k : Type u} [Field k] [PerfectField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProjectiveVariety k f]
    (hC : topologicalKrullDim C = 1) :
    let ν := C.normalization (MMP.finite_irreducibleComponents_of_isIntegral C)
    LiftsInvertible ν ∧
    (∃ (L : C.Modules) (_ : Stacks.Ample.IsInvertibleModule C L),
      Nonempty ((Scheme.Modules.pullback ν).obj L ≅ Scheme.Hom.relativeDifferentials (ν ≫ f))) ∧
    ∀ (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L],
      Nonempty ((Scheme.Modules.pullback ν).obj L ≅ Scheme.Hom.relativeDifferentials (ν ≫ f)) →
        Nontrivial (cohomologyOverField k f L 1) := by
  have hlift := MMP.Fourfold.liftsInvertible_normalization_of_topologicalKrullDim_le_one f hC.le
    (MMP.finite_irreducibleComponents_of_isIntegral C)
  haveI : IsCurve k f := { topologicalKrullDim_eq_one := hC }
  haveI hω : Stacks.Ample.IsInvertibleModule _ (Scheme.Hom.relativeDifferentials
      (C.normalization (MMP.finite_irreducibleComponents_of_isIntegral C) ≫ f)) :=
    MMP.Fourfold.isInvertible_relativeDifferentials_normalization_comp f _
  exact ⟨hlift, hlift _, fun L _ hL => nontrivial_cohomologyOverField_one f hC L hL⟩

end MMP.Fourfold

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open MMP MMP.Mori MMP.Fourfold

namespace MMP.Proofs.lem_fourfold_strict_fixed_coefficient_persists

/-- The pull-back of an affine family of real Cartier divisors is affine: in the coordinates of
`t -ᵥ δ` with respect to a basis `b`, `P t = P δ + ∑ᵢ cᵢ • (P (bᵢ +ᵥ δ) - P δ)`. -/
private theorem eq_add_sum_of_isRCartierPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    [CompactSpace Y] (f : Y ⟶ X) [IsDominant f]
    {W V : Type*} [AddCommGroup W] [Module ℝ W] [AddTorsor W V] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ W) (D : V →ᵃ[ℝ] RDivisor X) (P : V → RDivisor Y)
    (hP : ∀ t, MMP.Flips.IsRCartierPullback f (D t) (P t)) (δ t : V) :
    P t = P δ + ∑ i, b.repr (t -ᵥ δ) i • (P (b i +ᵥ δ) - P δ) := by
  have hsub : ∀ i, MMP.Flips.IsRCartierPullback f (D (b i +ᵥ δ) - D δ)
      (P (b i +ᵥ δ) - P δ) := fun i => by
    simpa [sub_eq_add_neg] using
      isRCartierPullback_add (hP (b i +ᵥ δ)) (isRCartierPullback_smul (-1) (hP δ))
  have hD : D t = D δ + ∑ i, b.repr (t -ᵥ δ) i • (D (b i +ᵥ δ) - D δ) := by
    have h1 : ∀ i, D (b i +ᵥ δ) - D δ = D.linear (b i) := fun i => by
      rw [AffineMap.map_vadd, vadd_eq_add, add_sub_cancel_right]
    simp_rw [h1, ← map_smul, ← map_sum, b.sum_repr]
    rw [add_comm, ← vadd_eq_add, ← AffineMap.map_vadd, vsub_vadd]
  refine MMP.Flips.IsRCartierPullback.eq f (hP t) ?_
  rw [hD]
  exact isRCartierPullback_add (hP δ)
    (isRCartierPullback_sum _ _ _ fun i _ => isRCartierPullback_smul _ (hsub i))

/-- The coefficients of the pull-back of an affine family of real Cartier divisors along a fixed
prime divisor are continuous in the parameter. -/
private theorem continuous_coeff_of_isRCartierPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    [CompactSpace Y] (f : Y ⟶ X) [IsDominant f]
    {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MetricSpace V] [NormedAddTorsor W V]
    (D : V →ᵃ[ℝ] RDivisor X) (P : V → RDivisor Y)
    (hP : ∀ t, MMP.Flips.IsRCartierPullback f (D t) (P t)) (Γ : Mori.PrimeDivisor Y) :
    Continuous fun t => (P t).coeff Γ := by
  classical
  refine continuous_iff_continuousAt.2 fun δ => ?_
  let b := Module.finBasis ℝ W
  have heq : (fun t => (P t).coeff Γ) = fun t =>
      (P δ).coeff Γ + ∑ i, b.repr (t -ᵥ δ) i * (P (b i +ᵥ δ) - P δ).coeff Γ := by
    funext t
    have hsum : ∀ F : Fin (Module.finrank ℝ W) → RDivisor Y,
        (∑ i, F i).coeff Γ = ∑ i, (F i).coeff Γ := fun F =>
      map_sum (DivisorWithCoeffs.coeffAddMonoidHom Γ) F Finset.univ
    rw [eq_add_sum_of_isRCartierPullback f b D P hP δ t]
    simp only [DivisorWithCoeffs.coeff_add, hsum, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  rw [heq]
  refine (continuous_const.add (continuous_finset_sum _ fun i _ => Continuous.mul ?_
    continuous_const)).continuousAt
  exact (continuous_apply i).comp ((b.equivFun.toLinearMap.continuous_of_finiteDimensional).comp
    (continuous_id.vsub continuous_const))

end MMP.Proofs.lem_fourfold_strict_fixed_coefficient_persists

namespace MMP.Fourfold

variable {k : Type u} [Field k] {X Y T Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  [IsIntegral X] [IsIntegral Y] [IsIntegral T]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsLocallyNoetherian T] [IsNormal T] [CompactSpace X] [CompactSpace Y] [CompactSpace T]

open MMP.Proofs.lem_fourfold_strict_fixed_coefficient_persists in
/-- **Persistence of strict exceptional fixed coefficients.** Let `p : T ⟶ X`, `q : T ⟶ Y` be
proper birational morphisms of normal varieties over `Z` (`p ≫ fX = q ≫ fY`), let `D`, `D'` be
affine families over a finite-dimensional real affine space `V` of real Cartier divisors on `X`,
`Y` with fixed finite supports, and let `P t`, `Q t` be the pull-backs `p^*D_t`, `q^*D'_t`. If
`q_*(P t - Q t) = 0` for every `t`, then there is a neighbourhood of `δ` on which every prime
divisor `G` of `X` with `0 < (p_*(P δ - Q δ)).coeff G` lies in the relative divisorial stable
base locus of `D t` over `Z`. -/
@[mmp "lem_fourfold_strict_fixed_coefficient_persists"]
public theorem eventually_isInRelativeDivisorialStableBase_of_coeff_pos
    {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MetricSpace V] [NormedAddTorsor W V]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT)
    (hZ : Mori.IsVariety k sZ)
    (p : T ⟶ X) (q : T ⟶ Y) (fX : X ⟶ Z) (fY : Y ⟶ Z)
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hfX : fX ≫ sZ = sX) (hfY : fY ≫ sZ = sY)
    (hZc : p ≫ fX = q ≫ fY)
    (D : V →ᵃ[ℝ] RDivisor X) (D' : V →ᵃ[ℝ] RDivisor Y)
    (hDc : ∀ t, RDivisor.IsRCartier (D t)) (hD'c : ∀ t, RDivisor.IsRCartier (D' t))
    (hDsupp : ∃ S : Finset (Mori.PrimeDivisor X), ∀ t, (D t).support ⊆ S)
    (hD'supp : ∃ S : Finset (Mori.PrimeDivisor Y), ∀ t, (D' t).support ⊆ S)
    (P Q : V → RDivisor T)
    (hP : ∀ t, MMP.Flips.IsRCartierPullback p (D t) (P t))
    (hQ : ∀ t, MMP.Flips.IsRCartierPullback q (D' t) (Q t))
    (hqE : ∀ t, RationalMap.transformDivisor q.toRationalMap (P t - Q t) = 0) (δ : V) :
    ∀ᶠ t in 𝓝 δ, ∀ G : Mori.PrimeDivisor X,
      0 < (RationalMap.transformDivisor p.toRationalMap (P δ - Q δ)).coeff G →
        IsInRelativeDivisorialStableBase fX (D t) G := by
  classical
  have := hp.isDominant
  have := hq.isDominant
  have hTX : IsNormalVariety k (p ≫ sX) := hpX ▸ hT
  -- only the finitely many primes of the support of `p_*E_δ` matter
  have hfin : ∀ G ∈ (RationalMap.transformDivisor p.toRationalMap (P δ - Q δ)).support,
      ∀ᶠ t in 𝓝 δ,
        0 < (RationalMap.transformDivisor p.toRationalMap (P δ - Q δ)).coeff G →
          IsInRelativeDivisorialStableBase fX (D t) G := by
    intro G _
    obtain ⟨G', _, _, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hTX hp G
    by_cases hpos : 0 < (RationalMap.transformDivisor p.toRationalMap (P δ - Q δ)).coeff G
    · have hcont : Continuous fun t => (P t - Q t).coeff G' :=
        ((continuous_coeff_of_isRCartierPullback p D P hP G').sub
          (continuous_coeff_of_isRCartierPullback q D' Q hQ G')).congr fun t =>
            (DivisorWithCoeffs.coeff_sub _ _ _).symm
      have h0 : 0 < (P δ - Q δ).coeff G' := hpos.trans_eq (htr _)
      filter_upwards [(hcont.tendsto δ).eventually (lt_mem_nhds h0)] with t ht _
      refine isInRelativeDivisorialStableBase_of_pos_transformDivisor hX hY hT p q fX fY hp hq
        hpX hqY hZc (hP t) (hQ t) (add_sub_cancel _ _).symm (hqE t) G ?_
      exact ht.trans_eq (htr _).symm
    · exact .of_forall fun t h => absurd h hpos
  filter_upwards [(Filter.eventually_all_finset _).2 hfin] with t ht G hG
  exact ht G (Finsupp.mem_support_iff.mpr hG.ne') hG

end MMP.Fourfold

end

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Mori MMP.Fourfold

namespace MMP.Proofs.lem_mmp_indexc_bad_locus_positive_fibres

/-- A proper birational morphism of complex varieties onto a normal variety is an isomorphism
over a neighbourhood of every point whose fibre has dimension at most `0`. -/
private lemma mem_biregularLocus_of_topologicalKrullDim_le {U R : Scheme.{0}}
    {sU : U ⟶ Spec (.of ℂ)} {sR : R ⟶ Spec (.of ℂ)} (hU : AlgebraicGeometry.IsVariety ℂ sU)
    (hR : AlgebraicGeometry.IsVariety ℂ sR)
    [IsNormal R] (f : U ⟶ R) (hf : f ≫ sR = sU) [IsProper f] (hb : IsBirationalMorphism f)
    {z : R} (hz : topologicalKrullDim (f ⁻¹' {z}) ≤ 0) : z ∈ biregularLocus f := by
  have := hU.toIsIntegral
  have := hR.toIsIntegral
  obtain ⟨⟨hO, hiso⟩, -, -⟩ := MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq
    ℂ hU hR f hf (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
  exact le_biregularLocus (V := ⟨_, hO⟩) hiso
    (MMP.Resolution.Bridges.finite_preimage_singleton_of_topologicalKrullDim_le f z hz)

end MMP.Proofs.lem_mmp_indexc_bad_locus_positive_fibres

namespace MMP.Fourfold

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

open MMP.Proofs.lem_mmp_indexc_bad_locus_positive_fibres in
/-- In a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, every closed point `z` of the bad
locus `badLocusBase fm fp` has a positive-dimensional fibre under `f⁻` or under `f⁺`. -/
@[mmp "lem_mmp_indexc_bad_locus_positive_fibres"]
public theorem IsThreefoldStepDiagram.pos_dim_fibre_of_mem_badLocusBase
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) {z : Z} (hz : IsClosed ({z} : Set Z))
    (hmem : z ∈ badLocusBase fm fp) :
    0 < topologicalKrullDim (fm ⁻¹' {z}) ∨ 0 < topologicalKrullDim (fp ⁻¹' {z}) := by
  by_contra! hne
  have hZ := h.isNormalVariety_target
  have := hZ.2
  have : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  have := h.isSmallMorphism_plus.isProper
  exact hmem ⟨mem_biregularLocus_of_topologicalKrullDim_le h.isNormalVariety_minus.1 hZ.1 fm
      h.comp_eq_minus h.isBirationalMorphism_minus hne.1,
    mem_biregularLocus_of_topologicalKrullDim_le h.isNormalVariety_plus.1 hZ.1 fp
      h.comp_eq_plus h.isSmallMorphism_plus.isBirationalMorphism hne.2⟩

end MMP.Fourfold

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Mori MMP.Fourfold

namespace MMP.Proofs.lem_mmp_indexc_lost_divisor_in_bad_locus

/-- A morphism which is an isomorphism over an open `V` preserves the coheight of points
lying over `V`. -/
private lemma coheight_eq_of_isBiregular {X Y : Scheme.{0}} (f : X ⟶ Y) {V : Y.Opens}
    (hV : IsBiregular f V) {x : X} (hx : f x ∈ V) :
    Order.coheight x = Order.coheight (f x) := by
  haveI : IsIso (f ∣_ V) := hV
  let x' : ((f ⁻¹ᵁ V : X.Opens) : Scheme) := ⟨x, hx⟩
  have h1 : (f ⁻¹ᵁ V).ι x' = x := rfl
  have h2 : V.ι ((f ∣_ V) x') = f x := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, h1]
  calc Order.coheight x = Order.coheight x' := by
        rw [← h1]; exact coheight_eq_of_isOpenImmersion (f ⁻¹ᵁ V).ι
    _ = Order.coheight ((f ∣_ V) x') :=
        (coheight_eq_of_isOpenImmersion (f ∣_ V)).symm
    _ = Order.coheight (f x) := by
        rw [← h2]; exact (coheight_eq_of_isOpenImmersion V.ι).symm

/-- If a valuation `u` of `k(Y)` dominates the local ring at `y`, then its restriction to
`k(X)` along a dominant morphism `f : Y ⟶ X` dominates the local ring at `f y`. -/
private lemma dominates_comap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (u : Valuation Y.functionField (WithZero (Multiplicative ℤ))) (y : Y)
    (h1 : ∀ a : Y.presheaf.stalk y, u (algebraMap _ Y.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
      u (algebraMap _ Y.functionField a) < 1) :
    (∀ a : X.presheaf.stalk (f y),
      u.comap (functionFieldMap f) (algebraMap _ X.functionField a) ≤ 1) ∧
    (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (f y)),
      u.comap (functionFieldMap f) (algebraMap _ X.functionField a) < 1) := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    exact h1 _
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    refine h2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))

/-- The key step: if `f⁻(η_E)` lies in the common biregular locus, then the centre on `X⁺` of
the valuation `ξ` corresponding to `ord_E` has coheight one. -/
private lemma coheight_centre_eq_one {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hZ : IsNormalVariety ℂ sZ) [IsDominant fm] [IsDominant fp]
    (E : MMP.Mori.PrimeDivisor Xm)
    (ξ : Valuation Xp.functionField (WithZero (Multiplicative ℤ)))
    (hξ : ξ.comap (functionFieldMap fp) = E.divisorialValuation.comap (functionFieldMap fm))
    (D : DivisorOver ℂ sXp) (hξD : ξ = D.valuation)
    (hηU : fm E.genericPoint ∈ commonBiregularLocus fm fp) :
    Order.coheight (D.f D.E.genericPoint) = 1 := by
  set y := D.f D.E.genericPoint
  obtain ⟨hm1, hm2⟩ := dominates_comap fm _ _
    (fun a => (PrimeDivisor.divisorialValuation_le_one_iff _ _).2 ⟨a, rfl⟩)
    (fun a ha => (E.divisorialValuation_algebraMap_lt_one_iff a).2 ha)
  obtain ⟨hp1, hp2⟩ := dominates_comap fp ξ y
    (fun a => hξD ▸ MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl a)
    (fun a ha => hξD ▸ MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D y rfl a ha)
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  have heq : fm E.genericPoint = fp y :=
    MMP.Positivity.DivisorOver.eq_of_dominates sZ _ hm1 hm2 (hξ ▸ hp1) (hξ ▸ hp2)
  rw [coheight_eq_of_isBiregular fp (isBiregular_commonBiregularLocus_right fm fp) (heq ▸ hηU),
    ← heq, ← coheight_eq_of_isBiregular fm (isBiregular_commonBiregularLocus_left fm fp) hηU,
    E.coheight_genericPoint]

end MMP.Proofs.lem_mmp_indexc_lost_divisor_in_bad_locus

namespace MMP.Fourfold

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsIntegral Z]

open MMP.Proofs.lem_mmp_indexc_lost_divisor_in_bad_locus in
/-- In a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, a prime divisor `E` of `X⁻` whose
valuation `ord_E` corresponds to a valuation of `k(X⁺)` exceptional over `X⁺` lies in the
negative-side bad locus `W⁻ = (f⁻)⁻¹(Σ)`. -/
@[mmp "lem_mmp_indexc_lost_divisor_in_bad_locus"]
public theorem IsThreefoldStepDiagram.support_subset_badLocusMinus
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (E : MMP.Mori.PrimeDivisor Xm)
    (hE : haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      ∃ ξ : Valuation Xp.functionField (WithZero (Multiplicative ℤ)),
      ξ.comap (functionFieldMap fp) = E.divisorialValuation.comap (functionFieldMap fm) ∧
        MMP.Intersection.IsExceptionalValuation ℂ sXp ξ) :
    (E.support : Set Xm) ⊆ (badLocusMinus fm fp : Set Xm) := by
  intro x hx
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  obtain ⟨ξ, hξ, D, -, hξD, hcod⟩ := hE
  rw [coe_badLocusMinus, Set.mem_preimage, coe_badLocusBase, Set.mem_compl_iff]
  intro hxU
  have hspec : E.genericPoint ⤳ x := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
  rw [MMP.Positivity.DivisorOver.codimension_center,
    coheight_centre_eq_one h.isNormalVariety_target E ξ hξ D hξD
      ((hspec.map fm.continuous).mem_open (commonBiregularLocus fm fp).isOpen hxU)] at hcod
  exact absurd hcod (by decide)

end MMP.Fourfold

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori
open scoped WithZero
open IsLocalRing

namespace MMP.Proofs.lem_mmp_indexd_echo_is_monomial

/-! ### Echo ideals are weighted monomial ideals -/

section Ideals

variable {R : Type*} [CommRing R]

/-- If `𝔪 = (x, t)` and `j ≥ 1`, the echo ideals `∑_a x^a 𝔪^{n - ja}` are the monomial ideals
generated by the `t^α x^β` with `α + jβ ≥ n`. -/
private lemma echoIdeal_eq_monomialIdeal {x t : R} {𝔪 : Ideal R}
    (h𝔪 : Ideal.span {x, t} = 𝔪) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    echoIdeal x 𝔪 j n = MMP.Resolution.monomialIdeal t x j n := by
  refine le_antisymm (iSup_le fun b => ?_) (Ideal.span_le.mpr ?_)
  · rw [← h𝔪, Set.pair_comm, ← monomialIdeal_one_eq_pow, MMP.Resolution.monomialIdeal,
      Ideal.span_mul_span']
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, rfl, _, ⟨a', b', h, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨a', b + b', ?_, by ring⟩
    have : b' ≤ j * b' := Nat.le_mul_of_pos_left b' hj
    rw [Nat.mul_add]
    omega
  · rintro _ ⟨a, b, h, rfl⟩
    refine Ideal.mem_iSup_of_mem b ?_
    rw [mul_comm (t ^ a)]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
      (Ideal.pow_le_pow_right (show n - j * b ≤ a by omega) (Ideal.pow_mem_pow ?_ a))
    exact h𝔪 ▸ Ideal.subset_span (by simp)

end Ideals

private lemma span_pair_eq_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A] {x y : A}
    (hxy : IsRegularSystemOfParameters ![x, y]) :
    Ideal.span {x, y} = IsLocalRing.maximalIdeal A := by
  rw [← hxy.1]; congr 1; ext; simp [Matrix.range_cons, Set.pair_comm]

/-- The monomial valuation `v_{x,t;j}(f)` is `M` exactly when `M` is the greatest `n` with
`f ∈ (x^a t^b : ja + b ≥ n)`. -/
private lemma monomialValuation_eq_coe_iff {R : Type*} [CommRing R] (x t : R) (j : ℕ) (f : R)
    (M : ℕ) :
    MMP.Resolution.monomialValuation t x j f = M ↔
      IsGreatest {n | f ∈ MMP.Resolution.monomialIdeal t x j n} M := by
  have h1 : (1 : R) ∈ MMP.Resolution.monomialIdeal t x j 0 :=
    Ideal.subset_span ⟨0, 0, Nat.zero_le _, by simp⟩
  have h0 : f ∈ MMP.Resolution.monomialIdeal t x j 0 := by
    rw [Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one]; trivial
  exact (isGreatest_iff_iSup_eq ⟨0, h0⟩).symm

/-- A point whose local ring has a regular system of parameters of length two is the generic
point of a closed subset of codimension two. -/
private lemma codimension_eq_two {X : Scheme.{u}} (Z : IrreducibleCloseds X)
    {x t : X.presheaf.stalk Z.isIrreducible.genericPoint}
    (ht : IsRegularSystemOfParameters ![x, t]) : codimension Z = 2 :=
  WithBot.coe_injective (by rw [codimension_eq_ringKrullDim_stalk_genericPoint, ht.2]; rfl)

/-- **An echo is the monomial valuation `v_{x,t;j}`.** In the setting of an echo, for a local
equation `x` of `S` at `η_V` completed by `t` to a regular system of parameters, a valuation is an
echo of order `j` of `S` at `V` if and only if it is `v_{x,t;j}`. -/
private theorem isEcho_iff_isWeightedMonomialValuation {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    {L : Finset (MMP.Mori.PrimeDivisor Y)} {S : MMP.Mori.PrimeDivisor Y}
    {V : IrreducibleCloseds Y} {j : ℕ}
    (hY : IsNormalVariety k sY) (hdim : topologicalKrullDim Y = 3) (hS : S ∈ L)
    (hVS : (V : Set Y) ⊆ S.support) (hV : topologicalKrullDim (V : Set Y) = 1)
    (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L) (hj : 1 ≤ j)
    {x t : Y.presheaf.stalk V.isIrreducible.genericPoint}
    (hx : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x})
    (ht : IsRegularSystemOfParameters ![x, t]) {ξ : Valuation Y.functionField ℤᵐ⁰} :
    IsEcho sY L S V j ξ ↔ IsWeightedMonomialValuation sY V x t j ξ := by
  have hval : ∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint,
      ((∃ M : ℕ, IsGreatest {n : ℕ | f ∈ echoIdeal x
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk V.isIrreducible.genericPoint)) j n} M ∧
          ξ (algebraMap _ Y.functionField f) = WithZero.exp (-(M : ℤ))) ↔
        ∃ M : ℕ, MMP.Resolution.monomialValuation t x j f = M ∧
          ξ (algebraMap _ Y.functionField f) = WithZero.exp (-(M : ℤ))) := by
    intro f
    simp only [echoIdeal_eq_monomialIdeal (span_pair_eq_maximalIdeal ht) hj,
      monomialValuation_eq_coe_iff]
  constructor
  · rintro ⟨-, -, -, -, -, -, -, -, x', hx', hξ⟩
    have hξx := isEchoValue_of_span_eq (hx'.symm.trans hx) hξ
    exact ⟨hY, codimension_eq_two V ht, (mem_oneLabelSmoothLocus_iff.1 hη).1, ht, hj,
      fun f hf => (hval f).1 (hξx f hf)⟩
  · intro h
    exact ⟨hY, hdim, hS, hVS, hV, hη, hj, h.isNormalizedDivisorialValuation_and_isCentre.2, x, hx,
      fun f hf => (hval f).2 (h.2.2.2.2.2 f hf)⟩

/-! ### Monomial conditions on an open neighbourhood -/

@[to_additive]
private lemma pair_prod {ι M : Type*} [DecidableEq ι] [CommMonoid M] {p q : ι} (hpq : p ≠ q)
    (g : ({p, q} : Finset ι) → M) :
    ∏ i, g i = g ⟨p, by simp⟩ * g ⟨q, by simp⟩ := by
  refine Finset.prod_eq_mul _ _ (by simp [Subtype.ext_iff, hpq]) (fun c _ hc => ?_)
    (by simp) (by simp)
  rcases c with ⟨c, hc'⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
  rcases hc' with rfl | rfl <;> simp at hc

private lemma weightedMonomialIdeal_pair {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {p q : ι} (hpq : p ≠ q) (a b : R) (j m : ℕ) :
    weightedMonomialIdeal (ι := ({p, q} : Finset ι)) (fun E => if E.1 = p then a else b)
      (fun E => if E.1 = p then j else 1) m = MMP.Resolution.monomialIdeal b a j m := by
  have hqp : q ≠ p := hpq.symm
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro r ⟨β, hβ, rfl⟩
    rw [pair_sum hpq] at hβ
    rw [pair_prod hpq]
    refine Ideal.subset_span ⟨β ⟨q, by simp⟩, β ⟨p, by simp⟩, ?_, ?_⟩
    · simp [hqp] at hβ; omega
    · simp [hqp, mul_comm]
  · rintro r ⟨i, l, h, rfl⟩
    refine Ideal.subset_span ⟨fun E => if E.1 = p then l else i, ?_, ?_⟩
    · rw [pair_sum hpq]; simp [hqp]; omega
    · rw [pair_prod hpq]; simp [hqp, mul_comm]

open Classical in
private lemma isMonomialValuationOfWeight_pair_iff {k : Type u} [Field k]
    {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [IsIntegral W]
    (hW : MMP.Mori.IsVariety k sW) (hsm : IsSmoothScheme sW)
    {SU LU : MMP.Mori.PrimeDivisor W} {Z : IrreducibleCloseds W} (xU tU : Γ(W, ⊤))
    (hSUx : ∀ u : W, IdealSheafData.stalk SU.idealSheaf u =
      Ideal.span {W.presheaf.germ ⊤ u trivial xU})
    (hLUt : ∀ u : W, IdealSheafData.stalk LU.idealSheaf u =
      Ideal.span {W.presheaf.germ ⊤ u trivial tU})
    (hne : SU ≠ LU) (hsnc : (MMP.Intersection.reducedDivisorOf {SU, LU}).IsSNC sW)
    (hZmax : Maximal (fun T : Set W => IsIrreducible T ∧ T ⊆ SU.support ∩ LU.support) (Z : Set W))
    {j : ℕ} (hj : 1 ≤ j) (ξU : Valuation W.functionField ℤᵐ⁰) :
    IsMonomialValuationOfWeight sW (MMP.Intersection.reducedDivisorOf {SU, LU}) {SU, LU} Z
        (fun E => W.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial
          (if E.1 = SU then xU else tU))
        (fun E => if E.1 = SU then j else 1) ξU ↔
      MMP.Intersection.IsCentre k sW ξU Z ∧
        ∀ f : W.presheaf.stalk Z.isIrreducible.genericPoint, f ≠ 0 →
          ∃ M : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Resolution.monomialIdeal
              (W.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial tU)
              (W.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial xU) j m} M ∧
            ξU (algebraMap _ W.functionField f) = WithZero.exp (-(M : ℤ)) := by
  have hz : (fun E : ({SU, LU} : Finset _) => W.presheaf.germ ⊤ Z.isIrreducible.genericPoint
      trivial (if E.1 = SU then xU else tU)) = fun E => if E.1 = SU then
        W.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial xU else
        W.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial tU :=
    funext fun E => apply_ite _ _ _ _
  rw [IsMonomialValuationOfWeight, hz]
  simp only [weightedMonomialIdeal_pair hne]
  have hmax : Maximal (fun S : Set W => IsIrreducible S ∧
      S ⊆ ⋂ E ∈ ({SU, LU} : Finset _), E.support) (Z : Set W) := by
    simpa only [Finset.set_biInter_insert, Finset.set_biInter_singleton] using hZmax
  have hst : ∀ E : ({SU, LU} : Finset _), IdealSheafData.stalk E.1.idealSheaf
      Z.isIrreducible.genericPoint = Ideal.span {(W.presheaf.germ ⊤ Z.isIrreducible.genericPoint
        trivial (if E.1 = SU then xU else tU))} := by
    rintro ⟨E, hE⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl
    · simp [hSUx]
    · simp [hne.symm, hLUt]
  constructor
  · rintro ⟨-, -, -, -, -, -, -, -, -, hc, hv⟩
    exact ⟨hc, hv⟩
  · rintro ⟨hc, hv⟩
    refine ⟨hW, hsm, MMP.Intersection.isReducedEffective_reducedDivisorOf _, hsnc,
      ⟨SU, by simp⟩, by rw [MMP.Intersection.support_reducedDivisorOf], hmax, hst,
      fun E => ?_, hc, hv⟩
    split_ifs <;> omega

/-- A variety over a field is a Noetherian scheme. -/
private lemma isNoetherian_of_isVariety {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY) : IsNoetherian Y := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := by
    rw [← isCompact_univ_iff, ← Set.preimage_univ (f := sY.base)]
    exact QuasiCompact.isCompact_preimage _ isOpen_univ isCompact_univ
  exact ⟨⟩

private lemma isVariety_ι_comp {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY) (U : Y.Opens) [Nonempty U] :
    MMP.Mori.IsVariety k (U.ι ≫ sY) := by
  have := isNoetherian_of_isVariety hY
  have : IsIntegral Y := hY.toIsIntegral
  have : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  exact { }

private lemma isSmoothScheme_ι_comp {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY) (U : Y.Opens)
    (hU : ∀ u ∈ U, IsRegularLocalRing (Y.presheaf.stalk u)) :
    IsSmoothScheme (U.ι ≫ sY) := by
  have hs : Smooth (U.ι ≫ sY) := by
    rw [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
    intro u
    have hr : IsRegularLocalRing (Y.presheaf.stalk (U.ι u)) := hU _ u.2
    exact @IsRegularLocalRing.of_ringEquiv _ _ hr _ _
      (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv
  refine eq_top_iff.2 (le_sSup ?_)
  change Smooth ((⊤ : U.toScheme.Opens).ι ≫ U.ι ≫ sY)
  infer_instance

/-- A ring equivalence of local rings carries a regular system of parameters to one. -/
private theorem isRegularSystemOfParameters_map_ringEquiv {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) {n : ℕ} {w : Fin n → A}
    (hw : IsRegularSystemOfParameters w) : IsRegularSystemOfParameters fun j => e (w j) := by
  refine ⟨?_, (ringKrullDim_eq_of_ringEquiv e).symm.trans hw.2⟩
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← hw.1, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Germs at `p ∈ U` of sections of an open `U ⊆ Y` whose images in `𝒪_{Y,p}` form a regular
system of parameters form one of `𝒪_{U,p}`. -/
private lemma isRegularSystemOfParameters_germ {Y : Scheme.{u}} (U : Y.Opens)
    (p : U.toScheme) {x t : Y.presheaf.stalk (U.ι p)} {xU tU : Γ(U.toScheme, ⊤)}
    (hxU : U.ι.stalkMap p x = U.toScheme.presheaf.germ ⊤ p trivial xU)
    (htU : U.ι.stalkMap p t = U.toScheme.presheaf.germ ⊤ p trivial tU)
    (ht : IsRegularSystemOfParameters ![x, t]) :
    IsRegularSystemOfParameters
      ![U.toScheme.presheaf.germ ⊤ p trivial xU, U.toScheme.presheaf.germ ⊤ p trivial tU] := by
  rw [← hxU, ← htU]
  convert isRegularSystemOfParameters_map_ringEquiv
    (asIso (U.ι.stalkMap p)).commRingCatIsoToRingEquiv ht using 1
  funext i; fin_cases i <;> rfl

private lemma genericPoint_eq_of_coe_eq_preimage {Y : Scheme.{u}} {V : IrreducibleCloseds Y}
    {U : Y.Opens} {p : U.toScheme} (hp : U.ι p = V.isIrreducible.genericPoint)
    {Z : IrreducibleCloseds U.toScheme} (hZ : (Z : Set U.toScheme) = U.ι ⁻¹' V) :
    Z.isIrreducible.genericPoint = p := by
  have h1 := Z.isIrreducible.isGenericPoint_genericPoint_closure
  rw [Z.isClosed.closure_eq] at h1
  have hV := V.isIrreducible.isGenericPoint_genericPoint_closure
  rw [V.isClosed.closure_eq] at hV
  have h2 := U.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image {p}
  rw [Set.image_singleton, hp, hV.def, ← hZ] at h2
  exact h1.eq h2

private lemma mem_monomialIdeal_map_iff {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (a b : R) (w ν : ℕ) (f : R) :
    e f ∈ MMP.Resolution.monomialIdeal (e a) (e b) w ν ↔
      f ∈ MMP.Resolution.monomialIdeal a b w ν := by
  have : MMP.Resolution.monomialIdeal (e a) (e b) w ν =
      (MMP.Resolution.monomialIdeal a b w ν).map e := by
    rw [MMP.Resolution.monomialIdeal, MMP.Resolution.monomialIdeal, Ideal.map_span]
    congr 1
    ext r
    constructor
    · rintro ⟨i, l, h, rfl⟩
      exact ⟨a ^ i * b ^ l, ⟨i, l, h, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨i, l, h, rfl⟩, rfl⟩
      exact ⟨i, l, h, by simp⟩
  rw [this, Ideal.apply_mem_of_equiv_iff]

private lemma forall_value_iff_of_isOpenImmersion {Y : Scheme.{u}} [IsIntegral Y]
    (U : Y.Opens) [Nonempty U] [IsDominant U.ι] (p : U.toScheme)
    (x t : Y.presheaf.stalk (U.ι p)) (j : ℕ) (ξU : Valuation U.toScheme.functionField ℤᵐ⁰) :
    (∀ f : Y.presheaf.stalk (U.ι p), f ≠ 0 →
      ∃ M : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Resolution.monomialIdeal t x j m} M ∧
        ξU.comap (functionFieldMap U.ι) (algebraMap _ Y.functionField f) =
          WithZero.exp (-(M : ℤ))) ↔
    (∀ g : U.toScheme.presheaf.stalk p, g ≠ 0 →
      ∃ M : ℕ, IsGreatest {m : ℕ | g ∈ MMP.Resolution.monomialIdeal
          ((U.ι.stalkMap p).hom t) ((U.ι.stalkMap p).hom x) j m} M ∧
        ξU (algebraMap _ U.toScheme.functionField g) = WithZero.exp (-(M : ℤ))) := by
  let e := (asIso (U.ι.stalkMap p)).commRingCatIsoToRingEquiv
  have hv : ∀ f, ξU.comap (functionFieldMap U.ι) (algebraMap _ Y.functionField f) =
      ξU (algebraMap _ U.toScheme.functionField (e f)) := fun f => by
    rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]; rfl
  rw [show (U.ι.stalkMap p).hom t = e t from rfl, show (U.ι.stalkMap p).hom x = e x from rfl]
  simp only [hv]
  constructor
  · intro h g hg
    obtain ⟨f, rfl⟩ := e.surjective g
    simpa only [mem_monomialIdeal_map_iff] using h f (by simpa using hg)
  · intro h f hf
    simpa only [mem_monomialIdeal_map_iff] using h (e f) (by simpa using hf)

/-! ### The neighbourhood `U` and the monomial condition on it -/

section Neighbourhood

/-- A section on `W ⊇ U`, as a global section of the open subscheme `U`. -/
private noncomputable def sectionOn {Y : Scheme.{u}} {W U : Y.Opens} (h : U ≤ W)
    (f : Γ(Y, W)) : Γ(U.toScheme, ⊤) :=
  U.toScheme.presheaf.map (homOfLE (show ⊤ ≤ U.ι ⁻¹ᵁ W from fun u _ => h u.2)).op
    ((U.ι.app W).hom f)

private theorem germ_sectionOn {Y : Scheme.{u}} {W U : Y.Opens} (h : U ≤ W)
    (f : Γ(Y, W)) (u : U.toScheme) :
    U.toScheme.presheaf.germ ⊤ u trivial (sectionOn h f) =
      (U.ι.stalkMap u).hom (Y.presheaf.germ W (U.ι u) (h u.2) f) := by
  have h1 := Scheme.Hom.germ_stalkMap U.ι W u (h u.2)
  have h2 := congrArg (fun φ => φ.hom f) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2, sectionOn]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- Near a point where the quotient of the local ring by an ideal sheaf is regular, it stays
regular. -/
private theorem exists_isOpen_forall_isRegularLocalRing_quotient {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (I : Y.IdealSheafData) {y : Y} (hy : y ∈ I.support)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk I y)) :
    ∃ W : Y.Opens, y ∈ W ∧ ∀ u ∈ W, u ∈ I.support →
      IsRegularLocalRing (Y.presheaf.stalk u ⧸ IdealSheafData.stalk I u) := by
  have hopen := MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (I.subschemeι ≫ sY)
  obtain ⟨W, hW, hWeq⟩ := I.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.mp hopen
  have hrange : ∀ u, u ∈ I.support → ∃ z : I.subscheme, I.subschemeι z = u := fun u hu => by
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι] at hu
    exact hu
  obtain ⟨z, rfl⟩ := hrange y hy
  have hz : z ∈ regularLocus I.subscheme :=
    IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv I z)
  refine ⟨⟨W, hW⟩, (hWeq ▸ hz : z ∈ I.subschemeι ⁻¹' W), fun u hu hus => ?_⟩
  obtain ⟨z', rfl⟩ := hrange u hus
  have hz' : z' ∈ regularLocus I.subscheme := hWeq ▸ (hu : z' ∈ I.subschemeι ⁻¹' W)
  have : IsRegularLocalRing (I.subscheme.presheaf.stalk z') := hz'
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv I z').symm

/-- The one-label smooth locus is open. -/
private theorem isOpen_oneLabelSmoothLocus {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (L : Finset (MMP.Mori.PrimeDivisor Y)) : IsOpen (oneLabelSmoothLocus L) := by
  refine (MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType sY).sdiff
    (IsClosed.union ?_ ?_)
  · refine isClosed_biUnion_finset fun S _ => ?_
    refine S.idealSheaf.subschemeι.isClosedEmbedding.isClosedMap _ ?_
    exact (MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType
      (S.idealSheaf.subschemeι ≫ sY)).isClosed_compl
  · refine isClosed_biUnion_finset fun S _ => isClosed_biUnion_finset fun S' _ => ?_
    exact isClosed_iUnion_of_finite fun _ => S.idealSheaf.support.isClosed.inter
      S'.idealSheaf.support.isClosed

private theorem exists_mul_mem_of_map_eq_span {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [IsNoetherianRing R]
    (J : Ideal R) (g : R) (h : J.map (algebraMap R S) = Ideal.span {algebraMap R S g}) :
    ∃ s ∉ p, s * g ∈ J ∧ ∀ j ∈ J, s * j ∈ Ideal.span {g} := by
  classical
  have hmem : ∀ (I : Ideal R) (a : R), algebraMap R S a ∈ I.map (algebraMap R S) →
      ∃ s ∈ p.primeCompl, s * a ∈ I := by
    intro I a ha
    obtain ⟨⟨⟨j, hj⟩, ⟨s', hs'⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl S).1 ha
    rw [← map_mul] at e
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).1 e
    refine ⟨c * s', p.primeCompl.mul_mem hc hs', ?_⟩
    have : c * s' * a = c * j := by simp only at hc'; rw [← hc']; ring
    rw [this]
    exact I.mul_mem_left _ hj
  obtain ⟨s0, hs0, hs0g⟩ := hmem J g (h ▸ Ideal.mem_span_singleton_self _)
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian J : J.FG)
  have hgen : ∀ j ∈ G, ∃ s ∈ p.primeCompl, s * j ∈ Ideal.span {g} := by
    intro j hj
    refine hmem _ j ?_
    rw [Ideal.map_span, Set.image_singleton, ← h]
    exact Ideal.mem_map_of_mem _ (hG ▸ Submodule.subset_span hj)
  choose s_ hs_ hs_j using hgen
  set s1 : R := ∏ j ∈ G.attach, s_ j.1 j.2
  have hs1 : s1 ∈ p.primeCompl := Submonoid.prod_mem _ fun j _ => hs_ j.1 j.2
  have hs1J : ∀ j ∈ J, s1 * j ∈ Ideal.span {g} := by
    intro j hj
    rw [← hG] at hj
    induction hj using Submodule.span_induction with
    | mem j hj =>
      have : s1 = s_ j hj * ∏ i ∈ G.attach.erase ⟨j, hj⟩, s_ i.1 i.2 :=
        (Finset.mul_prod_erase _ (fun i : G => s_ i.1 i.2) (Finset.mem_attach G ⟨j, hj⟩)).symm
      rw [this, mul_comm (s_ j hj), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hs_j j hj)
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul r a _ ha => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ ha
  refine ⟨s0 * s1, p.primeCompl.mul_mem hs0 hs1, ?_, fun j hj => ?_⟩
  · rw [mul_comm s0, mul_assoc]; exact J.mul_mem_left _ hs0g
  · rw [mul_comm s0, mul_assoc, mul_left_comm]
    exact Ideal.mul_mem_left _ _ (hs1J j hj)

/-- **Spreading out a principal stalk.** If the stalk at `y` of an ideal sheaf on a locally
Noetherian scheme is generated by the germ of a section `f`, then so is its stalk at every point
of a neighbourhood of `y`. -/
private theorem exists_forall_stalk_eq_span {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) {W : Y.Opens} (f : Γ(Y, W)) {y : Y} (hyW : y ∈ W)
    (h : IdealSheafData.stalk I y = Ideal.span {Y.presheaf.germ W y hyW f}) :
    ∃ W' : Y.Opens, y ∈ W' ∧ ∃ hW' : W' ≤ W, ∀ u (hu : u ∈ W'),
      IdealSheafData.stalk I u = Ideal.span {Y.presheaf.germ W u (hW' hu) f} := by
  obtain ⟨A, hA, hyA, hAW⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := W) hyW
  have := IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  set g : Γ(Y, A) := Y.presheaf.map (homOfLE hAW).op f
  have hg : ∀ u (hu : u ∈ A), Y.presheaf.germ A u hu g = Y.presheaf.germ W u (hAW hu) f :=
    fun u hu => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  letI : Algebra Γ(Y, A) (Y.presheaf.stalk y) := (Y.presheaf.germ A y hyA).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) (hA.primeIdealOf ⟨y, hyA⟩).asIdeal :=
    hA.isLocalization_stalk ⟨y, hyA⟩
  have hmap : (I.ideal ⟨A, hA⟩).map (algebraMap Γ(Y, A) (Y.presheaf.stalk y)) =
      Ideal.span {algebraMap Γ(Y, A) (Y.presheaf.stalk y) g} := by
    have := IdealSheafData.stalk_eq_map_germ I y ⟨A, hA⟩ hyA
    rw [h, ← hg y hyA] at this
    exact this.symm
  obtain ⟨s, hsp, hsg, hsJ⟩ := exists_mul_mem_of_map_eq_span (S := Y.presheaf.stalk y)
    (hA.primeIdealOf ⟨y, hyA⟩).asIdeal _ _ hmap
  refine ⟨Y.basicOpen s, ?_, (Y.basicOpen_le s).trans hAW, fun u hu => ?_⟩
  · rw [Scheme.mem_basicOpen _ _ _ hyA]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ _ s).2 hsp
  have huA : u ∈ A := Y.basicOpen_le s hu
  have hunit : IsUnit (Y.presheaf.germ A u huA s) := (Scheme.mem_basicOpen _ _ _ huA).1 hu
  rw [IdealSheafData.stalk_eq_map_germ I u ⟨A, hA⟩ huA, ← hg u huA]
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun j hj => ?_) ?_
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hsJ j hj)
    have := congrArg (Y.presheaf.germ A u huA).hom hc
    rw [map_mul, map_mul] at this
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨hunit.unit⁻¹ * (Y.presheaf.germ A u huA).hom c, ?_⟩
    rw [mul_assoc, this, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hm : (Y.presheaf.germ A u huA).hom (s * g) ∈ (I.ideal ⟨A, hA⟩).map
        (Y.presheaf.germ A u huA).hom := Ideal.mem_map_of_mem _ hsg
    rw [map_mul] at hm
    have := Ideal.mul_mem_left _ (hunit.unit⁻¹ : (Y.presheaf.stalk u)ˣ).1 hm
    rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this

/-- A lift of an element of the maximal ideal of a quotient lies in the maximal ideal. -/
private theorem mem_maximalIdeal_of_mk_mem {A : Type*} [CommRing A] [IsLocalRing A]
    (K : Ideal A) [IsLocalRing (A ⧸ K)] {a : A}
    (ha : Ideal.Quotient.mk K a ∈ maximalIdeal (A ⧸ K)) : a ∈ maximalIdeal A :=
  (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (hu.map _)

/-- **Lifting a regular system of parameters of a quotient.** If `A ⧸ K` has a regular system of
parameters `w`, and `z` is a family in `𝔪_A` of length `dim A` whose span contains `K` and
which contains lifts of all the `wᵢ`, then `z` is a regular system of parameters of `A`. -/
private theorem isRegularSystemOfParameters_of_lift {A : Type*} [CommRing A] [IsLocalRing A]
    (K : Ideal A) [IsLocalRing (A ⧸ K)] {n N : ℕ} {w : Fin n → A ⧸ K}
    (hw : IsRegularSystemOfParameters w) (z : Fin N → A) (hzm : ∀ i, z i ∈ maximalIdeal A)
    (hzK : K ≤ Ideal.span (Set.range z)) (hlift : ∀ i, ∃ j, Ideal.Quotient.mk K (z j) = w i)
    (hN : ringKrullDim A = N) : IsRegularSystemOfParameters z := by
  refine ⟨le_antisymm (Ideal.span_le.2 (Set.range_subset_iff.2 hzm)) ?_, hN⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := K)
  haveI : IsLocalHom (Ideal.Quotient.mk K) := IsLocalHom.of_surjective _ hsurj
  have hm : maximalIdeal A = (maximalIdeal (A ⧸ K)).comap (Ideal.Quotient.mk K) := by
    ext a
    exact ⟨fun ha => (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha
      (isUnit_of_map_unit _ _ hu), fun ha => mem_maximalIdeal_of_mk_mem K ha⟩
  rw [hm, ← hw.1]
  calc Ideal.comap (Ideal.Quotient.mk K) (Ideal.span (Set.range w))
      ≤ Ideal.comap (Ideal.Quotient.mk K) ((Ideal.span (Set.range z)).map (Ideal.Quotient.mk K)) :=
        Ideal.comap_mono (Ideal.span_le.2 (Set.range_subset_iff.2 fun i => by
          obtain ⟨j, hj⟩ := hlift i
          rw [← hj]
          exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)))
    _ = Ideal.span (Set.range z) := by
        rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.2 hzK]

/-- In a regular local ring, a nonzero `a ∈ 𝔪` with `A ⧸ (a)` regular is the first member of a
regular system of parameters. -/
private theorem exists_isRegularSystemOfParameters_cons {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {a : A} (ham : a ∈ maximalIdeal A) (ha0 : a ≠ 0)
    (hreg : IsRegularLocalRing (A ⧸ Ideal.span {a})) :
    ∃ (n : ℕ) (z : Fin (n + 1) → A), IsRegularSystemOfParameters z ∧ z 0 = a := by
  have := IsRegularLocalRing.isDomain A
  obtain ⟨n, w, hw⟩ := exists_isRegularSystemOfParameters (A ⧸ Ideal.span {a})
  have hdim : ringKrullDim (A ⧸ Ideal.span {a}) + 1 = ringKrullDim A :=
    Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha0)
      (p := maximalIdeal A) (maximalIdeal_height_eq_ringKrullDim) ham
  choose w' hw' using fun i => Ideal.Quotient.mk_surjective (I := Ideal.span {a}) (w i)
  have hw'm : ∀ i, w' i ∈ maximalIdeal A := fun i => mem_maximalIdeal_of_mk_mem _ (by
    rw [hw' i, ← hw.1]; exact Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨n, Fin.cons a w', isRegularSystemOfParameters_of_lift _ hw _ ?_ ?_ ?_ ?_, rfl⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ham
    · simpa using hw'm i
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨0, rfl⟩
  · exact fun i => ⟨i.succ, by simpa using hw' i⟩
  · rw [← hdim, hw.2]; rfl

/-- In a regular local ring, if `a, b ∈ 𝔪`, `a ≠ 0`, `b ∉ (a)`, and `A ⧸ (a)` and
`A ⧸ (a, b)` are regular, then `a, b` are the first two members of a regular system of
parameters. -/
private theorem exists_isRegularSystemOfParameters_cons_cons {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {a b : A} (ham : a ∈ maximalIdeal A) (hbm : b ∈ maximalIdeal A)
    (ha0 : a ≠ 0) (hba : b ∉ Ideal.span {a})
    (hreg : IsRegularLocalRing (A ⧸ Ideal.span {a}))
    (hreg2 : IsRegularLocalRing (A ⧸ (Ideal.span {a} ⊔ Ideal.span {b}))) :
    ∃ (n : ℕ) (z : Fin (n + 2) → A), IsRegularSystemOfParameters z ∧ z 0 = a ∧ z 1 = b := by
  have := IsRegularLocalRing.isDomain A
  have := IsRegularLocalRing.isDomain (A ⧸ Ideal.span {a})
  obtain ⟨n, w, hw⟩ := exists_isRegularSystemOfParameters (A ⧸ (Ideal.span {a} ⊔ Ideal.span {b}))
  have hdim1 : ringKrullDim (A ⧸ Ideal.span {a}) + 1 = ringKrullDim A :=
    Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha0)
      (p := maximalIdeal A) (maximalIdeal_height_eq_ringKrullDim) ham
  set b' := Ideal.Quotient.mk (Ideal.span {a}) b
  have hb'0 : b' ≠ 0 := fun h => hba (Ideal.Quotient.eq_zero_iff_mem.1 h)
  haveI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {a})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hb'm : b' ∈ maximalIdeal (A ⧸ Ideal.span {a}) := (mem_maximalIdeal _).2 fun hu =>
    (mem_maximalIdeal _).1 hbm (isUnit_of_map_unit _ _ hu)
  have hdim2 : ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {b'}) + 1 =
      ringKrullDim (A ⧸ Ideal.span {a}) :=
    Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hb'0)
      (p := maximalIdeal _) (maximalIdeal_height_eq_ringKrullDim) hb'm
  have he : ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {b'}) =
      ringKrullDim (A ⧸ (Ideal.span {a} ⊔ Ideal.span {b})) := by
    have : Ideal.span {b'} = (Ideal.span {b}).map (Ideal.Quotient.mk (Ideal.span {a})) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [this]
    exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup _ _)
  choose w' hw' using fun i =>
    Ideal.Quotient.mk_surjective (I := Ideal.span {a} ⊔ Ideal.span {b}) (w i)
  have hw'm : ∀ i, w' i ∈ maximalIdeal A := fun i => mem_maximalIdeal_of_mk_mem _ (by
    rw [hw' i, ← hw.1]; exact Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨n, Fin.cons a (Fin.cons b w'),
    isRegularSystemOfParameters_of_lift _ hw _ ?_ ?_ ?_ ?_, rfl, rfl⟩
  · intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact ham
    · exact hbm
    · simpa using hw'm i
  · refine sup_le ?_ ?_ <;> rw [Ideal.span_le, Set.singleton_subset_iff]
    · exact Ideal.subset_span ⟨0, rfl⟩
    · exact Ideal.subset_span ⟨1, rfl⟩
  · exact fun i => ⟨i.succ.succ, by simpa using hw' i⟩
  · rw [← hdim1, ← hdim2, he, hw.2]; push_cast; ring_nf

/-- A member of a regular system of parameters of `𝒪_{Y,y}` cuts out a prime divisor through
`y`: the closure of the generization of `y` at the prime it generates. -/
private theorem exists_primeDivisor_stalk_eq_span {Y : Scheme.{u}} {y : Y}
    [IsRegularLocalRing (Y.presheaf.stalk y)] {n : ℕ} {z : Fin n → Y.presheaf.stalk y}
    (hz : IsRegularSystemOfParameters z) (m : Fin n) :
    ∃ E : MMP.Mori.PrimeDivisor Y, y ∈ E.support ∧
      IdealSheafData.stalk E.idealSheaf y = Ideal.span {z m} := by
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  have hP := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hz m
  set q : PrimeSpectrum (Y.presheaf.stalk y) := ⟨Ideal.span {z m}, hP⟩
  have hz0 : z m ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz m
  have hzu : ¬ IsUnit (z m) := fun hu => hP.ne_top (Ideal.span_singleton_eq_top.2 hu)
  have h1 : Order.coheight (Y.fromSpecStalk y q) = 1 := by
    refine (Stacks.Chow.coheight_fromSpecStalk_eq_height (W := Y) y q).trans ?_
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hz0) hzu
  set E := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
  have hsupp : (E.support : Set Y) = closure {Y.fromSpecStalk y q} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  refine ⟨E, ?_, ?_⟩
  · rw [hsupp]
    exact specializes_iff_mem_closure.1 (MMP.Resolution.specializes_fromSpecStalk y q)
  · have hcl : E.idealSheaf.support = Closeds.closure {Y.fromSpecStalk y q} :=
      Closeds.ext (by rw [Closeds.coe_closure]; exact hsupp)
    rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf E, hcl]
    exact Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk y q

/-- A local equation of a prime divisor at a point of it is a nonzero element of the maximal
ideal. -/
private theorem mem_maximalIdeal_and_ne_zero_of_stalk_eq_span {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hy : y ∈ E.support) {a : Y.presheaf.stalk y}
    (ha : IdealSheafData.stalk E.idealSheaf y = Ideal.span {a}) :
    a ∈ maximalIdeal (Y.presheaf.stalk y) ∧ a ≠ 0 := by
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hy
  refine ⟨(mem_maximalIdeal _).2 fun hu => ?_, ?_⟩
  · exact (IdealSheafData.stalk_eq_top_iff_notMem_support E.idealSheaf y).1
      (by rw [ha, Ideal.span_singleton_eq_top]; exact hu) hy
  · rintro rfl
    exact Ideal.ne_bot_of_height_eq_one hqh (by rw [← hq, ha, Ideal.span_singleton_eq_bot])

/-- At a point of a prime divisor `E` where `E` is regular, `𝒪_{Y,y} ⧸ I_{E,y}` is regular. -/
private theorem isRegularLocalRing_quotient_of_notMem_image_singularLocus {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ E.support)
    (hsm : y ∉ E.idealSheaf.subschemeι '' singularLocus E.idealSheaf.subscheme) :
    IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk E.idealSheaf y) := by
  obtain ⟨z, rfl⟩ : y ∈ Set.range E.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have hz : IsRegularLocalRing (E.idealSheaf.subscheme.presheaf.stalk z) := by
    by_contra h
    exact hsm ⟨z, h, rfl⟩
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv _ z).symm

/-- If `x` is the only generization of itself in a closed subset `D` of a Noetherian sober
space, then near `x` the set `D` lies in `closure {x}`. -/
private theorem exists_isOpen_inter_subset_closure {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] {D : Set T} (hD : IsClosed D) {x : T}
    (hgen : ∀ ξ ∈ D, ξ ⤳ x → ξ = x) :
    ∃ W : Set T, IsOpen W ∧ x ∈ W ∧ W ∩ D ⊆ closure {x} := by
  obtain ⟨hfin, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hD
  set C := {W ∈ MMP.Resolution.componentsOf D | x ∉ W}
  have hcl : IsClosed (⋃₀ C) := (hfin.subset fun W hW => hW.1).isClosed_sUnion
    fun W hW => MMP.Resolution.Aux.isClosed_of_mem_componentsOf hD hW.1
  refine ⟨(⋃₀ C)ᶜ, hcl.isOpen_compl, fun ⟨W, hW, hxW⟩ => hW.2 hxW, ?_⟩
  rintro y ⟨hyC, hyD⟩
  obtain ⟨W, hW, hyW⟩ := hcov hyD
  have hxW : x ∈ W := by
    by_contra h
    exact hyC ⟨W, ⟨hW, h⟩, hyW⟩
  have hWc := MMP.Resolution.Aux.isClosed_of_mem_componentsOf hD hW
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW.1.1 hWc
  have hξx : ξ ⤳ x := by
    rw [specializes_iff_mem_closure, hξ.def]; exact hxW
  have hξD : ξ ∈ D := hW.1.2 hξ.mem
  rw [← hgen ξ hξD hξx, hξ.def]
  exact hyW

/-- A local equation `x` of a prime divisor `E` at a point `y` where `E` is regular lies in
`𝔪_y ∖ 𝔪_y²`. -/
private theorem mem_maximalIdeal_notMem_sq_of_regular {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y}
    (hy : y ∈ E.support) [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hsm : y ∉ E.idealSheaf.subschemeι '' singularLocus E.idealSheaf.subscheme)
    {x : Y.presheaf.stalk y} (hx : IdealSheafData.stalk E.idealSheaf y = Ideal.span {x}) :
    x ∈ IsLocalRing.maximalIdeal _ ∧ x ∉ IsLocalRing.maximalIdeal _ ^ 2 := by
  obtain ⟨hxm, hx0⟩ := mem_maximalIdeal_and_ne_zero_of_stalk_eq_span E hy hx
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  refine ⟨hxm, fun hx2 => ?_⟩
  have hquot := isRegularLocalRing_quotient_of_notMem_image_singularLocus E hy hsm
  rw [hx] at hquot
  exact Stacks.not_isRegularLocalRing_quotient_span_singleton_of_mem_sq
    (mem_nonZeroDivisors_of_ne_zero hx0) hx2 hquot

/-- The local ring of a normal threefold at the generic point of a curve has dimension two. -/
private theorem ringKrullDim_stalk_genericPoint_eq_two {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] {V : IrreducibleCloseds Y}
    (hY : MMP.Mori.IsNormalVariety k sY)
    (hdim : topologicalKrullDim Y = 3) (hV : topologicalKrullDim (V : Set Y) = 1) :
    ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed, hV, hdim] at h
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
  generalize Order.coheight V.isIrreducible.genericPoint = c at h ⊢
  have h' : ((1 + c : ℕ∞) : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_add]; exact h
  have h'' : 1 + c = 3 := WithBot.coe_inj.mp h'
  induction c using ENat.recTopCoe with
  | top => simp at h''
  | coe n =>
    have : 1 + n = 3 := by exact_mod_cast h''
    have hn : n = 2 := by omega
    subst hn; rfl

/-- In a two-dimensional regular local ring, an element of `𝔪 ∖ 𝔪²` is part of a regular system
of parameters. -/
private theorem exists_isRegularSystemOfParameters_pair {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2) {x : R}
    (hxm : x ∈ IsLocalRing.maximalIdeal R) (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ∃ t : R, MMP.Mori.IsRegularSystemOfParameters ![x, t] := by
  classical
  obtain ⟨s, hs, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  have h2 : (IsLocalRing.maximalIdeal R).spanFinrank = 2 := by
    have := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hdim
    exact_mod_cast this
  obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (hs.trans h2)
  have hab : Ideal.span {a, b} = IsLocalRing.maximalIdeal R := by simpa using hspan
  have key : ∀ {p q : R}, Ideal.span {p, q} = IsLocalRing.maximalIdeal R → ∀ c₀ c₁ : R,
      x = c₀ * p + c₁ * q → IsUnit c₀ → Ideal.span {x, q} = IsLocalRing.maximalIdeal R := by
    intro p q hpq c₀ c₁ hx hu
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · rintro _ (rfl | rfl)
      exacts [hxm, hpq ▸ Ideal.subset_span (by simp)]
    · have hp : p = ↑hu.unit⁻¹ * x - ↑hu.unit⁻¹ * c₁ * q := by
        rw [hx, mul_add, ← mul_assoc, IsUnit.val_inv_mul, one_mul]; ring
      rw [← hpq]
      refine Ideal.span_le.mpr ?_
      rintro _ (rfl | rfl)
      · rw [hp]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      · exact Ideal.subset_span (by simp)
  have ha : a ∈ IsLocalRing.maximalIdeal R := hab ▸ Ideal.subset_span (by simp)
  have hb : b ∈ IsLocalRing.maximalIdeal R := hab ▸ Ideal.subset_span (by simp)
  obtain ⟨c₀, c₁, hx⟩ := Ideal.mem_span_pair.mp (hab ▸ hxm : x ∈ Ideal.span {a, b})
  have hunit : IsUnit c₀ ∨ IsUnit c₁ := by
    by_contra! h
    apply hx2
    rw [← hx, pow_two]
    exact add_mem (Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 h.1) ha)
      (Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 h.2) hb)
  obtain ⟨t, ht⟩ : ∃ t, Ideal.span {x, t} = IsLocalRing.maximalIdeal R := by
    rcases hunit with hu | hu
    · exact ⟨b, key hab c₀ c₁ hx.symm hu⟩
    · exact ⟨a, key (by rwa [Set.pair_comm]) c₁ c₀ (by rw [← hx]; ring) hu⟩
  exact ⟨t, by rw [← ht]; congr 1; ext; simp [Matrix.range_cons, or_comm],
    by exact_mod_cast hdim⟩

open MMP.Threefold.Mori.OpenRestriction in
/-- A prime divisor of `Y` meeting an open `U` is the image of a prime divisor of `U`, whose
support is the preimage and whose stalks are those of the given one. -/
private theorem exists_primeDivisor_restrict {Y : Scheme.{u}} (U : Y.Opens)
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} (hyU : y ∈ U) (hy : y ∈ E.support) :
    ∃ EU : MMP.Mori.PrimeDivisor U.toScheme,
      OpenWeilRestriction.primeDivisorMap U.ι EU = E ∧ EU.support = U.ι ⁻¹' E.support ∧
      ∀ u, IdealSheafData.stalk EU.idealSheaf u =
        Ideal.map (U.ι.stalkMap u).hom (IdealSheafData.stalk E.idealSheaf (U.ι u)) := by
  obtain ⟨EU, hEU⟩ := exists_primeDivisorMap_eq_of_mem_support U.ι E ⟨y, hyU⟩ hy
  refine ⟨EU, hEU, ?_, fun u => ?_⟩
  · ext v
    rw [Set.mem_preimage, ← hEU]
    exact (mem_support_primeDivisorMap_iff U.ι EU v).symm
  · rw [← idealSheaf_comap_primeDivisorMap U.ι EU, hEU]
    exact stalk_comap_eq_map U.ι E.idealSheaf u

open Classical in
/-- A prime divisor in the support of `S_U + L_U` is `S_U` or `L_U`. -/
private theorem eq_or_eq_of_mem_support_reducedDivisorOf {W : Scheme.{u}}
    {SU LU : MMP.Mori.PrimeDivisor W}
    (E : MMP.Mori.PrimeDivisor W)
    (hE : E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support) : E = SU ∨ E = LU := by
  rw [MMP.Intersection.support_reducedDivisorOf] at hE
  simpa using hE

open Classical in
/-- The snc condition at a point for `S_U + L_U`, from a regular system of parameters containing
local equations of the components through the point. -/
private theorem exists_sncData {W : Scheme.{u}} {SU LU : MMP.Mori.PrimeDivisor W}
    (hne : SU ≠ LU) (u : W) {n : ℕ} (z : Fin n → W.presheaf.stalk u)
    (hz : IsRegularSystemOfParameters z) (iS iL : Fin n)
    (hS : u ∈ SU.support → IdealSheafData.stalk SU.idealSheaf u = Ideal.span {z iS})
    (hL : u ∈ LU.support → IdealSheafData.stalk LU.idealSheaf u = Ideal.span {z iL})
    (hSL : u ∈ SU.support → u ∈ LU.support → iS ≠ iL) :
    ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk u)
      (j : {E : MMP.Mori.PrimeDivisor W //
        E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support ∧ u ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf u = Ideal.span {z (j E)} := by
  classical
  refine ⟨n, z, fun E => if E.1 = SU then iS else iL, hz, ?_, fun E => ?_⟩
  · rintro ⟨E, hE, huE⟩ ⟨E', hE', huE'⟩ h
    apply Subtype.ext
    simp only at h ⊢
    rcases eq_or_eq_of_mem_support_reducedDivisorOf E hE with rfl | rfl <;>
      rcases eq_or_eq_of_mem_support_reducedDivisorOf E' hE' with rfl | rfl
    · rfl
    · simp only [if_neg hne.symm, ↓reduceIte] at h
      exact absurd h (hSL huE huE')
    · simp only [if_neg hne.symm, ↓reduceIte] at h
      exact absurd h.symm (hSL huE' huE)
    · rfl
  · obtain ⟨E, hE, huE⟩ := E
    rcases eq_or_eq_of_mem_support_reducedDivisorOf E hE with rfl | rfl
    · simp only [↓reduceIte]
      exact hS huE
    · simp only [if_neg hne.symm]
      exact hL huE

open Classical in
/-- The snc condition at a point outside `S_U` and `L_U`. -/
private theorem exists_sncData_of_notMem {W : Scheme.{u}} {SU LU : MMP.Mori.PrimeDivisor W}
    (u : W) [IsRegularLocalRing (W.presheaf.stalk u)] (hS : u ∉ SU.support)
    (hL : u ∉ LU.support) :
    ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk u)
      (j : {E : MMP.Mori.PrimeDivisor W //
        E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support ∧ u ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf u = Ideal.span {z (j E)} := by
  have hempty : ∀ E : {E : MMP.Mori.PrimeDivisor W //
      E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support ∧ u ∈ E.support}, False := by
    rintro ⟨E, hE, huE⟩
    rcases eq_or_eq_of_mem_support_reducedDivisorOf E hE with rfl | rfl
    exacts [hS huE, hL huE]
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (W.presheaf.stalk u)
  exact ⟨n, z, fun E => (hempty E).elim, hz, fun E => (hempty E).elim,
    fun E => (hempty E).elim⟩

/-! ### The neighbourhood `U` -/

open Classical in
/-- The existence of a completion `t` of `x` to a regular system of parameters of `𝒪_{Y,η_V}` and
of an open neighbourhood `U ⊆ Y°` of `η_V` on which `x`, `t` cut out an snc divisor
`(S ∩ U) + {t = 0}` with `V ∩ U` a component of `S ∩ {t = 0}`. -/
private theorem exists_regularSystemOfParameters_isSNC
    {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y] (L : Finset (MMP.Mori.PrimeDivisor Y)) (S : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y)
    (hY : IsNormalVariety k sY) (hdim : topologicalKrullDim Y = 3) (hS : S ∈ L)
    (hVS : (V : Set Y) ⊆ S.support) (hV : topologicalKrullDim (V : Set Y) = 1)
    (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L)
    (x : Y.presheaf.stalk V.isIrreducible.genericPoint)
    (hx : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x}) :
    (∃ t : Y.presheaf.stalk V.isIrreducible.genericPoint, IsRegularSystemOfParameters ![x, t] ∧
      ∃ (U : Y.Opens) (hηU : V.isIrreducible.genericPoint ∈ U),
        (U : Set Y) ⊆ oneLabelSmoothLocus L ∧
        (∀ S' ∈ L, S' ≠ S → Disjoint (U : Set Y) S'.support) ∧
        ∃ (xU tU : Γ(U.toScheme, ⊤)),
          U.ι.stalkMap ⟨_, hηU⟩ x = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial xU ∧
          U.ι.stalkMap ⟨_, hηU⟩ t = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial tU ∧
          ∃ (SU LU : MMP.Mori.PrimeDivisor U.toScheme) (Z : IrreducibleCloseds U.toScheme),
            SU.support = U.ι ⁻¹' S.support ∧
            (∀ u : U.toScheme, IdealSheafData.stalk SU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial xU}) ∧
            (∀ u : U.toScheme, IdealSheafData.stalk LU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial tU}) ∧
            SU ≠ LU ∧
            (MMP.Intersection.reducedDivisorOf {SU, LU}).IsSNC (U.ι ≫ sY) ∧
            (Z : Set U.toScheme) = U.ι ⁻¹' V ∧
            Maximal (fun T : Set U.toScheme => IsIrreducible T ∧ T ⊆ SU.support ∩ LU.support)
              (Z : Set U.toScheme)) := by
  have hYv : MMP.Mori.IsVariety k sY := hY.1
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  haveI := isNoetherian_of_isVariety hYv
  have hdim2' := ringKrullDim_stalk_genericPoint_eq_two hY hdim hV
  have hηgen' := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  revert x hx hη hdim2' hηgen'
  generalize V.isIrreducible.genericPoint = η
  intro hη x hx hdim2 hηgen
  have hηY := mem_oneLabelSmoothLocus_iff.1 hη
  haveI : IsRegularLocalRing (Y.presheaf.stalk η) := hηY.1
  have hηV : η ∈ (V : Set Y) := hηgen.mem
  have hηS : η ∈ S.support := hVS hηV
  obtain ⟨hxm, hx2⟩ := mem_maximalIdeal_notMem_sq_of_regular S hηS (hηY.2.1 S hS) hx
  obtain ⟨t, ht⟩ := exists_isRegularSystemOfParameters_pair hdim2 hxm hx2
  refine ⟨t, ht, ?_⟩
  -- the prime divisor `L' = {t = 0}` of `Y`
  obtain ⟨L', hηL', hL'⟩ := exists_primeDivisor_stalk_eq_span ht 1
  have ht1 : (![x, t] : Fin 2 → _) 1 = t := rfl
  have ht0 : (![x, t] : Fin 2 → _) 0 = x := rfl
  rw [ht1] at hL'
  -- sections representing `x` and `t`
  obtain ⟨Wx, hηWx, x', hx'⟩ := Y.presheaf.germ_exist (x := η) x
  obtain ⟨Wt, hηWt, t', ht'⟩ := Y.presheaf.germ_exist (x := η) t
  set W0 : Y.Opens := Wx ⊓ Wt
  have hηW0 : η ∈ W0 := ⟨hηWx, hηWt⟩
  set x0 : Γ(Y, W0) := Y.presheaf.map (homOfLE inf_le_left).op x'
  set t0 : Γ(Y, W0) := Y.presheaf.map (homOfLE inf_le_right).op t'
  have hxη : Y.presheaf.germ W0 η hηW0 x0 = x :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans hx'
  have htη : Y.presheaf.germ W0 η hηW0 t0 = t :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ht'
  -- the local equations spread out
  obtain ⟨W1, hηW1, hW1, hS1⟩ :=
    exists_forall_stalk_eq_span S.idealSheaf x0 hηW0 (by rw [hxη]; exact hx)
  obtain ⟨W2, hηW2, hW2, hL1⟩ :=
    exists_forall_stalk_eq_span L'.idealSheaf t0 hηW0 (by rw [htη]; exact hL')
  -- `L'` is regular near `η`
  obtain ⟨W3, hηW3, hW3⟩ := exists_isOpen_forall_isRegularLocalRing_quotient sY L'.idealSheaf
    hηL' (by
      rw [hL', ← ht1]
      exact MMP.Resolution.isRegularLocalRing_quotient_span_singleton_of_isRegularSystemOfParameters
        ht 1)
  -- `S ∩ L'` is regular near `η`
  have hm : Ideal.span {x} ⊔ Ideal.span {t} = IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    rw [← Ideal.span_insert]; exact span_pair_eq_maximalIdeal ht
  have hTη : IdealSheafData.stalk (S.idealSheaf ⊔ L'.idealSheaf) η =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    rw [IdealSheafData.stalk_sup, hx, hL', hm]
  have hmemT : ∀ y : Y, IdealSheafData.stalk (S.idealSheaf ⊔ L'.idealSheaf) y ≠ ⊤ →
      y ∈ (S.idealSheaf ⊔ L'.idealSheaf).support := fun y hy => by
    by_contra h
    exact hy ((IdealSheafData.stalk_eq_top_iff_notMem_support _ y).2 h)
  obtain ⟨W4, hηW4, hW4⟩ := exists_isOpen_forall_isRegularLocalRing_quotient sY
    (S.idealSheaf ⊔ L'.idealSheaf) (hmemT η (by rw [hTη]; exact Ideal.IsPrime.ne_top'))
    (by
      rw [hTη]
      exact MMP.Flips.isRegularLocalRing_of_isField (A := IsLocalRing.ResidueField _)
        (Field.toIsField _))
  -- near `η`, `S ∩ L'` lies in `V`
  have hgen : ∀ ξ ∈ (S.support ∩ L'.support : Set Y), ξ ⤳ η → ξ = η := by
    rintro ξ ⟨hξS, hξL⟩ h
    have h1 := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes S.idealSheaf h).1 hξS
    have h2 := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes L'.idealSheaf h).1 hξL
    rw [hx] at h1
    rw [hL'] at h2
    have hP : MMP.Intersection.primeOfSpecializes h =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk η) :=
      le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
        (hm ▸ sup_le h1 h2)
    have hηξ : η ⤳ ξ := MMP.Intersection.specializes_of_primeOfSpecializes_le
      (specializes_refl η) h
      (by rw [hP]; exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
    exact (h.antisymm hηξ).eq
  obtain ⟨W5, hW5o, hηW5, hW5⟩ :=
    exists_isOpen_inter_subset_closure
      (S.idealSheaf.support.isClosed.inter L'.idealSheaf.support.isClosed) hgen
  -- the other labels
  set C : Set Y := ⋃ S' ∈ L, ⋃ (_ : S' ≠ S), (S'.support : Set Y)
  have hC : IsClosed C := isClosed_biUnion_finset fun S' _ =>
    isClosed_iUnion_of_finite fun _ => S'.idealSheaf.support.isClosed
  have hηC : η ∉ C := by
    simp only [C, Set.mem_iUnion]
    rintro ⟨S', hS'L, hne, hηS'⟩
    exact hηY.2.2 S hS S' hS'L hne.symm ⟨hηS, hηS'⟩
  -- the neighbourhood `U`
  set U : Y.Opens := W1 ⊓ W2 ⊓ W3 ⊓ W4 ⊓ ⟨W5, hW5o⟩ ⊓
    ⟨oneLabelSmoothLocus L, isOpen_oneLabelSmoothLocus sY L⟩ ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  have hUmem : ∀ y ∈ U, y ∈ W1 ∧ y ∈ W2 ∧ y ∈ W3 ∧ y ∈ W4 ∧ y ∈ W5 ∧
      y ∈ oneLabelSmoothLocus L ∧ y ∉ C := fun y hy =>
    ⟨hy.1.1.1.1.1.1, hy.1.1.1.1.1.2, hy.1.1.1.1.2, hy.1.1.1.2, hy.1.1.2, hy.1.2, hy.2⟩
  have hηU : η ∈ U := ⟨⟨⟨⟨⟨⟨hηW1, hηW2⟩, hηW3⟩, hηW4⟩, hηW5⟩, hη⟩, hηC⟩
  have hUW0 : U ≤ W0 := fun y hy => hW1 (hUmem y hy).1
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  -- pointwise facts on `U`
  have hregU : ∀ y ∈ U, IsRegularLocalRing (Y.presheaf.stalk y) := fun y hy =>
    (mem_oneLabelSmoothLocus_iff.1 (hUmem y hy).2.2.2.2.2.1).1
  have hSfact : ∀ y (hy : y ∈ U), y ∈ S.support →
      Y.presheaf.germ W0 y (hUW0 hy) x0 ∈ IsLocalRing.maximalIdeal _ ∧
        Y.presheaf.germ W0 y (hUW0 hy) x0 ≠ 0 ∧
        IsRegularLocalRing (Y.presheaf.stalk y ⧸ Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) x0}) :=
    fun y hy hyS => by
    haveI := hregU y hy
    have hst := hS1 y (hUmem y hy).1
    have h1 := mem_maximalIdeal_and_ne_zero_of_stalk_eq_span S hyS hst
    have h2 := isRegularLocalRing_quotient_of_notMem_image_singularLocus S hyS
      ((mem_oneLabelSmoothLocus_iff.1 (hUmem y hy).2.2.2.2.2.1).2.1 S hS)
    rw [hst] at h2
    exact ⟨h1.1, h1.2, h2⟩
  have hLfact : ∀ y (hy : y ∈ U), y ∈ L'.support →
      Y.presheaf.germ W0 y (hUW0 hy) t0 ∈ IsLocalRing.maximalIdeal _ ∧
        Y.presheaf.germ W0 y (hUW0 hy) t0 ≠ 0 ∧
        IsRegularLocalRing (Y.presheaf.stalk y ⧸ Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) t0}) :=
    fun y hy hyL => by
    haveI := hregU y hy
    have hst := hL1 y (hUmem y hy).2.1
    have h1 := mem_maximalIdeal_and_ne_zero_of_stalk_eq_span L' hyL hst
    have h2 := hW3 y (hUmem y hy).2.2.1 hyL
    rw [hst] at h2
    exact ⟨h1.1, h1.2, h2⟩
  have hSLfact : ∀ y (hy : y ∈ U), y ∈ S.support → y ∈ L'.support →
      Y.presheaf.germ W0 y (hUW0 hy) t0 ∉ Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) x0} ∧
        IsRegularLocalRing (Y.presheaf.stalk y ⧸ (Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) x0} ⊔
          Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) t0})) := fun y hy hyS hyL => by
    have hstS := hS1 y (hUmem y hy).1
    have hstL := hL1 y (hUmem y hy).2.1
    refine ⟨fun hba => ?_, ?_⟩
    · have hs : S.genericPoint ⤳ y :=
        MMP.Resolution.Aux.genericPoint_specializes_of_mem_support S hyS
      have hsU : S.genericPoint ∈ U := hs.mem_open U.isOpen hy
      have hsS : S.genericPoint ∈ S.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      have hsL : S.genericPoint ∈ L'.support := by
        by_contra hn
        have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support L'.idealSheaf _).2 hn
        rw [MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes L'.idealSheaf hs, hstL] at htop
        have hle : Ideal.map (Y.presheaf.stalkSpecializes hs).hom
            (Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) t0}) ≤
            Ideal.map (Y.presheaf.stalkSpecializes hs).hom
              (IdealSheafData.stalk S.idealSheaf y) :=
          Ideal.map_mono (by rw [hstS, Ideal.span_le, Set.singleton_subset_iff]; exact hba)
        rw [← MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes S.idealSheaf hs,
          MMP.Resolution.Aux.stalk_idealSheaf_genericPoint, htop] at hle
        exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)
      have hsV : S.genericPoint ∈ closure {η} := hW5 ⟨(hUmem _ hsU).2.2.2.2.1, hsS, hsL⟩
      have hηs : η ⤳ S.genericPoint := specializes_iff_mem_closure.2 hsV
      have hsη : S.genericPoint ⤳ η :=
        MMP.Resolution.Aux.genericPoint_specializes_of_mem_support S hηS
      have heq : S.genericPoint = η := (hsη.antisymm hηs).eq
      have h2 : ((Order.coheight η : ℕ∞) : WithBot ℕ∞) = 2 := by
        rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]; exact hdim2
      rw [← heq, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
      exact absurd h2 (by decide)
    · have hT := hW4 y (hUmem y hy).2.2.2.1
      rw [IdealSheafData.stalk_sup, hstS, hstL] at hT
      haveI := hregU y hy
      refine hT (hmemT y ?_)
      rw [IdealSheafData.stalk_sup, hstS, hstL]
      exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (sup_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 (hSfact y hy hyS).1))
          (Ideal.span_le.2 (Set.singleton_subset_iff.2 (hLfact y hy hyL).1)))
  -- the data on `U`
  set xU := sectionOn hUW0 x0
  set tU := sectionOn hUW0 t0
  obtain ⟨SU, hSUmap, hSUsupp, hSUstalk⟩ := exists_primeDivisor_restrict U S hηU hηS
  obtain ⟨LU, hLUmap, hLUsupp, hLUstalk⟩ := exists_primeDivisor_restrict U L' hηU hηL'
  have hSUx : ∀ u : U.toScheme, IdealSheafData.stalk SU.idealSheaf u =
      Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial xU} := fun u => by
    rw [hSUstalk, hS1 (U.ι u) (hUmem _ u.2).1, Ideal.map_span, Set.image_singleton, germ_sectionOn]
  have hLUt : ∀ u : U.toScheme, IdealSheafData.stalk LU.idealSheaf u =
      Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial tU} := fun u => by
    rw [hLUstalk, hL1 (U.ι u) (hUmem _ u.2).2.1, Ideal.map_span, Set.image_singleton,
      germ_sectionOn]
  have hne : SU ≠ LU := by
    intro h
    have hSL : S = L' := by rw [← hSUmap, ← hLUmap, h]
    apply MMP.Resolution.notMem_span_singleton_of_isRegularSystemOfParameters ht
      (m := 0) (m' := 1) (by decide)
    rw [ht1, ht0, ← hx, hSL, hL']
    exact Ideal.mem_span_singleton_self t
  have hpt : ∀ u : U.toScheme, ∃ (n : ℕ) (z : Fin n → U.toScheme.presheaf.stalk u)
      (jj : {E : MMP.Mori.PrimeDivisor U.toScheme //
        E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support ∧ u ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf u = Ideal.span {z (jj E)} := by
    intro u
    haveI : IsRegularLocalRing (Y.presheaf.stalk (U.ι u)) := hregU _ u.2
    haveI : IsRegularLocalRing (Y.presheaf.stalk u.1) := hregU _ u.2
    let e := (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv
    have hex : e (Y.presheaf.germ W0 (U.ι u) (hUW0 u.2) x0) =
        U.toScheme.presheaf.germ ⊤ u trivial xU := (germ_sectionOn hUW0 x0 u).symm
    have het : e (Y.presheaf.germ W0 (U.ι u) (hUW0 u.2) t0) =
        U.toScheme.presheaf.germ ⊤ u trivial tU := (germ_sectionOn hUW0 t0 u).symm
    have hSu : u ∈ SU.support ↔ U.ι u ∈ S.support := by rw [hSUsupp]; rfl
    have hLu : u ∈ LU.support ↔ U.ι u ∈ L'.support := by rw [hLUsupp]; rfl
    by_cases hyS : U.ι u ∈ S.support <;> by_cases hyL : U.ι u ∈ L'.support
    · obtain ⟨hxm', hx0', hxr⟩ := hSfact _ u.2 hyS
      obtain ⟨htm', -, -⟩ := hLfact _ u.2 hyL
      obtain ⟨hba, hr2⟩ := hSLfact _ u.2 hyS hyL
      obtain ⟨n, z, hz, hz0, hz1⟩ :=
        exists_isRegularSystemOfParameters_cons_cons hxm' htm' hx0' hba hxr hr2
      refine exists_sncData hne u _ (isRegularSystemOfParameters_map_ringEquiv e hz) 0 1
        (fun _ => ?_) (fun _ => ?_)
        (fun _ _ => show (0 : Fin (n + 2)) ≠ 1 by simp)
      · rw [hSUx, ← hex, hz0]; rfl
      · rw [hLUt, ← het, hz1]; rfl
    · obtain ⟨hxm', hx0', hxr⟩ := hSfact _ u.2 hyS
      obtain ⟨n, z, hz, hz0⟩ := exists_isRegularSystemOfParameters_cons hxm' hx0' hxr
      refine exists_sncData hne u _ (isRegularSystemOfParameters_map_ringEquiv e hz) 0 0
        (fun _ => ?_)
        (fun h => absurd (hLu.1 h) hyL) (fun _ h => absurd (hLu.1 h) hyL)
      rw [hSUx, ← hex, hz0]; rfl
    · obtain ⟨htm', ht0', htr⟩ := hLfact _ u.2 hyL
      obtain ⟨n, z, hz, hz0⟩ := exists_isRegularSystemOfParameters_cons htm' ht0' htr
      refine exists_sncData hne u _ (isRegularSystemOfParameters_map_ringEquiv e hz) 0 0
        (fun h => absurd (hSu.1 h) hyS) (fun _ => ?_) (fun h => absurd (hSu.1 h) hyS)
      rw [hLUt, ← het, hz0]; rfl
    · haveI : IsRegularLocalRing (U.toScheme.presheaf.stalk u) := IsRegularLocalRing.of_ringEquiv e
      exact exists_sncData_of_notMem u (fun h => hyS (hSu.1 h)) (fun h => hyL (hLu.1 h))
  have hUs := isSmoothScheme_ι_comp hYv U hregU
  have hsnc : (MMP.Intersection.reducedDivisorOf {SU, LU}).IsSNC (U.ι ≫ sY) := by
    refine ⟨fun E hE => ?_, hpt⟩
    refine MMP.Resolution.isSmoothScheme_subscheme_of_forall_stalk_eq_span (U.ι ≫ sY) hUs
      E.idealSheaf fun u hu => ?_
    obtain ⟨n, z, jj, hz, -, hzE⟩ := hpt u
    exact ⟨n, z, jj ⟨E, hE, hu⟩, hz, hzE ⟨E, hE, hu⟩⟩
  let Z : IrreducibleCloseds U.toScheme :=
    ⟨U.ι ⁻¹' V, ⟨⟨⟨η, hηU⟩, hηV⟩, V.isIrreducible.2.preimage U.ι.isOpenEmbedding⟩,
      V.isClosed.preimage U.ι.continuous⟩
  have hVL : (V : Set Y) ⊆ L'.support := by
    rw [← hηgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hηL') L'.idealSheaf.support.isClosed
  have hZmax : Maximal (fun T : Set U.toScheme => IsIrreducible T ∧ T ⊆ SU.support ∩ LU.support)
      (Z : Set U.toScheme) := by
    refine ⟨⟨Z.isIrreducible, fun v hv => ⟨?_, ?_⟩⟩, fun T hT _ v hv => ?_⟩
    · rw [hSUsupp]; exact hVS hv
    · rw [hLUsupp]; exact hVL hv
    · obtain ⟨h1, h2⟩ := hT.2 hv
      rw [hSUsupp] at h1
      rw [hLUsupp] at h2
      have := hW5 ⟨(hUmem _ v.2).2.2.2.2.1, h1, h2⟩
      rwa [hηgen.def] at this
  refine ⟨U, hηU, fun y hy => (hUmem y hy).2.2.2.2.2.1,
    fun S' hS'L hne' => Set.disjoint_left.2 fun y hyU hyS' => (hUmem y hyU).2.2.2.2.2.2 ?_,
    xU, tU, ?_, ?_, SU, LU, Z, hSUsupp, hSUx, hLUt, hne, hsnc, rfl, hZmax⟩
  · simp only [C, Set.mem_iUnion]
    exact ⟨S', hS'L, hne', hyS'⟩
  · exact (congrArg _ hxη.symm).trans (germ_sectionOn hUW0 x0 ⟨η, hηU⟩).symm
  · exact (congrArg _ htη.symm).trans (germ_sectionOn hUW0 t0 ⟨η, hηU⟩).symm

end Neighbourhood

open Classical in
/-- On a neighbourhood `U` as in `exists_regularSystemOfParameters_isSNC`, an echo of order `j`
of `S` at `V` is the same as a valuation monomial of weight `(j, 1)` at `V ∩ U` for
`(S ∩ U) + {t = 0}`. -/
private theorem isEcho_iff_exists_isMonomialValuationOfWeight
    {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y] (L : Finset (MMP.Mori.PrimeDivisor Y)) (S : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) (j : ℕ)
    (hY : IsNormalVariety k sY) (hdim : topologicalKrullDim Y = 3) (hS : S ∈ L)
    (hVS : (V : Set Y) ⊆ S.support) (hV : topologicalKrullDim (V : Set Y) = 1)
    (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L) (hj : 1 ≤ j)
    (x : Y.presheaf.stalk V.isIrreducible.genericPoint)
    (hx : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x}) :
    ∀ t : Y.presheaf.stalk V.isIrreducible.genericPoint, IsRegularSystemOfParameters ![x, t] →
      ∀ (U : Y.Opens) (hηU : V.isIrreducible.genericPoint ∈ U),
        (U : Set Y) ⊆ oneLabelSmoothLocus L →
        ∀ (xU tU : Γ(U.toScheme, ⊤)),
          U.ι.stalkMap ⟨_, hηU⟩ x = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial xU →
          U.ι.stalkMap ⟨_, hηU⟩ t = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial tU →
          ∀ (SU LU : MMP.Mori.PrimeDivisor U.toScheme) (Z : IrreducibleCloseds U.toScheme),
            (∀ u : U.toScheme, IdealSheafData.stalk SU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial xU}) →
            (∀ u : U.toScheme, IdealSheafData.stalk LU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial tU}) →
            SU ≠ LU →
            (MMP.Intersection.reducedDivisorOf {SU, LU}).IsSNC (U.ι ≫ sY) →
            (Z : Set U.toScheme) = U.ι ⁻¹' V →
            Maximal (fun T : Set U.toScheme => IsIrreducible T ∧ T ⊆ SU.support ∩ LU.support)
              (Z : Set U.toScheme) →
            ∀ ξ : Valuation Y.functionField ℤᵐ⁰,
              haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
              haveI := isDominant_ι_of_nonempty U
              (IsEcho sY L S V j ξ ↔
                  ∃ ξU : Valuation U.toScheme.functionField ℤᵐ⁰,
                    ξU.comap (functionFieldMap U.ι) = ξ ∧
                    IsMonomialValuationOfWeight (U.ι ≫ sY)
                      (MMP.Intersection.reducedDivisorOf {SU, LU}) {SU, LU} Z
                      (fun E => U.toScheme.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial
                        (if E.1 = SU then xU else tU))
                      (fun E => if E.1 = SU then j else 1) ξU) := by
  intro t ht U hηU hUL xU tU hxU htU SU LU Z hSUx hLUt hne hsnc hZ hZmax ξ
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI := isDominant_ι_of_nonempty U
  have hYv : MMP.Mori.IsVariety k sY := hY.1
  have hUv := isVariety_ι_comp hYv U
  have hUs := isSmoothScheme_ι_comp hYv U
    (fun u hu => (mem_oneLabelSmoothLocus_iff.1 (hUL hu)).1)
  have h13 := isEcho_iff_isWeightedMonomialValuation (sY := sY) hY hdim hS hVS hV hη hj hx ht
    (ξ := ξ)
  have hgen : Z.isIrreducible.genericPoint = ⟨_, hηU⟩ :=
    genericPoint_eq_of_coe_eq_preimage rfl hZ
  have hYval : ∀ ξ' : Valuation Y.functionField ℤᵐ⁰,
      (∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint, f ≠ 0 →
        ∃ M : ℕ, MMP.Resolution.monomialValuation t x j f = M ∧
          ξ' (algebraMap _ Y.functionField f) = WithZero.exp (-(M : ℤ))) ↔
      (∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint, f ≠ 0 →
        ∃ M : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Resolution.monomialIdeal t x j m} M ∧
          ξ' (algebraMap _ Y.functionField f) = WithZero.exp (-(M : ℤ))) := fun ξ' =>
    forall_congr' fun f => forall_congr' fun _ => exists_congr fun M =>
      and_congr_left' (monomialValuation_eq_coe_iff x t j f M)
  have hUval : ∀ ξU : Valuation U.toScheme.functionField ℤᵐ⁰,
      (∀ g : U.toScheme.presheaf.stalk Z.isIrreducible.genericPoint, g ≠ 0 →
        ∃ M : ℕ, IsGreatest {m : ℕ | g ∈ MMP.Resolution.monomialIdeal
            (U.toScheme.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial tU)
            (U.toScheme.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial xU) j m} M ∧
          ξU (algebraMap _ U.toScheme.functionField g) = WithZero.exp (-(M : ℤ))) ↔
      (∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint, f ≠ 0 →
        ∃ M : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Resolution.monomialIdeal t x j m} M ∧
          ξU.comap (functionFieldMap U.ι) (algebraMap _ Y.functionField f) =
            WithZero.exp (-(M : ℤ))) := fun ξU => by
    rw [hgen, ← hxU, ← htU]
    exact (forall_value_iff_of_isOpenImmersion U ⟨_, hηU⟩ x t j ξU).symm
  rw [h13]
  constructor
  · intro hw
    let e := RingEquiv.ofBijective (functionFieldMap U.ι)
      (MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨⟨_, hηU⟩, trivial⟩)
    have hcomap : (ξ.comap e.symm.toRingHom).comap (functionFieldMap U.ι) = ξ := by
      ext a
      simp only [Valuation.comap_apply]
      congr 1
      exact e.symm_apply_apply a
    refine ⟨ξ.comap e.symm.toRingHom, hcomap, ?_⟩
    rw [isMonomialValuationOfWeight_pair_iff hUv hUs xU tU hSUx hLUt hne hsnc hZmax hj]
    have hvU := (hUval (ξ.comap e.symm.toRingHom)).2
      (by rw [hcomap]; exact (hYval ξ).1 hw.2.2.2.2.2)
    have hrsopU : IsRegularSystemOfParameters
        ![U.toScheme.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial xU,
          U.toScheme.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial tU] := by
      rw [hgen]
      exact isRegularSystemOfParameters_germ U ⟨_, hηU⟩ hxU htU ht
    have hpt : U.ι Z.isIrreducible.genericPoint = V.isIrreducible.genericPoint := by
      rw [hgen]; rfl
    have hregU : IsRegularLocalRing (U.toScheme.presheaf.stalk Z.isIrreducible.genericPoint) := by
      have hr : IsRegularLocalRing (Y.presheaf.stalk (U.ι Z.isIrreducible.genericPoint)) := by
        rw [hpt]; exact hw.2.2.1
      exact @IsRegularLocalRing.of_ringEquiv _ _ hr _ _
        (asIso (U.ι.stalkMap Z.isIrreducible.genericPoint)).commRingCatIsoToRingEquiv
    have hwU : IsWeightedMonomialValuation (U.ι ≫ sY) Z
        (U.toScheme.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial xU)
        (U.toScheme.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial tU) j
        (ξ.comap e.symm.toRingHom) := by
      refine ⟨⟨hUv, haveI := hY.2; inferInstance⟩, codimension_eq_two Z hrsopU, hregU,
        hrsopU, hj, fun g hg => ?_⟩
      obtain ⟨M, hM, hξM⟩ := hvU g hg
      exact ⟨M, (monomialValuation_eq_coe_iff _ _ _ _ _).2 hM, hξM⟩
    exact ⟨hwU.isNormalizedDivisorialValuation_and_isCentre.2, hvU⟩
  · rintro ⟨ξU, hcomap, hmono⟩
    rw [isMonomialValuationOfWeight_pair_iff hUv hUs xU tU hSUx hLUt hne hsnc hZmax hj]
      at hmono
    have hv := (hUval ξU).1 hmono.2
    rw [hcomap] at hv
    exact ⟨hY, codimension_eq_two V ht, (mem_oneLabelSmoothLocus_iff.1 hη).1, ht, hj,
      (hYval ξ).2 hv⟩

end MMP.Proofs.lem_mmp_indexd_echo_is_monomial

namespace MMP.Fourfold

open Classical in
open MMP.Proofs.lem_mmp_indexd_echo_is_monomial in
/-- **Echoes are monomial valuations.** Let `Y` be a normal threefold over `k` with labels `L`,
`S ∈ L`, `V ⊆ S` an irreducible closed curve whose generic point `η_V` lies in the one-label
smooth locus, `x` a local equation of `S` at `η_V` and `j ≥ 1`. Then there are `t ∈ 𝒪_{Y,η_V}`
completing `x` to a regular system of parameters and an open neighbourhood `U ⊆ Y°` of `η_V`
meeting no other label, on which `x, t` are regular and cut out smooth divisors `S ∩ U` and
`L = {t = 0}` meeting transversally, with `V ∩ U` a component of `S ∩ L`; and for every such
`t, U` and every normalized divisorial valuation `ξ` of `k(Y)`, the following are equivalent:
`ξ` is an echo of order `j` of `S` at `V`; `ξ` is monomial of weight `(j, 1)` at `V ∩ U` for
`(S ∩ U) + L`; `ξ = v_{x,t;j}`. -/
@[mmp "lem_mmp_indexd_echo_is_monomial"]
public theorem isEcho_tfae_isMonomialValuationOfWeight_isWeightedMonomialValuation
    {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y] (L : Finset (MMP.Mori.PrimeDivisor Y)) (S : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) (j : ℕ)
    (hY : IsNormalVariety k sY) (hdim : topologicalKrullDim Y = 3) (hS : S ∈ L)
    (hVS : (V : Set Y) ⊆ S.support) (hV : topologicalKrullDim (V : Set Y) = 1)
    (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L) (hj : 1 ≤ j)
    (x : Y.presheaf.stalk V.isIrreducible.genericPoint)
    (hx : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x}) :
    (∃ t : Y.presheaf.stalk V.isIrreducible.genericPoint, IsRegularSystemOfParameters ![x, t] ∧
      ∃ (U : Y.Opens) (hηU : V.isIrreducible.genericPoint ∈ U),
        (U : Set Y) ⊆ oneLabelSmoothLocus L ∧
        (∀ S' ∈ L, S' ≠ S → Disjoint (U : Set Y) S'.support) ∧
        ∃ (xU tU : Γ(U.toScheme, ⊤)),
          U.ι.stalkMap ⟨_, hηU⟩ x = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial xU ∧
          U.ι.stalkMap ⟨_, hηU⟩ t = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial tU ∧
          ∃ (SU LU : MMP.Mori.PrimeDivisor U.toScheme) (Z : IrreducibleCloseds U.toScheme),
            SU.support = U.ι ⁻¹' S.support ∧
            (∀ u : U.toScheme, IdealSheafData.stalk SU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial xU}) ∧
            (∀ u : U.toScheme, IdealSheafData.stalk LU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial tU}) ∧
            SU ≠ LU ∧
            (MMP.Intersection.reducedDivisorOf {SU, LU}).IsSNC (U.ι ≫ sY) ∧
            (Z : Set U.toScheme) = U.ι ⁻¹' V ∧
            Maximal (fun T : Set U.toScheme => IsIrreducible T ∧ T ⊆ SU.support ∩ LU.support)
              (Z : Set U.toScheme)) ∧
    ∀ t : Y.presheaf.stalk V.isIrreducible.genericPoint, IsRegularSystemOfParameters ![x, t] →
      ∀ (U : Y.Opens) (hηU : V.isIrreducible.genericPoint ∈ U),
        (U : Set Y) ⊆ oneLabelSmoothLocus L →
        (∀ S' ∈ L, S' ≠ S → Disjoint (U : Set Y) S'.support) →
        ∀ (xU tU : Γ(U.toScheme, ⊤)),
          U.ι.stalkMap ⟨_, hηU⟩ x = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial xU →
          U.ι.stalkMap ⟨_, hηU⟩ t = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial tU →
          ∀ (SU LU : MMP.Mori.PrimeDivisor U.toScheme) (Z : IrreducibleCloseds U.toScheme),
            SU.support = U.ι ⁻¹' S.support →
            (∀ u : U.toScheme, IdealSheafData.stalk SU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial xU}) →
            (∀ u : U.toScheme, IdealSheafData.stalk LU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial tU}) →
            SU ≠ LU →
            (MMP.Intersection.reducedDivisorOf {SU, LU}).IsSNC (U.ι ≫ sY) →
            (Z : Set U.toScheme) = U.ι ⁻¹' V →
            Maximal (fun T : Set U.toScheme => IsIrreducible T ∧ T ⊆ SU.support ∩ LU.support)
              (Z : Set U.toScheme) →
            ∀ ξ : Valuation Y.functionField ℤᵐ⁰,
              MMP.Intersection.IsNormalizedDivisorialValuation k sY ξ →
              haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
              haveI := isDominant_ι_of_nonempty U
              List.TFAE
                [IsEcho sY L S V j ξ,
                  ∃ ξU : Valuation U.toScheme.functionField ℤᵐ⁰,
                    ξU.comap (functionFieldMap U.ι) = ξ ∧
                    IsMonomialValuationOfWeight (U.ι ≫ sY)
                      (MMP.Intersection.reducedDivisorOf {SU, LU}) {SU, LU} Z
                      (fun E => U.toScheme.presheaf.germ ⊤ Z.isIrreducible.genericPoint trivial
                        (if E.1 = SU then xU else tU))
                      (fun E => if E.1 = SU then j else 1) ξU,
                  IsWeightedMonomialValuation sY V x t j ξ] := by
  refine ⟨exists_regularSystemOfParameters_isSNC sY L S V hY hdim hS hVS hV hη x hx, ?_⟩
  intro t ht U hηU hUL _ xU tU hxU htU SU LU Z _ hSUx hLUt hne hsnc hZ hZmax ξ _
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI := isDominant_ι_of_nonempty U
  tfae_have 1 ↔ 2 := isEcho_iff_exists_isMonomialValuationOfWeight sY L S V j hY hdim hS hVS hV
    hη hj x hx t ht U hηU hUL xU tU hxU htU SU LU Z hSUx hLUt hne hsnc hZ hZmax ξ
  tfae_have 1 ↔ 3 := isEcho_iff_isWeightedMonomialValuation hY hdim hS hVS hV hη hj hx ht
  tfae_finish

end MMP.Fourfold

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold
open scoped WithZero

variable {k : Type*} [Field k] {Y : Scheme} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  {L : Finset (MMP.Mori.PrimeDivisor Y)} {S : MMP.Mori.PrimeDivisor Y} {V : IrreducibleCloseds Y}

namespace MMP.Proofs.lem_mmp_indexd_echo_exists

open MMP.Proofs.lem_mmp_indexd_echo_is_monomial (span_pair_eq_maximalIdeal
  mem_maximalIdeal_notMem_sq_of_regular ringKrullDim_stalk_genericPoint_eq_two
  exists_isRegularSystemOfParameters_pair echoIdeal_eq_monomialIdeal)

/-- The order-reversing monoid map `WithTop ℤ → ℤᵐ⁰`, `n ↦ exp (-n)`, `⊤ ↦ 0`. -/
private def expNeg : WithTop ℤ → ℤᵐ⁰
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private lemma expNeg_coe (n : ℤ) : expNeg n = WithZero.exp (-n) := rfl

private lemma expNeg_top : expNeg ⊤ = 0 := rfl

private lemma expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg_top, ← WithTop.coe_add, expNeg_coe, neg_add, WithZero.exp_add, mul_comm]

private lemma expNeg_antitone : Antitone expNeg := by
  intro a b h
  cases b with
  | top => simp [expNeg_top]
  | coe n =>
    cases a with
    | top => simp at h
    | coe m =>
      simp only [expNeg_coe, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def valuationOfAddValuation {R : Type*} [Ring R] (V : AddValuation R (WithTop ℤ)) :
    Valuation R ℤᵐ⁰ where
  toFun z := expNeg (V z)
  map_zero' := by simp [expNeg_top]
  map_one' := by simp [← WithTop.coe_zero, expNeg_coe]
  map_mul' a b := by simp [V.map_mul, expNeg_add]
  map_add_le_max' a b := by
    rw [← expNeg_antitone.map_min]
    exact expNeg_antitone (V.map_add a b)

private lemma valuationOfAddValuation_apply {R : Type*} [Ring R]
    (V : AddValuation R (WithTop ℤ)) (z : R) :
    valuationOfAddValuation V z = expNeg (V z) := rfl

/-! ### Regular parameters -/

private lemma isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    MMP.Mori.IsRegularSystemOfParameters ![y, x] := by
  refine ⟨?_, hxy.2⟩
  rw [← span_pair_eq_maximalIdeal hxy]; congr 1; ext; simp [Matrix.range_cons, Set.pair_comm]

/-! ### The echo ideals of `x` itself -/

/-- If `x ∈ 𝔪 ∖ 𝔪²` and `j ≥ 1`, the largest `n` with `x ∈ ∑_a x^a 𝔪^{n - ja}` is `j`. -/
private lemma isGreatest_mem_echoIdeal_self {R : Type*} [CommRing R] {x : R} {𝔪 : Ideal R}
    (hxm : x ∈ 𝔪) (hx2 : x ∉ 𝔪 ^ 2) {j : ℕ} (hj : 1 ≤ j) :
    IsGreatest {n : ℕ | x ∈ echoIdeal x 𝔪 j n} j := by
  refine ⟨Ideal.mem_iSup_of_mem 1 (by simp [Ideal.mem_span_singleton_self]), fun n hn => ?_⟩
  by_contra hlt
  have hmem : x ∈ echoIdeal x 𝔪 j (j + 1) :=
    echoIdeal_antitone x 𝔪 j (by simp only [Set.mem_setOf_eq] at hn ⊢; omega) hn
  refine hx2 ((iSup_le fun a => ?_ : echoIdeal x 𝔪 j (j + 1) ≤ 𝔪 ^ 2) hmem)
  rcases a with _ | _ | a
  · simpa using Ideal.pow_le_pow_right (by omega)
  · have h1 : j + 1 - j * (0 + 1) = 1 := by omega
    rw [h1, zero_add, pow_one, pow_one, pow_two]
    exact Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hxm)
  · refine Ideal.mul_le_left.trans ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    rw [show a + 1 + 1 = 2 + a by omega, pow_add]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hxm 2)

/-! ### Echoes -/

/-- Echoes of the same order are equal: the defining formula pins their values on
`𝒪_{Y,η_V}`. -/
private lemma IsEcho.eq {j : ℕ} {ξ ξ' : Valuation Y.functionField ℤᵐ⁰}
    (h : IsEcho sY L S V j ξ) (h' : IsEcho sY L S V j ξ') : ξ = ξ' := by
  obtain ⟨-, -, -, -, -, -, -, -, x, hx, hξ⟩ := h
  have hξ' := (isEcho_iff_forall.mp h').2.2.2.2.2.2.2.2.2 x hx
  refine eq_of_forall_stalk_eq V.isIrreducible.genericPoint fun f => ?_
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨M, hM, hv⟩ := hξ f hf
  obtain ⟨M', hM', hv'⟩ := hξ' f hf
  rw [hv, hv', hM.unique hM']

/-- A local equation of `S` at `η_V`, with `η_V` in the one-label smooth locus, lies in
`𝔪 ∖ 𝔪²`. -/
private lemma localEquation_mem_maximalIdeal_notMem_sq (hS : S ∈ L)
    (hVS : (V : Set Y) ⊆ S.support) (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L)
    {x : Y.presheaf.stalk V.isIrreducible.genericPoint}
    (hx : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x}) :
    x ∈ IsLocalRing.maximalIdeal _ ∧ x ∉ IsLocalRing.maximalIdeal _ ^ 2 :=
  haveI := (mem_oneLabelSmoothLocus_iff.mp hη).1
  mem_maximalIdeal_notMem_sq_of_regular S
    (hVS (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem)
    ((mem_oneLabelSmoothLocus_iff.mp hη).2.1 S hS) hx

/-- An echo of order `j` takes the value `exp (-j)` on a local equation of `S` at `η_V`. -/
private lemma IsEcho.apply_localEquation {j : ℕ} {ξ : Valuation Y.functionField ℤᵐ⁰}
    (hξ : IsEcho sY L S V j ξ) {x : Y.presheaf.stalk V.isIrreducible.genericPoint}
    (hx : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x}) :
    ξ (algebraMap _ Y.functionField x) = WithZero.exp (-(j : ℤ)) := by
  obtain ⟨hxm, hx2⟩ := localEquation_mem_maximalIdeal_notMem_sq hξ.2.2.1 hξ.2.2.2.1
    hξ.2.2.2.2.2.1 hx
  obtain ⟨M, hM, hξM⟩ := (isEcho_iff_forall.mp hξ).2.2.2.2.2.2.2.2.2 x hx x
    (by rintro rfl; exact hx2 (Ideal.zero_mem _))
  rw [hξM, hM.unique (isGreatest_mem_echoIdeal_self hxm hx2 hξ.2.2.2.2.2.2.1)]

/-- For every `j ≥ 1` an echo of order `j` of `S` at `V` exists (namely the monomial valuation
`v_{x,t;j}`). -/
private lemma exists_isEcho (hY : MMP.Mori.IsNormalVariety k sY)
    (hdim : topologicalKrullDim Y = 3) (hS : S ∈ L) (hVS : (V : Set Y) ⊆ S.support)
    (hV : topologicalKrullDim (V : Set Y) = 1)
    (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L) {j : ℕ} (hj : 1 ≤ j) :
    ∃ ξ : Valuation Y.functionField ℤᵐ⁰, IsEcho sY L S V j ξ := by
  haveI hreg := (mem_oneLabelSmoothLocus_iff.mp hη).1
  obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S
    (hVS (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem)
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid
    (Y.presheaf.stalk V.isIrreducible.genericPoint)
  obtain ⟨x, hxq⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqh).principal
  have hx := hq.trans hxq
  obtain ⟨hxm, hx2⟩ := localEquation_mem_maximalIdeal_notMem_sq hS hVS hη hx
  have hdim2 := ringKrullDim_stalk_genericPoint_eq_two hY hdim hV
  obtain ⟨t, ht⟩ := exists_isRegularSystemOfParameters_pair hdim2 hxm hx2
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    Y.functionField (isRegularSystemOfParameters_swap ht) hj
  have hvalW : ∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint, f ≠ 0 →
      ∃ M : ℕ, MMP.Resolution.monomialValuation t x j f = M ∧
        valuationOfAddValuation W (algebraMap _ Y.functionField f) =
          WithZero.exp (-(M : ℤ)) := by
    intro f hf
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
    refine ⟨M, hM.symm, ?_⟩
    rw [valuationOfAddValuation_apply, hW, ← hM]
    rfl
  have hv : IsWeightedMonomialValuation sY V x t j (valuationOfAddValuation W) := by
    refine ⟨hY, ?_, hreg, ht, hj, hvalW⟩
    rw [MMP.Flips.codimension_eq_coheight_genericPoint]
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hdim2
    exact WithBot.coe_inj.mp hdim2
  refine ⟨_, hY, hdim, hS, hVS, hV, hη, hj,
    hv.isNormalizedDivisorialValuation_and_isCentre.2, x, hx, fun f hf => ?_⟩
  obtain ⟨M, hM, hfM⟩ := hvalW f hf
  refine ⟨M, ?_, hfM⟩
  simp_rw [echoIdeal_eq_monomialIdeal (span_pair_eq_maximalIdeal ht) hj]
  have h1 : (1 : Y.presheaf.stalk V.isIrreducible.genericPoint) ∈
      MMP.Resolution.monomialIdeal t x j 0 := Ideal.subset_span ⟨0, 0, le_rfl, by simp⟩
  exact (isGreatest_iff_iSup_eq ⟨0, by simpa using Ideal.mul_mem_left _ f h1⟩).2 hM

end MMP.Proofs.lem_mmp_indexd_echo_exists

namespace MMP.Fourfold

open MMP.Proofs.lem_mmp_indexd_echo_exists in
/-- **Echoes exist and are unique.** Let `Y` be a normal threefold over `k` with labels `L`,
`S ∈ L`, and `V ⊆ S` an irreducible closed curve whose generic point lies in the one-label
smooth locus. Then for every `j ≥ 1` there is exactly one echo `ξ_j` of order `j` of `S` at
`V`; every echo of order `j` takes the value `j` on every local equation `x` of `S` at `η_V`;
and echoes of different orders are distinct. -/
@[mmp "lem_mmp_indexd_echo_exists"]
public theorem existsUnique_isEcho {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] {L : Finset (MMP.Mori.PrimeDivisor Y)}
    {S : MMP.Mori.PrimeDivisor Y} {V : IrreducibleCloseds Y}
    (hY : MMP.Mori.IsNormalVariety k sY) (hdim : topologicalKrullDim Y = 3) (hS : S ∈ L)
    (hVS : (V : Set Y) ⊆ S.support) (hV : topologicalKrullDim (V : Set Y) = 1)
    (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L) :
    (∀ j : ℕ, 1 ≤ j → ∃! ξ : Valuation Y.functionField ℤᵐ⁰, IsEcho sY L S V j ξ) ∧
      (∀ (j : ℕ) (ξ : Valuation Y.functionField ℤᵐ⁰), IsEcho sY L S V j ξ →
        ∀ x : Y.presheaf.stalk V.isIrreducible.genericPoint,
          IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x} →
            ξ (algebraMap _ Y.functionField x) = WithZero.exp (-(j : ℤ))) ∧
      ∀ (j j' : ℕ) (ξ ξ' : Valuation Y.functionField ℤᵐ⁰), IsEcho sY L S V j ξ →
        IsEcho sY L S V j' ξ' → j ≠ j' → ξ ≠ ξ' := by
  refine ⟨fun j hj => ?_, fun j ξ hξ x hx => IsEcho.apply_localEquation hξ hx,
    fun j j' ξ ξ' h h' hne heq => ?_⟩
  · obtain ⟨ξ, hξ⟩ := exists_isEcho hY hdim hS hVS hV hη hj
    exact ⟨ξ, hξ, fun ξ' hξ' => IsEcho.eq hξ' hξ⟩
  · subst heq
    obtain ⟨x, hx, -⟩ := h.2.2.2.2.2.2.2.2
    have := (IsEcho.apply_localEquation h hx).symm.trans (IsEcho.apply_localEquation h' hx)
    simp at this
    exact hne this

end MMP.Fourfold

end
