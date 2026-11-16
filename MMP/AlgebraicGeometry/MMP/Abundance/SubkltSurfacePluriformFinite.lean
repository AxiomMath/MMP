module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.Analytic.Surface.PluriformCyclicCoverLift
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Positivity.AsymptoticAdjointIdeal
import MMP.AlgebraicGeometry.Analytic.PluriformIntegrableGauge
import MMP.AlgebraicGeometry.MMP.Fourfold.ConvexGeography
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle

/-!
# Finiteness of pluriform representations of subklt surfaces

Let `X` be a smooth projective complex surface, `B` an snc `ℚ`-divisor all of whose coefficients
are less than one (negative coefficients allowed), and `m > 0` with `mB` integral. Put
`V = H⁰(X, m(K_X + B))`. If a group `G` of birational self-maps of `X` acts on `V` by pluriform
pull-back, the image of `G` in `GL(V)` is finite. The invariant gauge `p(s) = ∫_X |s|^{2/m}` is
continuous and positive on `V`, and the cyclic cover of an eigenvector forces every eigenvalue of
every element of `G` to be an `N`-th root of unity for one `N` depending only on `(X, B, m)`; an
invariant positive gauge and bounded root orders force a finite image.

In particular, for a projective klt surface pair `(X, B)` with `m(K_X + B)` Cartier, the crepant
birational self-maps act on `H⁰(X, m(K_X + B))` with finite image. A crepant self-map preserves
`H⁰(X, m(K_X + B))`: a section `τ` satisfies `ord_D(τ) ≥ m(a(D, X, B) - 1)` along every divisor
`D` over `X` (a Hartogs bound against a local generator of `𝒪_X(m(K_X + B))`), and crepancy
preserves log discrepancies. On a log resolution `f : Y → X` with crepant snc subboundary `B_Y`
(coefficients `< 1` by kltness, `mB_Y` integral), `f^*` identifies `H⁰(X, m(K_X + B))` with
`H⁰(Y, m(K_Y + B_Y))`, and conjugation by `f^*` carries the crepant self-maps of `(X, B)` to a
group preserving the latter, so the smooth case applies.

## Main results

* `MMP.Fourfold.finite_range_pluriformPullback_logPluricanonicalSections`: both assertions.

## Implementation notes

* A birational self-map is recorded by its pull-back, a `ℂ`-automorphism of `k(X)`
  (`MMP.Fourfold.FunctionFieldEquiv`), so `G` is a subgroup of these automorphisms, acting on
  rational `m`-canonical forms by `MMP.Fourfold.pluriformPullback`.
* The image of `G` in `GL(V)` is stated as the finiteness of the set of maps
  `s ↦ σ^* s` on `V`, `σ ∈ G`; these maps are the restrictions of the elements of the image.
* That `G` acts on `V` is the hypothesis that each `σ^*`, `σ ∈ G`, maps `V` into `V`; since
  `σ⁻¹ ∈ G` and pull-back is functorial, `σ^*` then maps `V` onto `V`.
* In the klt assertion the conclusion also records that each crepant self-map preserves
  `H⁰(X, m(K_X + B))`, so that the crepant birational representation is defined.
* The smooth case passes to coordinates `V ≃ ℂ^d` and applies
  `MMP.Fourfold.finite_of_gauge_invariant_of_hasEigenvalue_pow` to the image of `G` in `GL(ℂ^d)`.
  The group transported to a resolution is the image of the crepant group under
  `AlgEquiv.autCongr` of the isomorphism of function fields `f^* : k(X) ≃ k(Y)`.

## References

* [O. Fujino, Y. Gongyo, *Log pluricanonical representations and the abundance conjecture*],
  Compositio Math. 150 (2014).
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Fourfold

section Smooth

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} {m : ℕ}

/-- The pluriform pull-back of an element of a group preserving `V = H⁰(X, m(K_X + B))`, as a
linear endomorphism of `V`, packaged as a homomorphism to the endomorphisms of `V`. -/
private noncomputable def sectionsRep [LocallyOfFiniteType sX]
    (hn : topologicalKrullDim X = 2) (G : Subgroup (FunctionFieldEquiv sX sX))
    (hG : ∀ σ ∈ G, ∀ s ∈ logPluricanonicalSections sX 2 m B,
        pluriformPullback sX sX σ.toHom 2 m s ∈ logPluricanonicalSections sX 2 m B) :
    G →* Module.End ℂ (logPluricanonicalSections sX 2 m B) where
  toFun σ := (pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m).restrict
    (hG σ σ.2)
  map_one' := LinearMap.ext fun s =>
    Subtype.ext (pluriformPullback_one hn m (s : RationalPluriForms sX 2 m))
  map_mul' σ τ := by
    refine LinearMap.ext fun s => Subtype.ext ?_
    letI := functionFieldAlgebra sX
    change pluriformPullback sX sX
        ((σ : FunctionFieldEquiv sX sX).toHom.comp (τ : FunctionFieldEquiv sX sX).toHom) 2 m s =
      pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m
        (pluriformPullback sX sX (τ : FunctionFieldEquiv sX sX).toHom 2 m s)
    rw [pluriformPullback_comp hn hn hn]

/-- **Finiteness from an invariant gauge.** A representation `R` of a group on a finite-dimensional
complex vector space has finite image if it preserves a continuous positive gauge homogeneous of
positive degree and every eigenvalue of every `R g` is an `N`-th root of unity. -/
theorem finite_range_of_gauge_invariant_of_pow_eq_one {V G : Type*} [AddCommGroup V]
    [Module ℂ V] [Module.Finite ℂ V] [Group G] (R : G →* Module.End ℂ V) (p : V → ℝ)
    (hp : @Continuous V ℝ (moduleTopology ℂ V) _ p) (hpos : ∀ v, v ≠ 0 → 0 < p v) {α : ℝ}
    (hα : 0 < α) (hhom : ∀ (c : ℂ) v, p (c • v) = ‖c‖ ^ α * p v)
    (hinv : ∀ g v, p (R g v) = p v) {N : ℕ} (hN : 0 < N)
    (heig : ∀ g v, v ≠ 0 → ∀ μ : ℂ, R g v = μ • v → μ ^ N = 1) :
    (Set.range R).Finite := by
  classical
  let e := (Module.finBasis ℂ V).equivFun
  let ρ : G →* Module.End ℂ (Fin (Module.finrank ℂ V) → ℂ) :=
    { toFun := fun g => (e : _ →ₗ[ℂ] _) ∘ₗ R g ∘ₗ (e.symm : _ →ₗ[ℂ] _)
      map_one' := LinearMap.ext fun w => by simp
      map_mul' := fun g h => LinearMap.ext fun w => by simp [Module.End.mul_apply] }
  have hρ : ∀ g w, ρ g w = e (R g (e.symm w)) := fun _ _ => rfl
  set H := (MonoidHom.toHomUnits ρ).range
  let q : (Fin (Module.finrank ℂ V) → ℂ) → NNReal := fun w => Real.toNNReal (p (e.symm w))
  have hq : Continuous q := by
    letI : TopologicalSpace V := moduleTopology ℂ V
    haveI : IsModuleTopology ℂ V := ⟨rfl⟩
    haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℂ V
    exact continuous_real_toNNReal.comp
      (hp.comp (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap))
  have hqhom : ∀ (c : ℂ) w, q (c • w) = ‖c‖₊ ^ α * q w := by
    intro c w
    simp only [q, map_smul, hhom]
    rw [Real.toNNReal_mul (Real.rpow_nonneg (norm_nonneg c) _)]
    congr 1
    ext
    simp [NNReal.coe_rpow, Real.rpow_nonneg (norm_nonneg c)]
  have hqinv : ∀ g ∈ H, ∀ w, q (g.1 w) = q w := by
    rintro _ ⟨g, rfl⟩ w
    simp only [q, MonoidHom.coe_toHomUnits, hρ, LinearEquiv.symm_apply_apply, hinv]
  have heig' : ∀ g ∈ H, ∀ μ : ℂ, Module.End.HasEigenvalue g.1 μ → μ ^ N = 1 := by
    rintro _ ⟨g, rfl⟩ μ hμ
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have h1 := hw.apply_eq_smul
    rw [MonoidHom.coe_toHomUnits, hρ] at h1
    refine heig g (e.symm w) ((LinearEquiv.map_ne_zero_iff e.symm).mpr hw.2) μ ?_
    have := congrArg e.symm h1
    rwa [LinearEquiv.symm_apply_apply, map_smul] at this
  have : Finite H := finite_of_gauge_invariant_of_hasEigenvalue_pow H q hq
    (fun w hw => Real.toNNReal_pos.mpr (hpos _ ((LinearEquiv.map_ne_zero_iff e.symm).mpr hw)))
    hα hqhom hqinv hN heig'
  refine (Set.finite_range fun u : H =>
    (e.symm : _ →ₗ[ℂ] _) ∘ₗ u.1.1 ∘ₗ (e : _ →ₗ[ℂ] _)).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨MonoidHom.toHomUnits ρ g, g, rfl⟩, LinearMap.ext fun v => by simp [hρ]⟩

/-- **Roots of unity from cyclic covers.** There is `N > 0` such that every eigenvalue of the
pluriform pull-back by a birational self-map of `X`, on an eigenvector in `H⁰(X, m(K_X + B))`, is
an `N`-th root of unity. -/
private theorem exists_pow_eq_one_of_pluriformPullback_eq_smul_of_mem
    (hn : topologicalKrullDim X = 2) (hXB : IsSNCSubboundaryPair sX B) (hB : ∀ P, B.coeff P < 1)
    (hm : 0 < m) (hmB : ∀ P, ∃ a : ℤ, (m : ℚ) * B.coeff P = a) :
    ∃ N : ℕ, 0 < N ∧ ∀ (σ : FunctionFieldEquiv sX sX) (s : RationalPluriForms sX 2 m),
      s ∈ logPluricanonicalSections sX 2 m B → s ≠ 0 → ∀ μ : ℂ,
        pluriformPullback sX sX σ.toHom 2 m s = μ • s → μ ^ N = 1 := by
  obtain ⟨b, hb⟩ := exists_cyclicCover_resolution_finrank_le hn hXB hB hm hmB
  obtain ⟨N, hN, hNlift⟩ := exists_pow_eq_one_of_pluriformPullback_eq_smul b
  refine ⟨N, hN, fun σ s hs hs0 μ hσ => ?_⟩
  obtain ⟨k, Y, hI, hNo, hNn, pp, hp, hproj, hsm, hbet, ω, hω0, hω1, hωm, η, hη, z, hz, hadj,
    hrank⟩ := hb s hs hs0
  exact (hNlift hn hXB hB hm hmB s hs hs0 Y pp hproj hsm hbet ω hω0 hω1 hωm η hη z hz hadj hrank
    σ μ hσ).2

/-- **Finiteness of subklt surface pluriform representations**, the smooth case. -/
private theorem finite_range_of_isSNCSubboundaryPair (hn : topologicalKrullDim X = 2)
    (hXB : IsSNCSubboundaryPair sX B) (hB : ∀ P, B.coeff P < 1)
    (hm : 0 < m) (hmB : ∀ P, ∃ a : ℤ, (m : ℚ) * B.coeff P = a)
    (G : Subgroup (FunctionFieldEquiv sX sX))
    (hG : ∀ σ ∈ G, ∀ s ∈ logPluricanonicalSections sX 2 m B,
      pluriformPullback sX sX σ.toHom 2 m s ∈ logPluricanonicalSections sX 2 m B) :
    (Set.range fun (σ : G) (s : logPluricanonicalSections sX 2 m B) =>
      pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m
        (s : RationalPluriForms sX 2 m)).Finite := by
  have : LocallyOfFiniteType sX := hXB.isProjectiveVariety.1.toLocallyOfFiniteType
  obtain ⟨N, hN, heig⟩ := exists_pow_eq_one_of_pluriformPullback_eq_smul_of_mem hn hXB hB hm hmB
  obtain ⟨p, hpc, hppos, hphom, hpinv, -⟩ :=
    exists_gauge_logPluricanonicalSections hn hXB hB hm hmB
  have : Module.Finite ℂ (logPluricanonicalSections sX 2 m B) :=
    finite_logPluricanonicalSections hn hXB
  have hfin := finite_range_of_gauge_invariant_of_pow_eq_one (sectionsRep hn G hG) p hpc
    hppos (by positivity : (0 : ℝ) < 2 / m) hphom (fun σ => hpinv σ (hG σ σ.2)) hN
    fun σ s hs0 μ hσ => heig σ s s.2 (fun h => hs0 (Subtype.ext h)) μ (congrArg Subtype.val hσ)
  refine (hfin.image fun r s => (r s : RationalPluriForms sX 2 m)).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨_, ⟨σ, rfl⟩, rfl⟩

end Smooth

section

universe u

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Discrepancy

open MMP.Threefold.Mori.Helpers MMP.Threefold.Mori.ModelIndependence

/-- **Composite pull-backs of pluri-forms.** For field extensions `K → K' → K''` over a field `k`
of characteristic zero, with `K, K'` essentially of finite type over `k` and all three of the same
transcendence degree, pulling back pluri-forms along `K → K'` and then `K' → K''` is pulling back
along `K → K''`. -/
theorem pullbackForms_pullbackForms_of_trdeg_eq {k K K' K'' : Type u} [Field k] [CharZero k]
    [Field K] [Field K'] [Field K''] [Algebra k K] [Algebra k K'] [Algebra k K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower k K K']
    [IsScalarTower k K' K''] [IsScalarTower k K K''] [IsScalarTower K K' K'']
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType k K']
    (h : Algebra.trdeg k K = Algebra.trdeg k K') (h' : Algebra.trdeg k K' = Algebra.trdeg k K'')
    {d : ℕ} (hd : (Algebra.trdeg k K).toNat = d) {m : ℤ} (τ : PluriForms k K d m) :
    pullbackForms (K' := K'') m (pullbackForms (K' := K') m τ) =
      pullbackForms (K' := K'') m τ := by
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator h hd
  obtain ⟨ω', hω'⟩ := exists_isPullbackGenerator (K' := K'') (d := d) h' (by rwa [← h])
  exact pullbackForms_comp hω (IsPullbackGenerator.of_span hω' hω.2.1 hω.2.2) τ

/-- A ring homomorphism `φ : k(Y) →+* k(X)` carrying the valuation `v_E` to `v_Γ` carries the
order `ord_E` to `ord_Γ`. -/
private theorem ord_eq_of_divisorialValuation_eq {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Γ : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (φ : Y.functionField →+* X.functionField)
    (hval : ∀ y, Γ.divisorialValuation (φ y) = E.divisorialValuation y) (y : Y.functionField) :
    X.ord (φ y) Γ.genericPoint = Y.ord y E.genericPoint := by
  obtain rfl | hy := eq_or_ne y 0
  · simp [Scheme.ord_zero]
  have h1 := hval y
  rw [Γ.divisorialValuation_eq_exp_neg_ord ((map_ne_zero φ).mpr hy),
    E.divisorialValuation_eq_exp_neg_ord hy, WithZero.exp_inj] at h1
  omega

/-- A surjection `φ : k(Y) → k(X)` carrying the valuation `v_E` to `v_Γ` restricts to an
isomorphism `𝒪_{Y,E} → 𝒪_{X,Γ}` of the valuation rings. -/
private theorem exists_ringHom_bijective_localRing {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Γ : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (φ : Y.functionField →+* X.functionField) (hφs : Function.Surjective φ)
    (hval : ∀ y, Γ.divisorialValuation (φ y) = E.divisorialValuation y) :
    ∃ ψ : E.localRing →+* Γ.localRing, Function.Bijective ψ ∧
      ∀ a, algebraMap Γ.localRing X.functionField (ψ a) =
        φ (algebraMap E.localRing Y.functionField a) := by
  refine exists_ringHom_bijective_of_range φ (fun a1 => ?_) (fun a2 => ?_)
  · have : E.divisorialValuation (algebraMap E.localRing Y.functionField a1) ≤ 1 :=
      (E.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    exact (Γ.divisorialValuation_le_one_iff _).mp this
  · obtain ⟨y, hy⟩ := hφs (algebraMap Γ.localRing X.functionField a2)
    have : E.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (Γ.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (E.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rwa [ha1]⟩

/-- **Orders along a valuation-preserving isomorphism of function fields.** Let
`φ : k(Y) → k(X)` be a surjective `k`-homomorphism carrying `v_E` to `v_Γ`. Then the pull-back of a
pluri-form along `φ` has the same order along `Γ` as the form along `E`. -/
private theorem ordAt_pullbackForms_eq_of_divisorialValuation_eq {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (Γ : MMP.Mori.PrimeDivisor X)
    (E : MMP.Mori.PrimeDivisor Y) (φ : Y.functionField →+* X.functionField)
    (hφs : Function.Surjective φ)
    (hval : ∀ y, Γ.divisorialValuation (φ y) = E.divisorialValuation y)
    (hφk : ∀ c : k, φ (@algebraMap k Y.functionField _ _ (functionFieldAlgebra sY) c) =
      @algebraMap k X.functionField _ _ (functionFieldAlgebra sX) c) {n : ℕ}
    (htr : letI := functionFieldAlgebra sX; letI := functionFieldAlgebra sY;
      Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField)
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = n)
    {m : ℤ} :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra sY
    letI := stalkAlgebra sY E.genericPoint
    letI := stalkAlgebra sX Γ.genericPoint
    haveI := isScalarTower_stalk_functionField sY E.genericPoint
    haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
    letI := φ.toAlgebra
    haveI : IsScalarTower k Y.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (hφk c).symm
    ∀ ω : PluriForms k Y.functionField n m,
      ordAt Γ.localRing (fun x => X.ord x Γ.genericPoint)
          (pullbackForms (K' := X.functionField) m ω) =
        ordAt E.localRing (fun y => Y.ord y E.genericPoint) ω := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sY
  letI := stalkAlgebra sY E.genericPoint
  letI := stalkAlgebra sX Γ.genericPoint
  haveI := isScalarTower_stalk_functionField sY E.genericPoint
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  letI := φ.toAlgebra
  haveI : IsScalarTower k Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (hφk c).symm
  intro ω
  obtain ⟨ψ, hψb, hψ⟩ := exists_ringHom_bijective_localRing φ hφs hval
  letI : Algebra E.localRing Γ.localRing := ψ.toAlgebra
  letI : Algebra E.localRing X.functionField :=
    ((algebraMap Γ.localRing X.functionField).comp ψ).toAlgebra
  have hS1 : IsScalarTower k E.localRing Γ.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective Γ.localRing X.functionField
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k E.localRing c))
    rw [hψ, ← IsScalarTower.algebraMap_apply k E.localRing Y.functionField c,
      ← IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c]
    exact IsScalarTower.algebraMap_apply k Y.functionField X.functionField c
  have hS2 : IsScalarTower E.localRing Γ.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower E.localRing Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq hψ
  have hS4 : IsScalarTower k E.localRing X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k E.localRing c))
    rw [IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c,
      IsScalarTower.algebraMap_apply k E.localRing Γ.localRing c]
    rfl
  have : Algebra.EssFiniteType k Y.functionField := essFiniteType_functionField (sX := sY)
  have hd1 : (Algebra.trdeg k Y.functionField).toNat = n := by rwa [← htr]
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator (k := k) (K := Y.functionField)
    (K' := X.functionField) htr.symm hd1
  obtain ⟨σE, hσE, h0σE⟩ := E.exists_topForms_generator (sX := sY) hd1
  have hωT : IsPullbackGenerator X.functionField
      (topFormsMap k E.localRing Y.functionField n σE) :=
    IsPullbackGenerator.of_span hω1 (span_singleton_topFormsMap (nonZeroDivisors _) hσE) h0σE
  exact ordAt_pullbackForms_eq (k := k) (K := Y.functionField) (K' := X.functionField)
    (A := E.localRing) (A' := Γ.localRing) (d := n) (m := m) hψb
    (v := fun y => Y.ord y E.genericPoint) (v' := fun y => X.ord y Γ.genericPoint)
    (fun x y hx hy => E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => E.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => Γ.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => Γ.ord_algebraMap_of_isUnit ha)
    (ord_eq_of_divisorialValuation_eq φ hval) hσE hωT ω

/-- **Orders of pulled-back forms along a valuation.** Let `σ` be a `k`-automorphism of `k(X)`,
`Γ` a prime divisor of `X` and `(Y, f, E)` a divisor over `X` whose valuation is `v_Γ ∘ σ`. Then
`ord_Γ(σ^* τ) = ord_D(τ)`. -/
private theorem ordForm_pluriformPullback_eq_ordPullback {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (σ : FunctionFieldEquiv sX sX) (Γ : MMP.Mori.PrimeDivisor X) (D : DivisorOver k sX)
    (hv : ∀ g : X.functionField, D.valuation g = Γ.divisorialValuation ((σ.toHom) g))
    {m : ℤ} (τ : RationalPluriForms sX n m) :
    Γ.ordForm (pluriformPullback sX sX σ.toHom n m τ) = D.ordPullback τ := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  let A := functionFieldAlgebra sX
  let AY := functionFieldAlgebra (D.f ≫ sX)
  let Af := functionFieldMapAlgebra D.f
  have hT1 := isScalarTower_functionFieldMap sX D.f
  have hb := D.isBirationalMorphism.functionFieldMap_bijective
  let F := RingEquiv.ofBijective _ hb
  let φ : D.Y.functionField →+* X.functionField := (σ.toHom).toRingHom.comp F.symm.toRingHom
  have hφ : ∀ g, φ (functionFieldMap D.f g) = (σ.toHom) g := fun g =>
    congrArg σ.toHom (F.symm_apply_apply g)
  have hφk : ∀ c : k, φ (algebraMap k D.Y.functionField c) = algebraMap k X.functionField c :=
    fun c => by
      rw [IsScalarTower.algebraMap_apply k X.functionField D.Y.functionField c]
      exact (hφ _).trans ((σ.toHom).commutes c)
  letI Aφ : Algebra D.Y.functionField X.functionField := φ.toAlgebra
  haveI hTφ : IsScalarTower k D.Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (hφk c).symm
  have hd : (Algebra.trdeg k X.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have htr : Algebra.trdeg k X.functionField = Algebra.trdeg k D.Y.functionField :=
    trdeg_functionField_eq_of_bijective sX D.f hb
  have : Algebra.EssFiniteType k X.functionField := essFiniteType_functionField (sX := sX)
  have : Algebra.EssFiniteType k D.Y.functionField := essFiniteType_functionField (sX := D.f ≫ sX)
  let Aσ : Algebra X.functionField X.functionField := (σ.toHom).toRingHom.toAlgebra
  have tσ : @IsScalarTower k X.functionField X.functionField _ Aσ.toSMul _ :=
    letI := Aσ
    IsScalarTower.of_algebraMap_eq fun c => ((σ.toHom).commutes c).symm
  have t3 : @IsScalarTower X.functionField D.Y.functionField X.functionField Af.toSMul
      Aφ.toSMul Aσ.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ Af Aφ Aσ fun g => (hφ g).symm
  have hcomp : pluriformPullback sX sX σ.toHom n m τ =
      pullbackForms (K' := X.functionField) m (pullbackForms (K' := D.Y.functionField) m τ) :=
    (@pullbackForms_pullbackForms_of_trdeg_eq k X.functionField D.Y.functionField
      X.functionField _ _ _ _ _ A AY A Af Aφ Aσ hT1 hTφ tσ t3 _ _ htr htr.symm n hd m τ).symm
  rw [hcomp]
  exact ordAt_pullbackForms_eq_of_divisorialValuation_eq Γ D.E φ
    (fun z => (σ.surjective z).elim fun g hg => ⟨_, (hφ g).trans hg⟩)
    (fun y => by
      obtain ⟨g, rfl⟩ := hb.2 y
      rw [hφ g, ← hv g]
      rfl) hφk htr hd (pullbackForms (K' := D.Y.functionField) m τ)

/-- **Hartogs bound for log pluricanonical forms.** Let `(X, B)` be a pair with canonical divisor
`K`, `m > 0` with `m(K + B)` Cartier, and `τ ≠ 0` in `H⁰(X, m(K + B))`. For every divisor `D` over
`X` there is a local generator `τ₀` of `𝒪_X(m(K + B))` at the centre of `D` computing the
discrepancy `a(D, X, B) = ord_D(τ₀) / m`, and `ord_D(τ₀) ≤ ord_D(τ)`. -/
private theorem exists_isDiscrepancy_ordPullback_le {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {B : QDivisor X}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) (D : DivisorOver k sX)
    {τ : RationalPluriForms sX n m} (hτ : τ ∈ logPluricanonicalSections sX n m B)
    (hτne : τ ≠ 0) :
    ∃ τ0 : RationalPluriForms sX n m, IsDiscrepancy sX n K B D ((D.ordPullback τ0 : ℚ) / m) ∧
      D.ordPullback τ0 ≤ D.ordPullback τ := by
  classical
  have hn := hK.topologicalKrullDim_eq
  have hP : MMP.Mori.IsPair sX B := ⟨hX, n, K, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  set x := D.f D.E.genericPoint
  obtain ⟨⟨D₀, hD₀⟩, U, hxU, τ0, hτ0⟩ := MMP.Positivity.IsPair.exists_generatesOn hP hK hmD x
  refine ⟨τ0, ⟨hX, hK, m, hm, hmD, U, hxU, τ0, hτ0, by field_simp⟩, ?_⟩
  let A := functionFieldAlgebra sX
  obtain ⟨bas, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set cτ := (ZTensorPower.basis bas m).repr τ () with hcτ
  set c0 := (ZTensorPower.basis bas m).repr τ0 () with hc0
  have hcτ0 : cτ ≠ 0 := repr_ne_zero_of_ne_zero bas hτne
  have hc00 : c0 ≠ 0 := repr_ne_zero_of_ne_zero bas hτ0.1
  set g := cτ / c0 with hg
  have hg0 : g ≠ 0 := div_ne_zero hcτ0 hc00
  have hcτg : cτ = g * c0 := by rw [hg, div_mul_cancel₀ _ hc00]
  have hY : D.ordPullback τ =
      D.Y.ord (functionFieldMap D.f g) D.E.genericPoint + D.ordPullback τ0 := by
    rw [hN m τ hτne, hN m τ0 hτ0.1, ← hcτ, ← hc0, hcτg, map_mul,
      Scheme.ord_mul ((map_ne_zero _).mpr hg0) ((map_ne_zero _).mpr hc00)]
    ring
  have hXg : ∀ Γ' : MMP.Mori.PrimeDivisor X,
      Γ'.ordForm τ = X.ord g Γ'.genericPoint + Γ'.ordForm τ0 := by
    intro Γ'
    obtain ⟨N', hN'⟩ := Γ'.exists_ordForm_eq_ord_add_mul hd bas
    rw [hN' m τ hτne, hN' m τ0 hτ0.1, ← hcτ, ← hc0, hcτg, Scheme.ord_mul hg0 hc00]
    ring
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot top_ne_bot] at hτ
  have hgx : ∀ Γ' : MMP.Mori.PrimeDivisor X, x ∈ Γ'.support → 0 ≤ X.ord g Γ'.genericPoint := by
    intro Γ' hxΓ'
    have h1 := hτ Γ' ⟨x, hxΓ', trivial⟩ hτne
    have h2 := hτ0.2 Γ' ⟨x, hxΓ', hxU⟩
    have hD₀c : ((D₀.coeff Γ' : ℤ) : ℚ) = m * B.coeff Γ' := by
      simpa using congrArg (fun D : QDivisor X => D.coeff Γ') hD₀
    have e : DivisorWithCoeffs.coeff ((m : ℤ) • B) Γ' = ((D₀.coeff Γ' : ℤ) : ℚ) := by
      rw [← hD₀]
      simp
    rw [DivisorWithCoeffs.coeff_roundDown, e, Int.floor_intCast] at h1
    rw [← hD₀c] at h2
    have h3 : Γ'.ordForm τ0 = -D₀.coeff Γ' := by
      exact_mod_cast (by push_cast; linarith : (Γ'.ordForm τ0 : ℚ) = ((-D₀.coeff Γ' : ℤ) : ℚ))
    rw [hXg Γ', h3] at h1
    linarith
  obtain ⟨r, hr⟩ := exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hg0 hgx
  linarith [ord_functionFieldMap_nonneg D hg0 r hr]

/-- **Sections against a divisor of known discrepancy.** If `D` is a divisor over `X` with
discrepancy `a(D, X, B) = -c` and `m(K + B)` is Cartier, then every `τ ≠ 0` in
`H⁰(X, m(K + B))` has `ord_D(τ) + ⌊mc⌋ ≥ 0`. -/
public theorem ordPullback_add_floor_nonneg {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {B : QDivisor X}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) (D : DivisorOver k sX)
    {τ : RationalPluriForms sX n m} (hτ : τ ∈ logPluricanonicalSections sX n m B)
    (hτne : τ ≠ 0) {c : ℚ} (hc : IsDiscrepancy sX n K B D (-c)) :
    0 ≤ D.ordPullback τ + ⌊((m : ℤ) • c : ℚ)⌋ := by
  obtain ⟨τ0, hdisc, hle⟩ := exists_isDiscrepancy_ordPullback_le hX hK hm hmD D hτ hτne
  have he := hc.eq hdisc
  rw [eq_div_iff (by positivity)] at he
  have h5 : -(D.ordPullback τ : ℤ) ≤ ⌊((m : ℤ) • c : ℚ)⌋ := by
    rw [Int.le_floor, zsmul_eq_mul]
    push_cast
    have : (D.ordPullback τ0 : ℚ) ≤ D.ordPullback τ := by exact_mod_cast hle
    linarith
  linarith

/-- **Crepant birational self-maps preserve `H⁰(X, m(K + B))`.** For a pair `(X, B)` with
canonical divisor `K` and `m(K + B)` Cartier, the pull-back by a crepant birational self-map
carries `H⁰(X, m(K + B))` into itself. -/
private theorem pluriformPullback_mem_logPluricanonicalSections {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {B : QDivisor X}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    {σ : FunctionFieldEquiv sX sX} (hσ : σ ∈ crepantBirationalAutomorphisms sX B)
    {τ : RationalPluriForms sX n m} (hτ : τ ∈ logPluricanonicalSections sX n m B) :
    pluriformPullback sX sX σ.toHom n m τ ∈ logPluricanonicalSections sX n m B := by
  classical
  have hn := hK.topologicalKrullDim_eq
  have hP : MMP.Mori.IsPair sX B := ⟨hX, n, K, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain rfl | hτne := eq_or_ne τ 0
  · rw [map_zero]
    exact zero_mem _
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot top_ne_bot]
  intro Γ _ _
  set DΓ := DivisorOver.ofPrimeDivisor k hX Γ
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK DΓ
  have hc' : c = -B.coeff Γ := hc.eq_neg_coeff_of_ofPrimeDivisor hX
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 X) by infer_instance)
  have hσ' : IsCrepantBirationalMap sX sX B B σ := hσ
  obtain ⟨n', D, hDv, hDlog⟩ := (hσ' DΓ.valuation (1 + c)).mp ⟨n, DΓ, rfl, hlog⟩
  obtain rfl : n' = n := by
    exact_mod_cast
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hDlog).symm.trans hn
  have hv : ∀ g : X.functionField, D.valuation g = Γ.divisorialValuation ((σ.toHom) g) := by
    intro g
    rw [hDv]
    change Γ.divisorialValuation (functionFieldMap (𝟙 X) _) = _
    rw [functionFieldMap_id_apply]
    rfl
  rw [ordForm_pluriformPullback_eq_ordPullback hX hn σ Γ D hv τ, DivisorWithCoeffs.coeff_roundDown,
    DivisorWithCoeffs.coeff_smul]
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  have h1 := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hDlog
  have hac : a = -B.coeff Γ := by
    rw [← hc']
    exact_mod_cast (by linarith : (a : ℝ) = c)
  exact ordPullback_add_floor_nonneg hX hK hm hmD D hτ hτne (hac ▸ ha)

end Discrepancy

section Resolution

open TopologicalSpace MMP.Resolution

section Crepant

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
  {f : Y ⟶ X}

/-- **The support of the crepant boundary.** For a birational morphism `f : Y ⟶ X` from a
normal variety, every prime divisor in the support of the crepant boundary `Δ_Y` is
`f`-exceptional or lies over `Supp Δ`. -/
private theorem genericPoint_mem_exceptionalSet_or_mem_of_mem_support [IsProper f]
    (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : G ∈ ΔY.support) :
    G.genericPoint ∈ (exceptionalSet f : Set Y) ∨
      f G.genericPoint ∈ (Δ.support.sup fun E => (E.idealSheaf.support : Set X)) := by
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  · obtain ⟨P, hc, hη, -⟩ := exists_coeff_eq_of_not_isExceptional hP hY hf hΔY hGe
    refine Or.inr ?_
    rw [hη, Finset.sup_set_eq_biUnion]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc,
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

end Crepant

/-- An element lies in the support of `∑_{E ∈ S} single E 1` exactly when it is in `S`. -/
public theorem mem_support_sum_single {α : Type*} (S : Finset α) (G : α) :
    G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ↔ G ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- **Valuative criterion at a divisor.** A proper birational morphism `f : Y ⟶ X` onto a normal
scheme is an isomorphism of local rings over the generic point of each prime divisor `Q` of `X`:
there is a prime divisor `E` of `Y` with `f(η_E) = η_Q` and `f^♯ : 𝒪_{X,η_Q} ≅ 𝒪_{Y,η_E}`. -/
private theorem exists_primeDivisor_isIso_stalkMap {X Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (f : Y ⟶ X)
    [IsProper f] (hf : IsBirationalMorphism f) (Q : MMP.Mori.PrimeDivisor X) :
    ∃ E : MMP.Mori.PrimeDivisor Y,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

/-- **Pull-back of sections to a crepant model.** For a pair `(X, B)` with `m(K + B)` Cartier and a
birational morphism `f : Y ⟶ X` from a normal variety with crepant boundary `B_Y`, the pull-back
`f^*` maps `H⁰(X, m(K + B))` into `H⁰(Y, m(K_Y + B_Y))`. -/
private theorem pullbackRationalPluriForms_mem_of_isCrepantBoundary {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} {B : QDivisor X} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {f : Y ⟶ X} [IsDominant f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {BY : QDivisor Y}
    (hBY : IsCrepantBoundary sX n K B f hY hf BY) {s : RationalPluriForms sX n m}
    (hs : s ∈ logPluricanonicalSections sX n m B) :
    pullbackRationalPluriForms sX f s ∈ logPluricanonicalSections (f ≫ sX) n m BY := by
  obtain rfl | hs0 := eq_or_ne s 0
  · have h0 : pullbackRationalPluriForms sX f (0 : RationalPluriForms sX n m) = 0 := by
      let := functionFieldAlgebra sX
      let := functionFieldAlgebra (f ≫ sX)
      let := functionFieldMapAlgebra f
      have := isScalarTower_functionFieldMap sX f
      change pullbackForms (K := X.functionField) (K' := Y.functionField) (m : ℤ) 0 = 0
      simpa using pullbackForms_add (K' := Y.functionField) (m := (m : ℤ))
        (0 : PluriForms k X.functionField n m) 0
    rw [h0]
    exact zero_mem _
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot top_ne_bot]
  intro E _ _
  change 0 ≤ (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX).ordPullback s + _
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul]
  exact ordPullback_add_floor_nonneg hX hK hm hmD _ hs hs0 (hBY E)

/-- **Sections descend from a crepant model.** For a pair `(X, B)` with `m(K + B)` Cartier and a
proper birational morphism `f : Y ⟶ X` from a normal variety with crepant boundary `B_Y`, a form
`s` with `f^* s ≠ 0` in `H⁰(Y, m(K_Y + B_Y))` lies in `H⁰(X, m(K + B))`. -/
private theorem mem_logPluricanonicalSections_of_pullback_mem {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} {B : QDivisor X}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {f : Y ⟶ X} [IsProper f]
    [IsDominant f] (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    {BY : QDivisor Y} (hBY : IsCrepantBoundary sX n K B f hY hf BY)
    {s : RationalPluriForms sX n m} (hfs0 : pullbackRationalPluriForms sX f s ≠ 0)
    (hs : pullbackRationalPluriForms sX f s ∈ logPluricanonicalSections (f ≫ sX) n m BY) :
    s ∈ logPluricanonicalSections sX n m B := by
  have hn := hK.topologicalKrullDim_eq
  have hP : MMP.Mori.IsPair sX B := ⟨hX, n, K, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot top_ne_bot] at hs ⊢
  intro Γ _ _
  obtain ⟨E, hEΓ, _⟩ := exists_primeDivisor_isIso_stalkMap f hf Γ
  have hord := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f
    hf.functionFieldMap_bijective hd E Γ hEΓ s
  obtain ⟨c, hcΓ⟩ :=
    MMP.Positivity.IsPair.exists_isDiscrepancy hP hK (DivisorOver.ofPrimeDivisor k hX Γ)
  have hc' := hcΓ.eq_neg_coeff_of_ofPrimeDivisor hX
  have hcE : IsDiscrepancy sX n K B ⟨Y, f, hY, hf, E⟩ c := by
    obtain ⟨hX', hK', m', hm', hC', U, hUx, τ, hτ, hτa⟩ := hcΓ
    refine ⟨hX', hK', m', hm', hC', U, ?_, τ, hτ, ?_⟩
    · change f E.genericPoint ∈ U
      rwa [hEΓ]
    · rw [hτa, DivisorOver.ordPullback_ofPrimeDivisor hX hn]
      change (Γ.ordForm τ : ℚ) = (E.ordForm (pullbackRationalPluriForms sX f τ) : ℚ)
      rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f
        hf.functionFieldMap_bijective hd E Γ hEΓ τ]
  have hcoef : BY.coeff E = B.coeff Γ := by linarith [(hBY E).eq hcE]
  have h := hs E ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
    hfs0
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at h ⊢
  rwa [hord, hcoef] at h

/-- **Pull-back along a birational morphism intertwines the actions.** For a dominant morphism
`f : Y ⟶ X` of integral `k`-schemes of dimension `n` inducing `k(X) ≅ k(Y)`, the pull-back `f^*` of
rational `m`-canonical forms has an inverse `L`, and transporting `k`-automorphisms of `k(X)` to
`k(Y)` along `f^*` makes `f^*` equivariant. -/
private theorem exists_pullbackRationalPluriForms_inverse {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)]
    (hf : Function.Bijective (functionFieldMap f)) {n : ℕ} (hn : topologicalKrullDim X = n)
    (hnY : topologicalKrullDim Y = n) (m : ℤ) :
    ∃ (L : RationalPluriForms (f ≫ sX) n m →ₗ[k] RationalPluriForms sX n m)
      (c : FunctionFieldEquiv sX sX →* FunctionFieldEquiv (f ≫ sX) (f ≫ sX)),
      (∀ s, L (pullbackRationalPluriForms sX f s) = s) ∧
      (∀ t, pullbackRationalPluriForms sX f (L t) = t) ∧
      ∀ σ s, pluriformPullback (f ≫ sX) (f ≫ sX)
          (FunctionFieldEquiv.toHom (f ≫ sX) (f ≫ sX) (c σ)) n m
          (pullbackRationalPluriForms sX f s) =
        pullbackRationalPluriForms sX f (pluriformPullback sX sX σ.toHom n m s) := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  let φf : FunctionFieldHom (f ≫ sX) sX :=
    { toRingHom := functionFieldMap f
      commutes' := fun c => by
        letI := functionFieldMapAlgebra f
        have := isScalarTower_functionFieldMap sX f
        exact (IsScalarTower.algebraMap_apply k X.functionField Y.functionField c).symm }
  have hφf : ∀ s : RationalPluriForms sX n m,
      pluriformPullback (f ≫ sX) sX φf n m s = pullbackRationalPluriForms sX f s := fun _ => rfl
  let F : X.functionField ≃ₐ[k] Y.functionField := AlgEquiv.ofBijective φf hf
  refine ⟨pluriformPullback sX (f ≫ sX) (FunctionFieldEquiv.toHom sX (f ≫ sX) F.symm) n m,
    (AlgEquiv.autCongr F).toMonoidHom, fun s => ?_, fun t => ?_, fun σ s => ?_⟩
  · rw [← hφf, pluriformPullback_comp hn hnY hn]
    have : (FunctionFieldEquiv.toHom sX (f ≫ sX) F.symm).comp φf =
        (1 : FunctionFieldEquiv sX sX).toHom := AlgHom.ext F.symm_apply_apply
    rw [this, pluriformPullback_one hn]
  · rw [← hφf, pluriformPullback_comp hnY hn hnY]
    have : φf.comp (FunctionFieldEquiv.toHom sX (f ≫ sX) F.symm) =
        (1 : FunctionFieldEquiv (f ≫ sX) (f ≫ sX)).toHom :=
      AlgHom.ext F.apply_symm_apply
    rw [this, pluriformPullback_one hnY]
  · rw [← hφf, ← hφf, pluriformPullback_comp hnY hnY hn, pluriformPullback_comp hnY hn hn]
    have : (FunctionFieldEquiv.toHom (f ≫ sX) (f ≫ sX)
        ((AlgEquiv.autCongr F).toMonoidHom σ)).comp φf =
        φf.comp (FunctionFieldEquiv.toHom sX sX σ) := AlgHom.ext fun x => by
      change F (σ (F.symm (F x))) = F (σ x)
      rw [F.symm_apply_apply]
    rw [this]

/-- **The crepant boundary on a log resolution of a klt surface pair.** On a log resolution
`f : Y ⟶ X` of a projective klt surface pair `(X, B)` with `m(K + B)` Cartier, the crepant boundary
`B_Y` is an snc subboundary with coefficients `< 1` and `m B_Y` integral. -/
private theorem isSNCSubboundaryPair_of_isCrepantBoundary {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hXB : IsKltPair sX B) (hproj : Mori.IsProjectiveVariety ℂ sX) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {f : Y ⟶ X}
    (hres : IsResolutionOfVariety sX f)
    (hS : IsSNCClosedSubset (f ≫ sX)
      ((exceptionalSet f : Set Y) ∪ f ⁻¹' (B.support.sup fun E => E.idealSheaf.support)))
    (hY : IsNormalVariety ℂ (f ≫ sX)) {BY : QDivisor Y}
    (hBY : IsCrepantBoundary sX 2 K B f hY hres.isBirationalMorphism BY) :
    IsSNCSubboundaryPair (f ≫ sX) BY ∧ (∀ F, BY.coeff F < 1) ∧
      ∀ P, ∃ a : ℤ, (m : ℚ) * BY.coeff P = a := by
  classical
  have hX : IsNormalVariety ℂ sX := hXB.1.isPair.1
  have hP : MMP.Mori.IsPair sX B := ⟨hX, 2, K, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have hPw : IsPairWith sX 2 K B := ⟨hX, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have hf := hres.isBirationalMorphism
  haveI : IsProper f := hres.isProjective.isProper
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : CompactSpace Y := (hY.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  haveI : LocallyOfFinitePresentation (f ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
  obtain ⟨S, hsncS, hmem⟩ := MMP.Mori.exists_finset_isSNC hres.isSmoothScheme
    (MMP.ProgramBaseChange.isSNCSubset_of_isSNCClosedSubset hres.isSmoothScheme
      (S := ⟨_, hS.1⟩) hS)
  have hBYS : BY.support ⊆ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support := fun G hG => by
    rw [Finset.ext (mem_support_sum_single S)]
    apply hmem
    exact genericPoint_mem_exceptionalSet_or_mem_of_mem_support hPw hY hf hBY hG
  have hlt : ∀ F, BY.coeff F < 1 := fun F => by
    have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hBY F)
      (show IsProper f from inferInstance)
    have h := hXB.2 2 _ _ hlog
    have : ((BY.coeff F : ℚ) : ℝ) < 1 := by
      push_cast at h
      linarith
    exact_mod_cast this
  refine ⟨⟨?_, hres.isSmoothScheme, hsncS.of_support_subset hBYS, fun P => (hlt P).le⟩, hlt,
    fun P => ?_⟩
  · exact (Mori.isProjectiveVariety_iff ℂ (f ≫ sX)).2 ⟨hres.isVariety_source,
      isProjectiveMorphism_of_isProjective_of_isAffine (f ≫ sX) (hres.isProjective.comp
        ((Mori.isProjectiveVariety_iff ℂ sX).1 hproj).2.isProjective)⟩
  · obtain ⟨D', hD'⟩ :=
      (IsPair.existsUnique_isCrepantBoundary hP hK f hY hf).2 BY hBY (m : ℤ) hmD
    exact ⟨D'.coeff P, by
      simpa [zsmul_eq_mul] using (congrArg (fun D : QDivisor Y => D.coeff P) hD').symm⟩

/-- **Finiteness of the crepant birational representation of a klt surface pair.** -/
private theorem finite_range_of_isKltPair {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hn : topologicalKrullDim X = 2) {B : QDivisor X}
    (hXB : IsKltPair sX B) (hproj : Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) :
    (Set.range fun (σ : crepantBirationalAutomorphisms sX B)
          (s : logPluricanonicalSections sX 2 m B) =>
        pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m
          (s : RationalPluriForms sX 2 m)).Finite := by
  have hX : IsNormalVariety ℂ sX := hXB.1.isPair.1
  have hP : MMP.Mori.IsPair sX B := ⟨hX, 2, K, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨Y, f, hres, -, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX B.support
  haveI : IsProper f := hres.isProjective.isProper
  have hfres : IsSmoothResolution sX f :=
    ⟨inferInstance, hres.isBirationalMorphism, hres.isSmoothScheme⟩
  have hf := hres.isBirationalMorphism
  obtain ⟨hY, hdimY, -⟩ := hfres.isNormalVariety hX
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI := hf.isDominant
  have hnY : topologicalKrullDim Y = 2 := hdimY.trans hn
  obtain ⟨⟨BY, hBY, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP hK f hY hf
  obtain ⟨hXBY, hlt, hmBY⟩ :=
    isSNCSubboundaryPair_of_isCrepantBoundary hXB hproj hK hm hmD hres hS hY hBY
  have ha := fun s (hs : s ∈ logPluricanonicalSections sX 2 m B) =>
    pullbackRationalPluriForms_mem_of_isCrepantBoundary hX hK hm hmD hY hf hBY hs
  obtain ⟨L, c, hLf, hfL, hc⟩ :=
    exists_pullbackRationalPluriForms_inverse (sX := sX) hf.functionFieldMap_bijective hn hnY m
  have hG' : ∀ σ' ∈ (crepantBirationalAutomorphisms sX B).map c,
      ∀ t ∈ logPluricanonicalSections (f ≫ sX) 2 m BY,
      pluriformPullback (f ≫ sX) (f ≫ sX) (FunctionFieldEquiv.toHom (f ≫ sX) (f ≫ sX) σ') 2 m t ∈
        logPluricanonicalSections (f ≫ sX) 2 m BY := by
    rintro _ ⟨σ, hσ, rfl⟩ t ht
    have h1 : L t ∈ logPluricanonicalSections sX 2 m B := by
      by_cases ht0 : t = 0
      · rw [ht0, map_zero]
        exact zero_mem _
      exact mem_logPluricanonicalSections_of_pullback_mem hX hK hm hmD hY hf hBY
        (by rwa [hfL]) (by rwa [hfL])
    rw [← hfL t, hc]
    exact ha _ (pluriformPullback_mem_logPluricanonicalSections hX hK hm hmD hσ h1)
  have hfin := finite_range_of_isSNCSubboundaryPair hnY hXBY hlt hm hmBY _ hG'
  refine (hfin.image fun h (s : logPluricanonicalSections sX 2 m B) =>
    L (h ⟨pullbackRationalPluriForms sX f s, ha _ s.2⟩)).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨_, ⟨⟨c σ, σ, σ.2, rfl⟩, rfl⟩, funext fun s => ?_⟩
  change L (pluriformPullback (f ≫ sX) (f ≫ sX)
    (FunctionFieldEquiv.toHom (f ≫ sX) (f ≫ sX) (c σ)) 2 m
    (pullbackRationalPluriForms sX f s)) = _
  rw [hc, hLf]

end Resolution

end

/-- **Finiteness of subklt surface pluriform representations.**
1. Let `X` be a smooth projective complex surface, `B` an snc `ℚ`-divisor with all coefficients
   less than one (`MMP.Fourfold.IsSNCSubboundaryPair`), and `m > 0` with `mB` integral. Let `G` be
   a group of birational self-maps of `X` whose pluriform pull-backs preserve
   `V = H⁰(X, m(K_X + B))` (`MMP.Fourfold.logPluricanonicalSections`). Then the set of maps
   `V → ω^{⊗m}_{k(X)}`, `s ↦ σ^* s` for `σ ∈ G`, is finite: the image of `G` in `GL(V)` is finite.
2. Let `(X, B)` be a projective klt surface pair over `ℂ` (`MMP.Fourfold.IsKltPair`), `K` a
   canonical divisor and `m > 0` with `m(K + B)` Cartier. Then every crepant birational self-map
   (`MMP.Fourfold.crepantBirationalAutomorphisms`) preserves `H⁰(X, m(K + B))`, and the image of
   the crepant birational self-maps acting on it is finite. -/
@[mmp "thm_fourfold_subklt_surface_weak_pluriform_finite"]
public theorem finite_range_pluriformPullback_logPluricanonicalSections :
    (∀ {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
      {sX : X ⟶ Spec (.of ℂ)} (_hn : topologicalKrullDim X = 2) {B : QDivisor X}
      (_hXB : IsSNCSubboundaryPair sX B) (_hB : ∀ P, B.coeff P < 1)
      {m : ℕ} (_hm : 0 < m) (_hmB : ∀ P, ∃ a : ℤ, (m : ℚ) * B.coeff P = a)
      (G : Subgroup (FunctionFieldEquiv sX sX))
      (_hG : ∀ σ ∈ G, ∀ s ∈ logPluricanonicalSections sX 2 m B,
        pluriformPullback sX sX σ.toHom 2 m s ∈ logPluricanonicalSections sX 2 m B),
      (Set.range fun (σ : G) (s : logPluricanonicalSections sX 2 m B) =>
        pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m
          (s : RationalPluriForms sX 2 m)).Finite) ∧
    (∀ {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
      {sX : X ⟶ Spec (.of ℂ)} (_hn : topologicalKrullDim X = 2) {B : QDivisor X}
      (_hXB : IsKltPair sX B) (_hproj : Mori.IsProjectiveVariety ℂ sX)
      {K : Divisor X} (_hK : K.IsCanonicalDivisor sX 2) {m : ℕ} (_hm : 0 < m)
      (_hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor),
      (∀ σ ∈ crepantBirationalAutomorphisms sX B, ∀ s ∈ logPluricanonicalSections sX 2 m B,
        pluriformPullback sX sX σ.toHom 2 m s ∈ logPluricanonicalSections sX 2 m B) ∧
      (Set.range fun (σ : crepantBirationalAutomorphisms sX B)
          (s : logPluricanonicalSections sX 2 m B) =>
        pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m
          (s : RationalPluriForms sX 2 m)).Finite) := by
  refine ⟨?_, ?_⟩
  · intro X _ _ _ sX hn B hXB hB m hm hmB G hG
    exact finite_range_of_isSNCSubboundaryPair hn hXB hB hm hmB G hG
  intro X _ _ _ sX hn B hXB hproj K hK m hm hmD
  exact ⟨fun σ hσ s hs =>
      pluriformPullback_mem_logPluricanonicalSections hXB.1.isPair.1 hK hm hmD hσ hs,
    finite_range_of_isKltPair hn hXB hproj hK hm hmD⟩

end MMP.Fourfold
