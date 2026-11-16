module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.Basic
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalImagePushforward
import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Resolution.SncComplementResolution
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# Comparison of push-forwards on two modifications

Let `X` be a non-singular variety over a field `k` of characteristic zero, `μ₁ : X₁ ⟶ X` a
proper and `μ₂ : X₂ ⟶ X` a projective birational morphism from non-singular varieties, and `Gᵢ`
an `ℝ`-divisor on `Xᵢ` with simple normal crossing support. Suppose that `g₁^*G₁ = g₂^*G₂`
whenever `V` is a non-singular variety and `gᵢ : V ⟶ Xᵢ` are proper birational morphisms with
`g₁ ≫ μ₁ = g₂ ≫ μ₂`. Then
`μ₁_*𝒪_{X₁}(K_{X₁/X} - ⌊G₁⌋) = μ₂_*𝒪_{X₂}(K_{X₂/X} - ⌊G₂⌋)` as `𝒪_X`-submodules of `K(X)`.
Both sides agree with the push-forward from a common resolution `V` of `X₁` and `X₂`
(`MMP.Intersection.exists_isResolution_comp_eq_comp`), by
`MMP.Intersection.IsRelativeCanonicalDivisor.multiplierIdealSections_sub_roundDown_eq_comp`
applied to `g₁` and to `g₂`.

On the way we record that on a Noetherian integral scheme every Cartier divisor has a Weil
divisor, and conversely that on a quasi-compact normal integral locally Noetherian scheme every
Cartier Weil divisor is the Weil divisor of a Cartier divisor.

## Main results

* `MMP.Intersection.multiplierIdealSections_sub_roundDown_eq_of_weilPullback_eq`: the push-forwards
  of `𝒪(K_{Xᵢ/X} - ⌊Gᵢ⌋)` along two modifications agree when the `Gᵢ` have the same pull-back to
  every common resolution.
* `MMP.Intersection.exists_isWeilDivisorOfCartier`: every Cartier divisor on a Noetherian
  integral scheme has a Weil divisor.
* `MMP.Intersection.exists_isWeilDivisorOfCartier_principalDivisor`: a principal Weil divisor is
  the Weil divisor of some Cartier divisor.
* `MMP.Mori.Divisor.IsCartier.exists_isWeilDivisorOfCartier`: a Cartier Weil divisor on a
  quasi-compact normal integral locally Noetherian scheme is the Weil divisor of a Cartier
  divisor.

## Implementation notes

The auxiliary lemmas live in the namespace `Proof_lem_p09a_pushforward_comparison`,
opened only for the main result.

`μ_*𝒪_{X'}(E)` is `MMP.Intersection.multiplierIdealSections μ E`, the family of its sections over
the opens of `X` as subsets of `K(X)`; the conclusion is the equality of these families.
`K_{Xᵢ/X}` is pinned by `MMP.Intersection.IsRelativeCanonicalDivisor` and its Weil divisor by
`MMP.Intersection.IsWeilDivisorOfCartier`; `⌊Gᵢ⌋` is the round-down of the Weil divisor of `Gᵢ`.
On the non-singular `V` an `ℝ`-divisor is determined by its Weil divisor, so the hypothesis
`g₁^*G₁ = g₂^*G₂` is stated as: `g₁^*G₁` and `g₂^*G₂` have a common Weil divisor
(`MMP.Intersection.IsWeilPullback`). The relative canonical divisor `K_{V/X}` of the common
resolution is the divisor of the Jacobian section, a regular homomorphism of line bundles; the
existence of the divisor of a regular homomorphism of invertible modules is proved here. The
source works over `ℂ`; the statement is made over any field of characteristic zero, where
resolution of singularities holds.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry II*][lazarsfeld2004], proof of Thm. 9.2.18.
-/

@[expose] public section

universe u

namespace MMP.Intersection

open CategoryTheory TopologicalSpace AlgebraicGeometry
open MMP.Mori (Divisor RDivisor)

/-! ### Weil divisors of Cartier divisors -/

/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : IsArtinianRing (X.presheaf.stalk x) :=
    isArtinianRing_iff_krullDimLE_zero.mpr (krullDimLE_of_coheight_le (by simp [hx]))
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
theorem exists_isWeilDivisorOfCartier {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    exact hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' =>
      h ((genericPoint_mem_cartierSupport_iff (V := primeDivisorSubvariety P)).mpr h'))
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The order of vanishing at a point `η` of coheight one of the image in `k(X)` of a nonzero
element of the local ring `𝒪_{X,η}` is its order. -/
private theorem ord_algebraMap_stalk_eq_ord {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {η : X} (hη : Order.coheight η = 1) {r : X.presheaf.stalk η}
    (hr : r ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk η) X.functionField r) η = (Ring.ord _ r).toNat := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hη]
  simp only [Scheme.ordHom]
  rw [Ring.ordFrac_eq_ord _ hr]
  have hnz : r ∈ nonZeroDivisors (X.presheaf.stalk η) := mem_nonZeroDivisors_of_ne_zero hr
  simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_pos hnz]
  rw [← ENat.coe_toNat (Ring.ord_ne_top hnz)]
  simp

open MMP.CartierDivisorSheaf in
/-- On a quasi-compact normal integral locally Noetherian scheme, the principal Weil divisor of
a rational function `φ` is the Weil divisor of some Cartier divisor. -/
theorem exists_isWeilDivisorOfCartier_principalDivisor {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (φ : (MMP.Mori.RationalFunctions X)ˣ) :
    ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A (MMP.Mori.principalDivisor φ) := by
  have hsub : ∀ W Z : irreducibleComponents X, W = Z := fun W Z => by
    have hmem : ∀ W : irreducibleComponents X, (W : Set X) = Set.univ := fun W => by
      simpa [irreducibleComponents_eq_singleton] using W.2
    exact Subtype.ext ((hmem W).trans (hmem Z).symm)
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  set r₀ := MMP.Threefold.Mori.Helpers.evalFF Z₀ (φ : MMP.Mori.RationalFunctions X)
  have hr0 : r₀ ≠ 0 := (φ.isUnit.map _).ne_zero
  set c : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (ofFunctionField (X := X) ⊤).toMonoidHom (Units.mk0 r₀ hr0)
  refine ⟨principalDivisor c, fun Q => ?_⟩
  rw [MMP.Mori.coeff_principalDivisor, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
    hsub Q.component Z₀]
  obtain ⟨⟨a, b⟩, hab⟩ :=
    IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk Q.genericPoint)) r₀
  have hbK : algebraMap _ X.functionField (b : X.presheaf.stalk Q.genericPoint) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero hr0 hbK hab
  have hloc : IsLocalEquationAt (principalDivisor c) Q.genericPoint
      (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _)) :=
    ⟨⊤, trivial, c, isLocalEquationOn_principalDivisor c, rfl⟩
  have hfrac : IsFraction (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _))
      a b := by
    refine ⟨isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors b.2, ?_⟩
    apply (totalQuotientStalkToFunctionField_bijective Q.genericPoint).1
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient]
    erw [MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField]
    rwa [mul_comm]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety Q).genericPoint) :=
    krullDimLE_of_coheight_le Q.coheight_genericPoint.le
  convert isOrderAlong_of_isFraction (V := primeDivisorSubvariety Q) hloc
    (mem_nonZeroDivisors_of_ne_zero ha0) b.2 hfrac using 1
  have h1 := Scheme.ord_mul (x := Q.genericPoint) hr0 hbK
  rw [hab, ord_algebraMap_stalk_eq_ord Q.coheight_genericPoint ha0,
    ord_algebraMap_stalk_eq_ord Q.coheight_genericPoint (nonZeroDivisors.ne_zero b.2)] at h1
  change _ = ((Ring.ord _ a).toNat : ℤ) -
    ((Ring.ord _ (b : X.presheaf.stalk Q.genericPoint)).toNat : ℤ)
  linarith

end MMP.Intersection

namespace MMP.Mori.Divisor

open AlgebraicGeometry MMP.Intersection

/-- **A Cartier Weil divisor is the Weil divisor of a Cartier divisor.** On a quasi-compact
normal integral locally Noetherian scheme, every Weil divisor `D` that is Cartier is the Weil
divisor of some Cartier divisor. -/
theorem IsCartier.exists_isWeilDivisorOfCartier {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D : Divisor X} (hD : D.IsCartier) :
    ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A D := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨C, ⟨eC⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  obtain ⟨w, hw⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier C
  obtain ⟨ew⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (eC ≪≫ ew)
  obtain ⟨P, hP⟩ := exists_isWeilDivisorOfCartier_principalDivisor ψ
  refine ⟨C + P, fun Q => ?_⟩
  have hDw : D = w + MMP.Mori.principalDivisor ψ := by
    rw [← hψ]
    abel
  rw [hDw, DivisorWithCoeffs.coeff_add]
  exact (hw Q).add (hP Q)

end MMP.Mori.Divisor

namespace Proof_lem_p09a_pushforward_comparison

open CategoryTheory TopologicalSpace AlgebraicGeometry MMP.Intersection
open MMP.Mori (Divisor RDivisor)

/-! ### Divisors of homomorphisms -/

section DivisorOfHom

variable {X : Scheme.{u}} {L M : X.Modules}

/-- Two trivializations of `L` and `M` near `p` represent a homomorphism `φ : L ⟶ M` by
functions whose germs at `p` differ by a unit of `𝒪_{X,p}`. -/
private theorem exists_germ_eq_germ_mul_unit (φ : L ⟶ M) {U U' : X.Opens} {e : Γ(L, U)}
    {e' : Γ(M, U)} {f : Γ(L, U')} {f' : Γ(M, U')}
    (he : IsTrivializingGenerator L U e) (he' : IsTrivializingGenerator M U e')
    (hf : IsTrivializingGenerator L U' f) (hf' : IsTrivializingGenerator M U' f')
    {r : Γ(X, U)} {s : Γ(X, U')} (hr : φ.app U e = r • e') (hs : φ.app U' f = s • f')
    {p : X} (hp : p ∈ U) (hp' : p ∈ U') :
    ∃ w : (X.presheaf.stalk p)ˣ, X.presheaf.germ U' p hp' s = X.presheaf.germ U p hp r * w := by
  let W : X.Opens := U ⊓ U'
  have hpW : p ∈ W := ⟨hp, hp'⟩
  let i : W ⟶ U := homOfLE inf_le_left
  let j : W ⟶ U' := homOfLE inf_le_right
  have heW := he.res (inf_le_left : W ≤ U)
  have he'W := he'.res (inf_le_left : W ≤ U)
  have hfW := hf.res (inf_le_right : W ≤ U')
  have hf'W := hf'.res (inf_le_right : W ≤ U')
  obtain ⟨a, ha⟩ := heW.bijective.2 (L.presheaf.map j.op f)
  obtain ⟨b, hb⟩ := hfW.bijective.2 (L.presheaf.map i.op e)
  obtain ⟨a', ha'⟩ := he'W.bijective.2 (M.presheaf.map j.op f')
  obtain ⟨b', hb'⟩ := hf'W.bijective.2 (M.presheaf.map i.op e')
  simp only at ha hb ha' hb'
  have hab' : a' * b' = 1 := by
    apply hf'W.bijective.1
    simp only
    rw [← smul_smul, hb', ha', one_smul]
  have hab : b * a = 1 := by
    apply heW.bijective.1
    simp only
    rw [← smul_smul, ha, hb, one_smul]
  have hnat : ∀ {Y Z : X.Opens} (k : Y ⟶ Z) (m : Γ(L, Z)),
      φ.app Y (L.presheaf.map k.op m) = M.presheaf.map k.op (φ.app Z m) := by
    intro Y Z k m
    simpa only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (φ.mapPresheaf.naturality k.op) m
  have key : a * X.presheaf.map i.op r = X.presheaf.map j.op s * a' := by
    apply he'W.bijective.1
    simp only
    rw [← smul_smul, ← smul_smul, ha', ← Scheme.Modules.map_smul, ← Scheme.Modules.map_smul,
      ← hr, ← hs, ← hnat, ← hnat, ← Scheme.Modules.Hom.app_smul, ha]
  have hu : IsUnit (X.presheaf.germ W p hpW (a * b')) := by
    refine IsUnit.of_mul_eq_one (X.presheaf.germ W p hpW (b * a')) ?_
    rw [← map_mul, show a * b' * (b * a') = (b * a) * (a' * b') by ring, hab, hab', mul_one,
      map_one]
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, ← TopCat.Presheaf.germ_res_apply X.presheaf j p hpW,
    ← TopCat.Presheaf.germ_res_apply X.presheaf i p hpW, ← map_mul]
  congr 1
  calc X.presheaf.map j.op s = X.presheaf.map j.op s * (a' * b') := by rw [hab', mul_one]
    _ = _ := by
      rw [← mul_assoc, ← key]
      ring

/-- A homomorphism `φ` of line bundles is represented near every point by a function. -/
private theorem exists_isTrivializingGenerator_app_eq_smul [Stacks.Ample.IsInvertibleModule X L]
    [Stacks.Ample.IsInvertibleModule X M] (φ : L ⟶ M) (x : X) :
    ∃ (U : X.Opens) (e : Γ(L, U)) (e' : Γ(M, U)) (r : Γ(X, U)), x ∈ U ∧
      IsTrivializingGenerator L U e ∧ IsTrivializingGenerator M U e' ∧ φ.app U e = r • e' := by
  obtain ⟨U₁, -, e₁, hx₁, he₁⟩ := exists_isTrivializingGenerator L (V := ⊤) (x := x) trivial
  obtain ⟨U, hU, e', hx, he'⟩ := exists_isTrivializingGenerator M hx₁
  obtain ⟨r, hr⟩ := he'.bijective.2 (φ.app U (L.presheaf.map (homOfLE hU).op e₁))
  exact ⟨U, _, e', r, hx, he₁.res hU, he', hr.symm⟩

/-- **The divisor of a regular homomorphism of line bundles exists**: a regular `φ : L ⟶ M`
between invertible modules on a locally Noetherian scheme has a divisor `div(φ)`. -/
private theorem exists_isDivisorOfHom [IsLocallyNoetherian X]
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X M] {φ : L ⟶ M}
    (hφ : IsRegularHom φ) : ∃ D : X.CartierDivisor, IsDivisorOfHom φ D := by
  have hunit : ∀ (U : X.Opens) (e : Γ(L, U)) (e' : Γ(M, U)), IsTrivializingGenerator L U e →
      IsTrivializingGenerator M U e' → ∀ r : Γ(X, U), φ.app U e = r • e' →
        IsUnit (toTotalQuotient U r) := fun U e e' he he' r hr =>
    isUnit_toTotalQuotientSheaf_app X.sheaf U r (hφ U e e' he he' r hr)
  choose U e e' r hx he he' hr using exists_isTrivializingGenerator_app_eq_smul φ
  have hu := fun x => hunit (U x) (e x) (e' x) (he x) (he' x) (r x) (hr x)
  obtain ⟨D, hD⟩ := exists_isLocalEquationOn_of_germ_eq_mul U
    (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
    (fun x => (hu x).unit) (fun i j p hi hj => by
      obtain ⟨w, hw⟩ := exists_germ_eq_germ_mul_unit φ (he i) (he' i) (he j) (he' j) (hr i) (hr j)
        hi hj
      refine ⟨w, ?_⟩
      simp only [IsUnit.unit_spec, germ_toTotalQuotient, hw, map_mul])
  refine ⟨D, hφ, fun x => ⟨U x, hx x, r x, hu x, hD x⟩, fun V f f' hf hf' s hs => ?_⟩
  refine ⟨hunit V f f' hf hf' s hs, isLocalEquationOn_of_forall_isLocalEquationAt fun p hp => ?_⟩
  obtain ⟨w, hw⟩ := exists_germ_eq_germ_mul_unit φ (he p) (he' p) hf hf' (hr p) hs (hx p) hp
  simpa only [IsUnit.unit_spec, germ_toTotalQuotient, hw, map_mul] using
    (show IsLocalEquationAt D p _ from ⟨U p, hx p, (hu p).unit, hD p, rfl⟩).mul_units w

end DivisorOfHom

/-- The relative canonical divisor `K_{V/X'}` of a birational morphism of non-singular
varieties exists. -/
private theorem exists_isRelativeCanonicalDivisor {k : Type u} [Field k] {X' V : Scheme.{u}}
    {sX' : X' ⟶ Spec (.of k)} [IsIntegral V] [MMP.Mori.IsVariety k sX']
    (hX' : MMP.Mori.IsSmoothScheme sX') {g : V ⟶ X'} [MMP.Mori.IsVariety k (g ≫ sX')]
    (hV : MMP.Mori.IsSmoothScheme (g ≫ sX')) (hg : MMP.Mori.IsBirationalMorphism g) {n : ℕ}
    (hn : topologicalKrullDim V = n) :
    ∃ K : V.CartierDivisor, IsRelativeCanonicalDivisor sX' g K := by
  haveI : LocallyOfFiniteType sX' := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (g ≫ sX') := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation sX' :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : LocallyOfFinitePresentation (g ≫ sX') :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : Smooth sX' := (MMP.Mori.isSmoothScheme_iff _).mp hX'
  haveI : Smooth (g ≫ sX') := (MMP.Mori.isSmoothScheme_iff _).mp hV
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX')
  have hdX' : topologicalKrullDim X' = topologicalKrullDim V :=
    topologicalKrullDim_eq_of_isBirationalMorphism sX' (g ≫ sX') hg
  have := smoothOfRelativeDimension_of_isVariety sX' n (hdX'.trans hn)
  have := smoothOfRelativeDimension_of_isVariety (g ≫ sX') n hn
  have hiX' := Stacks.Discriminant.isInvertible_relativeDifferentialForms sX' n
  haveI : Stacks.Ample.IsInvertibleModule V
      (Scheme.Hom.relativeDifferentialForms (g ≫ sX') n) :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms (g ≫ sX') n
  haveI : Stacks.Ample.IsInvertibleModule V ((Scheme.Modules.pullback g).obj
      (Scheme.Hom.relativeDifferentialForms sX' n)) :=
    @Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback _ _
      g.toLRSHom.toShHom _ hiX'
  have hreg := isRegularHom_jacobianSection sX' hg n
  obtain ⟨K, hK⟩ := exists_isDivisorOfHom hreg
  exact ⟨K, n, hn, Or.inl ⟨hreg, hK⟩⟩

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rw [hfac, ← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- Push-forward along equal morphisms agrees, whatever dominance instances are used. -/
private theorem multiplierIdealSections_congr {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f f' : Y ⟶ X} (e : f = f')
    [IsDominant f] [IsDominant f'] (E : Divisor Y) :
    multiplierIdealSections f E = multiplierIdealSections f' E := by
  subst e
  rfl

end Proof_lem_p09a_pushforward_comparison

namespace MMP.Intersection

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Proof_lem_p09a_pushforward_comparison

open MMP.Mori (Divisor RDivisor)

/-- **Comparison of push-forwards on two modifications** (Lazarsfeld, proof of Thm. 9.2.18).
Let `μ₁ : X₁ ⟶ X` be a proper and `μ₂ : X₂ ⟶ X` a projective birational morphism from
non-singular varieties to a non-singular variety `X` over a field of characteristic zero, with
relative canonical divisors `Kᵢ` (Weil divisors `wKᵢ`), and let `Gᵢ` be an `ℝ`-divisor on `Xᵢ`
whose Weil divisor `wGᵢ` has simple normal crossing support. Suppose that for every non-singular
variety `V` and proper birational `gᵢ : V ⟶ Xᵢ` with `g₁ ≫ μ₁ = g₂ ≫ μ₂`, the pull-backs
`g₁^*G₁` and `g₂^*G₂` have the same Weil divisor. Then
`μ₁_*𝒪_{X₁}(K_{X₁/X} - ⌊G₁⌋) = μ₂_*𝒪_{X₂}(K_{X₂/X} - ⌊G₂⌋)`. -/
@[mmp "lem_p09a_pushforward_comparison"]
theorem multiplierIdealSections_sub_roundDown_eq_of_weilPullback_eq
    {k : Type u} [Field k] [CharZero k] {X X₁ X₂ : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [MMP.Mori.IsVariety k sX] (hX : MMP.Mori.IsSmoothScheme sX) [IsIntegral X]
    [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂] {μ₁ : X₁ ⟶ X} {μ₂ : X₂ ⟶ X}
    [MMP.Mori.IsVariety k (μ₁ ≫ sX)] (hX₁ : MMP.Mori.IsSmoothScheme (μ₁ ≫ sX))
    [MMP.Mori.IsVariety k (μ₂ ≫ sX)] (hX₂ : MMP.Mori.IsSmoothScheme (μ₂ ≫ sX))
    [IsProper μ₁] [IsDominant μ₁] (hμ₁ : MMP.Mori.IsBirationalMorphism μ₁)
    (hμ₂p : IsProjectiveMorphism μ₂) [IsDominant μ₂] (hμ₂ : MMP.Mori.IsBirationalMorphism μ₂)
    {G₁ : RCartierDivisor X₁} {wG₁ : RDivisor X₁} (hwG₁ : IsWeilRDivisorOf G₁ wG₁)
    (hsnc₁ : HasSNCSupport (μ₁ ≫ sX) wG₁)
    {G₂ : RCartierDivisor X₂} {wG₂ : RDivisor X₂} (hwG₂ : IsWeilRDivisorOf G₂ wG₂)
    (hsnc₂ : HasSNCSupport (μ₂ ≫ sX) wG₂)
    (hG : ∀ (V : Scheme.{u}) (g₁ : V ⟶ X₁) (g₂ : V ⟶ X₂),
      MMP.Mori.IsVariety k (g₁ ≫ μ₁ ≫ sX) → MMP.Mori.IsSmoothScheme (g₁ ≫ μ₁ ≫ sX) →
      IsProper g₁ → MMP.Mori.IsBirationalMorphism g₁ →
      IsProper g₂ → MMP.Mori.IsBirationalMorphism g₂ → g₁ ≫ μ₁ = g₂ ≫ μ₂ →
      ∃ F : RDivisor V, IsWeilPullback g₁ G₁ F ∧ IsWeilPullback g₂ G₂ F)
    {K₁ : X₁.CartierDivisor} (hK₁ : IsRelativeCanonicalDivisor sX μ₁ K₁) {wK₁ : Divisor X₁}
    (hwK₁ : IsWeilDivisorOfCartier K₁ wK₁)
    {K₂ : X₂.CartierDivisor} (hK₂ : IsRelativeCanonicalDivisor sX μ₂ K₂) {wK₂ : Divisor X₂}
    (hwK₂ : IsWeilDivisorOfCartier K₂ wK₂) :
    multiplierIdealSections μ₁ (wK₁ - WeilRDivisor.roundDown wG₁) =
      multiplierIdealSections μ₂ (wK₂ - WeilRDivisor.roundDown wG₂) := by
  obtain ⟨V, g₁, g₂, ⟨-, hVvar, hVs, hg₁p, hg₁b⟩, hg₂p, hg₂b, hcomm⟩ :=
    exists_isResolution_comp_eq_comp sX μ₁ μ₂ hX₁ hX₂ hμ₂p hμ₁ hμ₂
  haveI := hVvar
  haveI := hg₂p
  haveI : IsProper μ₂ := isProper_of_isProjectiveMorphism μ₂ hμ₂p
  haveI : IsProper g₁ := isProper_of_isProjectiveMorphism g₁ hg₁p
  haveI : IsDominant g₁ := hg₁b.isDominant
  haveI : IsDominant g₂ := hg₂b.isDominant
  haveI : IsIntegral V := AlgebraicGeometry.IsVariety.toIsIntegral (f := g₁ ≫ μ₁ ≫ sX)
  haveI : LocallyOfFiniteType (g₁ ≫ μ₁ ≫ sX) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (g₁ ≫ μ₁ ≫ sX)
  haveI : Smooth (g₁ ≫ μ₁ ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hVs
  haveI : IsNormal V := isNormal_of_smooth_over_field (g₁ ≫ μ₁ ≫ sX)
  obtain ⟨F, hF₁, hF₂⟩ := hG V g₁ g₂ hVvar hVs inferInstance hg₁b inferInstance hg₂b hcomm
  obtain ⟨n, hn, -⟩ := id hK₁
  have hdV : topologicalKrullDim V = n :=
    (topologicalKrullDim_eq_of_isBirationalMorphism (μ₁ ≫ sX) (g₁ ≫ μ₁ ≫ sX) hg₁b).symm.trans hn
  haveI : MMP.Mori.IsVariety k ((g₁ ≫ μ₁) ≫ sX) := by rwa [Category.assoc]
  obtain ⟨KV, hKV⟩ := exists_isRelativeCanonicalDivisor hX (g := g₁ ≫ μ₁)
    (by rwa [Category.assoc]) (isBirationalMorphism_comp hg₁b hμ₁) hdV
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (g₁ ≫ μ₁ ≫ sX)
  haveI : IsNoetherian V := ⟨⟩
  obtain ⟨wKV, hwKV⟩ := exists_isWeilDivisorOfCartier KV
  haveI : MMP.Mori.IsVariety k (g₂ ≫ μ₂ ≫ sX) := by rwa [← reassoc_of% hcomm]
  have hV₂ : MMP.Mori.IsSmoothScheme (g₂ ≫ μ₂ ≫ sX) := by rwa [← reassoc_of% hcomm]
  have hKV₂ : IsRelativeCanonicalDivisor sX (g₂ ≫ μ₂) KV := hcomm ▸ hKV
  funext U
  rw [IsRelativeCanonicalDivisor.multiplierIdealSections_sub_roundDown_eq_comp hX hX₁ hμ₁ hVs hg₁b
      hwG₁ hsnc₁ hK₁ hwK₁ hKV hwKV hF₁ U,
    IsRelativeCanonicalDivisor.multiplierIdealSections_sub_roundDown_eq_comp hX hX₂ hμ₂ hV₂ hg₂b
      hwG₂ hsnc₂ hK₂ hwK₂ hKV₂ hwKV hF₂ U,
    multiplierIdealSections_congr hcomm]

end MMP.Intersection

end
