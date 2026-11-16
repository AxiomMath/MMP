module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Positivity.VeryAmpleAffineBase
public import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
import MMP.AlgebraicGeometry.MMP.Threefold.Basic
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Curves.RationalFunctionDegree
import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.Induction
import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme
import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistedInverseImageStructureSheaf
import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Hilbert polynomials of projective subschemes and degrees of effective divisors on curves

Two interfaces between the intersection theory of coherent sheaves and its classical forms.

Let `k` be a field and `i : Z ⟶ ℙᴺ_k` a closed immersion with `Z` nonempty of dimension `d`.
The Hilbert function `n ↦ χ(Z, 𝒪_Z(n))`, where `𝒪_Z(n)` is the `n`-th tensor power of the
restriction of the hyperplane sheaf `𝒪(1)`, agrees on all integers with a rational polynomial of
degree exactly `d` whose leading coefficient is strictly positive. No reducedness is assumed:
`Z` may be nonreduced and may have embedded points. Snapper's theorem (Stacks 0BEM) gives a
polynomial of degree at most `d`; its coefficient of `t^d` is `1 / d!` times the
self-intersection number `(𝒪(1)^d · Z)`, which is positive since `𝒪(1)` is ample (Stacks 0BEV).

Let `X` be a scheme over `k`, `D` an effective Cartier divisor on `X` and `i : C ⟶ X` an
integral curve, proper over `k`, whose image is not contained in `Supp D`. Then `i⁻¹(Supp D)` is
a finite set of points of `C`, and
`deg_C 𝒪_X(D) = ∑_{p ∈ i⁻¹(Supp D)} [κ(p) : k] · length_{𝒪_{C,p}} (𝒪_{C,p} / (f_p))`,
where `f_p ∈ 𝒪_{X,i(p)}` is a local equation of `D` at `i(p)`, read in `𝒪_{C,p}`. In
particular the degree is a natural number, and it is positive exactly when `i⁻¹(Supp D)` is
nonempty. Over an algebraically closed field every residue degree `[κ(p) : k]` is one, and at a
point `p` where `𝒪_{C,p}` is a discrete valuation ring (for instance a smooth point of `C`) the
local length is the order of vanishing `v_p(f_p)`. The proof pulls the canonical section `s_D`
back to a nonzero, hence regular, section of `i^*𝒪_X(D)`, whose zero scheme is finite over `k`
with points `i⁻¹(Supp D)` and local rings `𝒪_{C,p} / (f_p)`.

## Main results

* `MMP.Mori.exists_polynomial_subschemeHilbertFunction_projectiveSpace`: the Hilbert function of
  a nonempty closed subscheme of `ℙᴺ_k` of dimension `d` is a polynomial of degree `d` with
  positive leading coefficient.
* `MMP.Threefold.degreeOn_lineBundle_eq_finsum_residueDegree_mul_length`: the degree of an
  effective Cartier divisor on a curve as a sum of local contributions.

## Implementation notes

The Hilbert function is `subschemeHilbertFunction` of the structure morphism
`ℙᴺ_k ⟶ Spec k` and the hyperplane sheaf
`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec k)`. The dimension of `Z`
is its topological Krull dimension. The source argues by induction on `d` through hyperplane
sections, after a base change to an algebraically closed field; here positivity of the leading
coefficient is read off the positivity of the self-intersection number of `𝒪(1)` on `Z`.

The curve is a morphism `i : C ⟶ X` from an integral scheme of dimension at most one which is
proper over `k` through `X`; a closed integral curve `C ⊆ X` is the case of a closed immersion,
and `C ∩ Supp D` is then `i⁻¹(Supp D)`. A local equation of `D` at `x` is an element of `𝒪_{X,x}`
whose image in the stalk of the sheaf of total quotient rings is a local equation in the sense of
`MMP.Intersection.IsLocalEquationAt`; the formula holds for every choice of local equations. The
local lengths take values in `ℕ∞`, so the formula is stated in `ℕ∞` for a natural number `n`
with `deg_C 𝒪_X(D) = n`. The residue degree `[κ(p) : k]` is
`AlgebraicGeometry.Scheme.Hom.residueDegree` of `i ≫ sX` at `p`.

## References

* [R. Hartshorne, *Algebraic geometry*][Har77], I.7.5, III.Ex. 5.2
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.34, 1.35
* [Stacks Project, Tag 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ)
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

open Stacks.AmpleProjectiveImmersion

/-- The one-variable polynomial attached to a polynomial in a single variable has degree at most
its total degree. -/
private theorem natDegree_uniqueAlgEquiv_le {R σ : Type*} [CommSemiring R] [Unique σ]
    (P : MvPolynomial σ R) : (MvPolynomial.uniqueAlgEquiv R σ P).natDegree ≤ P.totalDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_
  rwa [Finsupp.support_single_ne_zero _ (by omega), Finset.sum_singleton, Finsupp.single_eq_same]

section HilbertPolynomial

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The Hilbert polynomial.** The Hilbert function `t ↦ χ(Z, L|_Z^{⊗ t})` of a closed
subscheme of dimension at most `d` of a proper `k`-scheme is a rational polynomial of degree at
most `d`. -/
private theorem exists_hilbertPolynomial (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℤ, p.eval (n : ℚ) = subschemeHilbertFunction k f i L n := by
  obtain ⟨P, hP0, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k (i ≫ f)
    (fun _ : Fin 1 => (Scheme.Modules.pullback i).obj L) (SheafOfModules.unit Z.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f))
  refine ⟨MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) P, ?_, fun n => ?_⟩
  · refine (natDegree_uniqueAlgEquiv_le P).trans ?_
    rcases hP0 with rfl | h
    · simp
    · exact_mod_cast h.trans ((topologicalKrullDim_subspace_le Z _).trans hd)
  · exact MvPolynomial.eval₂_const_uniqueAlgEquiv.trans (hP fun _ => n)

/-- **The self-intersection number is `d!` times the top coefficient of the Hilbert
polynomial.** If `p` has degree at most `d` and `p(n) = χ(Z, L|_Z^{⊗ n})` on `ℕ`, then
`(L^d · Z) = d! · [t^d] p`. -/
private theorem selfIntersectionNumber_eq_factorial_mul_coeff (d : ℕ)
    (hd : topologicalKrullDim Z = d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (p : Polynomial ℚ) (hp : p.natDegree ≤ d)
    (hval : ∀ t : ℕ, p.eval (t : ℚ) = subschemeHilbertFunction k f i L t) :
    (selfIntersectionNumber k f i d hd.le L : ℚ) = d.factorial * p.coeff d := by
  classical
  rw [← hilbertDegree_eq_factorial_mul_coeff k f i d hd L p hp hval]
  congr 1
  rw [selfIntersectionNumber, intersectionNumber_eq_sum_eulerCharacteristic,
    hilbertDegree]
  have key : ∀ T : Finset (Fin d),
      @eulerCharacteristic k _ Z (i ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun _ => (Scheme.Modules.pullback i).obj L) (fun j => if j ∈ T then 1 else 0))
          (isCoherent_twistedSheafUnitPullback k f i (fun _ => L)
            fun j => if j ∈ T then 1 else 0) =
        subschemeHilbertFunction k f i L T.card := by
    intro T
    have hs : (∑ j : Fin d, if j ∈ T then (1 : ℤ) else 0) = ∑ _j : Fin 1, (T.card : ℤ) := by
      simp [Finset.sum_boole]
    exact @eulerCharacteristic_eq_of_iso k _ Z (i ≫ f) _ _ _
      (isCoherent_twistedSheafUnitPullback k f i (fun _ => L) _)
      (isCoherent_twistedSheafUnitPullback k f i (fun _ : Fin 1 => L) _)
      (Twist.twistedSheafUnitIsoTensorPower _ _ (fun _ => Iso.refl _) _ ≪≫
        eqToIso (congrArg (Stacks.SheafOfModules.Invertible.tensorPower Z.presheaf
          Z.ringCatSheaf.2 ((Scheme.Modules.pullback i).obj L)) hs) ≪≫
        (Twist.twistedSheafUnitIsoTensorPower _ _ (fun _ => Iso.refl _) _).symm)
  simp_rw [key]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card
    (fun m => (-1 : ℤ) ^ (d - m) * subschemeHilbertFunction k f i L m)]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

end HilbertPolynomial

/-- **The Hilbert polynomial of a projective subscheme has degree its dimension and positive
leading coefficient.** For a field `k` and a nonempty closed subscheme `i : Z ⟶ ℙᴺ_k` of
dimension `d` (possibly nonreduced, possibly with embedded points), there is a rational
polynomial `P` of degree `d` with positive leading coefficient such that
`P(n) = χ(Z, 𝒪_Z(n))` for every integer `n`. -/
@[mmp "lem_mmp_foundation_projective_hyperplane_euler_polynomial"]
public theorem exists_polynomial_subschemeHilbertFunction_projectiveSpace
    (k : Type u) [Field k] (N : ℕ) {Z : Scheme.{u}}
    (i : Z ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion i] [Nonempty Z]
    (d : ℕ) (hd : topologicalKrullDim Z = d) :
    ∃ P : Polynomial ℚ, P.natDegree = d ∧ 0 < P.leadingCoeff ∧
      ∀ n : ℤ, P.eval (n : ℚ) =
        subschemeHilbertFunction k (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i
          (projectiveSpaceTwistingSheaf N (Spec (.of k))) n := by
  obtain ⟨p, hp, hval⟩ := exists_hilbertPolynomial k
    (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i d hd.le
    (projectiveSpaceTwistingSheaf N (Spec (.of k)))
  have hpos := selfIntersectionNumber_pos k
    (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) i d hd
    (projectiveSpaceTwistingSheaf N (Spec (.of k)))
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf N (Spec (.of k))))
  have hcoeff : 0 < p.coeff d := by
    have h := selfIntersectionNumber_eq_factorial_mul_coeff k _ i d hd _ p hp
      fun t => by exact_mod_cast hval t
    exact pos_of_mul_pos_right (h ▸ Int.cast_pos.2 hpos) (Nat.cast_nonneg _)
  have hdeg := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hp hcoeff.ne'
  exact ⟨p, hdeg, by rwa [Polynomial.leadingCoeff, hdeg], hval⟩

end MMP.Mori

namespace MMP.Threefold

open MMP.Intersection Opposite

/-- On an integral scheme of dimension at most one, proper over a field, a closed subset which is
not everything is a finite set of closed points. -/
private theorem finite_and_isClosed_singleton_of_isClosed {k : Type u} [Field k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1)
    {S : Set C} (hS : IsClosed S) (hne : ∃ c, c ∉ S) :
    S.Finite ∧ ∀ z ∈ S, IsClosed ({z} : Set C) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace C := (quasiCompact_iff_compactSpace g).1 inferInstance
  have : IsNoetherian C := ⟨⟩
  have hg : genericPoint C ∉ S := by
    intro h
    obtain ⟨c, hc⟩ := hne
    exact hc (hS.closure_subset_iff.2 (Set.singleton_subset_iff.2 h)
      ((genericPoint_spec C).specializes (Set.mem_univ c)).mem_closure)
  have := Stacks.CurveProjectiveCompletion.finite_compl_of_genericPoints_subset (Z := C)
    hS.isOpen_compl hdim (by
      intro x hx
      rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      exact hx ▸ hg)
  simpa using this

/-- Over an algebraically closed field, a closed point of a scheme locally of finite type has
residue degree one. -/
private theorem residueDegree_eq_one_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of k)) [LocallyOfFiniteType g] (p : C)
    (hp : IsClosed {p}) : g.residueDegree p = 1 := by
  have h := Stacks.Chow.residueDegree_eq_one_of_section g (pointOfClosedPoint g p hp)
    (pointOfClosedPoint_comp g p hp) (IsLocalRing.closedPoint _)
  convert h.1
  exact (pointOfClosedPoint_apply g p hp _).symm

/-- The zero scheme of a nonzero section of an invertible module on a proper integral curve is
finite over the base field. -/
private theorem isFinite_zeroScheme {k : Type u} [Field k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1)
    (L : C.Modules) [SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0) :
    IsFinite ((zeroScheme C L (s.eval (op ⊤))).subschemeι ≫ g) :=
  have : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme C L (s.eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection C L s).mpr
      (isRegularSection_of_eval_top_ne_zero L s hs)
  isFinite_divisorSubscheme k g hdim _

/-- The degree of an invertible module with a nonzero section on a proper integral curve is
the sum over the points of the zero scheme of the length of the local ring times the residue
degree. -/
private theorem invertibleCurveDegree_eq_finsum_zeroScheme {k : Type u} [Field k]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of k)) [IsProper g] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1) (L : C.Modules)
    [hL : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) :
    @invertibleCurveDegree k _ C g _ hdim L hL =
      ∑ᶠ z : (zeroScheme C L (s.eval (op ⊤))).subscheme,
        ((Module.length ((zeroScheme C L (s.eval (op ⊤))).subscheme.presheaf.stalk z)
          ((zeroScheme C L (s.eval (op ⊤))).subscheme.presheaf.stalk z)).toNat *
          ((zeroScheme C L (s.eval (op ⊤))).subschemeι ≫ g).residueDegree z : ℕ) := by
  have hreg := isRegularSection_of_eval_top_ne_zero L s hs
  have := isFinite_zeroScheme g hdim L s hs
  rw [invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme k g hdim L s hreg,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections,
    finrank_globalSections_eq_finsum_finrank_stalk]
  congr 2
  funext z
  rw [finrank_stalk_eq_length_mul_finrank_residueField,
    Stacks.Chow.residueDegree_eq_finrank_residueField]

/-- If `R → A` is surjective with kernel `J`, the length of `A` over itself is the length of
`R ⧸ J` over `R`. -/
private theorem length_self_eq_length_quotient {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (hs : Function.Surjective (algebraMap R A)) {J : Ideal R}
    (hJ : RingHom.ker (algebraMap R A) = J) :
    Module.length A A = Module.length R (R ⧸ J) := by
  rw [← Module.length_eq_of_surjective (S := R) (M := A) hs]
  have h : J = LinearMap.ker (Algebra.linearMap R A) := by
    rw [← hJ]
    ext x
    simp [RingHom.mem_ker]
  exact ((Submodule.quotEquivOfEq _ _ h).trans
    (LinearMap.quotKerEquivOfSurjective (Algebra.linearMap R A) hs)).length_eq.symm

/-- The length of the local ring of a closed subscheme at a point is the length of the quotient
of the ambient local ring by the stalk of the ideal sheaf. -/
private theorem length_stalk_subscheme {C : Scheme.{u}} (I : C.IdealSheafData) (z : I.subscheme) :
    Module.length (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z) =
      Module.length (C.presheaf.stalk (I.subschemeι z))
        (C.presheaf.stalk (I.subschemeι z) ⧸ IdealSheafData.stalk I (I.subschemeι z)) :=
  letI : Algebra _ _ := (I.subschemeι.stalkMap z).hom.toAlgebra
  length_self_eq_length_quotient (I.subschemeι.stalkMap_surjective z)
    (Stacks.Chow.ker_stalkMap_subschemeι_eq_stalk I z)

/-- A local ring of a scheme finite over a field has finite length. -/
private theorem length_stalk_ne_top {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsFinite g] (y : Y) :
    Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) ≠ ⊤ := by
  letI : Algebra k (Y.presheaf.stalk y) :=
    ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
  have h1 : Module.Finite k (Y.presheaf.stalk y) := finite_stalk_of_isFinite_over_field k g y
  have := IsArtinianRing.of_finite k (Y.presheaf.stalk y)
  exact Module.length_ne_top_iff.2 ((isArtinianRing_iff_isFiniteLength _).1 this)

/-- Composing with a closed immersion does not change residue degrees. -/
private theorem residueDegree_subschemeι_comp {C S : Scheme.{u}} (I : C.IdealSheafData)
    (g : C ⟶ S) (z : I.subscheme) :
    (I.subschemeι ≫ g).residueDegree z = g.residueDegree (I.subschemeι z) := by
  rw [Stacks.Chow.residueDegree_comp,
    Stacks.Chow.residueDegree_eq_one_of_isPreimmersion I.subschemeι, mul_one]

/-- The stalk at `x` of the ideal of the zero scheme of the canonical section `s_D` of an
effective Cartier divisor is generated by any local equation of `D` at `x`. -/
private theorem stalk_zeroScheme_canonicalSection {X : Scheme.{u}} (D : X.CartierDivisor)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (MMP.CartierDivisor.sheaf D)]
    (hD : IsEffective D) (x : X) (g : X.presheaf.stalk x)
    (hg : IsLocalEquationAt D x (stalkToTotalQuotient x g)) :
    IdealSheafData.stalk (Stacks.Divisors.zeroScheme X (MMP.CartierDivisor.sheaf D)
        (MMP.CartierDivisor.canonicalSection D hD)) x =
      Ideal.span {g} := by
  obtain ⟨U, hxU, s, hs, hsD⟩ := hD x
  obtain ⟨W, hWa, hxW, hWU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxU
  let i : W ⟶ U := homOfLE hWU
  let W' : X.affineOpens := ⟨W, hWa⟩
  have hg' := isLocalEquationOn_resUnit i hsD
  let r : Γ(X, W'.1) := X.presheaf.map i.op s
  have hr : ((resUnit i hs.unit : (X.totalQuotientSheaf.obj.obj (op W'.1))ˣ) : _) =
      toTotalQuotient W'.1 r := (toTotalQuotient_map i s).symm
  have hbij := MMP.CartierDivisor.isTrivializingGenerator_invSection hg' W'.1 le_rfl
  have hid : (MMP.CartierDivisor.sheaf D).presheaf.map (homOfLE (le_refl W'.1)).op
      (MMP.CartierDivisor.invSection hg') =
      MMP.CartierDivisor.invSection hg' := by
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    erw [MMP.CartierDivisorSheaf.sectionVal_map]
    change X.totalQuotientSheaf.obj.map (𝟙 _) _ = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [hid] at hbij
  let e := (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, W'.1) _
    (MMP.CartierDivisor.invSection hg')) hbij).symm
  have he : e ((MMP.CartierDivisor.sheaf D).presheaf.map (homOfLE le_top).op
      (MMP.CartierDivisor.canonicalSection D hD)) = r := by
    rw [LinearEquiv.symm_apply_eq]
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    change _ = MMP.CartierDivisorSheaf.sectionVal (r • MMP.CartierDivisor.invSection hg')
    erw [MMP.CartierDivisor.sectionVal_smul,
      MMP.CartierDivisor.sectionVal_canonicalSection_res, ← hr]
    exact (Units.mul_inv _).symm
  rw [Stacks.Divisors.stalk_zeroScheme_eq_span_germ _ _ W' e r he x hxW]
  obtain ⟨a, ha, hfa⟩ := IsLocalEquationOn.exists_isUnit_eq_mul_germ hg' hxW hg
  rw [hr, germ_toTotalQuotient, ← map_mul] at hfa
  rw [stalkToTotalQuotient_injective x hfa, Ideal.span_singleton_mul_left_unit ha]

/-- The pullback along `i` of the canonical section `s_D` of `𝒪_X(D)`, as a global section of
`i^*𝒪_X(D)`. -/
private noncomputable abbrev pullbackCanonicalSection {X C : Scheme.{u}} (i : C ⟶ X)
    (D : X.CartierDivisor) (hD : IsEffective D) :=
  (Stacks.NonvanishingSpelling.sectionsEquiv C
      ((Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf D))).symm
    (Stacks.NonvanishingPullback.pullbackGlobalSection i (MMP.CartierDivisor.sheaf D)
        (MMP.CartierDivisor.canonicalSection D hD))

/-- The degree of `𝒪_X(D)` on a curve not contained in `Supp D` is positive exactly when the
curve meets `Supp D`. -/
private theorem degreeOn_lineBundle_pos_iff (k : Type u) [Field k] {X C : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) [IsProper (i ≫ sX)] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1) (D : X.CartierDivisor) (hD : IsEffective D)
    (hne : ∃ c : C, i c ∉ cartierSupport D) :
    0 < MMP.Mori.degreeOn k sX i hdim (MMP.CartierDivisor.sheaf D) ↔
      (i ⁻¹' cartierSupport D).Nonempty := by
  have hsupp := MMP.CartierDivisor.mem_nonvanishingLocus_canonicalSection_iff D hD
  obtain ⟨c, hc⟩ := hne
  rw [MMP.Mori.degreeOn_eq_invertibleCurveDegree]
  refine ⟨fun h => ?_, fun ⟨p, hp⟩ => MMP.Threefold.Mori.invertibleCurveDegree_pullback_pos sX i
    hdim _ _ ⟨c, (hsupp _).2 hc⟩ ⟨p, fun h' => (hsupp _).1 h' hp⟩⟩
  by_contra hem
  rw [MMP.Threefold.Mori.invertibleCurveDegree_pullback_eq_zero sX i hdim _
      (MMP.CartierDivisor.canonicalSection D hD)
    fun c' => (hsupp _).2 fun h' => hem ⟨c', h'⟩] at h
  exact lt_irrefl _ h

/-- The zero scheme of the pulled-back canonical section has underlying set `i⁻¹(Supp D)`. -/
private theorem range_subschemeι_zeroScheme_pullbackCanonicalSection {X C : Scheme.{u}}
    (i : C ⟶ X) [IsIntegral C] (D : X.CartierDivisor) (hD : IsEffective D)
    [SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf D))]
    (hs : (pullbackCanonicalSection i D hD).eval (op ⊤) ≠ 0) :
    Set.range (zeroScheme C _ ((pullbackCanonicalSection i D hD).eval (op ⊤))).subschemeι =
      i ⁻¹' cartierSupport D := by
  have h := nonvanishingLocus_eq_compl_supportSet_zeroScheme _ _ hs
  rw [MMP.Threefold.Mori.nonvanishingLocus_pullbackSection] at h
  ext p
  have h2 := congrArg (p ∈ ·) h
  simp only [Set.mem_preimage, Set.mem_compl_iff, eq_iff_iff,
    MMP.CartierDivisor.mem_nonvanishingLocus_canonicalSection_iff,
    Scheme.IdealSheafData.mem_supportSet_iff_mem_support] at h2
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp only [Set.mem_preimage, SetLike.mem_coe]
  tauto

/-- The stalk at `p` of the ideal of the zero scheme of the pulled-back canonical section is
generated by the image of a local equation of `D` at `i p`. -/
private theorem stalk_zeroScheme_pullbackCanonicalSection {X C : Scheme.{u}} (i : C ⟶ X)
    (D : X.CartierDivisor) (hD : IsEffective D)
    [SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf D))]
    (p : C) (g : X.presheaf.stalk (i p))
    (hg : IsLocalEquationAt D (i p) (stalkToTotalQuotient (i p) g)) :
    IdealSheafData.stalk (zeroScheme C _ ((pullbackCanonicalSection i D hD).eval (op ⊤))) p =
      Ideal.span {(i.stalkMap p).hom g} := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (MMP.CartierDivisor.sheaf D) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf _ _).1
      (MMP.CartierDivisor.isInvertibleModule_sheaf D)
  have ht : (pullbackCanonicalSection i D hD).eval (op ⊤) =
      pullbackGlobalSections i (MMP.CartierDivisor.sheaf D)
        (MMP.CartierDivisor.canonicalSection D hD) := by
    open Stacks.AlgebraicGeometry.GeneratingSectionsRestrict in
    rw [pullbackGlobalSections_eq_pullbackGlobalSection]
    exact (Stacks.NonvanishingSpelling.sectionsEquiv C _).apply_symm_apply _
  change IdealSheafData.stalk (Stacks.Divisors.zeroScheme C _ _) p = _
  rw [ht, Stacks.Divisors.zeroScheme_pullback, IdealSheafData.stalk_comap,
    stalk_zeroScheme_canonicalSection D hD (i p) g hg, Ideal.map_span, Set.image_singleton]

/-- The degree of `𝒪_X(D)` on `C` as a sum over `i⁻¹(Supp D)` of residue degree times the length
of `𝒪_{C,p} / (f_p)`. -/
private theorem degreeOn_lineBundle_eq_finsum (k : Type u) [Field k] {X C : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (i : C ⟶ X) [IsProper (i ≫ sX)] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1) (D : X.CartierDivisor) (hD : IsEffective D)
    (hne : ∃ c : C, i c ∉ cartierSupport D) (hfin : (i ⁻¹' cartierSupport D).Finite)
    (f : (p : C) → X.presheaf.stalk (i p))
    (hf : ∀ p ∈ i ⁻¹' cartierSupport D,
      IsLocalEquationAt D (i p) (stalkToTotalQuotient (i p) (f p))) :
    ∃ n : ℕ, MMP.Mori.degreeOn k sX i hdim (MMP.CartierDivisor.sheaf D) = n ∧
      (n : ℕ∞) = ∑ᶠ p ∈ i ⁻¹' cartierSupport D, ((i ≫ sX).residueDegree p : ℕ∞) *
        Module.length (C.presheaf.stalk p)
          (C.presheaf.stalk p ⧸ Ideal.span {(i.stalkMap p).hom (f p)}) := by
  have : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf D)) :=
    MMP.Mori.isInvertible_pullback_obj i _
  obtain ⟨c, hc⟩ := hne
  have hs : (pullbackCanonicalSection i D hD).eval (op ⊤) ≠ 0 :=
    MMP.Threefold.Mori.eval_pullbackSection_ne_zero i _ _
      ⟨c, (MMP.CartierDivisor.mem_nonvanishingLocus_canonicalSection_iff D hD _).2 hc⟩
  have hrange := range_subschemeι_zeroScheme_pullbackCanonicalSection i D hD hs
  set Z := zeroScheme C _ ((pullbackCanonicalSection i D hD).eval (op ⊤))
  have := isFinite_zeroScheme (i ≫ sX) hdim _ _ hs
  have hinj : Function.Injective Z.subschemeι := Z.subschemeι.isClosedEmbedding.injective
  have : Fintype Z.subscheme := @Fintype.ofFinite _ ((Set.finite_range_iff hinj).1 (hrange ▸ hfin))
  refine ⟨_, invertibleCurveDegree_eq_finsum_zeroScheme (i ≫ sX) hdim _ _ hs, ?_⟩
  rw [← hrange, finsum_mem_range hinj, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Nat.cast_mul, residueDegree_subschemeι_comp,
    ENat.coe_toNat (length_stalk_ne_top (Z.subschemeι ≫ i ≫ sX) z), length_stalk_subscheme,
    stalk_zeroScheme_pullbackCanonicalSection i D hD _ _ (hf _ (hrange ▸ ⟨z, rfl⟩)), mul_comm]

/-- **The degree of an effective Cartier divisor on a curve.** Let `D` be an effective Cartier
divisor on a `k`-scheme `X` and `i : C ⟶ X` an integral curve proper over `k` whose image is not
contained in `Supp D`, and let `f_p ∈ 𝒪_{X,i(p)}` be a local equation of `D` at `i(p)` for every
`p ∈ i⁻¹(Supp D)`. Then `i⁻¹(Supp D)` is finite and
`deg_C 𝒪_X(D) = ∑_{p ∈ i⁻¹(Supp D)} [κ(p) : k] · length_{𝒪_{C,p}} (𝒪_{C,p} / (f_p))`
is a natural number; it is positive if and only if `i⁻¹(Supp D)` is nonempty; if `k` is
algebraically closed all residue degrees `[κ(p) : k]` are `1`; and where `𝒪_{C,p}` is a discrete
valuation ring the local length is the valuation of `f_p`. -/
@[mmp "lem_mmp_threefold_effective_cartier_curve_degree"]
public theorem degreeOn_lineBundle_eq_finsum_residueDegree_mul_length
    (k : Type u) [Field k] {X C : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (i : C ⟶ X)
    [IsProper (i ≫ sX)] [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1)
    (D : X.CartierDivisor) (hD : IsEffective D) (hne : ∃ c : C, i c ∉ cartierSupport D)
    (f : (p : C) → X.presheaf.stalk (i p))
    (hf : ∀ p ∈ i ⁻¹' cartierSupport D,
      IsLocalEquationAt D (i p) (stalkToTotalQuotient (i p) (f p))) :
    (i ⁻¹' cartierSupport D).Finite ∧
      (∃ n : ℕ, MMP.Mori.degreeOn k sX i hdim (MMP.CartierDivisor.sheaf D) = n ∧
        (n : ℕ∞) = ∑ᶠ p ∈ i ⁻¹' cartierSupport D, ((i ≫ sX).residueDegree p : ℕ∞) *
          Module.length (C.presheaf.stalk p)
            (C.presheaf.stalk p ⧸ Ideal.span {(i.stalkMap p).hom (f p)})) ∧
      (0 < MMP.Mori.degreeOn k sX i hdim (MMP.CartierDivisor.sheaf D) ↔
        (i ⁻¹' cartierSupport D).Nonempty) ∧
      (IsAlgClosed k → ∀ p ∈ i ⁻¹' cartierSupport D, (i ≫ sX).residueDegree p = 1) ∧
      ∀ p ∈ i ⁻¹' cartierSupport D, ∀ _ : IsDiscreteValuationRing (C.presheaf.stalk p),
        Module.length (C.presheaf.stalk p)
            (C.presheaf.stalk p ⧸ Ideal.span {(i.stalkMap p).hom (f p)}) =
          IsDiscreteValuationRing.addVal (C.presheaf.stalk p) ((i.stalkMap p).hom (f p)) := by
  obtain ⟨hfin, hcl⟩ := finite_and_isClosed_singleton_of_isClosed (i ≫ sX) hdim
    ((MMP.Intersection.isClosed_cartierSupport D).preimage i.continuous) hne
  have : LocallyOfFiniteType (i ≫ sX) := IsProper.toLocallyOfFiniteType
  exact ⟨hfin, degreeOn_lineBundle_eq_finsum k sX i hdim D hD hne hfin f hf,
    degreeOn_lineBundle_pos_iff k sX i hdim D hD hne,
    fun _ p hp => residueDegree_eq_one_of_isClosed _ p (hcl p hp),
    fun p _ _ => Ring.ord_eq_addVal _⟩

end MMP.Threefold
