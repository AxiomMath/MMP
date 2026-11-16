module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Basic
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple
import MMP.AlgebraicGeometry.Intersection.EulerPolynomialGenericRank
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Irreducible
public import MMP.AlgebraicGeometry.ProjectiveSpace.HomogeneousCoordinateRingSections
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ClosedImmersionTransport
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import StacksFrontier.AlgebraicGeometry.Constructions.ProjPointOfRingHom
import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
public import MMP.AlgebraicGeometry.Dimension.PureDimensional

/-!
# Generic translates, Hilbert polynomials and Bloch–Gieseker covers

*Euler polynomials.* For a proper dominant morphism `h : X' ⟶ X` of integral schemes proper over
a field `k`, both of dimension `d`, and invertible `L₁, …, L_r` on `X`, the degree-`d` part of
the Euler polynomial of the `h^*Lᵢ` on `X'` is `[k(X') : k(X)]` times that of the `Lᵢ` on `X`:
`h_* 𝒪_{X'}` is coherent of generic rank `[k(X') : k(X)]`, and by Leray and the projection
formula only `h_*` contributes in top degree.

*Kleiman's transversality theorem.* If a connected algebraic group `G` over an algebraically
closed field of characteristic zero acts transitively on a variety `P`, then for general `σ ∈ G`
the fibre product `X ×_{f, P, σ • h} Y` is empty or pure of dimension `dim X + dim Y - dim P`,
and smooth when `X` and `Y` are. The incidence scheme `(X × Y) ×_{P × P} (G × P)` is smooth over
`X × Y`, since `(s, q) ↦ (s q, q)` is smooth by homogeneity; generic flatness and generic
smoothness of its projection to `G` conclude.

*The Hilbert polynomial* of a `d`-dimensional subvariety of `ℙⁿ_K` has degree `d` and leading
coefficient `deg(Y) / d!` with `deg(Y) > 0`.

*Bloch–Gieseker covers.* On a smooth quasi-projective variety `X`, an invertible `L` has an
`m`-th root on a finite surjective cover `g : Y ⟶ X` by a smooth variety, along which a family of
effective Cartier divisors with snc sum of coefficients `1` keeps this property. For
`L = h^* 𝒪(1)`, `Y` is a component of `X ×_{ℙᴺ} ℙᴺ` along a general linear translate of the power
map `[xᵢ] ↦ [xᵢᵐ]`; in general `L ≅ L₁ ⊗ L₂⁻¹` with `Lᵢ` very ample, and one takes two steps.

## Main results

* `MMP.Mori.homogeneousComponent_eulerPolynomial_pullback_eq_finrank_smul`
* `MMP.Foundations.exists_dense_isPureDimensional_pullback_smul`: Kleiman's theorem.
* `MMP.Foundations.exists_dense_smooth_isPureDimensional_pullback_smul`: Kleiman–Bertini.
* `MMP.Foundation.exists_hilbertPolynomial_subvariety`
* `MMP.Mori.exists_isFinite_surjective_pullback_twistOne_iso_tensorPow_of_isSNC`
* `MMP.Mori.exists_isFinite_surjective_pullback_iso_tensorPow_of_isSNC`

## Implementation notes

The Euler polynomials are given as any rational polynomials interpolating the Euler
characteristic functions on `ℤ^r`. For Kleiman's theorem `G` is a group object in
`Over (Spec k)` acting on `P` by a module object `ModObj G P`; transitivity is that of the action
of the `k`-points `𝟙_ _ ⟶ G` on the `k`-points of `P`, and `σ • h` is the action of
`toUnit Y ≫ σ` on `h`. Purity `MMP.IsPureDimensional` holds for the empty scheme.
A subvariety of `ℙⁿ_K` is an integral closed subscheme of the polynomial model
`Proj K[T₀, …, Tₙ]`; its degree is the Stacks degree `AlgebraicGeometry.degreeWithRespectTo`
with respect to `𝒪(1)`, and `S(Y)_t` is the degree-`t` part of the quotient by the vanishing ideal
of its support. An effective Cartier divisor is an ideal sheaf `F` with
`Stacks.Divisors.IsEffectiveCartierDivisor F`, pulled back as `F.comap g`, and the Weil divisor
`∑ⱼ F_j` is pinned by its coefficients `∑ⱼ length(𝒪_{X,P} / (F_j)_P)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.36, 2.67
* [S. Kleiman, *The transversality of a general translate*][Kle74]
* [W. Fulton, *Intersection Theory*][fulton1998], §1.6
-/

namespace MMP.Mori

section EulerTopProjection

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Polynomials over `ℚ` agreeing at every integer point are equal. -/
private theorem eq_of_forall_eval_intCast {r : ℕ} {A B : MvPolynomial (Fin r) ℚ}
    (h : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) A =
      MvPolynomial.eval (fun j => (n j : ℚ)) B) : A = B := by
  refine MvPolynomial.funext_set (s := fun _ => Set.range ((↑) : ℤ → ℚ))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
  choose n hn using fun j => hx j (Set.mem_univ j)
  have : x = fun j => (n j : ℚ) := funext fun j => (hn j).symm
  subst this
  exact h n

/-- The transported stalk map at a point is the stalk map precomposed with the comparison of
stalks at equal points. -/
private theorem hom_eq_ndrec_stalkMap {X Y : Scheme.{u}} (h : X ⟶ Y) (x : X) {y : Y}
    (e : h x = y) :
    (e ▸ h.stalkMap x).hom =
      ((Y.presheaf.stalkCongr (Inseparable.of_eq e.symm)).hom ≫ h.stalkMap x).hom := by
  subst e
  simp

/-- **The rank of `h_*𝒪_{X'}` at the generic point is the degree of `h`**, for a proper dominant
morphism of integral schemes whose generic fibre is the generic point: the stalk of the direct
image there is the stalk of `𝒪_{X'}` at its generic point, by the product decomposition along the
fibre ([Stacks, Tag 02R6]). -/
private theorem fiberRank_pushforward_unit_genericPoint_eq_degreeOver {X X' : Scheme.{u}}
    [IsIntegral X] [IsIntegral X'] [IsLocallyNoetherian X'] (h : X' ⟶ X) [IsProper h]
    [IsDominant h]
    (hfib : ∀ z : X', h z = genericPoint X → z = genericPoint X') :
    Scheme.Modules.fiberRank
        ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit X'.ringCatSheaf))
        (genericPoint X) = degreeOver h := by
  classical
  have hgen : h (genericPoint X') = genericPoint X := map_genericPoint_of_isDominant h
  rw [← hgen]
  have hsupp : _root_.SheafOfModules.supp (Stacks.Ample.unitModule X') = Set.univ :=
    Set.eq_univ_of_forall fun x =>
      (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mpr
        (Stacks.Ample.unitStalkEquiv X' x).symm.injective.nontrivial
  have hηmem : genericPoint X' ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule X') :=
    hsupp ▸ Set.mem_univ _
  let : Unique ↥{z : X' | h z = h (genericPoint X') ∧
      z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule X')} :=
    { default := ⟨genericPoint X', rfl, hηmem⟩
      uniq := fun z => Subtype.ext (hfib z.1 (z.2.1.trans hgen)) }
  let : Fintype ↥{z : X' | h z = h (genericPoint X') ∧
      z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule X')} :=
    Fintype.ofSubsingleton ⟨genericPoint X', rfl, hηmem⟩
  have hirr : IrreducibleSpace ↥(_root_.SheafOfModules.supp (Stacks.Ample.unitModule X')) :=
    ((Homeomorph.setCongr hsupp).trans (Homeomorph.Set.univ X')).symm.surjective.irreducibleSpace
      ((Homeomorph.setCongr hsupp).trans (Homeomorph.Set.univ X')).symm.continuous
  have hcomp : (Set.univ : Set ↥(_root_.SheafOfModules.supp (Stacks.Ample.unitModule X'))) ∈
      irreducibleComponents ↥(_root_.SheafOfModules.supp (Stacks.Ample.unitModule X')) := by
    rw [irreducibleComponents_eq_singleton]
    rfl
  have hgenS : ∀ z : ↥{z : X' | h z = h (genericPoint X') ∧
        z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule X')},
      ∃ W : irreducibleComponents
        (_root_.SheafOfModules.supp (Stacks.Ample.unitModule X') : Set X'),
      IsGenericPoint z.1 (Subtype.val '' W.1 : Set X') := by
    intro z
    refine ⟨⟨Set.univ, hcomp⟩, ?_⟩
    have hz : z.1 = genericPoint X' := hfib z.1 (z.2.1.trans hgen)
    have himg : (Subtype.val ''
        (Set.univ : Set ↥(_root_.SheafOfModules.supp (Stacks.Ample.unitModule X'))) : Set X') =
        Set.univ := by
      rw [Subtype.coe_image_univ]
      exact hsupp
    rw [hz, himg]
    exact Set.top_eq_univ (α := X') ▸ genericPoint_spec X'
  have hfield : IsField (X.presheaf.stalk (h (genericPoint X'))) := by
    rw [hgen]
    exact isField_stalk_genericPoint X
  rw [fiberRank_eq_finrank_stalk_of_isField _ _ hfield]
  let : ∀ z : ↥{z : X' | h z = h (genericPoint X') ∧
        z ∈ _root_.SheafOfModules.supp (Stacks.Ample.unitModule X')},
      Module (X.presheaf.stalk (h (genericPoint X')))
        ((Stacks.Ample.unitModule X').presheaf.stalk z.1) :=
    Stacks.Chow.supportFibreStalkModule h (Stacks.Ample.unitModule X') (h (genericPoint X'))
  let : Module (X.presheaf.stalk (h (genericPoint X')))
      (X'.presheaf.stalk (genericPoint X')) :=
    Module.compHom _ (h.stalkMap (genericPoint X')).hom
  let e := Stacks.Chow.pushforwardStalkLinearEquivPi h (Stacks.Ample.unitModule X')
    (_root_.SheafOfModules.isClosed_supp _) (h (genericPoint X'))
    (Stacks.Chow.locallyFinite_irreducibleComponents_supp _) hgenS
  let u := Stacks.Ample.unitStalkEquiv X' (genericPoint X')
  let e' := e.trans (LinearEquiv.piUnique (X.presheaf.stalk (h (genericPoint X'))) _)
  let : Module (X.presheaf.stalk (h (genericPoint X')))
      ((Stacks.Ample.unitModule X').presheaf.stalk (genericPoint X')) :=
    Module.compHom _ (h.stalkMap (genericPoint X')).hom
  have h3 : Module.finrank (X.presheaf.stalk (h (genericPoint X')))
      ((Stacks.Ample.unitModule X').presheaf.stalk (genericPoint X')) =
      Module.finrank (X.presheaf.stalk (h (genericPoint X')))
        (X'.presheaf.stalk (genericPoint X')) :=
    LinearEquiv.finrank_eq
      { toFun := u
        map_add' := u.map_add
        map_smul' := fun a m => u.map_smul ((h.stalkMap (genericPoint X')).hom a) m
        invFun := u.symm
        left_inv := u.left_inv
        right_inv := u.right_inv }
  exact (LinearEquiv.finrank_eq e').trans
    (h3.trans (finrank_stalk_genericPoint_eq_degreeOver h hgen))

/-- **A sheaf missing the generic point contributes nothing in top degree**: a polynomial of
total degree at most the dimension of the support of a finite-type sheaf `G` on an integral
`d`-dimensional scheme has vanishing degree-`d` part as soon as the generic point lies outside
that support. -/
private theorem homogeneousComponent_eq_zero_of_genericPoint_notMem_supp {X : Scheme.{u}}
    [IsIntegral X] (d : ℕ) (hd : topologicalKrullDim X = d) (G : X.Modules) [G.IsFiniteType]
    (hη : genericPoint X ∉ _root_.SheafOfModules.supp G) {r : ℕ} (R : MvPolynomial (Fin r) ℚ)
    (hdeg : R = 0 ∨ (R.totalDegree : WithBot ℕ∞) ≤
      topologicalKrullDim (_root_.SheafOfModules.supp G)) :
    MvPolynomial.homogeneousComponent d R = 0 := by
  have hlt := topologicalKrullDim_lt_of_isClosed_ne_univ
    (_root_.SheafOfModules.isClosed_supp G) (fun he => hη (he ▸ Set.mem_univ _))
    (by rw [hd]; exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))
  rw [hd] at hlt
  rcases hdeg with h0 | hle
  · rw [h0, map_zero]
  · exact MvPolynomial.homogeneousComponent_eq_zero _ _ (by exact_mod_cast hle.trans_lt hlt)

/-- The direct image `h_* 𝒪_{X'}` is coherent, of generic rank `[k(X') : k(X)]`. -/
private theorem pushforward_unit_isCoherent_and_fiberRank_eq
    (k : Type u) [Field k] {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ Spec (.of k)) [IsProper f] (h : X' ⟶ X) [IsProper h] [IsDominant h]
    (d : ℕ) (hd : topologicalKrullDim X = d) (hd' : topologicalKrullDim X' = d) :
    ∃ hF : SheafOfModules.IsCoherent
        ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit X'.ringCatSheaf)),
      (Scheme.Modules.fiberRank
          ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit X'.ringCatSheaf))
          (genericPoint X) : ℚ) =
        (letI := functionFieldMapAlgebra h;
          Module.finrank X.functionField X'.functionField : ℚ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (h ≫ f)
  refine ⟨ProperCoherenceWitness.isCoherent_pushforward h _, ?_⟩
  rw [fiberRank_pushforward_unit_genericPoint_eq_degreeOver h fun z hz =>
    eq_genericPoint_of_map_eq_genericPoint_of_dim_eq h h.isClosedMap hd' hd hz]
  letI := functionFieldMapAlgebra h
  rw [degreeOver_eq_finrank h ?_]
  change functionFieldMap h = dominantFunctionFieldMap h
  exact (hom_eq_ndrec_stalkMap h (genericPoint X') _).symm

/-- The degree-`d` parts of the Euler polynomials of `𝒪_{X'}` twisted by the `h^* L_i` and of
`h_* 𝒪_{X'}` twisted by the `L_i` agree. -/
private theorem homogeneousComponent_eulerPolynomial_eq_pushforward
    (k : Type u) [Field k] {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ Spec (.of k)) [IsProper f] (h : X' ⟶ X) [IsProper h] [IsDominant h]
    (d : ℕ) (hd : topologicalKrullDim X = d) (hd' : topologicalKrullDim X' = d)
    {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (hF : SheafOfModules.IsCoherent
        ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit X'.ringCatSheaf)))
    (P R : MvPolynomial (Fin r) ℚ)
    (hP : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      (@eulerCharacteristic k _ X' (h ≫ f) _
        (twistedSheaf (SheafOfModules.unit X'.ringCatSheaf)
          (fun i => (Scheme.Modules.pullback h).obj (L i)) n)
        (@twistedSheaf_isCoherent X' r _ _ _
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (h ≫ f)) n) : ℚ))
    (hR : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) R =
      (@eulerCharacteristic k _ X f _
        (twistedSheaf ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit X'.ringCatSheaf))
          L n)
        (@twistedSheaf_isCoherent X r _ L _ hF n) : ℚ)) :
    MvPolynomial.homogeneousComponent d P = MvPolynomial.homogeneousComponent d R := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hO : (SheafOfModules.unit X'.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (h ≫ f)
  let E' : HasDerivedCategory.{u} X'.Modules := Scheme.Modules.hasDerivedCategory X'
  let E : HasDerivedCategory.{u} X.Modules := Scheme.Modules.hasDerivedCategory X
  let D' : HasDerivedCategory.{u + 1} X'.Modules := HasDerivedCategory.standard _
  let D : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
  let G : ℕ → X.Modules := fun q =>
    ((Scheme.Modules.pushforward h).rightDerived q).obj (SheafOfModules.unit X'.ringCatSheaf)
  -- `R^q h_*` in the `ℤ`-indexed spelling of the coherence and vanishing results
  let eG := fun (q : ℕ) (M : X'.Modules) =>
    (@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _ (Scheme.Modules.pushforward h) _
      D' D q).app M
  have hG : ∀ q, (G q).IsCoherent := fun q => by
    have := isWeakSerreClass_coherentModules X
    exact ObjectProperty.prop_of_iso (P := fun M : X.Modules => M.IsCoherent) (eG q _).symm
      (ProperCoherenceWitness.higherDirectImageIsCoherent X' X h inferInstance inferInstance _
        hO q)
  choose R' hR'deg hR'eval using fun q =>
    exists_eulerPolynomial_twistedSheaf_of_isProper k f L (G q) (hG q)
  obtain ⟨B, hB⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedNat_pushforward h
  have hGz : ∀ q, B ≤ q → Limits.IsZero (G q) := fun q hq =>
    hB _ (isQuasicoherent_of_isCoherent _) q hq
  -- the projection formula, for the `ℕ`-indexed higher direct images
  let eProj := fun (q : ℕ) (n : Fin r → ℤ) =>
    (@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _ (Scheme.Modules.pushforward h) _
        E' E q).app (twistedSheaf (SheafOfModules.unit X'.ringCatSheaf)
          (fun i => (Scheme.Modules.pullback h).obj (L i)) n) ≪≫
      Stacks.ProjectionFormula.higherDirectImageTwistedSheafIso h L
        (SheafOfModules.unit X'.ringCatSheaf) n q ≪≫
        twistedSheafIsoOfIso L
          ((@Stacks.DerivedIndexing.rightDerivedIso _ _ _ _ _ _ _ (Scheme.Modules.pushforward h) _
            E' E q).app (SheafOfModules.unit X'.ringCatSheaf)).symm n
  -- Leray and the projection formula
  have hLeray : ∀ n : Fin r → ℤ,
      (@eulerCharacteristic k _ X' (h ≫ f) _
        (twistedSheaf (SheafOfModules.unit X'.ringCatSheaf)
          (fun i => (Scheme.Modules.pullback h).obj (L i)) n)
        (@twistedSheaf_isCoherent X' r _ _ _ hO n) : ℚ) =
      ∑ q ∈ Finset.range (B + 1), (-1 : ℚ) ^ q *
        (@eulerCharacteristic k _ X f _ (twistedSheaf (G q) L n)
          (@twistedSheaf_isCoherent X r _ L _ (hG q) n) : ℚ) := by
    intro n
    have := @twistedSheaf_isCoherent X' r _ (fun i => (Scheme.Modules.pullback h).obj (L i)) _ hO n
    rw [eulerCharacteristic_eq_finsum_higherDirectImage k h f]
    have hterm : ∀ q : ℕ, (-1 : ℤ) ^ q * @eulerCharacteristic k _ X f _
          (((Scheme.Modules.pushforward h).rightDerivedPlus (q : ℤ)).obj
            (twistedSheaf (SheafOfModules.unit X'.ringCatSheaf)
              (fun i => (Scheme.Modules.pullback h).obj (L i)) n))
          (ProperCoherenceWitness.higherDirectImageIsCoherent X' X h
            (LocallyOfFiniteType.isLocallyNoetherian f) (IsProper.of_comp h f) _
            inferInstance q) =
        (-1 : ℤ) ^ q * @eulerCharacteristic k _ X f _ (twistedSheaf (G q) L n)
          (@twistedSheaf_isCoherent X r _ L _ (hG q) n) := by
      intro q
      congr 1
      exact @eulerCharacteristic_eq_of_iso k _ X f _ _ _
        (ProperCoherenceWitness.higherDirectImageIsCoherent X' X h
          (LocallyOfFiniteType.isLocallyNoetherian f) (IsProper.of_comp h f) _ inferInstance q)
        (@twistedSheaf_isCoherent X r _ L _ (hG q) n) ((eG q _).symm ≪≫ eProj q n)
    rw [finsum_congr hterm, finsum_eq_finsetSum_of_support_subset (s := Finset.range (B + 1))]
    · push_cast
      rfl
    · intro q hq
      by_contra hnot
      have hqB : B ≤ q := by
        simp at hnot
        omega
      refine hq ?_
      change (-1 : ℤ) ^ q * _ = 0
      rw [eulerCharacteristic_eq_zero_of_isZero k f _ _
        (isZero_twistedSheaf_of_isZero L (hGz q hqB) n), mul_zero]
  have hPsum : P = ∑ q ∈ Finset.range (B + 1), (-1 : ℚ) ^ q • R' q :=
    eq_of_forall_eval_intCast fun n => by
      rw [hP, hLeray, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [MvPolynomial.smul_eval, hR'eval]
  -- the generic fibre is the generic point
  have hfib : ∀ z : X', h z = genericPoint X → z = genericPoint X' := fun z hz =>
    eq_genericPoint_of_map_eq_genericPoint_of_dim_eq h h.isClosedMap hd' hd hz
  have hvan : ∀ q, 0 < q → MvPolynomial.homogeneousComponent d (R' q) = 0 := by
    intro q hq
    have hfin : (h ⁻¹' {genericPoint X}).Finite :=
      (Set.finite_singleton (genericPoint X')).subset fun z hz => hfib z hz
    have hz0 := Stacks.FormalFunctions.isZero_stalk_higherDirectImage_of_finite_fibre
      h (genericPoint X) hfin (SheafOfModules.unit X'.ringCatSheaf) (q : ℤ)
      (by exact_mod_cast hq)
    have hnotmem : genericPoint X ∉ _root_.SheafOfModules.supp (G q) := by
      intro hmem
      have hmem' := Eq.mp (congrArg (fun S => genericPoint X ∈ S)
        (_root_.SheafOfModules.supp_eq_of_iso (eG q (SheafOfModules.unit X'.ringCatSheaf)))) hmem
      exact (not_nontrivial_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero hz0))
        ((_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ _).mp hmem')
    have : (G q).IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
    exact homogeneousComponent_eq_zero_of_genericPoint_notMem_supp d hd (G q) hnotmem _
      (hR'deg q)
  -- in degree zero the higher direct image is the direct image
  have hR0 : R' 0 = R := eq_of_forall_eval_intCast fun n => by
    rw [hR'eval, hR]
    exact_mod_cast @eulerCharacteristic_eq_of_iso k _ X f _ _ _
      (@twistedSheaf_isCoherent X r _ L _ (hG 0) n)
      (@twistedSheaf_isCoherent X r _ L _ hF n)
      (twistedSheafIsoOfIso L
        ((Functor.rightDerivedZeroIsoSelf (Scheme.Modules.pushforward h)).app _) n)
  rw [hPsum, map_sum, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos B)),
    pow_zero, one_smul, hR0]
  intro q _ hq0
  rw [map_smul, hvan q (Nat.pos_of_ne_zero hq0), smul_zero]

/-- **The top Euler-polynomial part under a generically finite morphism.** Let `h : X' ⟶ X` be a
proper dominant morphism of integral schemes proper over a field `k` (via `f` and `h ≫ f`), both
of dimension `d`, and let `L₁, …, L_r` be invertible on `X`. If `P` and `Q` are rational
polynomials with `P(n) = χ(X', h^*L₁^{n₁} ⊗ ⋯ ⊗ h^*L_r^{n_r})` and
`Q(n) = χ(X, L₁^{n₁} ⊗ ⋯ ⊗ L_r^{n_r})` for all `n ∈ ℤ^r`, then the degree-`d` homogeneous
component of `P` is `[k(X') : k(X)]` times that of `Q`. -/
@[mmp "lem_mmp_foundation_generically_finite_euler_top_projection"]
public theorem homogeneousComponent_eulerPolynomial_pullback_eq_finrank_smul
    (k : Type u) [Field k] {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ Spec (.of k)) [IsProper f] (h : X' ⟶ X) [IsProper h] [IsDominant h]
    (d : ℕ) (hd : topologicalKrullDim X = d) (hd' : topologicalKrullDim X' = d)
    {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (P Q : MvPolynomial (Fin r) ℚ)
    (hP : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      (@eulerCharacteristic k _ X' (h ≫ f) _
        (twistedSheaf (SheafOfModules.unit X'.ringCatSheaf)
          (fun i => (Scheme.Modules.pullback h).obj (L i)) n)
        (@twistedSheaf_isCoherent X' r _ _ _
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (h ≫ f)) n) : ℚ))
    (hQ : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) Q =
      (@eulerCharacteristic k _ X f _ (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) L n)
        (@twistedSheaf_isCoherent X r _ L _
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f) n) : ℚ)) :
    MvPolynomial.homogeneousComponent d P =
      (letI := functionFieldMapAlgebra h; Module.finrank X.functionField X'.functionField : ℚ) •
        MvPolynomial.homogeneousComponent d Q := by
  obtain ⟨hF, hrk⟩ := pushforward_unit_isCoherent_and_fiberRank_eq k f h d hd hd'
  obtain ⟨R, -, hR⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f L _ hF
  rw [homogeneousComponent_eulerPolynomial_eq_pushforward k f h d hd hd' L hF P R hP hR,
    homogeneousComponent_eulerPolynomial_eq_fiberRank_smul k f d hd L _ hF R Q hR hQ, hrk]

end EulerTopProjection

end MMP.Mori

namespace MMP.Foundations

section Transversality

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

universe u

/-! ### Smooth loci and homogeneity -/

/-- Postcomposing with an open immersion does not change the smooth locus. -/
private theorem smoothLocus_comp_isOpenImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z)
    [IsOpenImmersion e] [LocallyOfFinitePresentation f] :
    (f ≫ e).smoothLocus = f.smoothLocus := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  have : IsIso (e.stalkMap (f x)) := IsOpenImmersion.instIsIsoCommRingCatStalkMap e (f x)
  refine Iff.trans ?_
    (RingHom.FormallySmooth.respectsIso.cancel_left_isIso (e.stalkMap (f x)) (f.stalkMap x))
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  rfl

private theorem smoothLocus_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) :
    f.smoothLocus = g.smoothLocus := by
  subst h
  rfl

/-- **Homogeneity.** Let `T` be locally of finite type over an algebraically closed field `k`
and `W` a nonempty open subset of `T`. If any `k`-point of `T` is carried to any other by an
automorphism of `T` over `k` preserving `W`, then `W` is all of `T`: its closed complement would
contain a closed point, which is a `k`-point. -/
private theorem eq_top_of_homogeneous {k : Type u} [Field k] [IsAlgClosed k]
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] (W : T.left.Opens)
    (hW : (W : Set T.left).Nonempty)
    (hmove : ∀ x y : 𝟙_ (Over (Spec (.of k))) ⟶ T,
      ∃ φ : T ≅ T, x ≫ φ.hom = y ∧ φ.hom.left ⁻¹ᵁ W = W) :
    W = ⊤ := by
  have := LocallyOfFiniteType.jacobsonSpace T.hom
  rw [← TopologicalSpace.Opens.coe_eq_univ, ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints H W.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  let x' : 𝟙_ (Over (Spec (.of k))) ⟶ T :=
    Over.homMk _ ((pointEquivClosedPoint T.hom).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ (Over (Spec (.of k))) ⟶ T :=
    Over.homMk _ ((pointEquivClosedPoint T.hom).symm ⟨y, hyc⟩).2
  obtain ⟨φ, hφ, hφW⟩ := hmove x' y'
  have hφx : φ.hom.left x = y := by
    let pt : (𝟙_ (Over (Spec (.of k)))).left := IsLocalRing.closedPoint k
    have h1 : φ.hom.left (x'.left pt) = y'.left pt := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ]
    simp only [x', y', pt, Over.homMk_left, pointEquivClosedPoint_symm_apply_coe] at h1
    convert h1 using 2 <;> exact (pointOfClosedPoint_apply _ _ _ _).symm
  apply hx
  rw [← hφW]
  change φ.hom.left x ∈ W
  rw [hφx]
  exact hy

/-! ### Translations -/

section Translation

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {P : Over (Spec (.of k))} [ModObj G P]

private theorem comp_smul_id {T : Over (Spec (.of k))} (x : T ⟶ P)
    (σ : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    x ≫ ((toUnit P ≫ σ) • 𝟙 P) = (toUnit T ≫ σ) • x := by
  rw [ModObj.comp_smul, Category.comp_id, ← Category.assoc, comp_toUnit]

/-- Translation by a `k`-point `σ` of `G`, as an automorphism of `P`. -/
private noncomputable def smulIso (σ : 𝟙_ (Over (Spec (.of k))) ⟶ G) : P ≅ P where
  hom := (toUnit P ≫ σ) • 𝟙 P
  inv := (toUnit P ≫ σ⁻¹) • 𝟙 P
  hom_inv_id := by
    rw [comp_smul_id, ← mul_smul, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, one_smul]
  inv_hom_id := by
    rw [comp_smul_id, ← mul_smul, ← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, one_smul]

end Translation

/-! ### The critical-locus argument

A morphism `g : T ⟶ S` from a regular Noetherian scheme to an integral base whose generic point
has residue field of characteristic zero is smooth over a neighbourhood of the generic point: at a
point over the generic point the fibre is regular over a perfect field, hence smooth, and the image
of the non-smooth locus is constructible and avoids the generic point. This is the argument of the
free system Bertini theorem `MMP.Threefold.Bridges.exists_dense_open_smooth_zeroScheme`. -/

section CriticalLocus

open Topology TopologicalSpace

private theorem flat_fromSpecResidueField_of_isField {S : Scheme.{u}} (s : S)
    (hs : IsField (S.presheaf.stalk s)) : Flat (S.fromSpecResidueField s) := by
  have hbij : Function.Bijective (S.residue s).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s) :=
      (IsLocalRing.residue_eq_zero_iff a).mp ha
    rwa [(IsLocalRing.isField_iff_maximalIdeal_eq).mp hs] at this
  have : IsIso (S.residue s) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  dsimp only [Scheme.fromSpecResidueField]
  infer_instance

private theorem mem_smoothLocus_of_isField_stalk {T S : Scheme.{u}} (g : T ⟶ S)
    [LocallyOfFinitePresentation g] (t : T)
    (hT : IsRegularLocalRing (T.presheaf.stalk t))
    (hs : IsField (S.presheaf.stalk (g t))) (hchar : CharZero (S.residueField (g t))) :
    t ∈ g.smoothLocus := by
  set s := g t with hsdef
  have hflat := flat_fromSpecResidueField_of_isField s hs
  have hsq : IsPullback (g.fiberι s) (g.fiberToSpecResidueField s) g
      (S.fromSpecResidueField s) := IsPullback.of_hasPullback _ _
  have : LocallyOfFinitePresentation (g.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFinitePresentation
      (Limits.pullback.snd g (S.fromSpecResidueField s)))
  have : LocallyOfFiniteType (g.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType
      (Limits.pullback.snd g (S.fromSpecResidueField s)))
  have hloc := Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hsq (Or.inr hflat)
  have : PerfectField (S.residueField s) := PerfectField.ofCharZero
  -- regularity of the fibre stalk
  obtain ⟨e, -⟩ := quotientStalk_bridge g t
  have hm : Ideal.map (g.stalkMap (g.fiberι (g t) (g.asFiber t))).hom
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (g (g.fiberι (g t) (g.asFiber t))))) = ⊥ := by
    have h1 : IsField (S.presheaf.stalk (g (g.fiberι (g t) (g.asFiber t)))) := by
      rw [g.fiberι_asFiber]; exact hs
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp h1, Ideal.map_bot]
  have : IsRegularLocalRing (T.presheaf.stalk (g.fiberι (g t) (g.asFiber t))) := by
    rw [g.fiberι_asFiber]; exact hT
  have hreg : IsRegularLocalRing ((g.fiber s).presheaf.stalk (g.asFiber t)) :=
    IsRegularLocalRing.of_ringEquiv
      (((Ideal.quotEquivOfEq hm).trans (RingEquiv.quotientBot _)).symm.trans e)
  have hsm := (smoothAt_iff_isRegularLocalRing_stalk (k := ↥(S.residueField s))
    (g.fiberToSpecResidueField s)
    (g.asFiber t) ?_).mpr hreg
  · have hmem : g.asFiber t ∈ (g.fiberToSpecResidueField s).smoothLocus :=
      Scheme.Hom.mem_smoothLocus.mpr (hsm.formallySmooth_stalkMap _ _)
    rw [hloc] at hmem
    have := g.fiberι_asFiber t
    rw [Scheme.Hom.mem_preimage, this] at hmem
    exact hmem
  · let _ : Algebra (S.residueField s) ((g.fiber s).residueField (g.asFiber t)) :=
      ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
        (g.fiberToSpecResidueField s).appTop ≫ (g.fiber s).Γevaluation (g.asFiber t)).hom.toAlgebra
    exact Algebra.isSeparableExtension_of_perfectField _ _

private theorem exists_isOpen_mem_subset_of_isConstructible' {T : Type*} [TopologicalSpace T]
    {E : Set T} (hE : IsConstructible E) {gp : T}
    (hgp : IsGenericPoint gp (Set.univ : Set T)) (hgpE : gp ∈ E) :
    ∃ U : Set T, IsOpen U ∧ gp ∈ U ∧ U ⊆ E := by
  obtain ⟨t, ht, hEeq⟩ := Topology.isConstructible_iff_exists_finset_biUnion_inter_compl.mp hE
  rw [hEeq] at hgpE ⊢
  obtain ⟨p, hpt, hgpU, hgpV⟩ := Set.mem_iUnion₂.mp hgpE
  have hVempty : p.2 = ∅ := by
    have hsub : (Set.univ : Set T) ⊆ p.2ᶜ := by
      rw [← hgp]
      exact (ht p hpt).2.2.1.isClosed_compl.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hgpV)
    simpa using Set.subset_compl_comm.mp hsub
  exact ⟨p.1, (ht p hpt).1, hgpU, fun x hx =>
    Set.mem_biUnion hpt ⟨hx, by simp [hVempty]⟩⟩

private theorem exists_opens_subset_smoothLocus {T S : Scheme.{u}} (g : T ⟶ S)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [NoetherianSpace T] [CompactSpace S]
    [QuasiSeparatedSpace S] (gp : S) (hgp : IsGenericPoint gp (Set.univ : Set S))
    (hfield : IsField (S.presheaf.stalk gp)) (hchar : CharZero (S.residueField gp))
    (hT : ∀ t, IsRegularLocalRing (T.presheaf.stalk t)) :
    ∃ U : S.Opens, gp ∈ U ∧ ((g ⁻¹ᵁ U : T.Opens) : Set T) ⊆ g.smoothLocus := by
  have : QuasiSeparatedSpace T := NoetherianSpace.to_quasiSeparatedSpace
  have hZ : IsConstructible ((g.smoothLocus : Set T)ᶜ) := by
    rw [isConstructible_compl]
    exact (NoetherianSpace.isCompact _).isConstructible g.smoothLocus.2
  have himg : IsConstructible (g '' (g.smoothLocus : Set T)ᶜ) := g.isConstructible_image hZ
  have hgpnot : gp ∉ g '' (g.smoothLocus : Set T)ᶜ := by
    rintro ⟨t, ht, rfl⟩
    exact ht (mem_smoothLocus_of_isField_stalk g t (hT t) hfield hchar)
  obtain ⟨U, hUo, hgpU, hUsub⟩ := exists_isOpen_mem_subset_of_isConstructible'
    ((isConstructible_compl).mpr himg) hgp hgpnot
  refine ⟨⟨U, hUo⟩, hgpU, fun t ht => ?_⟩
  by_contra hns
  exact hUsub ht ⟨t, hns, rfl⟩

end CriticalLocus

/-! ### The group and the homogeneous space are smooth -/

section Smoothness

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {G : Over (Spec (.of k))} [GrpObj G] [IsReduced G.left] [LocallyOfFiniteType G.hom]

private theorem smooth_hom_of_grpObj : Smooth G.hom := by
  have : PerfectField k := PerfectField.ofCharZero
  have : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  have : GeometricallyReduced G.hom := geometricallyReduced_of_isReduced G.hom
  exact smooth_of_grpObj G.hom

variable (G) in
private theorem smooth_hom_of_isPretransitive (P : Over (Spec (.of k))) [ModObj G P] [IsVariety k P.hom]
    [MulAction.IsPretransitive (𝟙_ (Over (Spec (.of k))) ⟶ G) (𝟙_ (Over (Spec (.of k))) ⟶ P)] :
    Smooth P.hom := by
  have : PerfectField k := PerfectField.ofCharZero
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine eq_top_of_homogeneous (T := P) _ P.hom.dense_smoothLocus_of_perfectField.nonempty ?_
  intro x y
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (𝟙_ (Over (Spec (.of k))) ⟶ G) x y
  refine ⟨smulIso σ, ?_, ?_⟩
  · change x ≫ ((toUnit P ≫ σ) • 𝟙 P) = y
    rw [comp_smul_id, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, hσ]
  · rw [Scheme.Hom.preimage_smoothLocus_eq]
    simp only [Over.w]

end Smoothness

/-! ### Equivariance of the incidence map

The map `α = ModObj.leftSMul G P : G × P ⟶ P × P`, `(s, q) ↦ (s q, q)`, intertwines the
automorphism `(s, q) ↦ (τ s ρ⁻¹, ρ q)` of `G × P` with the automorphism `(a, b) ↦ (τ a, ρ b)` of
`P × P`. -/

section Equivariance

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {P : Over (Spec (.of k))} [ModObj G P]

private theorem smul_eq_fst_smul_snd : γ[G, P] = fst G P • snd G P := by
  rw [CategoryTheory.Hom.smul_def, lift_fst_snd, Category.id_comp]

/-- `(s, q) ↦ (τ s ρ⁻¹, ρ q)` on `G × P`. -/
private noncomputable def srcMap (τ ρ : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ⊗ P ⟶ G ⊗ P :=
  lift ((toUnit (G ⊗ P) ≫ τ) * fst G P * (toUnit (G ⊗ P) ≫ ρ)⁻¹)
    ((toUnit (G ⊗ P) ≫ ρ) • snd G P)

/-- `(a, b) ↦ (τ a, ρ b)` on `P × P`. -/
private noncomputable def tgtMap (τ ρ : 𝟙_ (Over (Spec (.of k))) ⟶ G) : P ⊗ P ⟶ P ⊗ P :=
  lift ((toUnit (P ⊗ P) ≫ τ) • fst P P) ((toUnit (P ⊗ P) ≫ ρ) • snd P P)

private theorem srcMap_comp_srcMap (τ ρ : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    srcMap (P := P) τ ρ ≫ srcMap τ⁻¹ ρ⁻¹ = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [srcMap, MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
  · simp [srcMap, ModObj.comp_smul, ← mul_smul, GrpObj.comp_inv]

private theorem tgtMap_comp_tgtMap (τ ρ : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    tgtMap (P := P) τ ρ ≫ tgtMap τ⁻¹ ρ⁻¹ = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [tgtMap, ModObj.comp_smul, ← mul_smul, GrpObj.comp_inv]
  · simp [tgtMap, ModObj.comp_smul, ← mul_smul, GrpObj.comp_inv]

/-- `srcMap τ ρ` as an automorphism of `G × P`. -/
private noncomputable def srcIso (τ ρ : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ⊗ P ≅ G ⊗ P where
  hom := srcMap τ ρ
  inv := srcMap τ⁻¹ ρ⁻¹
  hom_inv_id := srcMap_comp_srcMap τ ρ
  inv_hom_id := by simpa using srcMap_comp_srcMap (P := P) τ⁻¹ ρ⁻¹

private theorem srcIso_hom (τ ρ : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (srcIso (P := P) τ ρ).hom = srcMap τ ρ :=
  rfl

/-- `tgtMap τ ρ` as an automorphism of `P × P`. -/
private noncomputable def tgtIso (τ ρ : 𝟙_ (Over (Spec (.of k))) ⟶ G) : P ⊗ P ≅ P ⊗ P where
  hom := tgtMap τ ρ
  inv := tgtMap τ⁻¹ ρ⁻¹
  hom_inv_id := tgtMap_comp_tgtMap τ ρ
  inv_hom_id := by simpa using tgtMap_comp_tgtMap (P := P) τ⁻¹ ρ⁻¹

private theorem srcMap_comp_leftSMul (τ ρ : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    srcMap τ ρ ≫ ModObj.leftSMul G P = ModObj.leftSMul G P ≫ tgtMap τ ρ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [srcMap, tgtMap, smul_eq_fst_smul_snd, ModObj.comp_smul, ← mul_smul, mul_assoc]
  · simp [srcMap, tgtMap, ModObj.comp_smul]

end Equivariance

/-! ### The incidence map is smooth -/

section IncidenceSmooth

variable {k : Type u} [Field k]

private theorem isNoetherian_of_over {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  { }

private theorem charZero_residueField [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (x : X) : CharZero (X.residueField x) :=
  charZero_of_injective_ringHom
    (f := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom) (RingHom.injective _)

private theorem isIntegral_pullback_self [IsAlgClosed k] (P : Over (Spec (.of k)))
    [IsVariety k P.hom] : IsIntegral (pullback P.hom P.hom) := by
  have : GeometricallyIrreducible P.hom :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k P.left P.hom
  have : GeometricallyReduced P.hom := geometricallyReduced_of_isReduced P.hom
  have : GeometricallyIntegral P.hom :=
    .of_geometricallyReduced_of_geometricallyIrreducible P.hom
  have := LocallyOfFiniteType.isLocallyNoetherian P.hom
  infer_instance

variable [IsAlgClosed k] [CharZero k] {G : Over (Spec (.of k))} [GrpObj G] [IsReduced G.left]
  [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]

variable (G) in
private theorem smooth_leftSMul (P : Over (Spec (.of k))) [ModObj G P] [IsVariety k P.hom]
    [MulAction.IsPretransitive (𝟙_ (Over (Spec (.of k))) ⟶ G) (𝟙_ (Over (Spec (.of k))) ⟶ P)] :
    Smooth (ModObj.leftSMul G P).left := by
  have : PerfectField k := PerfectField.ofCharZero
  have : Smooth G.hom := smooth_hom_of_grpObj
  have : Smooth P.hom := smooth_hom_of_isPretransitive G P
  have : LocallyOfFiniteType (G ⊗ P).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom P.hom ≫ G.hom))
  have : QuasiCompact (G ⊗ P).hom :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom P.hom ≫ G.hom))
  have : Smooth (G ⊗ P).hom := inferInstanceAs (Smooth (pullback.fst G.hom P.hom ≫ G.hom))
  have : LocallyOfFiniteType (P ⊗ P).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst P.hom P.hom ≫ P.hom))
  have : QuasiCompact (P ⊗ P).hom :=
    inferInstanceAs (QuasiCompact (pullback.fst P.hom P.hom ≫ P.hom))
  have : IsSeparated (P ⊗ P).hom :=
    inferInstanceAs (IsSeparated (pullback.fst P.hom P.hom ≫ P.hom))
  set α := ModObj.leftSMul G P
  have hαw : α.left ≫ (P ⊗ P).hom = (G ⊗ P).hom := Over.w α
  have : LocallyOfFiniteType (α.left ≫ (P ⊗ P).hom) := by rw [hαw]; infer_instance
  have : LocallyOfFiniteType α.left := locallyOfFiniteType_of_comp α.left (P ⊗ P).hom
  have : IsLocallyNoetherian (P ⊗ P).left := LocallyOfFiniteType.isLocallyNoetherian (P ⊗ P).hom
  have : QuasiCompact (α.left ≫ (P ⊗ P).hom) := by rw [hαw]; infer_instance
  have : QuasiCompact α.left := QuasiCompact.of_comp α.left (P ⊗ P).hom
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine eq_top_of_homogeneous (T := G ⊗ P) _ ?_ ?_
  · -- the critical-locus argument at the generic point of `P × P`
    have : IsNoetherian (G ⊗ P).left := isNoetherian_of_over (G ⊗ P).hom
    have : IsNoetherian (P ⊗ P).left := isNoetherian_of_over (P ⊗ P).hom
    have : IsIntegral (P ⊗ P).left := isIntegral_pullback_self P
    have : QuasiSeparatedSpace (P ⊗ P).left := NoetherianSpace.to_quasiSeparatedSpace
    obtain ⟨U, hgU, hU⟩ := exists_opens_subset_smoothLocus α.left (genericPoint (P ⊗ P).left)
      (genericPoint_spec _) (Field.toIsField (P ⊗ P).left.functionField)
      (charZero_residueField (P ⊗ P).hom _)
      ((MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk (G ⊗ P).hom).1
        inferInstance)
    have := LocallyOfFiniteType.jacobsonSpace (P ⊗ P).hom
    obtain ⟨z, hzU, hzc⟩ := nonempty_inter_closedPoints ⟨_, hgU⟩ U.2.isLocallyClosed
    let z' : 𝟙_ (Over (Spec (.of k))) ⟶ P ⊗ P :=
      Over.homMk _ ((pointEquivClosedPoint (P ⊗ P).hom).symm ⟨z, hzc⟩).2
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (𝟙_ (Over (Spec (.of k))) ⟶ G)
      (z' ≫ snd P P) (z' ≫ fst P P)
    let w : 𝟙_ (Over (Spec (.of k))) ⟶ G ⊗ P := lift σ (z' ≫ snd P P)
    have hw : w ≫ α = z' := by
      rw [ModObj.lift_leftSMul, hσ]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · exact lift_fst _ _
      · exact lift_snd _ _
    let pt : (𝟙_ (Over (Spec (.of k)))).left := IsLocalRing.closedPoint k
    refine ⟨w.left pt, hU ?_⟩
    change α.left (w.left pt) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hw]
    have hz : z'.left pt = z := by
      simp only [z', pt, Over.homMk_left, pointEquivClosedPoint_symm_apply_coe]
      exact pointOfClosedPoint_apply _ _ _ _
    rw [hz]
    exact hzU
  · intro x y
    obtain ⟨ρ, hρ⟩ := MulAction.exists_smul_eq (𝟙_ (Over (Spec (.of k))) ⟶ G)
      (x ≫ snd G P) (y ≫ snd G P)
    let τ := (y ≫ fst G P) * ρ * (x ≫ fst G P)⁻¹
    refine ⟨srcIso τ ρ, ?_, ?_⟩
    · refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp [srcIso_hom, srcMap, MonObj.comp_mul, GrpObj.comp_inv, τ, mul_assoc]
      · simp [srcIso_hom, srcMap, ModObj.comp_smul, hρ]
    · change (srcMap τ ρ).left ⁻¹ᵁ α.left.smoothLocus = α.left.smoothLocus
      have : IsIso (srcMap (P := P) τ ρ).left :=
        inferInstanceAs (IsIso ((Over.forget _).map (srcIso (P := P) τ ρ).hom))
      have : IsIso (tgtMap (P := P) τ ρ).left :=
        inferInstanceAs (IsIso ((Over.forget _).map (tgtIso (P := P) τ ρ).hom))
      have : IsOpenImmersion (srcMap (P := P) τ ρ).left := IsOpenImmersion.of_isIso _
      rw [Scheme.Hom.preimage_smoothLocus_eq,
        smoothLocus_eq_of_eq (g := α.left ≫ (tgtMap τ ρ).left)
          (by rw [← Over.comp_left, srcMap_comp_leftSMul, Over.comp_left])]
      exact smoothLocus_comp_isOpenImmersion _ _

end IncidenceSmooth

/-! ### The incidence scheme

`Z = (X × Y) ×_{P × P} (G × P)`, the pullback of `α` along `(f, h) : X × Y ⟶ P × P`, whose points
are the triples `(x, y, s)` with `f x = s (h y)`; its fibre over a `k`-point `σ` of `G` is the
translated fibre product `X ×_{f, P, σ h} Y`. -/

section Incidence

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {P : Over (Spec (.of k))} [ModObj G P] {X Y : Over (Spec (.of k))}

/-- `(f, h) : X × Y ⟶ P × P`. -/
private noncomputable abbrev pairMap (f : X ⟶ P) (h : Y ⟶ P) : X ⊗ Y ⟶ P ⊗ P :=
  lift (fst X Y ≫ f) (snd X Y ≫ h)

variable (G) in
/-- The incidence scheme. -/
private noncomputable abbrev incidence (f : X ⟶ P) (h : Y ⟶ P) : Over (Spec (.of k)) :=
  pullback (pairMap f h) (ModObj.leftSMul G P)

variable (G) in
/-- The projection of the incidence scheme to `G`. -/
private noncomputable abbrev incidenceToG (f : X ⟶ P) (h : Y ⟶ P) : incidence G f h ⟶ G :=
  pullback.snd _ _ ≫ fst G P

/-- The translated fibre product, in `Over (Spec k)`. -/
private noncomputable abbrev transl (f : X ⟶ P) (h : Y ⟶ P)
    (σ : 𝟙_ (Over (Spec (.of k))) ⟶ G) : Over (Spec (.of k)) :=
  pullback f ((toUnit Y ≫ σ) • h)

private theorem transl_condition (f : X ⟶ P) (h : Y ⟶ P) (σ : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    {T : Over (Spec (.of k))} (a : T ⟶ transl f h σ) :
    a ≫ pullback.fst _ _ ≫ f = (toUnit T ≫ σ) • (a ≫ pullback.snd _ _ ≫ h) := by
  rw [pullback.condition, ModObj.comp_smul, ModObj.comp_smul]
  simp only [comp_toUnit_assoc]

/-- The inclusion of the translated fibre product into the incidence scheme. -/
private noncomputable def translToIncidence (f : X ⟶ P) (h : Y ⟶ P)
    (σ : 𝟙_ (Over (Spec (.of k))) ⟶ G) : transl f h σ ⟶ incidence G f h :=
  pullback.lift (lift (pullback.fst _ _) (pullback.snd _ _))
    (lift (toUnit _ ≫ σ) (pullback.snd _ _ ≫ h)) (by
      rw [ModObj.lift_leftSMul]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simpa using transl_condition f h σ (𝟙 _)
      · simp)

@[reassoc]
private theorem translToIncidence_fst (f : X ⟶ P) (h : Y ⟶ P)
    (σ : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    translToIncidence f h σ ≫ pullback.fst _ _ = lift (pullback.fst _ _) (pullback.snd _ _) :=
  pullback.lift_fst _ _ _

private theorem translToIncidence_snd (f : X ⟶ P) (h : Y ⟶ P)
    (σ : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    translToIncidence f h σ ≫ pullback.snd _ _ = lift (toUnit _ ≫ σ) (pullback.snd _ _ ≫ h) :=
  pullback.lift_snd _ _ _

private theorem incidence_snd_snd (f : X ⟶ P) (h : Y ⟶ P) {T : Over (Spec (.of k))}
    (a : T ⟶ incidence G f h) :
    a ≫ pullback.snd _ _ ≫ snd G P = a ≫ pullback.fst _ _ ≫ snd X Y ≫ h := by
  have := congrArg (· ≫ snd P P) (a ≫= pullback.condition (f := pairMap f h)
    (g := ModObj.leftSMul G P))
  simpa only [Category.assoc, lift_snd, ModObj.leftSMul_snd] using this.symm

private theorem incidence_fst_fst (f : X ⟶ P) (h : Y ⟶ P) {T : Over (Spec (.of k))}
    (a : T ⟶ incidence G f h) :
    a ≫ pullback.fst _ _ ≫ fst X Y ≫ f =
      (a ≫ pullback.snd _ _ ≫ fst G P) • (a ≫ pullback.snd _ _ ≫ snd G P) := by
  have := congrArg (· ≫ fst P P) (a ≫= pullback.condition (f := pairMap f h)
    (g := ModObj.leftSMul G P))
  simp only [Category.assoc, lift_fst, ModObj.leftSMul_fst] at this
  rw [this, smul_eq_fst_smul_snd, ModObj.comp_smul, ModObj.comp_smul]

private theorem isPullback_translToIncidence (f : X ⟶ P) (h : Y ⟶ P)
    (σ : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    IsPullback (translToIncidence f h σ) (toUnit _) (incidenceToG G f h) σ := by
  have w : translToIncidence f h σ ≫ incidenceToG G f h = toUnit _ ≫ σ := by
    rw [incidenceToG, ← Category.assoc, translToIncidence_snd, lift_fst]
  have h3 : ∀ s : PullbackCone (incidenceToG G f h) σ,
      s.fst ≫ pullback.snd _ _ ≫ fst G P = toUnit _ ≫ σ := fun s => by
    have := s.condition
    rwa [toUnit_unique s.snd (toUnit _)] at this
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ w) ?_
  refine PullbackCone.IsLimit.mk _
    (fun s => pullback.lift (s.fst ≫ pullback.fst _ _ ≫ fst X Y)
      (s.fst ≫ pullback.fst _ _ ≫ snd X Y) ?_) ?_ ?_ ?_
  · rw [Category.assoc, Category.assoc, incidence_fst_fst, ModObj.comp_smul, h3,
      incidence_snd_snd]
    simp only [Category.assoc, comp_toUnit_assoc]
  · intro s
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, translToIncidence_fst]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, lift_fst]; exact pullback.lift_fst _ _ _
      · rw [Category.assoc, lift_snd]; exact pullback.lift_snd _ _ _
    · rw [Category.assoc, translToIncidence_snd]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [Category.assoc, lift_fst, comp_toUnit_assoc]
        exact (h3 s).symm
      · simp only [Category.assoc, lift_snd, pullback.lift_snd_assoc]
        exact (incidence_snd_snd f h s.fst).symm
  · intro s; exact toUnit_unique _ _
  · intro s m hm _
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, ← hm, Category.assoc, translToIncidence_fst_assoc, lift_fst]
    · rw [pullback.lift_snd, ← hm, Category.assoc, translToIncidence_fst_assoc, lift_snd]

/-- The incidence square, in schemes. -/
private theorem isPullback_incidence_left (f : X ⟶ P) (h : Y ⟶ P) :
    IsPullback (pullback.fst (pairMap f h) (ModObj.leftSMul G P)).left
      (pullback.snd (pairMap f h) (ModObj.leftSMul G P)).left (pairMap f h).left
      (ModObj.leftSMul G P).left :=
  (IsPullback.of_hasPullback _ _).map (Over.forget _)

end Incidence

section Dimension

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsReduced G.left] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [ConnectedSpace G.left]
    (P : Over (Spec (.of k))) [ModObj G P] [IsVariety k P.hom]
    [MulAction.IsPretransitive (𝟙_ (Over (Spec (.of k))) ⟶ G) (𝟙_ (Over (Spec (.of k))) ⟶ P)]
    {X Y : Over (Spec (.of k))} [IsVariety k X.hom] [IsVariety k Y.hom]

/-! ### Dimension bookkeeping -/

/-- The projection of the incidence scheme to `X × Y` is smooth and quasi-compact, being a base
change of the incidence map `α`. -/
private theorem smooth_quasiCompact_incidence_fst (f : X ⟶ P) (h : Y ⟶ P) :
    Smooth (pullback.fst (pairMap f h) (ModObj.leftSMul G P)).left ∧
      QuasiCompact (pullback.fst (pairMap f h) (ModObj.leftSMul G P)).left := by
  have : IsSeparated (P ⊗ P).hom :=
    inferInstanceAs (IsSeparated (pullback.fst P.hom P.hom ≫ P.hom))
  have : QuasiCompact (G ⊗ P).hom :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom P.hom ≫ G.hom))
  have : QuasiCompact ((ModObj.leftSMul G P).left ≫ (P ⊗ P).hom) := by
    rw [Over.w]; infer_instance
  have : QuasiCompact (ModObj.leftSMul G P).left := QuasiCompact.of_comp _ (P ⊗ P).hom
  have hpb := isPullback_incidence_left (G := G) f h
  exact ⟨MorphismProperty.of_isPullback hpb.flip (smooth_leftSMul G P),
    MorphismProperty.of_isPullback hpb.flip inferInstance⟩

/-- On an irreducible scheme locally of finite type over `k` the local dimension is the
dimension. -/
private theorem topologicalKrullDimAt_eq_of_irreducibleSpace {T : Scheme.{u}}
    (p : T ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IrreducibleSpace T] (t : T) :
    topologicalKrullDimAt T t = topologicalKrullDim T :=
  topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k T p
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace T) t

/-- An irreducible scheme locally of finite type over `k` has finite dimension: it is the
dimension of the local ring at a closed point. -/
private theorem exists_nat_topologicalKrullDim {T : Scheme.{u}} (p : T ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [IrreducibleSpace T] : ∃ d : ℕ, topologicalKrullDim T = d := by
  have := LocallyOfFiniteType.jacobsonSpace p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have hne : Nonempty T := IrreducibleSpace.toNonempty
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (@Set.univ_nonempty T hne)
    isClosed_univ.isLocallyClosed
  rw [← topologicalKrullDimAt_eq_of_irreducibleSpace k p x,
    topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point p x hx]
  have h1 := ringKrullDim_ne_top (R := T.presheaf.stalk x)
  have h2 := ringKrullDim_ne_bot (R := T.presheaf.stalk x)
  generalize ringKrullDim (T.presheaf.stalk x) = r at h1 h2 ⊢
  induction r using WithBot.recBotCoe with
  | bot => exact absurd rfl h2
  | coe r =>
    induction r using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe d => exact ⟨d, rfl⟩

private theorem eq_natCast_of_add_eq {a : WithBot ℕ∞} {c m : ℕ}
    (h : a + (c : WithBot ℕ∞) = (m : WithBot ℕ∞)) : ∃ i : ℕ, a = i ∧ i + c = m := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exfalso; norm_cast at h
    | coe i => exact ⟨i, rfl, by exact_mod_cast h⟩

private theorem fiber_dim_arith {fq fa : WithBot ℕ∞} {dG dP dX dY : ℕ}
    (h1 : fq + (dG : WithBot ℕ∞) = fa + ((dX + dY : ℕ) : WithBot ℕ∞))
    (h2 : fa + ((dP + dP : ℕ) : WithBot ℕ∞) = ((dG + dP : ℕ) : WithBot ℕ∞)) :
    dP ≤ dX + dY ∧ fq = ((dX + dY - dP : ℕ) : WithBot ℕ∞) := by
  obtain ⟨i, rfl, hi⟩ := eq_natCast_of_add_eq h2
  have h1' : fq + (dG : WithBot ℕ∞) = ((i + (dX + dY) : ℕ) : WithBot ℕ∞) := by
    rw [h1]
    push_cast
    rfl
  obtain ⟨j, rfl, hj⟩ := eq_natCast_of_add_eq h1'
  refine ⟨by omega, ?_⟩
  rw [show j = dX + dY - dP by omega]

/-- A morphism flat over an open `U` of the target is flat at every point over `U`. -/
private theorem flat_stalkMap_of_flat_resLE {X S : Scheme.{u}} (q : X ⟶ S) (U : S.Opens)
    (hU : Flat (q.resLE U (q ⁻¹ᵁ U) le_rfl)) (x : X) (hx : q x ∈ U) :
    (q.stalkMap x).hom.Flat := by
  let x' : ((q ⁻¹ᵁ U : X.Opens) : Scheme.{u}) := ⟨x, hx⟩
  have h1 := Flat.stalkMap (q.resLE U (q ⁻¹ᵁ U) le_rfl) x'
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι (q.resLE U (q ⁻¹ᵁ U) le_rfl x')
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap (q ⁻¹ᵁ U).ι x'
  have h2 : ((q.resLE U (q ⁻¹ᵁ U) le_rfl ≫ U.ι).stalkMap x').hom.Flat := by
    have := (RingHom.Flat.respectsIso.cancel_left_isIso
      (U.ι.stalkMap (q.resLE U (q ⁻¹ᵁ U) le_rfl x'))
      ((q.resLE U (q ⁻¹ᵁ U) le_rfl).stalkMap x')).mpr h1
    rwa [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp] at this
  rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.stalkMap_comp] at h2
  exact (RingHom.Flat.respectsIso.cancel_right_isIso (q.stalkMap ((q ⁻¹ᵁ U).ι x'))
    ((q ⁻¹ᵁ U).ι.stalkMap x')).mp h2

/-- A scheme locally of finite type over a field whose local dimension is `d` at every point is
pure of dimension `d`: the dimension of an irreducible component is the local dimension at its
generic point, which lies on no other component. -/
private theorem isPureDimensional_of_forall_topologicalKrullDimAt {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (d : ℕ)
    (hd : ∀ x : X, topologicalKrullDimAt X x = d) : MMP.IsPureDimensional X d := by
  intro Z hZ
  refine ⟨d, rfl, ?_⟩
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hξZ : ξ ∈ Z := by rw [← hξ.def]; exact subset_closure rfl
  have h := hd ξ
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X p ξ] at h
  rw [← h]
  refine le_antisymm (le_iSup₂_of_le Z ⟨hZ, hξZ⟩ le_rfl) (iSup₂_le fun C hC => ?_)
  have hZC : Z ⊆ C := by
    rw [← hξ.def]
    exact (isClosed_of_mem_irreducibleComponents C hC.1).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hC.2)
  rw [Set.Subset.antisymm (hZ.2 hC.1.1 hZC) hZC]

/-- **The dimension count.** For `σ` in a dense open of `G`, the translated fibre product is either
empty or of local dimension `dim X + dim Y - dim P` at each of its points. Since `α` is smooth,
hence flat, its fibres have local dimension `dim G - dim P` (additivity of fibre dimension along
the flat composite `G × P ⟶ P × P ⟶ Spec k`); by base change the incidence scheme has local
dimension `dim X + dim Y + dim G - dim P` everywhere. Over the dense open where the projection to
`G` is flat (generic flatness), additivity once more gives the fibre dimension
`dim X + dim Y - dim P`, and the fibre over `σ` is the translated fibre product
(`isPullback_translToIncidence`). -/
private theorem exists_dense_forall_topologicalKrullDimAt (f : X ⟶ P) (h : Y ⟶ P)
    {dX dY dP : ℕ}
    (hdX : topologicalKrullDim X.left = dX) (hdY : topologicalKrullDim Y.left = dY)
    (hdP : topologicalKrullDim P.left = dP) :
    ∃ U : G.left.Opens, Dense (U : Set G.left) ∧
      ∀ σ : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.range σ.left ⊆ U →
        IsEmpty ((pullback f.left ((toUnit Y ≫ σ) • h).left : Scheme.{u}) : Type u) ∨
          (dP ≤ dX + dY ∧ ∀ x : ((pullback f.left ((toUnit Y ≫ σ) • h).left : Scheme.{u}) :
            Type u),
            topologicalKrullDimAt _ x = ((dX + dY - dP : ℕ) : WithBot ℕ∞)) := by
  have : Subsingleton (Spec (.of k)) := inferInstance
  have : PerfectField k := PerfectField.ofCharZero
  have : Smooth G.hom := smooth_hom_of_grpObj
  have : Smooth P.hom := smooth_hom_of_isPretransitive G P
  have : Smooth (ModObj.leftSMul G P).left := smooth_leftSMul G P
  have : IrreducibleSpace G.left := irreducibleSpace_of_connectedSpace G
  have : IsIntegral G.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsNoetherian G.left := isNoetherian_of_over G.hom
  obtain ⟨dG, hdG⟩ := exists_nat_topologicalKrullDim k G.hom
  -- local dimensions of the products
  have hprod : ∀ {A B : Over (Spec (.of k))} [LocallyOfFiniteType A.hom]
      [IrreducibleSpace A.left] [LocallyOfFiniteType B.hom] [IrreducibleSpace B.left] {a b : ℕ},
      topologicalKrullDim A.left = a →
      topologicalKrullDim B.left = b → ∀ w : (A ⊗ B).left,
        topologicalKrullDimAt (A ⊗ B).left w = ((a + b : ℕ) : WithBot ℕ∞) := by
    intro A B _ _ _ _ a b ha hb w
    have := topologicalKrullDimAt_pullback k A.hom B.hom w
    rw [topologicalKrullDimAt_eq_of_irreducibleSpace k A.hom,
      topologicalKrullDimAt_eq_of_irreducibleSpace k B.hom, ha, hb] at this
    exact this.trans (by push_cast; rfl)
  have : LocallyOfFiniteType (P ⊗ P).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst P.hom P.hom ≫ P.hom))
  -- the fibres of `α` have local dimension `dG - dP`
  have hfibα : ∀ z : (G ⊗ P).left,
      topologicalKrullDimAt ((ModObj.leftSMul G P).left.fiber ((ModObj.leftSMul G P).left z))
        ((ModObj.leftSMul G P).left.asFiber z) + ((dP + dP : ℕ) : WithBot ℕ∞) =
        ((dG + dP : ℕ) : WithBot ℕ∞) := by
    intro z
    have e1 := topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt (ModObj.leftSMul G P).left
      (P ⊗ P).hom z (Flat.stalkMap _ z)
    rw [topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton
        ((ModObj.leftSMul G P).left ≫ (P ⊗ P).hom) z,
      topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton (P ⊗ P).hom,
      hprod hdP hdP, hprod hdG hdP] at e1
    exact e1.symm
  -- the incidence scheme has local dimension `dim(α-fibre) + dX + dY`
  have hpb := isPullback_incidence_left (G := G) f h
  obtain ⟨_, _⟩ := smooth_quasiCompact_incidence_fst k G P f h
  have : LocallyOfFiniteType (X ⊗ Y).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom Y.hom ≫ X.hom))
  have : QuasiCompact (X ⊗ Y).hom :=
    inferInstanceAs (QuasiCompact (pullback.fst X.hom Y.hom ≫ X.hom))
  have : LocallyOfFiniteType (incidence G f h).hom := by
    rw [← Over.w (pullback.fst (pairMap f h) (ModObj.leftSMul G P))]; infer_instance
  have : QuasiCompact (incidence G f h).hom := by
    rw [← Over.w (pullback.fst (pairMap f h) (ModObj.leftSMul G P))]; infer_instance
  have hZdim : ∀ z : (incidence G f h).left, topologicalKrullDimAt (incidence G f h).left z =
      topologicalKrullDimAt ((ModObj.leftSMul G P).left.fiber ((ModObj.leftSMul G P).left
        ((pullback.snd (pairMap f h) (ModObj.leftSMul G P)).left z)))
        ((ModObj.leftSMul G P).left.asFiber
          ((pullback.snd (pairMap f h) (ModObj.leftSMul G P)).left z)) +
        ((dX + dY : ℕ) : WithBot ℕ∞) := by
    intro z
    have e2 := topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt
      (pullback.fst (pairMap f h) (ModObj.leftSMul G P)).left (X ⊗ Y).hom z (Flat.stalkMap _ z)
    rw [topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton
        ((pullback.fst (pairMap f h) (ModObj.leftSMul G P)).left ≫ (X ⊗ Y).hom) z,
      topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton (X ⊗ Y).hom,
      hprod hdX hdY, topologicalKrullDimAt_fiber_eq_of_isPullback hpb.flip z] at e2
    exact e2
  -- generic flatness of the projection to `G`, and the fibre dimension over the flat locus
  have hqw : (incidenceToG G f h).left ≫ G.hom = (incidence G f h).hom := Over.w _
  have : LocallyOfFiniteType ((incidenceToG G f h).left ≫ G.hom) := by rw [hqw]; infer_instance
  have : LocallyOfFiniteType (incidenceToG G f h).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((incidenceToG G f h).left ≫ G.hom) := by rw [hqw]; infer_instance
  have : QuasiCompact (incidenceToG G f h).left := QuasiCompact.of_comp _ G.hom
  set q := (incidenceToG G f h).left with hq
  obtain ⟨U, hU, hflat, -⟩ := exists_dense_open_flat_finitePresentation_structureSheaf q
  have hqdim : ∀ z, q z ∈ U → topologicalKrullDimAt (q.fiber (q z)) (q.asFiber z) +
      (dG : WithBot ℕ∞) = topologicalKrullDimAt (incidence G f h).left z := by
    intro z hz
    have e3 := topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt q G.hom z
      (flat_stalkMap_of_flat_resLE q U hflat z hz)
    rw [topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton (q ≫ G.hom) z,
      topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton G.hom,
      topologicalKrullDimAt_eq_of_irreducibleSpace k G.hom, hdG] at e3
    exact e3.symm
  -- the fibre over `σ` is the translated fibre product
  refine ⟨U, hU, fun σ hσ => ?_⟩
  by_cases hE : IsEmpty ((pullback f.left ((toUnit Y ≫ σ) • h).left : Scheme.{u}) : Type u)
  · exact Or.inl hE
  right
  have hF : IsPullback (pullback.fst f ((toUnit Y ≫ σ) • h)).left
      (pullback.snd f ((toUnit Y ≫ σ) • h)).left f.left ((toUnit Y ≫ σ) • h).left :=
    (IsPullback.of_hasPullback f ((toUnit Y ≫ σ) • h)).map (Over.forget _)
  have hbig : IsPullback (translToIncidence f h σ).left (toUnit (transl f h σ)).left q
      σ.left := (isPullback_translToIncidence f h σ).map (Over.forget _)
  have hx : ∀ x : ((pullback f.left ((toUnit Y ≫ σ) • h).left : Scheme.{u}) : Type u),
      dP ≤ dX + dY ∧ topologicalKrullDimAt _ x = ((dX + dY - dP : ℕ) : WithBot ℕ∞) := by
    intro x
    have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
      inferInstanceAs (Subsingleton (Spec (.of k)))
    rw [topologicalKrullDimAt_eq_of_isIso hF.isoPullback.inv x,
      ← topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton (toUnit (transl f h σ)).left,
      topologicalKrullDimAt_fiber_eq_of_isPullback hbig]
    set z := (translToIncidence f h σ).left (hF.isoPullback.inv x)
    have hzU : q z ∈ U := by
      have : q z = σ.left ((toUnit (transl f h σ)).left (hF.isoPullback.inv x)) := by
        rw [← Scheme.Hom.comp_apply, hbig.w, Scheme.Hom.comp_apply]
      rw [this]
      exact hσ ⟨_, rfl⟩
    exact fiber_dim_arith ((hqdim z hzU).trans (hZdim z)) (hfibα _)
  obtain ⟨x₀⟩ := not_isEmpty_iff.mp hE
  exact ⟨(hx x₀).1, fun x => (hx x).2⟩

/-- The dimension half: generic translates are pure of the expected dimension. -/
private theorem exists_dense_isPureDimensional (f : X ⟶ P) (h : Y ⟶ P) {dX dY dP : ℕ}
    (hdX : topologicalKrullDim X.left = dX) (hdY : topologicalKrullDim Y.left = dY)
    (hdP : topologicalKrullDim P.left = dP) :
    ∃ U : G.left.Opens, Dense (U : Set G.left) ∧
      ∀ σ : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.range σ.left ⊆ U →
        MMP.IsPureDimensional (pullback f.left ((toUnit Y ≫ σ) • h).left)
            ((dX + dY : ℤ) - dP) := by
  obtain ⟨U, hU, hσU⟩ := exists_dense_forall_topologicalKrullDimAt k G P f h hdX hdY hdP
  refine ⟨U, hU, fun σ hσ => ?_⟩
  rcases hσU σ hσ with he | ⟨hle, hd⟩
  · exact MMP.isPureDimensional_of_isEmpty _
  · have : LocallyOfFiniteType (((toUnit Y ≫ σ) • h).left ≫ P.hom) := by
      rw [Over.w]; infer_instance
    have hg : LocallyOfFiniteType ((toUnit Y ≫ σ) • h).left :=
      locallyOfFiniteType_of_comp _ P.hom
    have : LocallyOfFiniteType (pullback.fst f.left ((toUnit Y ≫ σ) • h).left) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip hg
    have := isPureDimensional_of_forall_topologicalKrullDimAt k
      (pullback.fst f.left ((toUnit Y ≫ σ) • h).left ≫ X.hom) _ hd
    convert this using 1
    push_cast [hle]
    ring

/-- The smoothness half: for smooth `X` and `Y`, generic translates are smooth, by removing
the closure of the image in `G` of the critical locus of the projection from the incidence
scheme. -/
private theorem exists_dense_smooth (f : X ⟶ P) (h : Y ⟶ P) [Smooth X.hom] [Smooth Y.hom] :
    ∃ U : G.left.Opens, Dense (U : Set G.left) ∧
      ∀ σ : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.range σ.left ⊆ U →
        Smooth (pullback.fst f.left ((toUnit Y ≫ σ) • h).left ≫ X.hom) := by
  have : IrreducibleSpace G.left := irreducibleSpace_of_connectedSpace G
  have : IsIntegral G.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsNoetherian G.left := isNoetherian_of_over G.hom
  have : QuasiSeparatedSpace G.left := NoetherianSpace.to_quasiSeparatedSpace
  -- the incidence scheme is smooth over `k`
  obtain ⟨_, _⟩ := smooth_quasiCompact_incidence_fst k G P f h
  have : Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))
  have : QuasiCompact (X ⊗ Y).hom :=
    inferInstanceAs (QuasiCompact (pullback.fst X.hom Y.hom ≫ X.hom))
  have hZ : Smooth (incidence G f h).hom := by
    rw [← Over.w (pullback.fst (pairMap f h) (ModObj.leftSMul G P))]; infer_instance
  have : QuasiCompact (incidence G f h).hom := by
    rw [← Over.w (pullback.fst (pairMap f h) (ModObj.leftSMul G P))]; infer_instance
  have : IsNoetherian (incidence G f h).left := isNoetherian_of_over (incidence G f h).hom
  -- the projection to `G`
  have hqw : (incidenceToG G f h).left ≫ G.hom = (incidence G f h).hom := Over.w _
  have : LocallyOfFiniteType ((incidenceToG G f h).left ≫ G.hom) := by rw [hqw]; infer_instance
  have : LocallyOfFiniteType (incidenceToG G f h).left :=
    locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((incidenceToG G f h).left ≫ G.hom) := by rw [hqw]; infer_instance
  have : QuasiCompact (incidenceToG G f h).left := QuasiCompact.of_comp _ G.hom
  -- the critical-locus argument at the generic point of `G`
  obtain ⟨U, hgU, hU⟩ := exists_opens_subset_smoothLocus (incidenceToG G f h).left
    (genericPoint G.left) (genericPoint_spec _) (Field.toIsField G.left.functionField)
    (charZero_residueField G.hom _)
    ((MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk _).1 hZ)
  refine ⟨U, U.2.dense ⟨_, hgU⟩, fun σ hσ => ?_⟩
  set q := (incidenceToG G f h).left with hq
  have hres : Smooth (q ∣_ U) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← smoothLocus_comp_isOpenImmersion _ U.ι,
      smoothLocus_eq_of_eq (morphismRestrict_ι q U), ← Scheme.Hom.preimage_smoothLocus_eq]
    refine top_le_iff.mp fun x _ => hU ?_
    exact x.2
  -- `σ` factors through `U`
  let σ' : Spec (.of k) ⟶ U := IsOpenImmersion.lift U.ι σ.left (by rw [U.range_ι]; exact hσ)
  have hσ' : σ' ≫ U.ι = σ.left := IsOpenImmersion.lift_fac _ _ _
  have hbig : IsPullback (translToIncidence f h σ).left (toUnit (transl f h σ)).left q
      (σ' ≫ U.ι) := by
    rw [hσ']; exact (isPullback_translToIncidence f h σ).map (Over.forget _)
  have hsm : Smooth (toUnit (transl f h σ)).left :=
    MorphismProperty.of_isPullback (hbig.of_right' (isPullback_morphismRestrict q U).flip) hres
  -- the translated fibre product in `Over (Spec k)` is the one of the statement
  have hF : IsPullback (pullback.fst f ((toUnit Y ≫ σ) • h)).left
      (pullback.snd f ((toUnit Y ≫ σ) • h)).left f.left ((toUnit Y ≫ σ) • h).left :=
    (IsPullback.of_hasPullback f ((toUnit Y ≫ σ) • h)).map (Over.forget _)
  have key : pullback.fst f.left ((toUnit Y ≫ σ) • h).left ≫ X.hom =
      hF.isoPullback.inv ≫ (toUnit (transl f h σ)).left := by
    rw [show (toUnit (transl f h σ)).left = (transl f h σ).hom from rfl,
      ← Over.w (pullback.fst f ((toUnit Y ≫ σ) • h)), ← Category.assoc, hF.isoPullback_inv_fst]
  rw [key]
  infer_instance

end Dimension

/-- **Kleiman's transversality theorem.** Let `G` be a connected algebraic group over an
algebraically closed field `k` of characteristic zero, acting transitively on the `k`-points of a
variety `P`, and let `f : X ⟶ P`, `h : Y ⟶ P` be morphisms from varieties of dimensions `dX`,
`dY`, with `dim P = dP`. There is a dense open `U ⊆ G` such that for every `k`-point `σ` of `G`
lying in `U`, the fibre product `X ×_{f, P, σ • h} Y` is pure of dimension `dX + dY - dP`
(possibly empty), and it is smooth over `k` whenever `X` and `Y` are. -/
@[mmp "lem_mmp_foundation_homogeneous_transversality"]
public theorem exists_dense_isPureDimensional_pullback_smul
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsReduced G.left] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [ConnectedSpace G.left]
    (P : Over (Spec (.of k))) [ModObj G P] [IsVariety k P.hom]
    [MulAction.IsPretransitive (𝟙_ (Over (Spec (.of k))) ⟶ G) (𝟙_ (Over (Spec (.of k))) ⟶ P)]
    {X Y : Over (Spec (.of k))} [IsVariety k X.hom] [IsVariety k Y.hom]
    (f : X ⟶ P) (h : Y ⟶ P) {dX dY dP : ℕ}
    (hdX : topologicalKrullDim X.left = dX) (hdY : topologicalKrullDim Y.left = dY)
    (hdP : topologicalKrullDim P.left = dP) :
    ∃ U : G.left.Opens, Dense (U : Set G.left) ∧
      ∀ σ : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.range σ.left ⊆ U →
        MMP.IsPureDimensional (pullback f.left ((toUnit Y ≫ σ) • h).left)
            ((dX + dY : ℤ) - dP) ∧
          (Smooth X.hom → Smooth Y.hom →
            Smooth (pullback.fst f.left ((toUnit Y ≫ σ) • h).left ≫ X.hom)) := by
  obtain ⟨U₁, hU₁, hσ₁⟩ := exists_dense_isPureDimensional k G P f h hdX hdY hdP
  by_cases hs : Smooth X.hom ∧ Smooth Y.hom
  · obtain ⟨hX, hY⟩ := hs
    obtain ⟨U₂, hU₂, hσ₂⟩ := exists_dense_smooth k G P f h
    refine ⟨U₁ ⊓ U₂, hU₁.inter_of_isOpen_left hU₂ U₁.isOpen, fun σ hσ => ?_⟩
    exact ⟨hσ₁ σ (hσ.trans fun _ hx => hx.1), fun _ _ => hσ₂ σ (hσ.trans fun _ hx => hx.2)⟩
  · exact ⟨U₁, hU₁, fun σ hσ => ⟨hσ₁ σ hσ, fun hX hY => (hs ⟨hX, hY⟩).elim⟩⟩

/-- **Kleiman–Bertini.** Let `G` be a connected algebraic group over an algebraically closed
field `k` of characteristic zero, acting transitively on the `k`-points of a variety `P`, and let
`f : X ⟶ P`, `g : Y ⟶ P` be morphisms from smooth varieties of dimensions `dX`, `dY`, with
`dim P = dP`. There is a dense open `U ⊆ G` such that for every `k`-point `σ` of `G` lying in
`U`, the fibre product `X ×_{f, P, σ • g} Y` is smooth over `k` and pure of dimension
`dX + dY - dP` (possibly empty). -/
@[mmp "lem_mmp_foundation_km_kleiman_bertini"]
public theorem exists_dense_smooth_isPureDimensional_pullback_smul
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsReduced G.left] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [ConnectedSpace G.left]
    (P : Over (Spec (.of k))) [ModObj G P] [IsVariety k P.hom]
    [MulAction.IsPretransitive (𝟙_ (Over (Spec (.of k))) ⟶ G) (𝟙_ (Over (Spec (.of k))) ⟶ P)]
    {X Y : Over (Spec (.of k))} [IsVariety k X.hom] [IsVariety k Y.hom]
    [Smooth X.hom] [Smooth Y.hom]
    (f : X ⟶ P) (g : Y ⟶ P) {dX dY dP : ℕ}
    (hdX : topologicalKrullDim X.left = dX) (hdY : topologicalKrullDim Y.left = dY)
    (hdP : topologicalKrullDim P.left = dP) :
    ∃ U : G.left.Opens, Dense (U : Set G.left) ∧
      ∀ σ : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.range σ.left ⊆ U →
        Smooth (pullback.fst f.left ((toUnit Y ≫ σ) • g).left ≫ X.hom) ∧
          MMP.IsPureDimensional (pullback f.left ((toUnit Y ≫ σ) • g).left)
            ((dX + dY : ℤ) - dP) := by
  obtain ⟨U, hU, hσ⟩ :=
    MMP.Foundations.exists_dense_isPureDimensional_pullback_smul k G P f g hdX hdY hdP
  exact ⟨U, hU, fun σ hσU => ⟨(hσ σ hσU).2 ‹_› ‹_›, (hσ σ hσU).1⟩⟩

end Transversality

end MMP.Foundations

namespace MMP.Foundation

section HilbertPolynomial

open CategoryTheory AlgebraicGeometry Filter AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff
  MMP.isInvertibleModule_pullback_twistingSheaf

/-- The intersection numbers of an integral closed subscheme `V` of a proper `k`-scheme are those
of the identity of `V` against the pulled-back modules: [Stacks, Tag 0BET] for
`V.subschemeι`, whose kernel is `V`. -/
private lemma intersectionNumber_id_pullback_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (V : X.IdealSheafData) [IsIntegral V.subscheme] {d : ℕ}
    (hd : topologicalKrullDim V.subscheme = d) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    intersectionNumber k (V.subschemeι ≫ f) (𝟙 V.subscheme) d hd.le
        (fun q => (Scheme.Modules.pullback V.subschemeι).obj (L q)) =
      intersectionNumber k f V.subschemeι d hd.le L := by
  have hker : topologicalKrullDim V.subschemeι.ker.subscheme ≤ d := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hd.le
  refine (intersectionNumber_subschemeι_ker_eq k f V.subschemeι d hd hker L).trans ?_
  have key : ∀ (J : X.IdealSheafData) (_ : J = V) (h : topologicalKrullDim J.subscheme ≤ d),
      intersectionNumber k f J.subschemeι d h L =
        intersectionNumber k f V.subschemeι d hd.le L := by
    rintro J rfl h
    rfl
  exact key _ (Scheme.IdealSheafData.ker_subschemeι V) hker

/-- **Hilbert polynomial of a projective variety.** Let `Y ⊆ ℙⁿ_K` be an integral closed
subscheme of dimension `d` over a field `K`, with homogeneous ideal `I(Y) ⊆ S = K[T₀, …, Tₙ]`.
Then its degree `deg Y = (𝒪(1)^d · Y)` is positive, and there is `P ∈ ℚ[t]` of degree `d` with
leading coefficient `deg Y / d!` such that `dim_K (S ⧸ I(Y))_t = P(t)` for all large `t`. -/
@[mmp "lem_mmp_foundation_km2c_homogeneous_hilbert_polynomial"]
public theorem exists_hilbertPolynomial_subvariety {K : Type u} [Field K] {n : ℕ}
    (V : (AlgebraicGeometry.Proj (polyGrading K n)).IdealSheafData) [IsIntegral V.subscheme]
    {d : ℕ} (hd : topologicalKrullDim V.subscheme = d) :
    0 < degreeWithRespectTo K (projToSpecCoeff K n) V.subschemeι d hd
        (twistingSheaf (polyGrading K n) 1) (MMP.isAmple_twistingSheaf_one_polyGrading K n) ∧
      ∃ P : Polynomial ℚ, P.natDegree = d ∧
        P.leadingCoeff = (degreeWithRespectTo K (projToSpecCoeff K n) V.subschemeι d hd
          (twistingSheaf (polyGrading K n) 1) (MMP.isAmple_twistingSheaf_one_polyGrading K n) : ℚ) /
            d.factorial ∧
        ∀ᶠ t : ℕ in atTop,
          (Module.finrank K ((polyGrading K n t).map
            (Ideal.Quotient.mkₐ K (ProjectiveSpectrum.vanishingIdeal
              (V.support : Set (AlgebraicGeometry.Proj (polyGrading K n)))).toIdeal).toLinearMap) :
            ℚ) = P.eval (t : ℚ) := by
  set deg := degreeWithRespectTo K (projToSpecCoeff K n) V.subschemeι d hd
    (twistingSheaf (polyGrading K n) 1) (MMP.isAmple_twistingSheaf_one_polyGrading K n)
  have hpos : 0 < deg := degreeWithRespectTo_pos K _ _ d hd _ _
  have hamp := MMP.isAmple_pullback_twistingSheaf_one K n V.subschemeι
  obtain ⟨-, Q, hQ, hRR⟩ := asymptotic_riemann_roch K (V.subschemeι ≫ projToSpecCoeff K n) d hd
    ((Scheme.Modules.pullback V.subschemeι).obj (twistingSheaf (polyGrading K n) 1)) hamp
  have hdeg : degreeWithRespectTo K (V.subschemeι ≫ projToSpecCoeff K n) (𝟙 V.subscheme) d hd
      ((Scheme.Modules.pullback V.subschemeι).obj (twistingSheaf (polyGrading K n) 1)) hamp =
      deg :=
    intersectionNumber_id_pullback_eq (projToSpecCoeff K n) V hd
      (fun _ => twistingSheaf (polyGrading K n) 1)
  rw [hdeg] at hRR
  set a : ℚ := (deg : ℚ) / d.factorial
  have ha : a ≠ 0 := div_ne_zero (by exact_mod_cast hpos.ne') (by positivity)
  have hlt : Q.degree < (Polynomial.C a * Polynomial.X ^ d).degree := by
    rwa [Polynomial.degree_C_mul_X_pow d ha]
  refine ⟨hpos, Q + Polynomial.C a * Polynomial.X ^ d, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_add_eq_right_of_degree_lt hlt, Polynomial.natDegree_C_mul_X_pow d a ha]
  · rw [Polynomial.leadingCoeff_add_of_degree_lt hlt, Polynomial.leadingCoeff_C_mul_X_pow]
  · filter_upwards [hRR,
      MMP.eventually_finrank_globalSections_tensorPower_eq_finrank_homogeneousQuotient K n V]
      with t h1 h2
    rw [← h2, h1]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    ring

end HilbertPolynomial

end MMP.Foundation

namespace MMP.Mori

section BlochGiesekerGloballyGenerated

open CategoryTheory Limits AlgebraicGeometry Topology MMP.Intersection
  MMP.Intersection.Scheme.Modules

/-- The image of an irreducible component under an open embedding with closed range is an
irreducible component, of the same dimension. -/
private theorem image_mem_irreducibleComponents_of_isOpenEmbedding {A B : Type*}
    [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hf : IsOpenEmbedding f) (hc : IsClosed (Set.range f))
    {C : Set A} (hC : C ∈ irreducibleComponents A) :
    f '' C ∈ irreducibleComponents B ∧ topologicalKrullDim (f '' C) = topologicalKrullDim C := by
  have hirr : IsIrreducible (f '' C) := hC.1.image f hf.continuous.continuousOn
  obtain ⟨W, hW, hCW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  have hne : (W ∩ Set.range f).Nonempty := by
    obtain ⟨x, hx⟩ := hC.1.nonempty
    exact ⟨f x, hCW ⟨x, hx, rfl⟩, x, rfl⟩
  have hpre := preimage_mem_irreducibleComponents hW hf hne
  have hCeq : C = f ⁻¹' W :=
    (Set.image_subset_iff.mp hCW).antisymm (hC.2 hpre.1 (Set.image_subset_iff.mp hCW))
  have hWsub : W ⊆ Set.range f := by
    have hcl := isClosed_of_mem_irreducibleComponents W hW
    have := subset_closure_inter_of_isPreirreducible_of_isOpen hW.1.2 hf.isOpen_range hne
    exact this.trans (closure_minimal Set.inter_subset_right hc)
  have himg : f '' C = W := by
    rw [hCeq, Set.image_preimage_eq_of_subset hWsub]
  refine ⟨himg ▸ hW, ?_⟩
  have he : IsEmbedding (f ∘ (Subtype.val : C → A)) := hf.isEmbedding.comp IsEmbedding.subtypeVal
  have h1 := (IsHomeomorph.topologicalKrullDim_eq _ he.toHomeomorph.isHomeomorph)
  rw [h1, Set.range_comp, Subtype.range_coe]

/-- On a scheme whose local rings are domains, two irreducible components through a point
coincide: both are the closure of the irreducible set of generalizations of the point. -/
private theorem eq_of_mem_irreducibleComponents_of_isDomain_stalk.{u} {Z : Scheme.{u}}
    (hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) {C C' : Set Z}
    (hC : C ∈ irreducibleComponents Z) (hC' : C' ∈ irreducibleComponents Z) {x : Z}
    (hx : x ∈ C) (hx' : x ∈ C') : C = C' := by
  haveI := hdom x
  have hS : IsIrreducible (Set.range (Z.fromSpecStalk x)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (Z.fromSpecStalk x).continuous.continuousOn
  have key : ∀ D ∈ irreducibleComponents Z, x ∈ D →
      D = closure (Set.range (Z.fromSpecStalk x)) := by
    intro D hD hxD
    have hcl := isClosed_of_mem_irreducibleComponents D hD
    obtain hgen := hD.1.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hgen
    have hη : hD.1.genericPoint ∈ Set.range (Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hgen.specializes hxD
    have hsub : D ⊆ closure (Set.range (Z.fromSpecStalk x)) := by
      rw [← hgen.def]
      exact closure_mono (Set.singleton_subset_iff.mpr hη)
    exact hsub.antisymm (hD.2 hS.closure hsub)
  rw [key C hC hx, key C' hC' hx']

/-- On a quasi-compact scheme smooth over a field, every irreducible component is open. -/
private theorem isOpen_of_mem_irreducibleComponents_of_smooth.{u} {k : Type u} [Field k]
    {Z : Scheme.{u}}
    (s : Z ⟶ Spec (.of k)) [Smooth s] [QuasiCompact s] {C : Set Z}
    (hC : C ∈ irreducibleComponents Z) : IsOpen C := by
  classical
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian Z := ⟨⟩
  have hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x =>
    haveI := isRegularLocalRing_stalk_of_smooth_over_field s x
    IsRegularLocalRing.isDomain _
  have hfin : (irreducibleComponents Z).Finite := finite_irreducibleComponents_of_isNoetherian
  have : Cᶜ = ⋃ C' ∈ {C' ∈ irreducibleComponents Z | C' ≠ C}, C' := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨fun hx => ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x,
      fun h => hx (h ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩, ?_⟩
    rintro ⟨C', ⟨hC', hne⟩, hxC'⟩ hx
    exact hne (eq_of_mem_irreducibleComponents_of_isDomain_stalk hdom hC' hC hxC' hx)
  rw [← isClosed_compl_iff, this]
  exact (hfin.subset fun _ h => h.1).isClosed_biUnion fun C' h =>
    isClosed_of_mem_irreducibleComponents C' h.1

/-- A scheme smooth over a field is reduced: its local rings are regular, hence domains. -/
private theorem isReduced_of_smooth.{u} {k : Type u} [Field k] {Z : Scheme.{u}}
    (s : Z ⟶ Spec (.of k)) [Smooth s] : IsReduced Z := by
  haveI : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x =>
    haveI := isRegularLocalRing_stalk_of_smooth_over_field s x
    haveI := IsRegularLocalRing.isDomain (Z.presheaf.stalk x)
    isReduced_of_noZeroDivisors
  exact isReduced_of_isReduced_stalk _

/-- **An irreducible component of a smooth scheme is an integral open and closed subscheme.** On a
scheme smooth and quasi-compact over a field, an irreducible component `C` is open
(`isOpen_of_mem_irreducibleComponents_of_smooth`), and the open subscheme on it is integral, its
inclusion a closed immersion. -/
private theorem exists_opens_isIntegral_of_mem_irreducibleComponents.{u} {k : Type u} [Field k]
    {Z : Scheme.{u}} (s : Z ⟶ Spec (.of k)) [Smooth s] [QuasiCompact s] {C : Set Z}
    (hC : C ∈ irreducibleComponents Z) :
    ∃ U : Z.Opens, (U : Set Z) = C ∧ IsIntegral U.toScheme ∧ IsClosedImmersion U.ι := by
  let U : Z.Opens := ⟨C, isOpen_of_mem_irreducibleComponents_of_smooth s hC⟩
  haveI := isReduced_of_smooth s
  haveI : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hC.1
  exact ⟨U, rfl, isIntegral_of_irreducibleSpace_of_isReduced _,
    IsClosedImmersion.of_isPreimmersion _ (U.range_ι ▸ isClosed_of_mem_irreducibleComponents C hC)⟩

/-- **A component of a finite cover maps onto the base.** If `X₁` is smooth
over `k` and `q : X₁ ⟶ X` is finite and surjective onto a variety, then `X₁` has finitely many
connected components, each open and closed and integral (the local rings of a smooth scheme are
domains); their images are closed and cover the irreducible `X`, so one of them maps onto `X`. -/
private theorem exists_isVariety_isOpenImmersion_isClosedImmersion.{u} (k : Type u) [Field k]
    {X X₁ : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX] (q : X₁ ⟶ X)
    [IsFinite q] [Surjective q] [Smooth (q ≫ sX)] :
    ∃ (Y : Scheme.{u}) (i : Y ⟶ X₁), IsOpenImmersion i ∧ IsClosedImmersion i ∧
      MMP.Mori.IsVariety k (i ≫ q ≫ sX) ∧ Surjective (i ≫ q) := by
  classical
  haveI : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  haveI : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  haveI : IsNoetherian X₁ := ⟨⟩
  have hfin : (irreducibleComponents X₁).Finite := finite_irreducibleComponents_of_isNoetherian
  -- one component maps onto `X`
  obtain ⟨C, hC, hCsurj⟩ : ∃ C ∈ irreducibleComponents X₁, Set.univ ⊆ q '' C := by
    have hirr : IsIrreducible (Set.univ : Set X) := IrreducibleSpace.isIrreducible_univ X
    obtain ⟨z, hz, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr
      (hfin.toFinset.image fun C => q '' C) (by
        intro z hz
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hz
        exact q.isClosedMap _ (isClosed_of_mem_irreducibleComponents C (hfin.mem_toFinset.mp hC)))
      (by
        intro x _
        obtain ⟨y, rfl⟩ := q.surjective x
        refine Set.mem_sUnion.mpr
          ⟨q '' irreducibleComponent y, ?_, y, mem_irreducibleComponent, rfl⟩
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr
          (irreducibleComponent_mem_irreducibleComponents y), rfl⟩))
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨C, hfin.mem_toFinset.mp hC, hsub⟩
  obtain ⟨U, rfl, hU, hUc⟩ := exists_opens_isIntegral_of_mem_irreducibleComponents (q ≫ sX) hC
  refine ⟨U.toScheme, U.ι, inferInstance, hUc, { toIsIntegral := hU }, ⟨fun x => ?_⟩⟩
  obtain ⟨y, hy, rfl⟩ := hCsurj (Set.mem_univ x)
  exact ⟨⟨y, hy⟩, rfl⟩

/-- **Effective Cartier divisors pull back along a surjection of integral schemes.** A local
equation `f` of `F` is nonzero at the generic point of `X`, which is the
image of the generic point of `Y`; so `g^♯ f` is nonzero, hence a nonzerodivisor on the integral
`Y`, and it generates the ideal of `g⁻¹ F` locally. -/
private theorem isEffectiveCartierDivisor_comap_of_surjective.{u} {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [Surjective g] (F : X.IdealSheafData)
    [hF : Stacks.Divisors.IsEffectiveCartierDivisor F] :
    Stacks.Divisors.IsEffectiveCartierDivisor (F.comap g) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun y => ?_
  obtain ⟨W, hyW, -, t, ht, hgen⟩ :=
    Stacks.Blowup.exists_affineOpens_ideal_eq_span_le F hF (g y) ⊤ trivial
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ g ⁻¹ᵁ (W : X.Opens) from hyW) (g ⁻¹ᵁ (W : X.Opens)).isOpen
  have hVW : (V : Y.Opens) ≤ g ⁻¹ᵁ (W : X.Opens) := hVsub
  refine ⟨V, hV, hyV, (g.appLE W.1 V hVW).hom t,
    ?_, Stacks.IdealSheaf.ideal_comap_eq_span F g W ⟨V, hV⟩ hVW hgen⟩
  haveI : Nonempty (V : Y.Opens) := ⟨⟨y, hyV⟩⟩
  refine IsRegular.of_ne_zero' ?_
  intro h0
  have hb := Scheme.basicOpen_appLE g V W.1 hVW t
  rw [h0, Scheme.basicOpen_zero] at hb
  haveI : Nonempty (W.1 : X.Opens) := ⟨⟨g y, hyW⟩⟩
  have hne : (X.basicOpen t : Set X).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    apply ht.ne_zero
    rw [← AlgebraicGeometry.basicOpen_eq_bot_iff]
    exact TopologicalSpace.Opens.coe_eq_empty.mp hc
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y', rfl⟩ := g.surjective x
  have hne' : ((V : Y.Opens) ⊓ g ⁻¹ᵁ (X.basicOpen t) : Set Y).Nonempty :=
    (IrreducibleSpace.isIrreducible_univ Y).2 _ _ V.isOpen (g ⁻¹ᵁ (X.basicOpen t)).isOpen
      ⟨y, trivial, hyV⟩ ⟨y', trivial, hx⟩ |>.mono fun _ h => h.2
  obtain ⟨z, hz⟩ := hne'
  have : z ∈ ((V ⊓ g ⁻¹ᵁ X.basicOpen t : Y.Opens) : Set Y) := hz
  rw [← hb] at this
  exact this

/-- A scheme quasi-compact and locally of finite type over a field, and non-empty, has
dimension a natural number. -/
private theorem exists_topologicalKrullDim_eq_natCast.{u} (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have h2 : topologicalKrullDim X ≠ ⊥ := by
    rw [Ne, topologicalKrullDim, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  generalize topologicalKrullDim X = v at h1 h2
  induction v using WithBot.recBotCoe with
  | bot => exact absurd rfl h2
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe n => exact ⟨n, rfl⟩

/-- Pure dimension passes along an immersion that is both open and closed. -/
private theorem isPureDimensional_of_isOpenImmersion_of_isClosedImmersion.{u} {Y Z : Scheme.{u}}
    (i : Y ⟶ Z) [IsOpenImmersion i] [IsClosedImmersion i] {d : ℤ}
    (hZ : MMP.IsPureDimensional Z d) : MMP.IsPureDimensional Y d := by
  intro C hC
  obtain ⟨hW, hdim⟩ := image_mem_irreducibleComponents_of_isOpenEmbedding i.isOpenEmbedding
    i.isClosedEmbedding.isClosed_range hC
  obtain ⟨n, hn, hd⟩ := hZ _ hW
  exact ⟨n, hn, hdim.symm.trans hd⟩

/-- Smoothness of a closed subscheme restricts to its inverse image along an open immersion. -/
private theorem smooth_comap_of_isOpenImmersion.{u} {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsOpenImmersion i]
    (s : Z ⟶ Spec (.of k)) (G : Z.IdealSheafData) (hs : Smooth (G.subschemeι ≫ s)) :
    Smooth ((G.comap i).subschemeι ≫ i ≫ s) := by
  have hcomp : (G.comap i).subschemeι ≫ i ≫ s =
      (G.comapIso i).hom ≫ pullback.snd i G.subschemeι ≫ G.subschemeι ≫ s := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst_assoc, pullback.condition_assoc]
  rw [hcomp]
  infer_instance

/-- Pure dimension `n - |J|` of a scheme, as the snc criterion phrases it. -/
private theorem forall_topologicalKrullDim_add_card_of_isPureDimensional.{u} {Z : Scheme.{u}}
    (n c : ℕ) (hZ : MMP.IsPureDimensional Z ((n : ℤ) - c)) :
    ∀ C ∈ irreducibleComponents (Set.univ : Set Z), topologicalKrullDim C + c = n := by
  intro C hC
  let e := Homeomorph.Set.univ Z
  obtain ⟨hW, hdim⟩ := image_mem_irreducibleComponents_of_isOpenEmbedding e.isOpenEmbedding
    (by rw [e.range_coe]; exact isClosed_univ) hC
  obtain ⟨n', hn', hd⟩ := hZ _ hW
  rw [← hdim, hd]
  have : n' + c = n := by omega
  rw [← this]
  push_cast
  rfl

/-- Pulling back the `m`-th tensor power of an invertible sheaf is the `m`-th tensor power of the
pullback. -/
private theorem nonempty_pullback_tensorPow_iso.{u} {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback g).obj (tensorPow A m) ≅
      tensorPow ((Scheme.Modules.pullback g).obj A) m) := by
  obtain ⟨tA⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X A m
  obtain ⟨tA'⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule Y
    ((Scheme.Modules.pullback g).obj A) m
  exact ⟨(Scheme.Modules.pullback g).mapIso tA ≪≫
    Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso g A m ≪≫
    tA'.symm⟩

section HyperplaneForms

/-! ### Zero schemes of linear forms on `ℙ^ι_k` -/

universe v

attribute [local instance] MvPolynomial.gradedAlgebra ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.AlgebraicGeometry.ProjStalkGlobalSections

variable (k : Type v) [Field k] (ι : Type v)

/-- `k[xᵢ]` is generated in degree one. -/
private theorem adjoin_one_eq_top : Algebra.adjoin (MvPolynomial.homogeneousSubmodule ι k 0)
    ((MvPolynomial.homogeneousSubmodule ι k 1 : Set (MvPolynomial ι k))) = ⊤ :=
  MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top ι k

/-- `𝒪(1)` on `ℙ^ι_k` is invertible. -/
private instance isInvertible_twistingSheafModule_one :
    SheafOfModules.IsInvertible (ProjSpace k ι).sheaf.obj (ProjSpace k ι).ringCatSheaf.property
      (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ)) :=
  Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.isInvertibleModule_twistingSheafOne _
    (adjoin_one_eq_top k ι)

/-- The hyperplane `{ℓ = 0}` of a linear form `ℓ`: the zero scheme of the section `ℓ` of `𝒪(1)`. -/
private noncomputable def formZero (ℓ : MvPolynomial.homogeneousSubmodule ι k 1) :
    (ProjSpace k ι).IdealSheafData :=
  Stacks.Divisors.zeroScheme (ProjSpace k ι)
    (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ))
    (degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ℓ)

variable {k ι}

private theorem app_top_apply_eq {X : Scheme.{v}} {M N : X.Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    φ.app ⊤ x = φ.val.app (Opposite.op ⊤) x := rfl

section ProjMap

variable (ψ : MvPolynomial.homogeneousSubmodule ι k →+*ᵍ MvPolynomial.homogeneousSubmodule ι k)
  (hψ : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι k) ≤
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι k)).map ψ)
  (hsurj : Function.Surjective ψ) (ℓ : MvPolynomial.homogeneousSubmodule ι k 1)

private theorem pullbackTwistIso_pullbackSection :
    (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso ψ hψ hsurj
      (adjoin_one_eq_top k ι) ((1 : ℕ) : ℤ)).hom.val.app (Opposite.op ⊤)
        (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection (Proj.map ψ hψ)
          (twistingSheaf (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ))
          (degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ℓ)) =
      degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ⟨ψ ℓ, ψ.map_mem ℓ.2⟩ :=
  Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso_degreeSection
    ψ hψ hsurj (adjoin_one_eq_top k ι) 1 ℓ

private theorem pullbackGlobalSections_projMap_eq :
    pullbackGlobalSections (Proj.map ψ hψ)
          (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ))
          (degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ℓ) =
     Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection (Proj.map ψ hψ)
          (twistingSheaf (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ))
          (degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ℓ) :=
  AlgebraicGeometry.pullbackGlobalSections_apply _ _ _

private theorem pullbackTwistIso_pullbackGlobalSections :
    (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso ψ hψ hsurj
      (adjoin_one_eq_top k ι) ((1 : ℕ) : ℤ)).hom.app ⊤
        (pullbackGlobalSections (Proj.map ψ hψ)
          (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ))
          (degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ℓ)) =
      degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ⟨ψ ℓ, ψ.map_mem ℓ.2⟩ :=
  (app_top_apply_eq _ _).trans ((congrArg _ (pullbackGlobalSections_projMap_eq ψ hψ ℓ)).trans
    (pullbackTwistIso_pullbackSection ψ hψ hsurj ℓ))

private theorem formZero_comap_projMap_eq_zeroScheme :
    (formZero k ι ℓ).comap (Proj.map ψ hψ) = Stacks.Divisors.zeroScheme _
      ((Scheme.Modules.pullback (Proj.map ψ hψ)).obj
        (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ)))
      (pullbackGlobalSections (Proj.map ψ hψ)
          (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ))
          (degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ℓ)) :=
  (Stacks.Divisors.zeroScheme_pullback _ _ _).symm

include hsurj in
-- The instance is an implicit argument so that it unifies with the one of
-- `formZero_comap_projMap_eq_zeroScheme`; a synthesized one makes the kernel check time out.
private theorem zeroScheme_pullbackGlobalSections_projMap
    {inst : SheafOfModules.IsInvertible (ProjSpace k ι).sheaf.obj
      (ProjSpace k ι).ringCatSheaf.property
      ((Scheme.Modules.pullback (Proj.map ψ hψ)).obj
        (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ)))} :
    Stacks.Divisors.zeroScheme _
      ((Scheme.Modules.pullback (Proj.map ψ hψ)).obj
        (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ)))
      (pullbackGlobalSections (Proj.map ψ hψ)
          (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ))
          (degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ℓ)) =
      formZero k ι ⟨ψ ℓ, ψ.map_mem ℓ.2⟩ :=
  AlgebraicGeometry.zeroScheme_eq_of_iso
    (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso ψ hψ hsurj
      (adjoin_one_eq_top k ι) ((1 : ℕ) : ℤ))
    (pullbackTwistIso_pullbackGlobalSections ψ hψ hsurj ℓ)

include hsurj in
/-- **The inverse image of a hyperplane under a surjective graded substitution.** For `ψ` graded,
surjective and satisfying the irrelevant-ideal condition of `Proj.map`,
`(Proj ψ)⁻¹{ℓ = 0} = {ψ ℓ = 0}`. -/
private theorem formZero_comap_projMap :
    (formZero k ι ℓ).comap (Proj.map ψ hψ) = formZero k ι ⟨ψ ℓ, ψ.map_mem ℓ.2⟩ :=
  (formZero_comap_projMap_eq_zeroScheme ψ hψ ℓ).trans
    (zeroScheme_pullbackGlobalSections_projMap ψ hψ hsurj ℓ)

end ProjMap

/-! ### Pulled-back linear forms are linear combinations of the pulled-back coordinates -/

section Linear

variable {S : Type v} {σ : Type v} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

omit [GradedRing 𝒮] in
private theorem mem_twistGrading_zero {n : ℕ} {x : S} (hx : x ∈ 𝒮 n) :
    x ∈ twistGrading (S := S) 𝒮 (n : ℤ) 0 := by
  simp [twistGrading, integerGrading, homogeneousSubmodule, hx]

private theorem degreeSection_add (n : ℕ) (a b : 𝒮 n) :
    degreeSection 𝒮 n (a + b) = degreeSection 𝒮 n a + degreeSection 𝒮 n b := by
  show degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))
      ⟨((a + b : 𝒮 n) : S), mem_twistGrading_zero 𝒮 (a + b).2⟩ = _
  rw [show (⟨((a + b : 𝒮 n) : S), mem_twistGrading_zero 𝒮 (a + b).2⟩ :
        twistGrading (S := S) 𝒮 (n : ℤ) 0) =
      ⟨(a : S), mem_twistGrading_zero 𝒮 a.2⟩ + ⟨(b : S), mem_twistGrading_zero 𝒮 b.2⟩ from rfl]
  exact map_add (degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))) _ _

private theorem degreeSection_mul_degreeZero (n : ℕ) (z : 𝒮 0) (a b : 𝒮 n)
    (hb : (b : S) = (z : S) * (a : S)) :
    degreeSection 𝒮 n b = degreeZeroRingToGlobalSections 𝒮 z • degreeSection 𝒮 n a := by
  letI : Module ↥(𝒮 0) (twistGlobalSections 𝒮 n) :=
    Module.compHom _ (degreeZeroRingToGlobalSections 𝒮)
  have key : (⟨(b : S), mem_twistGrading_zero 𝒮 b.2⟩ :
        twistGrading (S := S) 𝒮 (n : ℤ) 0) = z • ⟨(a : S), mem_twistGrading_zero 𝒮 a.2⟩ := by
    refine Subtype.ext ?_
    show (b : S) = (z : S) • (a : S)
    rw [hb, smul_eq_mul]
  show degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))
      ⟨(b : S), mem_twistGrading_zero 𝒮 b.2⟩ = _
  rw [key]
  exact LinearMap.map_smul (degreeZeroToGlobalSections 𝒮
    (twistGrading (S := S) 𝒮 (n : ℤ))) z ⟨(a : S), mem_twistGrading_zero 𝒮 a.2⟩

private theorem degreeZeroRingToGlobalSections_val (z : 𝒮 0) (x : ProjectiveSpectrum.top 𝒮) :
    HomogeneousLocalization.val ((degreeZeroRingToGlobalSections 𝒮 z).1 ⟨x, trivial⟩) =
      algebraMap S (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (z : S) := by
  rw [← Proj.stalkIso'_germ 𝒮 ⊤ x trivial (degreeZeroRingToGlobalSections 𝒮 z),
    degreeZeroRingToGlobalSections_stalk]
  change Localization.mk z.1 (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) = _
  exact Localization.mk_algebraMap (A := S) z.1

private theorem degreeZeroRingToGlobalSections_eq_toSpecZero (z : 𝒮 0) :
    degreeZeroRingToGlobalSections 𝒮 z =
      (Proj.toSpecZero 𝒮).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (𝒮 0))).inv.hom z) := by
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  rw [degreeZeroRingToGlobalSections_val 𝒮 z x.1]
  exact (Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val 𝒮 z x.1).symm

end Linear

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **Pulling back a linear form.** For `t : X ⟶ ℙ^ι_k` over `k`, the pulled-back section of the
linear form `∑ⱼ bⱼ xⱼ` is `∑ⱼ bⱼ t^* xⱼ`, for the `k`-module structure of `Γ(X, t^* 𝒪(1))` given
by the structure morphism of `X`. -/
private theorem pullback_degreeSection_linearForm [Fintype ι] {X : Scheme.{v}}
    [X.Over (Spec (.of k))]
    (t : X ⟶ ProjSpace k ι) (ht : t ≫ ProjSpace.toSpec k ι = X ↘ Spec (.of k)) (b : ι → k)
    (hb : ∑ j, MvPolynomial.C (b j) * MvPolynomial.X j ∈ MvPolynomial.homogeneousSubmodule ι k 1)
    (hX : ∀ j, (MvPolynomial.X j : MvPolynomial ι k) ∈ MvPolynomial.homogeneousSubmodule ι k 1) :
    letI := globalSectionsModule (k := k) (X := X)
    pullbackGlobalSections t
        (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ))
        (degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ⟨_, hb⟩) =
      ∑ j, b j • pullbackGlobalSections t
        (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((1 : ℕ) : ℤ))
        (degreeSection (MvPolynomial.homogeneousSubmodule ι k) 1 ⟨MvPolynomial.X j, hX j⟩) := by
  letI := globalSectionsModule (k := k) (X := X)
  set 𝒜 := MvPolynomial.homogeneousSubmodule ι k
  have hCX : ∀ j, MvPolynomial.C (b j) * MvPolynomial.X j ∈ 𝒜 1 := fun j =>
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 ((MvPolynomial.isHomogeneous_X k j).C_mul _)
  let D : 𝒜 1 →+ Γ(twistingSheafModule 𝒜 ((1 : ℕ) : ℤ), ⊤) :=
    AddMonoidHom.mk' (degreeSection 𝒜 1) (degreeSection_add 𝒜 1)
  have hsum : (⟨_, hb⟩ : 𝒜 1) = ∑ j, ⟨_, hCX j⟩ :=
    Subtype.ext (by simp [Submodule.coe_sum])
  rw [hsum, show degreeSection 𝒜 1 (∑ j, ⟨_, hCX j⟩) =
    D (∑ j, ⟨_, hCX j⟩) from rfl, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hz : MvPolynomial.C (b j) ∈ 𝒜 0 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ _)
  have h1 : D ⟨_, hCX j⟩ =
      (@id Γ(ProjSpace k ι, ⊤) (degreeZeroRingToGlobalSections 𝒜 ⟨_, hz⟩)) •
        (@id Γ(twistingSheafModule 𝒜 ((1 : ℕ) : ℤ), ⊤) (degreeSection 𝒜 1 ⟨_, hX j⟩)) :=
    degreeSection_mul_degreeZero 𝒜 1 ⟨_, hz⟩ _ _ rfl
  rw [h1, SectionsEqualizer.pullbackGlobalSections_smul]
  have h2 : t.appTop.hom (degreeZeroRingToGlobalSections 𝒜 ⟨_, hz⟩) = baseRingHom k X (b j) := by
    rw [degreeZeroRingToGlobalSections_eq_toSpecZero]
    change _ = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom (b j)
    rw [← ht, ProjSpace.toSpec, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
    rfl
  exact congrArg (· • _) h2

end HyperplaneForms

/-- The coordinate hyperplane `Hᵢ = {xᵢ = 0}` of `ℙᴺ_k`: the zero scheme of the section `xᵢ` of
`𝒪(1)`. -/
private noncomputable def coordinateHyperplane.{u} (k : Type u) [Field k] (N : ℕ)
    (i : Fin (N + 1)) :
    (ProjSpace k (ULift.{u} (Fin (N + 1)))).IdealSheafData :=
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (N + 1))) (R := k)
  formZero k _ ⟨MvPolynomial.X (ULift.up i),
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X k _)⟩

/-- `p : ℙᴺ ⟶ ℙᴺ` is the `m`-th power map chart by chart: it maps each standard chart
`D₊(xᵢ) ≅ 𝔸ᴺ` onto itself, with preimage the chart, as `Spec` of `yⱼ ↦ yⱼᵐ`. -/
private def IsPowerMapChartwise.{u} (k : Type u) [Field k] (N m : ℕ)
    (p : ProjSpace k (ULift.{u} (Fin (N + 1))) ⟶ ProjSpace k (ULift.{u} (Fin (N + 1)))) : Prop :=
  ∀ i : ULift.{u} (Fin (N + 1)),
    p ⁻¹ᵁ (ProjSpace.affineChart k i).opensRange = (ProjSpace.affineChart k i).opensRange ∧
    (AffineSpace.SpecIso {j // j ≠ i} (.of k)).inv ≫ ProjSpace.affineChart k i ≫ p =
      Spec.map (CommRingCat.ofHom (MvPolynomial.expand (R := CommRingCat.of k)
          (σ := {j // j ≠ i}) m).toRingHom) ≫
        (AffineSpace.SpecIso {j // j ≠ i} (.of k)).inv ≫ ProjSpace.affineChart k i

section Expand

variable {k : Type*} [CommRing k] {σ : Type*} [Finite σ]

/-- `yⱼ ↦ yⱼᵐ` is of finite type. -/
private theorem expand_finiteType (m : ℕ) :
    (MvPolynomial.expand m : MvPolynomial σ k →ₐ[k] MvPolynomial σ k).toRingHom.FiniteType := by
  refine RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C) ?_
  have : (MvPolynomial.expand m : MvPolynomial σ k →ₐ[k] MvPolynomial σ k).toRingHom.comp
      MvPolynomial.C = MvPolynomial.C := by
    ext r
    simp [MvPolynomial.expand_C]
  rw [this]
  rw [← MvPolynomial.algebraMap_eq, RingHom.finiteType_algebraMap]
  infer_instance

/-- `yⱼ ↦ yⱼᵐ` is integral: `yⱼ` is a root of `Tᵐ - yⱼᵐ`. -/
private theorem expand_isIntegral {m : ℕ} (hm : 0 < m) :
    (MvPolynomial.expand m : MvPolynomial σ k →ₐ[k] MvPolynomial σ k).toRingHom.IsIntegral := by
  set f := (MvPolynomial.expand m : MvPolynomial σ k →ₐ[k] MvPolynomial σ k).toRingHom
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : f (MvPolynomial.C a) = MvPolynomial.C a := MvPolynomial.expand_C m a
    rw [← this]
    exact RingHom.isIntegralElem_map f
  | add p q hp hq => exact RingHom.IsIntegralElem.add f hp hq
  | mul_X p i hp =>
    refine RingHom.IsIntegralElem.mul f hp ?_
    refine ⟨Polynomial.X ^ m - Polynomial.C (MvPolynomial.X i), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ hm.ne'
    · simp [Polynomial.eval₂_sub, f, MvPolynomial.expand_X]

/-- `yⱼ ↦ yⱼᵐ` is finite. -/
private theorem expand_finite {m : ℕ} (hm : 0 < m) :
    (MvPolynomial.expand m : MvPolynomial σ k →ₐ[k] MvPolynomial σ k).toRingHom.Finite :=
  RingHom.IsIntegral.to_finite (expand_isIntegral hm) (expand_finiteType m)

end Expand

/-- On each chart, `p` restricted is the power map `Spec (expand m)`, up to isomorphism. -/
private theorem arrow_iso_of_isPowerMapChartwise.{u} (k : Type u) [Field k] (N m : ℕ)
    (p : ProjSpace k (ULift.{u} (Fin (N + 1))) ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (hp : IsPowerMapChartwise k N m p) (i : ULift.{u} (Fin (N + 1))) :
    Nonempty (Arrow.mk (p ∣_ (ProjSpace.affineChart k i).opensRange) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (MvPolynomial.expand (R := CommRingCat.of k)
          (σ := {j // j ≠ i}) m).toRingHom))) := by
  obtain ⟨hpre, hsq⟩ := hp i
  obtain ⟨s, hs⟩ : ∃ s, s = (AffineSpace.SpecIso {j // j ≠ i} (.of k)).inv ≫
      ProjSpace.affineChart k i := ⟨_, rfl⟩
  have hsq' : s ≫ p = Spec.map (CommRingCat.ofHom (MvPolynomial.expand (R := CommRingCat.of k)
      (σ := {j // j ≠ i}) m).toRingHom) ≫ s := by
    subst hs
    simpa only [Category.assoc] using hsq
  haveI : IsOpenImmersion s := by
    rw [hs]
    infer_instance
  have hrange : s.opensRange = (ProjSpace.affineChart k i).opensRange := by
    subst hs; exact Scheme.Hom.opensRange_comp_of_isIso _ _
  let eA := s.isoOpensRange ≪≫ Scheme.isoOfEq _ hrange
  have heA : eA.hom ≫ ((ProjSpace.affineChart k i).opensRange).ι = s := by
    simp [eA]
  have heA' : eA.inv ≫ s = ((ProjSpace.affineChart k i).opensRange).ι := by
    rw [← heA, Iso.inv_hom_id_assoc]
  let eS := Scheme.isoOfEq _ hpre ≪≫ eA.symm
  refine ⟨Arrow.isoMk eS eA.symm ?_⟩
  rw [← cancel_mono s]
  simp only [Arrow.mk_hom, Category.assoc, eS, Iso.trans_hom, Iso.symm_hom, heA']
  rw [← hsq']
  simp only [reassoc_of% heA', Scheme.isoOfEq_hom_ι_assoc, morphismRestrict_ι]

section PowerMap

/-! ### The power map, chart by chart

On the chart `D₊(xᵢ)` the power map is the point of `ℙ^ι` given by `xₗ ↦ (xₗ / xᵢ)ᵐ`; on an
overlap `D₊(xᵢ xⱼ)` the two coordinate vectors differ by the unit `(xᵢ / xⱼ)ᵐ`, so the charts
glue (`Stacks.ProjPoint.glue`). -/

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization Stacks.AlgebraicGeometry.PolyChart

variable {k : Type u} [Field k] {ι : Type u}

private theorem X_mem_one' (i : ι) :
    (MvPolynomial.X i : MvPolynomial ι k) ∈ MvPolynomial.homogeneousSubmodule ι k 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X k i)

variable (k) in
/-- The constants `k → k[x]_{(xᵢ)}`. -/
private noncomputable def awayScalars (i : ι) :
    k →+* Away (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) :=
  (fromZeroRingHom _ _).comp (constHom k (ι := ι))

private theorem chartVar_self (i : ι) : chartVar k i i = 1 := by
  apply val_injective
  simp [chartVar]

/-- **A degree-zero fraction is a polynomial in the chart coordinates.** For `p` homogeneous of
degree `n`, `p / xᵢⁿ = p(xₗ / xᵢ)` in `k[x]_{(xᵢ)}`. -/
private theorem away_mk_eq_eval₂ (j : ι) (m : ℕ) (p : MvPolynomial ι k)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι k (m • 1)) :
    Away.mk (MvPolynomial.homogeneousSubmodule ι k) (X_mem_one' j) m p hp =
      MvPolynomial.eval₂ (awayScalars k j) (chartVar k j) p := by
  apply val_injective
  have hhom : p.IsHomogeneous m := by
    simpa using (MvPolynomial.mem_homogeneousSubmodule _ _).mp hp
  let R := MvPolynomial ι k
  let L := Localization.Away (MvPolynomial.X j : R)
  have hunit : IsUnit (algebraMap R L (MvPolynomial.X j)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let v : L := ↑hunit.unit⁻¹
  have hv : algebraMap R L (MvPolynomial.X j) * v = 1 := hunit.unit.mul_inv
  have hsc : ∀ c : k, (awayScalars k j c).val = algebraMap k L c := by
    intro c
    change (Localization.mk ((constHom k (ι := ι) c : MvPolynomial.homogeneousSubmodule ι k 0) : R)
      1 : L) = _
    rw [Localization.mk_one_eq_algebraMap]
    rfl
  have hch : ∀ i, (chartVar k j i).val = v * algebraMap R L (MvPolynomial.X i) := by
    intro i
    change (Localization.mk (MvPolynomial.X i : R)
      ⟨(MvPolynomial.X j : R) ^ 1, ⟨1, rfl⟩⟩ : L) = _
    rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul, mul_comm v, mul_assoc]
    simp only [pow_one]
    rw [mul_comm v, hv, mul_one]
  have hval : (MvPolynomial.eval₂ (awayScalars k j) (chartVar k j) p).val =
      MvPolynomial.eval₂ (algebraMap k L) (fun i => v * algebraMap R L (MvPolynomial.X i)) p := by
    rw [← HomogeneousLocalization.algebraMap_apply, MvPolynomial.eval₂_comp_left]
    have h1 : (algebraMap (Away (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j)) L).comp
        (awayScalars k j) = algebraMap k L := RingHom.ext hsc
    have h2 : (algebraMap (Away (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j)) L) ∘
        chartVar k j = fun i => v * algebraMap R L (MvPolynomial.X i) := funext hch
    rw [h1, h2]
  rw [hval, hhom.eval₂_const_mul]
  change (Localization.mk p ⟨(MvPolynomial.X j : R) ^ m, ⟨m, rfl⟩⟩ : L) = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  have he : MvPolynomial.eval₂ (algebraMap k L) (fun i => algebraMap R L (MvPolynomial.X i)) p =
      algebraMap R L p := by
    rw [show algebraMap k L = (algebraMap R L).comp MvPolynomial.C from
      IsScalarTower.algebraMap_eq k R L]
    exact (MvPolynomial.eval₂_comp_left (algebraMap R L) MvPolynomial.C MvPolynomial.X p).symm.trans
      (by rw [MvPolynomial.eval₂_eta])
  rw [he]
  change algebraMap R L p = v ^ m * algebraMap R L p * algebraMap R L (MvPolynomial.X j ^ m)
  rw [map_pow, mul_comm (v ^ m), mul_assoc, ← mul_pow, mul_comm v, hv, one_pow, mul_one]

variable (k) in
/-- The substitution `xₗ ↦ (xₗ / xᵢ)ᵐ` into the chart ring `k[x]_{(xᵢ)}`. -/
private noncomputable def powerChartHom (m : ℕ) (i : ι) :
    MvPolynomial ι k →+* Away (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom (awayScalars k i) (fun l => chartVar k i l ^ m)

private theorem powerChartHom_X_self (m : ℕ) (i : ι) :
    powerChartHom k m i (MvPolynomial.X i) = 1 := by
  simp [powerChartHom, chartVar_self]

private theorem isUnit_powerChartHom (m : ℕ) (i : ι) :
    IsUnit (powerChartHom k m i (MvPolynomial.X i)) := by
  rw [powerChartHom_X_self]
  exact isUnit_one

variable (k) in
/-- The power map on the chart `D₊(xᵢ)`: the point `[(xₗ / xᵢ)ᵐ]ₗ` of `ℙ^ι` over `k[x]_{(xᵢ)}`. -/
private noncomputable def powerChart (m : ℕ) (i : ι) :
    Spec (.of (Away (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i))) ⟶
      ProjSpace k ι :=
  Stacks.ProjPoint.point _ (powerChartHom k m i) (MvPolynomial.X i) (X_mem_one' i) one_pos
    (isUnit_powerChartHom m i)

private theorem awayEval_powerChartHom_mk (m : ℕ) (i : ι) (n : ℕ) (a : MvPolynomial ι k)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule ι k (n • 1)) :
    Stacks.ProjPoint.awayEval _ (powerChartHom k m i) (MvPolynomial.X i)
      (isUnit_powerChartHom m i) (Away.mk _ (X_mem_one' i) n a ha) = powerChartHom k m i a := by
  rw [Stacks.ProjPoint.awayEval_mk]
  have h := Stacks.ProjPoint.val_inv_pow_mul_pow (isUnit_powerChartHom (k := k) m i) n
  have h1 : (powerChartHom k m i (MvPolynomial.X i)) ^ n = 1 := by
    rw [powerChartHom_X_self, one_pow]
  rw [h1, mul_one] at h
  rw [h, mul_one]

/-- For `m = 1` the chart point is the chart itself. -/
private theorem powerChart_one (i : ι) :
    powerChart k 1 i = Proj.awayι _ (MvPolynomial.X i) (X_mem_one' i) one_pos := by
  have key : Stacks.ProjPoint.awayEval _ (powerChartHom k 1 i) (MvPolynomial.X i)
      (isUnit_powerChartHom 1 i) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X_mem_one' i) x
    rw [awayEval_powerChartHom_mk, RingHom.id_apply, away_mk_eq_eval₂]
    simp [powerChartHom]
  rw [powerChart, Stacks.ProjPoint.point, key, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp]

/-- On `D₊(xᵢ xⱼ)`: `xₗ xᵢ / (xᵢ xⱼ) = (xᵢ xᵢ / (xᵢ xⱼ)) · (xₗ xⱼ / (xᵢ xⱼ))`. -/
private theorem awayMap_chartVar_eq (i j l : ι) :
    awayMap _ (X_mem_one' i) (mul_comm (MvPolynomial.X i) (MvPolynomial.X j)) (chartVar k j l) =
      awayMap _ (X_mem_one' i) (mul_comm (MvPolynomial.X i) (MvPolynomial.X j))
          (chartVar k j i) *
        awayMap _ (X_mem_one' j)
          (rfl : (MvPolynomial.X i : MvPolynomial ι k) * MvPolynomial.X j = _)
          (chartVar k i l) := by
  apply val_injective
  simp only [chartVar, awayMap_mk, val_mul, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by
    simp
    ring⟩

/-- **The chart points agree on the overlaps**: on `D₊(xᵢ xⱼ)` the coordinate vectors
`((xₗ / xᵢ)ᵐ)ₗ` and `((xₗ / xⱼ)ᵐ)ₗ` differ by the unit `(xᵢ / xⱼ)ᵐ`. -/
private theorem powerChart_compat (m : ℕ) (i j : ι) :
    Spec.map (CommRingCat.ofHom (awayMap _ (X_mem_one' j)
        (rfl : (MvPolynomial.X i : MvPolynomial ι k) * MvPolynomial.X j = _))) ≫
      powerChart k m i =
    Spec.map (CommRingCat.ofHom (awayMap _ (X_mem_one' i)
        (mul_comm (MvPolynomial.X i : MvPolynomial ι k) (MvPolynomial.X j)))) ≫
      powerChart k m j := by
  set f := awayMap (MvPolynomial.homogeneousSubmodule ι k) (X_mem_one' (k := k) j)
    (rfl : (MvPolynomial.X i : MvPolynomial ι k) * MvPolynomial.X j = _) with hf
  set g := awayMap (MvPolynomial.homogeneousSubmodule ι k) (X_mem_one' (k := k) i)
    (mul_comm (MvPolynomial.X i : MvPolynomial ι k) (MvPolynomial.X j)) with hg
  set ν := g (chartVar k j i) with hνdef
  have hS : g.comp (awayScalars k j) = f.comp (awayScalars k i) := by
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, awayScalars, hf, hg, awayMap_fromZeroRingHom]
  have hν : ν * f (chartVar k i j) = 1 := by
    rw [hνdef, hf, hg, ← awayMap_chartVar_eq, chartVar_self, map_one]
  have hψ : f.comp (powerChartHom k m i) =
      MvPolynomial.eval₂Hom (f.comp (awayScalars k i)) (fun l => f (chartVar k i l) ^ m) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun l => ?_)
    · rw [RingHom.comp_apply, powerChartHom, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C,
        RingHom.comp_apply]
    · simp [powerChartHom]
  have hψ' : g.comp (powerChartHom k m j) =
      MvPolynomial.eval₂Hom (f.comp (awayScalars k i))
        (fun l => ν ^ m * f (chartVar k i l) ^ m) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun l => ?_)
    · simp only [RingHom.comp_apply, powerChartHom, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply g, hS]
      rfl
    · simp only [RingHom.comp_apply, powerChartHom, MvPolynomial.eval₂Hom_X', map_pow]
      rw [hνdef, hf, hg, awayMap_chartVar_eq, mul_pow]
  have hu : IsUnit ν := ⟨⟨ν, f (chartVar k i j), hν, (mul_comm _ _).trans hν⟩, rfl⟩
  have hφ : ∀ (n : ℕ) (a : MvPolynomial ι k), a ∈ MvPolynomial.homogeneousSubmodule ι k n →
      g.comp (powerChartHom k m j) a =
        ((hu.pow m).unit : _) ^ n * f.comp (powerChartHom k m i) a := by
    intro n a ha
    rw [hψ, hψ', IsUnit.unit_spec]
    exact ((MvPolynomial.mem_homogeneousSubmodule _ _).1 ha).eval₂Hom_const_mul _ _ _
  have hu1 : IsUnit (f.comp (powerChartHom k m i) (MvPolynomial.X i)) := by
    rw [RingHom.comp_apply, powerChartHom_X_self, map_one]; exact isUnit_one
  have hu' : IsUnit (g.comp (powerChartHom k m j) (MvPolynomial.X i)) := by
    rw [hφ 1 _ (X_mem_one' i)]
    exact ((hu.pow m).unit ^ 1).isUnit.mul hu1
  unfold powerChart
  rw [Stacks.ProjPoint.SpecMap_comp_point, Stacks.ProjPoint.SpecMap_comp_point]
  exact (Stacks.ProjPoint.point_eq_of_scale _ (hu.pow m).unit hφ _ (X_mem_one' i) one_pos _
    hu').trans (Stacks.ProjPoint.point_indep _ _ (X_mem_one' i) (X_mem_one' j) one_pos one_pos _ _)

/-- The irrelevant ideal of `k[xᵢ]` lies in the span of the variables. -/
private theorem irrelevant_le_span_X' :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι k)).toIdeal ≤
      Ideal.span (Set.range fun i : ι => (MvPolynomial.X i : MvPolynomial ι k)) := by
  refine (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr fun d hd f hf => ?_
  show f ∈ Ideal.span (Set.range fun i : ι => (MvPolynomial.X i : MvPolynomial ι k))
  rw [← Set.image_univ]
  change f ∈ Ideal.span (MvPolynomial.X '' Set.univ)
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro e he
  have hdeg := ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hf)
    (MvPolynomial.mem_support_iff.mp he)
  by_contra hcon
  push Not at hcon
  have : e = 0 := Finsupp.ext fun i => by simpa using hcon i (Set.mem_univ i)
  subst this
  simp at hdeg
  omega

variable (k) in
/-- **The `m`-th power map** `[xᵢ] ↦ [xᵢᵐ]` of `ℙ^ι_k`, glued from the chart points. -/
private noncomputable def powerMap (m : ℕ) : ProjSpace k ι ⟶ ProjSpace k ι :=
  Stacks.ProjPoint.glue (MvPolynomial.homogeneousSubmodule ι k)
    (fun i : ι => (MvPolynomial.X i : MvPolynomial ι k)) X_mem_one' (fun _ => one_pos)
    irrelevant_le_span_X' (powerChart k m) (powerChart_compat m)

private theorem awayι_powerMap (m : ℕ) (i : ι) :
    Proj.awayι _ (MvPolynomial.X i) (X_mem_one' i) one_pos ≫ powerMap k m = powerChart k m i :=
  Stacks.ProjPoint.awayι_glue _ _ _ _ _ _ _ i

/-- The power map lies over `k`, chart by chart. -/
private theorem powerChart_toSpec (m : ℕ) (i : ι) :
    powerChart k m i ≫ ProjSpace.toSpec k ι = Spec.map (CommRingCat.ofHom (awayScalars k i)) := by
  rw [powerChart, ProjSpace.toSpec, ← Category.assoc, Stacks.ProjPoint.point_comp_toSpecZero,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  change powerChartHom k m i (MvPolynomial.C a) = awayScalars k i a
  rw [powerChartHom, MvPolynomial.eval₂Hom_C]

/-- The standard affine cover of `ℙ^ι_k` by the charts `D₊(xᵢ)`. -/
private noncomputable abbrev chartCover : (ProjSpace k ι).OpenCover :=
  (Proj.affineOpenCoverOfIrrelevantLESpan _ (fun i : ι => (MvPolynomial.X i : MvPolynomial ι k))
    X_mem_one' (fun _ => one_pos) irrelevant_le_span_X').openCover

private theorem powerMap_toSpec (m : ℕ) :
    powerMap k m ≫ ProjSpace.toSpec k ι = ProjSpace.toSpec k ι := by
  refine (chartCover (k := k) (ι := ι)).hom_ext _ _ fun (i : ι) => ?_
  change Proj.awayι _ (MvPolynomial.X i) (X_mem_one' i) one_pos ≫ _ =
    Proj.awayι _ (MvPolynomial.X i) (X_mem_one' i) one_pos ≫ _
  rw [← Category.assoc, awayι_powerMap, powerChart_toSpec, ← powerChart_one, powerChart_toSpec]

/-- The preimage of `D₊(xᵢ)` on the chart `D₊(xⱼ)` is `D((xᵢ / xⱼ)ᵐ)`. -/
private theorem powerChart_preimage_basicOpen (m : ℕ) (i j : ι) :
    powerChart k m j ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) =
      PrimeSpectrum.basicOpen (chartVar k j i ^ m) := by
  rw [powerChart, Stacks.ProjPoint.point, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ (X_mem_one' j) one_pos (X_mem_one' i) one_pos,
    SpecMap_preimage_basicOpen]
  congr 1
  exact (awayEval_powerChartHom_mk m j 1 _ _).trans (by simp [powerChartHom])

private theorem powerMap_preimage_basicOpen (m : ℕ) (hm : 0 < m) (i : ι) :
    powerMap k m ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) = Proj.basicOpen _ (MvPolynomial.X i) := by
  ext x
  obtain ⟨(j : ι), y, rfl⟩ := (chartCover (k := k) (ι := ι)).exists_eq x
  have h1 : (Proj.awayι _ (MvPolynomial.X j) (X_mem_one' j) one_pos ≫ powerMap k m) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X i) =
      Proj.awayι _ (MvPolynomial.X j) (X_mem_one' j) one_pos ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X i) := by
    rw [awayι_powerMap, ← powerChart_one, powerChart_preimage_basicOpen,
      powerChart_preimage_basicOpen, PrimeSpectrum.basicOpen_pow _ _ hm, pow_one]
  exact SetLike.ext_iff.mp h1 y

end PowerMap

/-- **The power map is chartwise the `m`-th power.** `powerMap` lies over `k`, the preimage of
`D₊(xᵢ)` is `D₊(xᵢ)`, and on the chart `𝔸^{ι ∖ i} ≅ D₊(xᵢ)` it is `Spec` of `yⱼ ↦ yⱼᵐ`: the
chart point of `powerMap` on `D₊(xᵢ)` is `xₗ / xᵢ ↦ (xₗ / xᵢ)ᵐ`. -/
private theorem powerMap_toSpec_and_isPowerMapChartwise.{u} (k : Type u) [Field k] (N m : ℕ)
    (hm : 0 < m) :
    powerMap k (ι := ULift.{u} (Fin (N + 1))) m ≫ ProjSpace.toSpec k _ = ProjSpace.toSpec k _ ∧
      IsPowerMapChartwise k N m (powerMap k m) := by
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (N + 1))) (R := k)
  refine ⟨powerMap_toSpec m, fun i => ⟨?_, ?_⟩⟩
  · rw [ProjSpace.opensRange_affineChart]
    exact powerMap_preimage_basicOpen m hm i
  · simp only [ProjSpace.affineChart, Iso.inv_hom_id_assoc, Category.assoc]
    rw [awayι_powerMap, ← powerChart_one, powerChart, powerChart,
      show (Stacks.AlgebraicGeometry.PolyChart.chartIso k i).toCommRingCatIso.hom =
        CommRingCat.ofHom (Stacks.AlgebraicGeometry.PolyChart.chartIso k i).toRingHom from rfl,
      Stacks.ProjPoint.SpecMap_comp_point, Stacks.ProjPoint.SpecMap_comp_point,
      Stacks.ProjPoint.SpecMap_comp_point]
    refine Stacks.ProjPoint.point_congr_ringHom _ ?_ _ _ _ _ _
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun l => ?_)
    · simp only [RingHom.comp_apply, powerChartHom, MvPolynomial.eval₂Hom_C]
      have : (Stacks.AlgebraicGeometry.PolyChart.chartIso k i).toRingHom (awayScalars k i a) =
          MvPolynomial.C a := by
        have e : (Stacks.AlgebraicGeometry.PolyChart.chartIso k i).symm (MvPolynomial.C a) =
            awayScalars k i a := by
          rw [Stacks.AlgebraicGeometry.PolyChart.chartIso_symm_apply,
            Stacks.AlgebraicGeometry.PolyChart.toAway, MvPolynomial.eval₂Hom_C]
          rfl
        rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← e, RingEquiv.apply_symm_apply]
      rw [this]
      simp
    · simp only [RingHom.comp_apply, powerChartHom, MvPolynomial.eval₂Hom_X', map_pow, pow_one]
      by_cases hl : l = i
      · subst hl
        simp [chartVar_self]
      · have : (Stacks.AlgebraicGeometry.PolyChart.chartIso k i).toRingHom
            (Stacks.AlgebraicGeometry.PolyChart.chartVar k i l) = MvPolynomial.X ⟨l, hl⟩ := by
          have e : (Stacks.AlgebraicGeometry.PolyChart.chartIso k i).symm
              (MvPolynomial.X ⟨l, hl⟩) = Stacks.AlgebraicGeometry.PolyChart.chartVar k i l := by
            rw [Stacks.AlgebraicGeometry.PolyChart.chartIso_symm_apply,
              Stacks.AlgebraicGeometry.PolyChart.toAway, MvPolynomial.eval₂Hom_X']
          rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← e,
            RingEquiv.apply_symm_apply]
        rw [this]
        simp

section PowerMapTwist

/-! ### The power map pulls `𝒪(1)` back to `𝒪(m)`

The hyperplane `{xⱼ = 0}` pulls back under the power map to the zero scheme of the section `xⱼᵐ`
of `𝒪(m)`: on the chart `D₊(xᵢ)` both are cut out by `(xⱼ / xᵢ)ᵐ`. An invertible sheaf is the
invertible sheaf of the zero scheme of a regular section, so `p^* 𝒪(1) ≅ 𝒪(m)`, and
`𝒪(m) ≅ 𝒪(1)^{⊗ m}` since `k[xᵢ]` is generated in degree one. -/

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization ProjectiveSpectrum.Proj

variable {k : Type u} [Field k] {ι : Type u}

/-- Equal morphisms have equal maps on sections, whatever the containments. -/
private theorem appLE_congr_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- `k[x]_{(xᵢ)} ⟶ Γ(D₊(xᵢ))` is bijective. -/
private theorem bijective_awayToSection (i : ι) :
    Function.Bijective
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)).hom := by
  have : IsIso (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)) := by
    rw [← Proj.basicOpenIsoAway_hom _ _ (X_mem_one' i) one_pos]; infer_instance
  exact ConcreteCategory.bijective_of_isIso _

/-- **The power map on the sections of a chart**: on `D₊(xᵢ)` it acts on degree-zero fractions
by the chart ring map `xₗ / xᵢ ↦ (xₗ / xᵢ)ᵐ`. -/
private theorem powerMap_appLE_awayToSection (m : ℕ) (hm : 0 < m) (i : ι)
    (u : Away (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)) :
    ((powerMap k m).appLE (Proj.basicOpen _ (MvPolynomial.X i))
        (Proj.basicOpen _ (MvPolynomial.X i)) (powerMap_preimage_basicOpen m hm i).ge).hom
        ((Proj.awayToSection _ (MvPolynomial.X i)).hom u) =
      (Proj.awayToSection _ (MvPolynomial.X i)).hom
        (Stacks.ProjPoint.awayEval _ (powerChartHom k m i) (MvPolynomial.X i)
          (isUnit_powerChartHom m i) u) := by
  let 𝒮 := MvPolynomial.homogeneousSubmodule ι k
  set D := Proj.basicOpen 𝒮 (MvPolynomial.X i) with hDdef
  set a := Proj.awayι 𝒮 (MvPolynomial.X i) (X_mem_one' i) one_pos with hadef
  set ψ := Stacks.ProjPoint.awayEval 𝒮 (powerChartHom k m i) (MvPolynomial.X i)
    (isUnit_powerChartHom m i) with hψdef
  have hD : (⊤ : (Spec (CommRingCat.of (Away 𝒮 (MvPolynomial.X i)))).Opens) ≤ a ⁻¹ᵁ D := by
    have hDa : D = a.opensRange := (Proj.opensRange_awayι 𝒮 _ (X_mem_one' i) one_pos).symm
    rw [hDa, Scheme.Hom.preimage_opensRange]
  have key : ∀ x, (a.appLE D ⊤ hD).hom ((Proj.awayToSection 𝒮 (MvPolynomial.X i)).hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒮 (MvPolynomial.X i)))).inv.hom x :=
    Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection one_pos (X_mem_one' i) hD
  have hinj : Function.Injective (a.appLE D ⊤ hD).hom := by
    intro s t hst
    obtain ⟨s, rfl⟩ := (bijective_awayToSection (k := k) i).2 s
    obtain ⟨t, rfl⟩ := (bijective_awayToSection (k := k) i).2 t
    rw [key, key] at hst
    rw [(ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒮 (MvPolynomial.X i)))).inv).1 hst]
  apply hinj
  have h1 := Scheme.Hom.appLE_comp_appLE a (powerMap k m) D D ⊤
    (powerMap_preimage_basicOpen m hm i).ge hD
  have hcomp : a ≫ powerMap k m = Spec.map (CommRingCat.ofHom ψ) ≫ a := awayι_powerMap m i
  have h2 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom ψ)) a D ⊤ ⊤ hD le_top
  have h3 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  have e1 := congrArg (fun φ => φ.hom ((Proj.awayToSection 𝒮 (MvPolynomial.X i)).hom u))
    (h1.trans ((appLE_congr_of_eq hcomp _ _ _ _).trans h2.symm))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e1
  rw [e1, key, key]
  have e2 := congrArg (fun φ => φ.hom u) h3
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e2
  exact e2.symm

/-- The chart function `b / xᵢⁿ` of a nonzerodivisor `b` of degree `n` is a nonzerodivisor. -/
private theorem isRegular_chartFraction_X (i : ι) (n : ℕ)
    (b : MvPolynomial.homogeneousSubmodule ι k (n • 1)) (hb : IsRegular (b : MvPolynomial ι k)) :
    IsRegular (chartFraction (MvPolynomial.homogeneousSubmodule ι k) (X_mem_one' i) n b) := by
  let 𝒮 := MvPolynomial.homogeneousSubmodule ι k
  let g : MvPolynomial ι k := MvPolynomial.X i
  have hreg : IsRegular (algebraMap _ (Localization.Away g) (b : MvPolynomial ι k)) :=
    isRegular_iff_mem_nonZeroDivisors.2 (IsLocalization.map_nonZeroDivisors_le
      (Submonoid.powers g) (Localization.Away g)
      (Submonoid.mem_map_of_mem _ (isRegular_iff_mem_nonZeroDivisors.1 hb)))
  have key : ∀ y : Submonoid.powers g,
      IsRegular (IsLocalization.mk' (Localization.Away g) (b : MvPolynomial ι k) y) := fun y => by
    rw [← IsLocalization.mk'_spec (Localization.Away g) (b : MvPolynomial ι k) y] at hreg
    exact hreg.of_mul_left
  have hA : IsRegular (Away.mk 𝒮 (X_mem_one' i) n (b : MvPolynomial ι k) b.2) := by
    have hval : (Away.mk 𝒮 (X_mem_one' i) n (b : MvPolynomial ι k) b.2).val =
        IsLocalization.mk' (Localization.Away g) (b : MvPolynomial ι k)
          (⟨g ^ n, n, rfl⟩ : Submonoid.powers g) := by
      rw [Away.val_mk, Localization.mk_eq_mk']
    have hval' := key (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
    rw [← hval] at hval'
    refine ⟨fun x y h => val_injective _ (hval'.1 ?_), fun x y h => val_injective _ (hval'.2 ?_)⟩
    · simpa only [val_mul] using congrArg val h
    · simpa only [val_mul] using congrArg val h
  let e := (Proj.awayToSection 𝒮 g).hom
  have he := bijective_awayToSection (k := k) i
  change IsRegular (e (Away.mk 𝒮 (X_mem_one' i) n (b : MvPolynomial ι k) b.2))
  refine ⟨fun x y h => ?_, fun x y h => ?_⟩
  · obtain ⟨x, rfl⟩ := he.2 x
    obtain ⟨y, rfl⟩ := he.2 y
    refine congrArg e (hA.1 (he.1 ?_))
    simpa only [map_mul] using h
  · obtain ⟨x, rfl⟩ := he.2 x
    obtain ⟨y, rfl⟩ := he.2 y
    refine congrArg e (hA.2 (he.1 ?_))
    simpa only [map_mul] using h

private theorem X_pow_mem (m : ℕ) (j : ι) :
    (MvPolynomial.X j : MvPolynomial ι k) ^ m ∈ MvPolynomial.homogeneousSubmodule ι k (m • 1) :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (by
    simpa using (MvPolynomial.isHomogeneous_X k j).pow m)

private local instance isInvertible_twistingSheafModule (n : ℤ) :
    SheafOfModules.IsInvertible (ProjSpace k ι).sheaf.obj (ProjSpace k ι).ringCatSheaf.property
      (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) n) :=
  algebraicGeometry_isInvertible_twistingSheaf _ (adjoin_one_eq_top k ι) n

/-- The zero scheme of `xⱼᵐ`, a section of `𝒪(m)`. -/
private noncomputable abbrev powZero (m : ℕ) (j : ι) : (ProjSpace k ι).IdealSheafData :=
  Stacks.Divisors.zeroScheme (ProjSpace k ι)
    (twistingSheafModule (MvPolynomial.homogeneousSubmodule ι k) ((m • 1 : ℕ) : ℤ))
    (degreeSection (MvPolynomial.homogeneousSubmodule ι k) (m • 1) ⟨_, X_pow_mem m j⟩)

private theorem powZero_ideal (m : ℕ) (i j : ι) :
    (powZero (k := k) m j).ideal ⟨Proj.basicOpen _ (MvPolynomial.X i),
        Proj.isAffineOpen_basicOpen _ _ (X_mem_one' i) one_pos⟩ =
      Ideal.span {(chartFraction (MvPolynomial.homogeneousSubmodule ι k) (X_mem_one' i) m
        ⟨_, X_pow_mem m j⟩)} :=
  zeroScheme_degreeSection_ideal_basicOpen _ (X_mem_one' i) one_pos m _

/-- `{xⱼᵐ = 0}` is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_powZero (m : ℕ) (j : ι) :
    Stacks.Divisors.IsEffectiveCartierDivisor (powZero (k := k) m j) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  have hx : x ∈ ⨆ i : ι, Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k)
      (MvPolynomial.X i) := by
    rw [Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨_, Proj.isAffineOpen_basicOpen _ _ (X_mem_one' i) one_pos, hxi, _,
    isRegular_chartFraction_X i m _
      (IsRegular.of_ne_zero (pow_ne_zero m (MvPolynomial.X_ne_zero j))),
    powZero_ideal m i j⟩

/-- **The inverse image of a coordinate hyperplane under the power map** is `{xⱼᵐ = 0}`. -/
private theorem formZero_comap_powerMap (m : ℕ) (hm : 0 < m) (j : ι) :
    (formZero k ι ⟨MvPolynomial.X j, X_mem_one' j⟩).comap (powerMap k m) = powZero m j := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun i : ι => ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i),
      Proj.isAffineOpen_basicOpen _ _ (X_mem_one' i) one_pos⟩)
    (Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top k ι) fun i => ?_
  have h1 : (formZero k ι ⟨MvPolynomial.X j, X_mem_one' j⟩).ideal
      ⟨Proj.basicOpen _ (MvPolynomial.X i),
        Proj.isAffineOpen_basicOpen _ _ (X_mem_one' i) one_pos⟩ =
      Ideal.span {(chartFraction (MvPolynomial.homogeneousSubmodule ι k) (X_mem_one' i) 1
        ⟨MvPolynomial.X j, X_mem_one' j⟩)} :=
    zeroScheme_degreeSection_ideal_basicOpen _ (X_mem_one' i) one_pos 1 _
  rw [Stacks.IdealSheaf.ideal_comap_eq_span _ (powerMap k m) _ _
    (powerMap_preimage_basicOpen m hm i).ge h1, powZero_ideal]
  congr 2
  change ((powerMap k m).appLE _ _ _).hom ((Proj.awayToSection _ _).hom
      (Away.mk _ (X_mem_one' i) 1 (MvPolynomial.X j) _)) =
    (Proj.awayToSection _ _).hom (Away.mk _ (X_mem_one' i) m (MvPolynomial.X j ^ m) _)
  rw [powerMap_appLE_awayToSection m hm i, awayEval_powerChartHom_mk, away_mk_eq_eval₂]
  simp [powerChartHom]

/-- An invertible module is the invertible sheaf of the zero scheme of a section cutting out an
effective Cartier divisor. -/
private theorem nonempty_iso_invertibleSheaf_zeroScheme {Y : Scheme.{u}} (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] (σ : Γ(M, ⊤))
    (hσ : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme Y M σ)) :
    Nonempty (M ≅ Stacks.Divisors.invertibleSheaf' (Stacks.Divisors.zeroScheme Y M σ)) := by
  have hreg := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Y M
    (Stacks.Divisors.sectionsOfTop M σ)).mp (by
      rw [Stacks.Divisors.sectionsOfTop_eval_top]; exact hσ)
  have e := invertibleSheafIsoZeroSchemeOfIsRegularSection M _ hreg
  rw [Stacks.Divisors.sectionsOfTop_eval_top] at e
  exact ⟨e⟩

/-- **The power map pulls `𝒪(1)` back to `𝒪(1)^{⊗ m}`.** -/
private theorem nonempty_pullback_twistOne_powerMap_iso (m : ℕ) (hm : 0 < m) [Nonempty ι] :
    Nonempty ((Scheme.Modules.pullback (powerMap k m)).obj (ProjSpace.twistOne k ι) ≅
      tensorPow (ProjSpace.twistOne k ι) m) := by
  let 𝒮 := MvPolynomial.homogeneousSubmodule ι k
  obtain ⟨j⟩ := ‹Nonempty ι›
  set T := twistingSheafModule 𝒮 ((1 : ℕ) : ℤ)
  haveI : Stacks.Ample.IsInvertibleModule (ProjSpace k ι) T := isInvertible_twistingSheafModule _
  haveI : SheafOfModules.IsInvertible (ProjSpace k ι).sheaf.obj
      (ProjSpace k ι).ringCatSheaf.property ((Scheme.Modules.pullback (powerMap k m)).obj T) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (powerMap k m) T
  set σ' := pullbackGlobalSections (powerMap k m) T (degreeSection 𝒮 1 ⟨_, X_mem_one' j⟩)
  have hZ : Stacks.Divisors.zeroScheme _ _ σ' = powZero m j :=
    (Stacks.Divisors.zeroScheme_pullback _ _ _).trans (formZero_comap_powerMap m hm j)
  have hcart := isEffectiveCartierDivisor_powZero (k := k) m j
  obtain ⟨e₁⟩ := nonempty_iso_invertibleSheaf_zeroScheme _ σ' (hZ ▸ hcart)
  obtain ⟨e₂⟩ := nonempty_iso_invertibleSheaf_zeroScheme
    (twistingSheafModule 𝒮 ((m • 1 : ℕ) : ℤ)) _ hcart
  rw [hZ] at e₁
  haveI : Stacks.Ample.IsInvertibleModule (Proj 𝒮) (twistingSheaf 𝒮 1) :=
    isInvertible_twistingSheafModule _
  obtain ⟨e₃⟩ := Stacks.AlgebraicGeometry.ProjTwistPowers.nonempty_tensorPowModule_iso_twistingSheaf
    𝒮 (adjoin_one_eq_top k ι) ((m • 1 : ℕ) : ℤ)
  obtain ⟨e₄⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule (Proj 𝒮)
    (twistingSheaf 𝒮 1) (m • 1)
  exact ⟨e₁ ≪≫ e₂.symm ≪≫ e₃.symm ≪≫ e₄.symm ≪≫
    eqToIso (congrArg (tensorPow (ProjSpace.twistOne k ι)) (show m • 1 = m by
      rw [smul_eq_mul, mul_one]))⟩

end PowerMapTwist

/-- **The power map exists**, over `k`, chartwise `[xᵢ] ↦ [xᵢᵐ]`, with
`p^* 𝒪(1) ≅ 𝒪(1)^{⊗ m}`. -/
private theorem exists_powerMap.{u} (k : Type u) [Field k] (N m : ℕ) (hm : 0 < m) :
    ∃ p : ProjSpace k (ULift.{u} (Fin (N + 1))) ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))),
      p ≫ ProjSpace.toSpec k _ = ProjSpace.toSpec k _ ∧
      (∃ L : (ProjSpace k (ULift.{u} (Fin (N + 1)))).Modules,
        AlgebraicGeometry.SheafOfModules.IsInvertible
          (ProjSpace k (ULift.{u} (Fin (N + 1)))).sheaf.obj
          (ProjSpace k (ULift.{u} (Fin (N + 1)))).ringCatSheaf.property L ∧
        Nonempty ((Scheme.Modules.pullback p).obj (ProjSpace.twistOne k _) ≅ tensorPow L m)) ∧
      IsPowerMapChartwise k N m p := by
  obtain ⟨hpk, hp⟩ := powerMap_toSpec_and_isPowerMapChartwise k N m hm
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (N + 1))) (R := k)
  haveI : Nonempty (ULift.{u} (Fin (N + 1))) := ⟨⟨0⟩⟩
  exact ⟨powerMap k m, hpk, ⟨_, isInvertible_twistingSheafModule 1,
    nonempty_pullback_twistOne_powerMap_iso m hm⟩, hp⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The power map is finite and surjective**. Both properties are local on
the target, and over the chart `D₊(xᵢ)`, whose preimage is `D₊(xᵢ)`, the map is `Spec` of
`k[yⱼ] → k[yⱼ]`, `yⱼ ↦ yⱼᵐ`: a finite (each `yⱼ` is a root of `T^m - yⱼᵐ`) injective ring map,
so `Spec` of it is finite and, by lying over, surjective. -/
private theorem isFinite_surjective_of_isPowerMapChartwise.{u} (k : Type u) [Field k] (N m : ℕ)
    (hm : 0 < m)
    (p : ProjSpace k (ULift.{u} (Fin (N + 1))) ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (hp : IsPowerMapChartwise k N m p) : IsFinite p ∧ Surjective p := by
  have hcov : ⨆ i : ULift.{u} (Fin (N + 1)), (ProjSpace.affineChart k i).opensRange = ⊤ := by
    simp only [ProjSpace.opensRange_affineChart]
    exact Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top k _
  have hF : IsFinite p := by
    refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top _ hcov).mpr fun i => ?_
    obtain ⟨e⟩ := arrow_iso_of_isPowerMapChartwise k N m p hp i
    refine (MorphismProperty.arrow_mk_iso_iff _ e).mpr ?_
    exact (IsFinite.SpecMap_iff _).mpr (expand_finite hm)
  refine ⟨hF, ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top _ hcov).mpr fun i => ?_
  · obtain ⟨e⟩ := arrow_iso_of_isPowerMapChartwise k N m p hp i
    refine (MorphismProperty.arrow_mk_iso_iff _ e).mpr ?_
    refine ⟨?_⟩
    rw [Spec.map_base]
    exact RingHom.IsIntegral.comap_surjective (expand_isIntegral hm)
      (MvPolynomial.expand_injective hm)

section KummerLocalRings

/-! ### Local rings of `R[T]/(Tᵐ - f)` and of the cover of `𝔸ᴺ` by the power map -/

open IsLocalRing

section Algebra

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {m : ℕ} {f : R}

/-- In `B = R[T]/(Tᵐ - f)` the class of `T` is an `m`-th root of `f`. -/
private theorem pow_eq_algebraMap_of_ker_eq_span (φ : Polynomial R →ₐ[R] B)
    (hker : RingHom.ker φ = Ideal.span {Polynomial.X ^ m - Polynomial.C f}) :
    φ Polynomial.X ^ m = algebraMap R B f := by
  have h : Polynomial.X ^ m - Polynomial.C f ∈ RingHom.ker φ := hker ▸ Ideal.subset_span rfl
  rwa [RingHom.mem_ker, map_sub, map_pow, ← Polynomial.algebraMap_eq (R := R), φ.commutes,
    sub_eq_zero] at h

/-- `R[T]/(Tᵐ - f)` is `AdjoinRoot (Tᵐ - f)`. -/
private noncomputable def algEquivAdjoinRoot (φ : Polynomial R →ₐ[R] B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {Polynomial.X ^ m - Polynomial.C f}) :
    AdjoinRoot (Polynomial.X ^ m - Polynomial.C f) ≃ₐ[R] B :=
  (Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hφ)

/-- `R[T]/(Tᵐ - f)` is a free `R`-module of finite rank, for `m > 0`. -/
private theorem free_finite_of_ker_eq_span (hm : 0 < m) (φ : Polynomial R →ₐ[R] B)
    (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {Polynomial.X ^ m - Polynomial.C f}) :
    Module.Free R B ∧ Module.Finite R B := by
  let pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C f hm.ne')
  let e := (algEquivAdjoinRoot φ hφ hker).toLinearEquiv
  haveI : Module.Free R (AdjoinRoot (Polynomial.X ^ m - Polynomial.C f)) :=
    Module.Free.of_basis pb.basis
  haveI : Module.Finite R (AdjoinRoot (Polynomial.X ^ m - Polynomial.C f)) := pb.finite
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- **The local rings of `R[T]/(Tᵐ - f)` have the dimension of those of `R`.** The extension is
free, so it has going down, and integral, so the fibre of a prime has dimension zero. -/
private theorem ringKrullDim_atPrime_eq_of_ker_eq_span [IsNoetherianRing R] (hm : 0 < m)
    (φ : Polynomial R →ₐ[R] B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {Polynomial.X ^ m - Polynomial.C f})
    (P : Ideal R) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] (hQ : Q.comap (algebraMap R B) = P) :
    ringKrullDim (Localization.AtPrime Q) = ringKrullDim (Localization.AtPrime P) := by
  obtain ⟨hfree, hfin⟩ := free_finite_of_ker_eq_span hm φ hφ hker
  haveI := hfree
  haveI := hfin
  haveI : IsNoetherianRing B := isNoetherianRing_of_surjective _ _ φ.toRingHom hφ
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  haveI : Q.LiesOver P := ⟨hQ.symm⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q,
    IsLocalization.AtPrime.ringKrullDim_eq_height P,
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P Q]
  set I := P.map (algebraMap R B)
  have hIQ : I ≤ Q := Ideal.map_le_iff_le_comap.2 hQ.ge
  have hker' : RingHom.ker (Ideal.Quotient.mk I) ≤ Q := by rw [Ideal.mk_ker]; exact hIQ
  haveI hQp : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker'
  have hcomap : (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = Q := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hker']
  have h0 : (Q.map (Ideal.Quotient.mk I)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨hQp, bot_le⟩, fun J hJ hJQ => ?_⟩
    haveI := hJ.1
    have hle : J.comap (Ideal.Quotient.mk I) ≤ Q := hcomap ▸ Ideal.comap_mono hJQ
    have heq : J.comap (Ideal.Quotient.mk I) = Q := by
      by_contra hne
      have hlt := Ideal.IntegralClosure.comap_lt_comap (R := R) (lt_of_le_of_ne hle hne)
      simp only [Ideal.under_def] at hlt
      rw [hQ] at hlt
      refine hlt.not_ge ?_
      intro r hr
      change Ideal.Quotient.mk I (algebraMap R B r) ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)]
      exact J.zero_mem
    rw [← heq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [h0, add_zero]

/-- **Over the branch locus.** If `f = u z_c` in `R_P` for a regular system of parameters `z`
and a unit `u`, then in the local ring of `R[T]/(Tᵐ - f)` at a prime over `P` the root `T` of
`Tᵐ = f` takes the place of `z_c` in a regular system of parameters. -/
private theorem isRegularSystemOfParameters_update [IsNoetherianRing R] (hm : 0 < m)
    (φ : Polynomial R →ₐ[R] B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {Polynomial.X ^ m - Polynomial.C f})
    (P : Ideal R) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] (hQ : Q.comap (algebraMap R B) = P)
    {n : ℕ} {z : Fin n → Localization.AtPrime P} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (c : Fin n) (u : Localization.AtPrime P) (hu : IsUnit u)
    (hf : algebraMap R (Localization.AtPrime P) f = u * z c) :
    MMP.Mori.IsRegularSystemOfParameters (Function.update
      (fun i => Localization.localRingHom P Q (algebraMap R B) hQ.symm (z i)) c
      (algebraMap B (Localization.AtPrime Q) (φ Polynomial.X))) := by
  set ψ := Localization.localRingHom P Q (algebraMap R B) hQ.symm with hψdef
  set t := φ Polynomial.X with htdef
  set z' := Function.update (fun i => ψ (z i)) c (algebraMap B (Localization.AtPrime Q) t)
    with hz'def
  refine ⟨?_, by rw [ringKrullDim_atPrime_eq_of_ker_eq_span hm φ hφ hker P Q hQ, hz.2]⟩
  have hψ : ∀ r : R, ψ (algebraMap R _ r) = algebraMap B _ (algebraMap R B r) := fun r =>
    Localization.localRingHom_to_map P Q (algebraMap R B) hQ.symm r
  have hmaxP : ∀ i, z i ∈ maximalIdeal (Localization.AtPrime P) := fun i =>
    hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hfP : f ∈ P := by
    have h : algebraMap R (Localization.AtPrime P) f ∈ maximalIdeal _ :=
      hf ▸ Ideal.mul_mem_left _ _ (hmaxP c)
    exact (Localization.AtPrime.comap_maximalIdeal (I := P)).le (Ideal.mem_comap.2 h)
  have htQ : t ∈ Q := ‹Q.IsPrime›.mem_of_pow_mem m (by
    rw [pow_eq_algebraMap_of_ker_eq_span φ hker, ← Ideal.mem_comap, hQ]; exact hfP)
  have hzc' : z' c = algebraMap B _ t := by simp [z']
  have hzi' : ∀ i, i ≠ c → z' i = ψ (z i) := fun i hi => by simp [z', hi]
  set J := Ideal.span (Set.range z')
  have htJ : algebraMap B (Localization.AtPrime Q) t ∈ J := hzc' ▸ Ideal.subset_span ⟨c, rfl⟩
  have hzJ : ∀ i, ψ (z i) ∈ J := by
    intro i
    by_cases hi : i = c
    · subst hi
      obtain ⟨v, rfl⟩ := hu
      have h1 : ψ (z i) = ψ ↑v⁻¹ * algebraMap B _ t ^ m := by
        rw [← map_pow, pow_eq_algebraMap_of_ker_eq_span φ hker, ← hψ, hf, ← map_mul, ← mul_assoc,
          Units.inv_mul, one_mul]
      rw [h1]
      exact J.mul_mem_left _ (J.pow_mem_of_mem htJ m hm)
    · exact hzi' i hi ▸ Ideal.subset_span ⟨i, rfl⟩
  have hPJ : ∀ r ∈ P, algebraMap B _ (algebraMap R B r) ∈ J := by
    intro r hr
    rw [← hψ]
    have h : algebraMap R (Localization.AtPrime P) r ∈ Ideal.span (Set.range z) := by
      rw [hz.1, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hr
    have hle : Ideal.span (Set.range z) ≤ J.comap ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hzJ i
    exact hle h
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = c
    · subst hi
      rw [hzc', ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ htQ
    · rw [hzi' i hi]
      exact map_nonunit ψ _ (hmaxP i)
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨p, rfl⟩ := hφ b
    obtain ⟨q, hq⟩ : Polynomial.X ∣ p - Polynomial.C (p.coeff 0) :=
      Polynomial.X_dvd_iff.2 (by simp)
    have hb' : φ p = algebraMap R B (p.coeff 0) + t * φ q := by
      rw [htdef, ← map_mul, ← hq, ← Polynomial.algebraMap_eq (R := R), ← φ.commutes, ← map_add]
      congr 1
      ring
    have h0 : p.coeff 0 ∈ P := by
      rw [← hQ, Ideal.mem_comap]
      have : algebraMap R B (p.coeff 0) = φ p - t * φ q := by
        rw [hb']
        ring
      rw [this]
      exact Q.sub_mem hb (Q.mul_mem_right _ htQ)
    rw [Ideal.mem_comap, hb', map_add, map_mul]
    exact J.add_mem (hPJ _ h0) (J.mul_mem_right _ htJ)

/-- For `m` invertible in `R`, the localization of `R[T]/(Tᵐ - f)` away from `T` is standard
étale over `R`: it is the standard étale algebra of the pair `(Tᵐ - f, T)`. -/
private theorem etale_localization_away_of_ker_eq_span (hm : 0 < m) (hmu : IsUnit (m : R))
    (φ : Polynomial R →ₐ[R] B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {Polynomial.X ^ m - Polynomial.C f}) :
    Algebra.Etale R (Localization.Away (φ Polynomial.X)) := by
  let P : StandardEtalePair R :=
    { f := Polynomial.X ^ m - Polynomial.C f, monic_f := Polynomial.monic_X_pow_sub_C f hm.ne'
      g := Polynomial.X
      cond := ⟨Polynomial.C (↑hmu.unit⁻¹ : R) * Polynomial.X, 0, m, by
        rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
          Polynomial.derivative_X_pow, mul_zero, add_zero]
        calc Polynomial.C (m : R) * Polynomial.X ^ (m - 1) *
              (Polynomial.C (↑hmu.unit⁻¹ : R) * Polynomial.X)
            = Polynomial.C ((m : R) * ↑hmu.unit⁻¹) * (Polynomial.X ^ (m - 1) * Polynomial.X) := by
              rw [Polynomial.C_mul]
              ring
          _ = Polynomial.X ^ m := by
              rw [IsUnit.mul_val_inv, Polynomial.C_1, one_mul, pow_sub_one_mul hm.ne']⟩ }
  let e₀ := algEquivAdjoinRoot φ hφ hker
  have he₀ : e₀ (AdjoinRoot.mk P.f P.g) = φ Polynomial.X := rfl
  have H : Submonoid.map e₀.toRingEquiv.toMonoidHom (.powers (AdjoinRoot.mk P.f P.g)) =
      .powers (φ Polynomial.X) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers he₀
  let e₂ : Localization.Away (AdjoinRoot.mk P.f P.g) ≃ₐ[R] Localization.Away (φ Polynomial.X) :=
    { __ := IsLocalization.ringEquivOfRingEquiv _ _ _ H,
      commutes' r := by
        simp [IsScalarTower.algebraMap_apply R (AdjoinRoot P.f) (Localization.Away _),
          IsScalarTower.algebraMap_apply R B (Localization.Away (φ Polynomial.X))]
        rw [← AdjoinRoot.algebraMap_eq, e₀.commutes] }
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans e₂)

/-- **Away from the branch locus.** If `f ∉ P` and `m` is invertible, a regular system of
parameters of `R_P` stays one in the local ring of `R[T]/(Tᵐ - f)` at a prime over `P`: the
extension is étale there, so the maximal ideal of `R_P` generates that of `B_Q`. -/
private theorem isRegularSystemOfParameters_map_of_notMem [IsNoetherianRing R] (hm : 0 < m)
    (hmu : IsUnit (m : R)) (φ : Polynomial R →ₐ[R] B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {Polynomial.X ^ m - Polynomial.C f})
    (P : Ideal R) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] (hQ : Q.comap (algebraMap R B) = P)
    (hfP : f ∉ P) {n : ℕ} {z : Fin n → Localization.AtPrime P}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    MMP.Mori.IsRegularSystemOfParameters
      (fun i => Localization.localRingHom P Q (algebraMap R B) hQ.symm (z i)) := by
  set ψ := Localization.localRingHom P Q (algebraMap R B) hQ.symm with hψdef
  refine ⟨?_, by rw [ringKrullDim_atPrime_eq_of_ker_eq_span hm φ hφ hker P Q hQ, hz.2]⟩
  have hψ : ∀ r : R, ψ (algebraMap R _ r) = algebraMap B _ (algebraMap R B r) := fun r =>
    Localization.localRingHom_to_map P Q (algebraMap R B) hQ.symm r
  set t := φ Polynomial.X with htdef
  have htQ : t ∉ Q := fun h => hfP (by
    rw [← hQ, Ideal.mem_comap, ← pow_eq_algebraMap_of_ker_eq_span φ hker]
    exact Q.pow_mem_of_mem h m hm)
  have htu : IsUnit (algebraMap B (Localization.AtPrime Q) t) :=
    IsLocalization.map_units (Localization.AtPrime Q) (⟨t, htQ⟩ : Q.primeCompl)
  haveI := etale_localization_away_of_ker_eq_span hm hmu φ hφ hker
  letI : Algebra (Localization.Away t) (Localization.AtPrime Q) :=
    (IsLocalization.Away.lift t htu).toAlgebra
  haveI : IsScalarTower B (Localization.Away t) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.Away.lift_eq t htu b).symm
  haveI : IsScalarTower R (Localization.Away t) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R B (Localization.Away t),
        IsScalarTower.algebraMap_apply R B (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply B (Localization.Away t) (Localization.AtPrime Q)]
  have hle : Submonoid.powers t ≤ Q.primeCompl := (Submonoid.powers_le).2 htQ
  haveI : IsLocalization (Submonoid.map (algebraMap B (Localization.Away t)) Q.primeCompl)
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers t) Q.primeCompl hle
  haveI : Algebra.FormallyUnramified (Localization.Away t) (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.of_isLocalization
      (Submonoid.map (algebraMap B (Localization.Away t)) Q.primeCompl)
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.comp R (Localization.Away t) _
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) := ψ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime Q)]
      exact (hψ r).symm
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) :=
    (inferInstance : IsLocalHom ψ)
  haveI : Algebra.FormallyUnramified (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.of_restrictScalars R _ _
  haveI : Algebra.FiniteType R B :=
    Algebra.FiniteType.of_surjective φ hφ
  haveI : Algebra.EssFiniteType B (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.of_isLocalization _ Q.primeCompl
  haveI : Algebra.EssFiniteType R (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.comp R B _
  haveI : Algebra.EssFiniteType (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.of_comp R _ _
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := Localization.AtPrime P)
    (S := Localization.AtPrime Q), ← hz.1, Ideal.map_span, ← Set.range_comp]
  rfl

/-- The image of an element of `R` lies in the maximal ideal of `B_Q` iff it lies in `P`. -/
private theorem algebraMap_mem_maximalIdeal_atPrime_iff (P : Ideal R) [P.IsPrime] (Q : Ideal B)
    [Q.IsPrime] (hQ : Q.comap (algebraMap R B) = P) (r : R) :
    algebraMap B (Localization.AtPrime Q) (algebraMap R B r) ∈ maximalIdeal _ ↔ r ∈ P := by
  rw [← hQ, Ideal.mem_comap]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q _

end Algebra

/-- **Parameters adapted to a family.** A regular system of parameters `z` of a local ring
together with an injective choice of parameters `z (c l)` associated to the members `g l` of a
family that lie in the maximal ideal. -/
private def HasSNCParameters (A : Type*) [CommRing A] [IsLocalRing A] {Λ : Type*}
    (g : Λ → A) : Prop :=
  ∃ (n : ℕ) (z : Fin n → A) (c : {l // g l ∈ maximalIdeal A} → Fin n),
    MMP.Mori.IsRegularSystemOfParameters z ∧
    (∀ l, ∃ u, IsUnit u ∧ g l.1 = u * z (c l)) ∧ Function.Injective c

/-- Adapted parameters restrict along an injective reindexing. -/
private theorem HasSNCParameters.comp {A : Type*} [CommRing A] [IsLocalRing A] {Λ Λ' : Type*}
    {g : Λ → A} (h : HasSNCParameters A g) (e : Λ' → Λ) (he : Function.Injective e) :
    HasSNCParameters A (g ∘ e) := by
  obtain ⟨n, z, c, hz, hc, hinj⟩ := h
  exact ⟨n, z, fun l => c ⟨e l.1, l.2⟩, hz, fun l => hc ⟨e l.1, l.2⟩,
    fun l l' h => Subtype.ext (he (congrArg Subtype.val (hinj h)))⟩

/-- Adapted parameters are transported by ring isomorphisms. -/
private theorem HasSNCParameters.map_ringEquiv {A A' : Type*} [CommRing A] [IsLocalRing A]
    [CommRing A']
    [IsLocalRing A'] {Λ : Type*} {g : Λ → A} (h : HasSNCParameters A g) (e : A ≃+* A') :
    HasSNCParameters A' (fun l => e (g l)) := by
  obtain ⟨n, z, c, hz, hc, hinj⟩ := h
  have hmem : ∀ a, e a ∈ maximalIdeal A' ↔ a ∈ maximalIdeal A := fun a => by
    simp only [mem_maximalIdeal, mem_nonunits_iff, MulEquiv.isUnit_map]
  refine ⟨n, fun i => e (z i), fun l => c ⟨l.1, (hmem _).1 l.2⟩, ⟨?_, ?_⟩, fun l => ?_,
    fun l l' hll' => Subtype.ext (Subtype.mk.inj (hinj hll'))⟩
  · have : maximalIdeal A' = (maximalIdeal A).map e := by
      refine le_antisymm (fun a ha => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => (hmem a).2 ha)
      rw [← e.apply_symm_apply a]
      exact Ideal.mem_map_of_mem _ ((hmem _).1 (by rwa [e.apply_symm_apply]))
    rw [this, ← hz.1, Ideal.map_span, ← Set.range_comp]
    rfl
  · rw [← hz.2]; exact (ringKrullDim_eq_of_ringEquiv e).symm
  · obtain ⟨u, hu, hl'⟩ := hc ⟨l.1, (hmem _).1 l.2⟩
    exact ⟨e u, hu.map e, show e (g l.1) = e u * e (z _) by rw [hl', map_mul]⟩

section Step

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {m : ℕ}

/-- **Adjoining an `m`-th root of a member of the family.** If `R_P` has parameters adapted to
`g`, then the local ring of `R[T]/(Tᵐ - g j)` at a prime over `P` has parameters adapted to the
rest of the family, and has the same dimension. -/
private theorem hasSNCParameters_of_ker_eq_span [IsNoetherianRing R] (hm : 0 < m)
    (hmu : IsUnit (m : R))
    {Λ : Type*} (g : Λ → R) (j : Λ) (φ : Polynomial R →ₐ[R] B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {Polynomial.X ^ m - Polynomial.C (g j)})
    (P : Ideal R) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] (hQ : Q.comap (algebraMap R B) = P)
    (h : HasSNCParameters (Localization.AtPrime P) (fun l => algebraMap R _ (g l))) :
    HasSNCParameters (Localization.AtPrime Q)
        (fun l : {l // l ≠ j} => algebraMap B _ (algebraMap R B (g l))) ∧
      ringKrullDim (Localization.AtPrime Q) = ringKrullDim (Localization.AtPrime P) := by
  refine ⟨?_, ringKrullDim_atPrime_eq_of_ker_eq_span hm φ hφ hker P Q hQ⟩
  obtain ⟨n, z, c, hz, hc, hinj⟩ := h
  set ψ := Localization.localRingHom P Q (algebraMap R B) hQ.symm with hψdef
  have hψ : ∀ r : R, ψ (algebraMap R _ r) = algebraMap B _ (algebraMap R B r) := fun r =>
    Localization.localRingHom_to_map P Q (algebraMap R B) hQ.symm r
  have hmemP : ∀ r : R, algebraMap R (Localization.AtPrime P) r ∈ maximalIdeal _ ↔ r ∈ P :=
    fun r => IsLocalization.AtPrime.to_map_mem_maximal_iff _ P r
  have hmemQ := algebraMap_mem_maximalIdeal_atPrime_iff P Q hQ
  by_cases hjP : g j ∈ P
  · obtain ⟨u, hu, hju⟩ := hc ⟨j, (hmemP _).2 hjP⟩
    refine ⟨n, _, fun l => c ⟨l.1.1, (hmemP _).2 ((hmemQ _).1 l.2)⟩,
      isRegularSystemOfParameters_update hm φ hφ hker P Q hQ hz _ u hu hju,
      fun l => ?_, fun l l' hll' => Subtype.ext (Subtype.ext
        (congrArg (fun x => x.1) (hinj hll')))⟩
    obtain ⟨v, hv, hlv⟩ := hc ⟨l.1.1, (hmemP _).2 ((hmemQ _).1 l.2)⟩
    have hne : c ⟨l.1.1, (hmemP _).2 ((hmemQ _).1 l.2)⟩ ≠ c ⟨j, (hmemP _).2 hjP⟩ := fun h' =>
      l.1.2 (congrArg Subtype.val (hinj h'))
    refine ⟨ψ v, hv.map ψ, ?_⟩
    rw [Function.update_of_ne hne]
    change algebraMap B _ (algebraMap R B (g l.1.1)) = ψ v * ψ (z _)
    exact (hψ _).symm.trans ((congrArg ψ hlv).trans (map_mul ψ v _))
  · refine ⟨n, _, fun l => c ⟨l.1.1, (hmemP _).2 ((hmemQ _).1 l.2)⟩,
      isRegularSystemOfParameters_map_of_notMem hm hmu φ hφ hker P Q hQ hjP hz,
      fun l => ?_, fun l l' hll' => Subtype.ext (Subtype.ext
        (congrArg (fun x => x.1) (hinj hll')))⟩
    obtain ⟨v, hv, hlv⟩ := hc ⟨l.1.1, (hmemP _).2 ((hmemQ _).1 l.2)⟩
    refine ⟨ψ v, hv.map ψ, ?_⟩
    change algebraMap B _ (algebraMap R B (g l.1.1)) = ψ v * ψ (z _)
    exact (hψ _).symm.trans ((congrArg ψ hlv).trans (map_mul ψ v _))

end Step

section Chain

variable (C : Type*) [CommRing C] {σ : Type*} [DecidableEq σ] (m : ℕ) (f : σ → C)

/-- The ideal of `C[t_σ]` adjoining an `m`-th root `t_l` of `f l` for `l ∈ s` and killing `t_l`
for `l ∉ s`. -/
private noncomputable def rootIdeal (s : Finset σ) : Ideal (MvPolynomial σ C) :=
  Ideal.span (Set.range (fun l : s => MvPolynomial.X (l : σ) ^ m - MvPolynomial.C (f l)) ∪
    Set.range (fun l : {l // l ∉ s} => (MvPolynomial.X (l : σ) : MvPolynomial σ C)))

/-- `C` with `m`-th roots of the `f l`, `l ∈ s`, adjoined. -/
private abbrev RootRing (s : Finset σ) := MvPolynomial σ C ⧸ rootIdeal C m f s

variable {C m f}

private theorem X_pow_sub_C_mem_rootIdeal {s : Finset σ} {l : σ} (hl : l ∈ s) :
    MvPolynomial.X l ^ m - MvPolynomial.C (f l) ∈ rootIdeal C m f s :=
  Ideal.subset_span (Or.inl ⟨⟨l, hl⟩, rfl⟩)

private theorem X_mem_rootIdeal {s : Finset σ} {l : σ} (hl : l ∉ s) :
    MvPolynomial.X l ∈ rootIdeal C m f s :=
  Ideal.subset_span (Or.inr ⟨⟨l, hl⟩, rfl⟩)

/-- The class of `t_l` in `RootRing`. -/
private noncomputable abbrev rootVar (s : Finset σ) (l : σ) : RootRing C m f s :=
  Ideal.Quotient.mk _ (MvPolynomial.X l)

private theorem rootVar_pow {s : Finset σ} {l : σ} (hl : l ∈ s) :
    rootVar (m := m) (f := f) s l ^ m = algebraMap C _ (f l) := by
  change Ideal.Quotient.mk _ (MvPolynomial.X l) ^ m = Ideal.Quotient.mk _ (MvPolynomial.C (f l))
  rw [← map_pow]
  exact Ideal.Quotient.eq.2 (X_pow_sub_C_mem_rootIdeal hl)

private theorem rootVar_eq_zero {s : Finset σ} {l : σ} (hl : l ∉ s) :
    rootVar (m := m) (f := f) s l = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (X_mem_rootIdeal hl)

/-- The ring hom `C[t_σ] → B` sending `t_l` to `v l`, for `v l` an `m`-th root of `f l` when
`l ∈ s` and `v l = 0` otherwise, descends to `RootRing s`. -/
private noncomputable def rootRingLift {B : Type*} [CommRing B] [Algebra C B] (s : Finset σ)
    (v : σ → B)
    (hv : ∀ l ∈ s, v l ^ m = algebraMap C B (f l)) (hv' : ∀ l ∉ s, v l = 0) :
    RootRing C m f s →ₐ[C] B :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval v) (by
    intro p hp
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ h₁ h₂ => by simp [h₁, h₂])
      (fun a _ _ h => by simp [h]) hp
    rintro _ (⟨⟨l, hl⟩, rfl⟩ | ⟨⟨l, hl⟩, rfl⟩)
    · simp [hv l hl]
    · simp [hv' l hl])

private theorem rootRingLift_rootVar {B : Type*} [CommRing B] [Algebra C B] (s : Finset σ)
    (v : σ → B)
    (hv : ∀ l ∈ s, v l ^ m = algebraMap C B (f l)) (hv' : ∀ l ∉ s, v l = 0) (l : σ) :
    rootRingLift s v hv hv' (rootVar s l) = v l :=
  MvPolynomial.aeval_X v l

private theorem rootRing_algHom_ext {B : Type*} [CommRing B] [Algebra C B] {s : Finset σ}
    {g₁ g₂ : RootRing C m f s →ₐ[C] B} (h : ∀ l, g₁ (rootVar s l) = g₂ (rootVar s l)) :
    g₁ = g₂ :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext h)

variable (j : σ) {s : Finset σ}

/-- The inclusion `RootRing s → RootRing (insert j s)`, sending `t_j` to `0` in the source's
spelling, where it is already zero. -/
private noncomputable def rootRingIncl (hj : j ∉ s) :
    RootRing C m f s →ₐ[C] RootRing C m f (insert j s) :=
  rootRingLift s (fun l => if l ∈ s then rootVar _ l else 0)
    (fun l hl => by rw [if_pos hl, rootVar_pow (Finset.mem_insert_of_mem hl)])
    (fun l hl => if_neg hl)

private theorem rootRingIncl_rootVar (hj : j ∉ s) (l : σ) :
    rootRingIncl (m := m) (f := f) j hj (rootVar s l) =
      if l ∈ s then rootVar (insert j s) l else 0 :=
  rootRingLift_rootVar _ _ _ _ l

/-- **One more root.** `RootRing (insert j s)` is `RootRing s [T] / (Tᵐ - f j)`, over the
inclusion `rootRingIncl`. -/
private theorem exists_rootRing_insert_presentation (hj : j ∉ s) :
    letI := (rootRingIncl (m := m) (f := f) j hj).toRingHom.toAlgebra
    ∃ φ : Polynomial (RootRing C m f s) →ₐ[RootRing C m f s] RootRing C m f (insert j s),
      Function.Surjective φ ∧ φ Polynomial.X = rootVar (insert j s) j ∧
      RingHom.ker φ = Ideal.span {(Polynomial.X ^ m -
        Polynomial.C (algebraMap C (RootRing C m f s) (f j)))} := by
  letI := (rootRingIncl (m := m) (f := f) j hj).toRingHom.toAlgebra
  set ι := rootRingIncl (m := m) (f := f) j hj
  have hι : ∀ b, algebraMap (RootRing C m f s) (RootRing C m f (insert j s)) b = ι b := fun _ => rfl
  set φ := Polynomial.aeval (R := RootRing C m f s) (rootVar (m := m) (f := f) (insert j s) j)
  set g : Polynomial (RootRing C m f s) := Polynomial.X ^ m -
    Polynomial.C (algebraMap C (RootRing C m f s) (f j))
  -- the inverse map
  let T := Polynomial (RootRing C m f s) ⧸ Ideal.span {g}
  let v : σ → T := fun l => if l = j then Ideal.Quotient.mk _ Polynomial.X else
    if l ∈ s then Ideal.Quotient.mk _ (Polynomial.C (rootVar s l)) else 0
  have hvj : v j = Ideal.Quotient.mk _ Polynomial.X := if_pos rfl
  have hT : ∀ c, algebraMap C T c =
      Ideal.Quotient.mk (Ideal.span {g}) (Polynomial.C (algebraMap C (RootRing C m f s) c)) :=
    fun c => by
      show algebraMap C (Polynomial (RootRing C m f s) ⧸ Ideal.span {g}) c = _
      rw [← Polynomial.algebraMap_apply, Ideal.Quotient.mk_algebraMap]
  have hv : ∀ l ∈ insert j s, v l ^ m = algebraMap C T (f l) := by
    intro l hl
    rw [hT]
    by_cases hlj : l = j
    · subst hlj
      rw [hvj, ← map_pow]
      exact Ideal.Quotient.eq.2 (Ideal.subset_span (Set.mem_singleton g))
    · have hls : l ∈ s := (Finset.mem_insert.1 hl).resolve_left hlj
      have hvl : v l = Ideal.Quotient.mk _ (Polynomial.C (rootVar s l)) := by
        simp only [v, if_neg hlj, if_pos hls]
      rw [hvl, ← map_pow, ← map_pow, rootVar_pow hls]
  have hv' : ∀ l ∉ insert j s, v l = 0 := fun l hl => by
    have h1 : l ≠ j := fun h => hl (h ▸ Finset.mem_insert_self j s)
    have h2 : l ∉ s := fun h => hl (Finset.mem_insert_of_mem h)
    simp only [v, if_neg h1, if_neg h2]
  let κ := rootRingLift (insert j s) v hv hv'
  have hκφ : ∀ p, κ (φ p) = Ideal.Quotient.mk _ p := by
    have hC : (κ.toRingHom.comp ι.toRingHom) =
        (Ideal.Quotient.mk (Ideal.span {g})).comp Polynomial.C := by
      have := rootRing_algHom_ext (g₁ := κ.comp ι)
        (g₂ := (Ideal.Quotient.mkₐ C (Ideal.span {g})).comp
          (IsScalarTower.toAlgHom C (RootRing C m f s) (Polynomial (RootRing C m f s))))
        (fun l => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, rootRingIncl_rootVar]
          by_cases hls : l ∈ s
          · rw [if_pos hls, rootRingLift_rootVar]
            simp only [v, if_neg (fun h : l = j => hj (h ▸ hls)), if_pos hls]
            rfl
          · rw [if_neg hls, map_zero, rootVar_eq_zero hls, map_zero, map_zero])
      exact congrArg AlgHom.toRingHom this
    have := Polynomial.ringHom_ext (f := κ.toRingHom.comp φ.toRingHom)
      (g := Ideal.Quotient.mk (Ideal.span {g}))
      (fun b => by
        have h := congrArg (fun F => F b) hC
        simp only [RingHom.comp_apply] at h
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Polynomial.aeval_C, φ]
        exact h)
      (by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Polynomial.aeval_X, φ]
        rw [rootRingLift_rootVar, hvj])
    exact fun p => congrArg (fun F => F p) this
  refine ⟨φ, ?_, Polynomial.aeval_X _, ?_⟩
  · intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine ⟨Polynomial.C (algebraMap C _ a), ?_⟩
      rw [Polynomial.aeval_C, hι, AlgHom.commutes]
      rfl
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p l hp =>
      obtain ⟨a, ha⟩ := hp
      by_cases hlj : l = j
      · subst hlj
        exact ⟨a * Polynomial.X, by rw [map_mul, ha, map_mul, Polynomial.aeval_X]⟩
      · by_cases hls : l ∈ s
        · refine ⟨a * Polynomial.C (rootVar s l), ?_⟩
          rw [map_mul, ha, map_mul, Polynomial.aeval_C, hι, rootRingIncl_rootVar, if_pos hls]
        · refine ⟨0, ?_⟩
          rw [map_zero, map_mul, show Ideal.Quotient.mk _ (MvPolynomial.X l) =
            rootVar (m := m) (f := f) (insert j s) l from rfl,
            rootVar_eq_zero (fun h => (Finset.mem_insert.1 h).elim hlj hls), mul_zero]
  · apply le_antisymm
    · intro p hp
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hκφ, RingHom.mem_ker.1 hp, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simp only [g, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, φ, hι]
      rw [AlgHom.commutes, rootVar_pow (Finset.mem_insert_self j s), sub_self]

variable (C m f) in
/-- `RootRing ∅ = C`. -/
private noncomputable def rootRingEmptyEquiv : C ≃ₐ[C] RootRing C m f (∅ : Finset σ) :=
  AlgEquiv.ofAlgHom (Algebra.ofId C _)
    (rootRingLift ∅ (fun _ => 0) (fun l hl => absurd hl (Finset.notMem_empty l)) (fun _ _ => rfl))
    (rootRing_algHom_ext fun l => by
      rw [AlgHom.comp_apply, rootRingLift_rootVar, map_zero, AlgHom.id_apply,
        rootVar_eq_zero (Finset.notMem_empty l)])
    (AlgHom.ext fun a => by
      rw [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes, AlgHom.id_apply]
      rfl)

private theorem hasSNCParameters_atPrime_congr {A : Type*} [CommRing A] {I J : Ideal A} [I.IsPrime]
    [J.IsPrime] (hIJ : I = J) {Λ : Type*} (g : Λ → A) :
    HasSNCParameters (Localization.AtPrime I) (fun l => algebraMap A _ (g l)) ↔
      HasSNCParameters (Localization.AtPrime J) (fun l => algebraMap A _ (g l)) := by
  subst hIJ
  rfl

private theorem ringKrullDim_atPrime_congr {A : Type*} [CommRing A] {I J : Ideal A} [I.IsPrime]
    [J.IsPrime] (hIJ : I = J) :
    ringKrullDim (Localization.AtPrime I) = ringKrullDim (Localization.AtPrime J) := by
  subst hIJ
  rfl

/-- **Adjoining the roots one at a time.** If `C_P` has parameters adapted to `f`, the local
ring of `RootRing s` at a prime over `P` has parameters adapted to the `f l`, `l ∉ s`, and the
same dimension. -/
private theorem hasSNCParameters_rootRing [IsNoetherianRing C] [Finite σ] (hm : 0 < m)
    (hmu : IsUnit (m : C)) (s : Finset σ) (Q : Ideal (RootRing C m f s)) [Q.IsPrime]
    (h : HasSNCParameters (Localization.AtPrime (Q.comap (algebraMap C (RootRing C m f s))))
      (fun l => algebraMap C _ (f l))) :
    HasSNCParameters (Localization.AtPrime Q) (fun l : {l // l ∉ s} =>
        algebraMap _ (Localization.AtPrime Q) (algebraMap C (RootRing C m f s) (f l))) ∧
      ringKrullDim (Localization.AtPrime Q) =
        ringKrullDim (Localization.AtPrime (Q.comap (algebraMap C (RootRing C m f s)))) := by
  induction s using Finset.induction_on with
  | empty =>
    let e := (rootRingEmptyEquiv C m f).toRingEquiv
    let eQ := Localization.localRingEquiv (Q.comap e) Q e rfl
    refine ⟨?_, (ringKrullDim_eq_of_ringEquiv eQ).symm⟩
    have h2 := (h.map_ringEquiv eQ).comp
      (Subtype.val : {l : σ // l ∉ (∅ : Finset σ)} → σ) Subtype.val_injective
    convert h2 using 2 with l
    exact (Localization.localRingHom_to_map _ _ _ rfl _).symm
  | @insert j s hj ih =>
    letI := (rootRingIncl (m := m) (f := f) j hj).toRingHom.toAlgebra
    set ι := rootRingIncl (m := m) (f := f) j hj
    have hι : ∀ a, algebraMap (RootRing C m f s) (RootRing C m f (insert j s))
        (algebraMap C _ a) = algebraMap C _ a := ι.commutes
    set Q' := Q.comap (algebraMap (RootRing C m f s) (RootRing C m f (insert j s)))
    have hPQ : Q'.comap (algebraMap C (RootRing C m f s)) =
        Q.comap (algebraMap C (RootRing C m f (insert j s))) := by
      ext a
      simp only [Q', Ideal.mem_comap, hι]
    rw [← hasSNCParameters_atPrime_congr hPQ] at h
    rw [← ringKrullDim_atPrime_congr hPQ]
    obtain ⟨ih1, ih2⟩ := ih Q' h
    obtain ⟨φ, hφ, -, hker⟩ := exists_rootRing_insert_presentation (m := m) (f := f) j hj
    have hmu' : IsUnit (m : RootRing C m f s) := by
      simpa using hmu.map (algebraMap C (RootRing C m f s))
    obtain ⟨h1, h2⟩ := hasSNCParameters_of_ker_eq_span hm hmu'
      (fun l : {l // l ∉ s} => algebraMap C (RootRing C m f s) (f l)) ⟨j, hj⟩ φ hφ hker Q' Q rfl
      ih1
    refine ⟨?_, h2.trans ih2⟩
    let e : {l // l ∉ insert j s} → {l' : {l // l ∉ s} // l' ≠ ⟨j, hj⟩} := fun l =>
      ⟨⟨l.1, fun h => l.2 (Finset.mem_insert_of_mem h)⟩,
        fun h => l.2 (by rw [show l.1 = j from congrArg Subtype.val h]; exact
          Finset.mem_insert_self j s)⟩
    have he : Function.Injective e := fun a b hab =>
      Subtype.ext (congrArg (fun x => x.1.1) hab)
    convert h1.comp e he using 2 with l
    simp only [Function.comp_apply, e, hι]

end Chain

section Pushout

open CategoryTheory CategoryTheory.Limits

universe u

variable {k : Type u} [CommRing k] {σ : Type u} [DecidableEq σ] [Fintype σ] {C : Type u}
  [CommRing C] (m : ℕ) (ψ : MvPolynomial σ k →+* C)

/-- The coordinates `yₗ ↦ tₗ` of `RootRing`. -/
private noncomputable def rootRingCoord :
    MvPolynomial σ k →+* RootRing C m (fun l => ψ (MvPolynomial.X l)) Finset.univ :=
  MvPolynomial.eval₂Hom ((algebraMap C _).comp (ψ.comp MvPolynomial.C)) (rootVar Finset.univ)

/-- **`RootRing` is the base change of the `m`-th power map.** The square
`k[y] --ψ--> C`, `k[y] --expand m--> k[y] --(yₗ ↦ tₗ)--> RootRing` is a pushout of rings. -/
private theorem isPushout_rootRing :
    IsPushout (CommRingCat.ofHom ψ)
      (CommRingCat.ofHom (MvPolynomial.expand m : MvPolynomial σ k →ₐ[k] _).toRingHom)
      (CommRingCat.ofHom (algebraMap C (RootRing C m (fun l => ψ (MvPolynomial.X l))
        Finset.univ)))
      (CommRingCat.ofHom (rootRingCoord m ψ)) := by
  have hsq : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap C
      (RootRing C m (fun l => ψ (MvPolynomial.X l)) Finset.univ)) =
      CommRingCat.ofHom (MvPolynomial.expand m : MvPolynomial σ k →ₐ[k] _).toRingHom ≫
        CommRingCat.ofHom (rootRingCoord m ψ) := by
    ext1
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun l => ?_)
    · simp [rootRingCoord]
    · simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.expand_X,
        rootRingCoord, MvPolynomial.coe_eval₂Hom]
      rw [MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, rootVar_pow (Finset.mem_univ l)]
  refine IsPushout.of_isColimit' ⟨hsq⟩ (PushoutCocone.IsColimit.mk _ (fun s => ?_) ?_ ?_ ?_)
  · refine CommRingCat.ofHom (Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom s.inl.hom
      (fun l => s.inr.hom (MvPolynomial.X l))) ?_)
    intro p hp
    refine Submodule.span_induction ?_ (by simp)
      (fun _ _ _ _ h₁ h₂ => by rw [map_add, h₁, h₂, add_zero])
      (fun a _ _ h => by rw [smul_eq_mul, map_mul, h, mul_zero]) hp
    rintro _ (⟨⟨l, -⟩, rfl⟩ | ⟨⟨l, hl⟩, rfl⟩)
    · have hc := congrArg (fun F => F.hom (MvPolynomial.X l)) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.expand_X] at hc
      simp only [map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X,
        MvPolynomial.eval₂_C, hc, sub_self]
    · exact absurd (Finset.mem_univ l) hl
  · intro s
    ext1
    refine RingHom.ext fun c => ?_
    exact MvPolynomial.eval₂_C _ _ c
  · intro s
    ext1
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun l => ?_)
    · have hc := congrArg (fun F => F.hom (MvPolynomial.C a)) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.expand_C] at hc
      simp [rootRingCoord, ← hc]
      exact MvPolynomial.eval₂_C _ _ _
    · simp [rootRingCoord]
  · intro s φ h1 h2
    ext1
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c => ?_) (fun l => ?_))
    · have := congrArg (fun F => F.hom c) h1
      simp at this ⊢
      exact this
    · have := congrArg (fun F => F.hom (MvPolynomial.X l)) h2
      simp [rootRingCoord] at this ⊢
      exact this

end Pushout

end KummerLocalRings

section ChartPullback

/-! ### The power map over a chart

Over the standard chart `D₊(xᵢ) ≅ 𝔸^{ι ∖ i}` the power map is `Spec` of `yⱼ ↦ yⱼᵐ`, so over an
affine open `Spec C` of `Z` mapping into the chart, the fibre product `Z ×_{ℙ, p} ℙ` is
`Spec C[tⱼ]/(tⱼᵐ - fⱼ)`, `fⱼ` the pulled-back coordinates. -/

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization ProjectiveSpectrum.Proj

/-- `fromSpec` is the identity on the sections over its affine open. -/
private theorem fromSpec_appLE_self_apply {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) (x : Γ(X, U)) :
    (hU.fromSpec.appLE U ⊤ e).hom x = (Scheme.ΓSpecIso Γ(X, U)).inv.hom x := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_of_le U le_rfl]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp,
    show ((homOfLE le_top).op ≫ (homOfLE e).op : Opposite.op (⊤ : (Spec Γ(X, U)).Opens) ⟶ _) =
      𝟙 _ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), CategoryTheory.Functor.map_id]
  rfl

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι]

/-- The chart `Spec k[xⱼ : j ≠ i] ⟶ ℙ^ι` onto `D₊(xᵢ)`. -/
private noncomputable abbrev chartSpec (i : ι) :
    Spec (.of (MvPolynomial {j // j ≠ i} (CommRingCat.of k))) ⟶ ProjSpace k ι :=
  (AffineSpace.SpecIso {j // j ≠ i} (.of k)).inv ≫ ProjSpace.affineChart k i

private theorem chartSpec_eq (i : ι) :
    chartSpec (k := k) i =
      Spec.map (Stacks.AlgebraicGeometry.PolyChart.chartIso k i).toCommRingCatIso.hom ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) (X_mem_one' i)
        one_pos := by
  simp [chartSpec, ProjSpace.affineChart]

private theorem range_chartSpec (i : ι) :
    Set.range (chartSpec (k := k) i) =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) : Set _) := by
  show Set.range ((AffineSpace.SpecIso {j // j ≠ i} (.of k)).inv ≫ ProjSpace.affineChart k i) = _
  rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
    ProjSpace.opensRange_affineChart]

/-- **The chart on sections**: the function `xₗ / xᵢ` on `D₊(xᵢ)` pulls back to the coordinate
`xₗ`. -/
private theorem chartSpec_appLE_chartFraction (i : ι) (l : {j // j ≠ i})
    (h : (⊤ : (Spec (.of (MvPolynomial {j // j ≠ i} (CommRingCat.of k)))).Opens) ≤
      chartSpec i ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)) :
    ((chartSpec i).appLE _ ⊤ h).hom (chartFraction (MvPolynomial.homogeneousSubmodule ι k)
        (X_mem_one' i) 1 ⟨MvPolynomial.X l.1, X_mem_one' l.1⟩) =
      (Scheme.ΓSpecIso _).inv.hom (MvPolynomial.X l) := by
  set χ := (Stacks.AlgebraicGeometry.PolyChart.chartIso k i).toCommRingCatIso.hom
  set a := Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) (X_mem_one' i)
    one_pos
  have hD : (⊤ : (Spec (CommRingCat.of (Away (MvPolynomial.homogeneousSubmodule ι k)
      (MvPolynomial.X i)))).Opens) ≤ a ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) := by
    have hDa : Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) =
        a.opensRange := (Proj.opensRange_awayι _ _ (X_mem_one' i) one_pos).symm
    rw [hDa, Scheme.Hom.preimage_opensRange]
  have h1 := Scheme.Hom.appLE_comp_appLE (Spec.map χ) a _ ⊤ ⊤ hD le_top
  have e1 := congrArg (fun φ => φ.hom (chartFraction (MvPolynomial.homogeneousSubmodule ι k)
      (X_mem_one' i) 1 ⟨MvPolynomial.X l.1, X_mem_one' l.1⟩))
    ((appLE_congr_of_eq (chartSpec_eq i) _ ⊤ h _).trans h1.symm)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e1
  rw [e1]
  change ((Spec.map χ).appLE ⊤ ⊤ _).hom ((a.appLE _ ⊤ hD).hom
    ((Proj.awayToSection _ (MvPolynomial.X i)).hom (Away.mk _ (X_mem_one' i) 1
      (MvPolynomial.X l.1) _))) = _
  rw [Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection one_pos (X_mem_one' i) hD]
  have h3 := congrArg (fun φ => φ.hom (Away.mk (MvPolynomial.homogeneousSubmodule ι k)
    (X_mem_one' i) 1 (MvPolynomial.X l.1) (by simpa using X_mem_one' l.1)))
    (Scheme.ΓSpecIso_inv_naturality χ)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
  refine h3.symm.trans ?_
  congr 1
  change (Stacks.AlgebraicGeometry.PolyChart.chartIso k i) _ = _
  rw [← ProjSpace.chartIso_symm_X k i l, RingEquiv.apply_symm_apply]

/-- **The pulled-back hyperplane `{xₗ = 0}` near a point of an affine open over the chart** is cut
out by the pulled-back coordinate. -/
private theorem stalk_formZero_comap {Z : Scheme.{u}} (g : Z ⟶ ProjSpace k ι) (i : ι)
    {U : Z.Opens} (hU : IsAffineOpen U)
    (hUD : U ≤ g ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i))
    (ψ : CommRingCat.of (MvPolynomial {j // j ≠ i} (CommRingCat.of k)) ⟶ Γ(Z, U))
    (hψ : Spec.map ψ ≫ chartSpec i = hU.fromSpec ≫ g) (l : {j // j ≠ i}) (z : Z) (hz : z ∈ U) :
    IdealSheafData.stalk ((formZero k ι ⟨MvPolynomial.X l.1, X_mem_one' l.1⟩).comap g) z =
      Ideal.span {Z.presheaf.germ U z hz (ψ.hom (MvPolynomial.X l))} := by
  set D := Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
  have hDa : IsAffineOpen D := Proj.isAffineOpen_basicOpen _ _ (X_mem_one' i) one_pos
  set t := chartFraction (MvPolynomial.homogeneousSubmodule ι k) (X_mem_one' i) 1
    ⟨MvPolynomial.X l.1, X_mem_one' l.1⟩
  have h1 : (formZero k ι ⟨MvPolynomial.X l.1, X_mem_one' l.1⟩).ideal ⟨D, hDa⟩ =
      Ideal.span {t} :=
    zeroScheme_degreeSection_ideal_basicOpen _ (X_mem_one' i) one_pos 1 _
  have h2 := Stacks.IdealSheaf.ideal_comap_eq_span _ g ⟨D, hDa⟩ ⟨U, hU⟩ hUD h1
  have h3 : (g.appLE D U hUD).hom t = ψ.hom (MvPolynomial.X l) := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(Z, U)).inv).1
    have e0 : (⊤ : (Spec Γ(Z, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    rw [← fromSpec_appLE_self_apply hU e0]
    have e1 := Scheme.Hom.appLE_comp_appLE hU.fromSpec g D U ⊤ hUD e0
    have e2 : (⊤ : (Spec (.of (MvPolynomial {j // j ≠ i} (CommRingCat.of k)))).Opens) ≤
        chartSpec i ⁻¹ᵁ D := by
      intro x _
      show chartSpec i x ∈ (D : Set (ProjSpace k ι))
      rw [← range_chartSpec]; exact ⟨x, rfl⟩
    have e3 := Scheme.Hom.appLE_comp_appLE (Spec.map ψ) (chartSpec i) D ⊤ ⊤ e2 le_top
    have e4 := congrArg (fun φ => φ.hom t)
      (e1.trans ((appLE_congr_of_eq hψ.symm _ _ _ _).trans e3.symm))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e4
    rw [e4, chartSpec_appLE_chartFraction i l e2]
    have h5 := congrArg (fun φ => φ.hom (MvPolynomial.X l)) (Scheme.ΓSpecIso_inv_naturality ψ)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h5
    exact h5.symm
  rw [IdealSheafData.stalk_eq_map_germ _ z ⟨U, hU⟩ hz, h2, h3, Ideal.map_span,
    Set.image_singleton]

end ChartPullback

open Order in
/-- On an integral scheme of finite type over a field, of dimension `d`, a closed point has
codimension `d`. -/
private theorem coheight_eq_of_isClosed_singleton.{u} (k : Type u) [Field k] {U : Scheme.{u}}
    (sU : U ⟶ Spec (.of k)) [IsIntegral U] [LocallyOfFiniteType sU] (d : ℕ)
    (hd : topologicalKrullDim U = d) (u : U) (hu : IsClosed ({u} : Set U)) :
    coheight u = d := by
  let : U.Over (Spec (.of k)) := ⟨sU⟩
  haveI : LocallyOfFiniteType (U ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sU)
  have hpure : MMP.Intersection.IsPureDimensional U d := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ U).isHomeomorph.topologicalKrullDim_eq]; exact hd
  have h := MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure u
  have h0 : height u = 0 := by
    rw [height_eq_zero]
    intro y hy
    rw [Scheme.le_iff_specializes] at hy ⊢
    have : y ∈ closure ({u} : Set U) := specializes_iff_mem_closure.mp hy
    rw [hu.closure_eq, Set.mem_singleton_iff] at this
    rw [this]
  rw [h0, zero_add] at h
  exact h

/-- **The local rings of the fibre product with a power map.** If the coordinate hyperplanes
pull back to a simple normal crossing family on the smooth `Z`, the local rings of
`Z ×_{g, ℙ, p} ℙ` are regular, of the dimension of the local rings of `Z` below them. Over an
affine open `Spec C` of `Z` mapping into the chart `D₊(xᵢ)`, the fibre product is
`Spec C[tⱼ]/(tⱼᵐ - fⱼ)` (`isPushout_rootRing`), and the parameters adapted to the `fⱼ`
propagate (`hasSNCParameters_rootRing`). -/
private theorem isRegularLocalRing_stalk_pullback_of_isPowerMapChartwise.{u} (k : Type u) [Field k]
    [CharZero k] (N m : ℕ) (hm : 0 < m)
    (p : ProjSpace k (ULift.{u} (Fin (N + 1))) ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (hp : IsPowerMapChartwise k N m p)
    (Z : Scheme.{u}) (g : Z ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    [Smooth (g ≫ ProjSpace.toSpec k _)]
    (hg : MMP.Resolution.IsSNCFamily (g ≫ ProjSpace.toSpec k _)
      (fun i => (coordinateHyperplane k N i).comap g)) (w : ↥(pullback g p)) :
    IsRegularLocalRing ((pullback g p).presheaf.stalk w) ∧
      ringKrullDim ((pullback g p).presheaf.stalk w) =
        ringKrullDim (Z.presheaf.stalk (pullback.fst g p w)) := by
  obtain ⟨sZ, hsZ⟩ : ∃ sZ, sZ = g ≫ ProjSpace.toSpec k (ULift.{u} (Fin (N + 1))) := ⟨_, rfl⟩
  haveI : Smooth sZ := hsZ ▸ ‹_›
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  classical
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (N + 1))) (R := k)
  obtain ⟨i, hi⟩ : ∃ i : ULift.{u} (Fin (N + 1)), g (pullback.fst g p w) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)
        (MvPolynomial.X i) := by
    have : g (pullback.fst g p w) ∈ (⨆ i : ULift.{u} (Fin (N + 1)), Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) (MvPolynomial.X i)) := by
      rw [Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  set D := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)
    (MvPolynomial.X i) with hDdef
  set a := chartSpec (k := k) i with hadef
  have hpa : Spec.map (CommRingCat.ofHom (MvPolynomial.expand (R := CommRingCat.of k)
      (σ := {j // j ≠ i}) m).toRingHom) ≫ a = a ≫ p := by
    have := (hp i).2
    simp only [a, chartSpec, Category.assoc] at this ⊢
    exact this.symm
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hUle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show pullback.fst g p w ∈ g ⁻¹ᵁ D from hi) (g ⁻¹ᵁ D).isOpen
  have hUD : U ≤ g ⁻¹ᵁ D := hUle
  replace hU : IsAffineOpen U := hU
  have hrange : Set.range (hU.fromSpec ≫ g) ⊆ Set.range a := by
    rintro _ ⟨x, rfl⟩
    rw [hadef, range_chartSpec]
    have hx : hU.fromSpec x ∈ (U : Set Z) := by rw [← hU.range_fromSpec]; exact ⟨x, rfl⟩
    exact hUD hx
  set ψ := Spec.preimage (IsOpenImmersion.lift a (hU.fromSpec ≫ g) hrange) with hψdef
  have hψ : Spec.map ψ ≫ a = hU.fromSpec ≫ g := by
    rw [hψdef, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  set f : {j // j ≠ i} → Γ(Z, U) := fun l => ψ.hom (MvPolynomial.X l) with hfdef
  have hPO := isPushout_rootRing m ψ.hom
  rw [CommRingCat.ofHom_hom] at hPO
  have hPB := isPullback_SpecMap_of_isPushout _ _ _ _ hPO
  set Θ := hPB.isoPullback.hom ≫ pullback.map _ _ g p hU.fromSpec a a hψ hpa with hΘdef
  have hΘfst : Θ ≫ pullback.fst g p =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, U) (RootRing Γ(Z, U) m f Finset.univ))) ≫
        hU.fromSpec := by
    rw [hΘdef, Category.assoc, pullback.lift_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst]
  obtain ⟨q, rfl⟩ : w ∈ Set.range Θ := by
    have hw : w ∈ Set.range (pullback.map _ _ g p hU.fromSpec a a hψ hpa) := by
      rw [Scheme.Pullback.range_map]
      refine ⟨by rw [hU.range_fromSpec]; exact hzU, ?_⟩
      show pullback.snd g p w ∈ Set.range a
      rw [hadef, range_chartSpec]
      have hc : p (pullback.snd g p w) = g (pullback.fst g p w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      have hpre := (hp i).1
      rw [ProjSpace.opensRange_affineChart] at hpre
      have : pullback.snd g p w ∈ p ⁻¹ᵁ D := by
        show p (pullback.snd g p w) ∈ D
        rw [hc]; exact hi
      rw [hpre] at this
      exact this
    obtain ⟨x, hx⟩ := hw
    refine ⟨hPB.isoPullback.inv x, ?_⟩
    rw [← Scheme.Hom.comp_apply, hΘdef, Iso.inv_hom_id_assoc, hx]
  set RR := RootRing Γ(Z, U) m f Finset.univ with hRRdef
  set z := pullback.fst g p (Θ q) with hzdef
  -- the prime of `q` lies over the prime of `z`
  have hfz : hU.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, U) RR))) q) = z := by
    rw [hzdef, ← Scheme.Hom.comp_apply, ← hΘfst, Scheme.Hom.comp_apply]
  have hpt : (Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, U) RR))) q =
      hU.primeIdealOf ⟨z, hzU⟩ :=
    hU.fromSpec.isOpenEmbedding.injective (hfz.trans (hU.fromSpec_primeIdealOf ⟨z, hzU⟩).symm)
  have hqP : q.asIdeal.comap (algebraMap Γ(Z, U) RR) = (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal hpt
  -- parameters adapted to the coordinates at `z`
  haveI hdomz : IsDomain (Z.presheaf.stalk z) := by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sZ z
    exact IsRegularLocalRing.isDomain _
  have hE : ∀ l : {j // j ≠ i}, IdealSheafData.stalk
      ((coordinateHyperplane k N l.1.down).comap g) z =
        Ideal.span {Z.presheaf.germ U z hzU (f l)} := fun l =>
    stalk_formZero_comap g i hU hUD ψ hψ l z hzU
  obtain ⟨n, zz, c, hzz, hc, hcinj⟩ := hg.2 z
  have H0 : HasSNCParameters (Z.presheaf.stalk z)
      (fun l : {j // j ≠ i} => Z.presheaf.germ U z hzU (f l)) := by
    have hsupp : ∀ l : {l : {j // j ≠ i} //
        Z.presheaf.germ U z hzU (f l) ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk z)},
        z ∈ ((coordinateHyperplane k N l.1.1.down).comap g).support := by
      intro l
      by_contra hn
      rw [← Stacks.Divisors.stalk_eq_top_iff_notMem_support, hE, Ideal.span_singleton_eq_top]
        at hn
      exact (IsLocalRing.mem_maximalIdeal _).1 l.2 hn
    refine ⟨n, zz, fun l => c ⟨l.1.1.down, hsupp l⟩, hzz, fun l => ?_, fun l l' h => ?_⟩
    · have h1 := hc ⟨l.1.1.down, hsupp l⟩
      rw [hE] at h1
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h1
      refine ⟨↑u⁻¹, u⁻¹.isUnit, ?_⟩
      change Z.presheaf.germ U z hzU (f l.1) = _
      rw [← hu, mul_comm, Units.mul_inv_cancel_right]
    · have h2 : l.1.1.down = l'.1.1.down := congrArg Subtype.val (hcinj h)
      exact Subtype.ext (Subtype.ext (ULift.ext h2))
  letI := Z.presheaf.algebra_section_stalk ⟨z, hzU⟩
  haveI := hU.isLocalization_stalk ⟨z, hzU⟩
  set P := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal with hPdef
  let ez := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) (Z.presheaf.stalk z)
  have H1 : HasSNCParameters (Localization.AtPrime P) (fun l => algebraMap Γ(Z, U) _ (f l)) := by
    have := H0.map_ringEquiv ez.symm.toRingEquiv
    convert this using 2 with l
    exact (ez.symm.commutes (f l)).symm
  -- the chain
  haveI : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hmu : IsUnit (m : Γ(Z, U)) := by
    let ρ : k →+* Γ(Z, U) := (Z.presheaf.map (homOfLE le_top).op).hom.comp
      ((sZ.app ⊤).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    have h : IsUnit (m : k) := (Nat.cast_ne_zero.2 hm.ne').isUnit
    exact map_natCast ρ m ▸ h.map ρ
  haveI hqPprime : (q.asIdeal.comap (algebraMap Γ(Z, U) RR)).IsPrime := hqP ▸ inferInstance
  have H2 := (hasSNCParameters_atPrime_congr hqP f).2 H1
  haveI hqprime : q.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := RR) q
  obtain ⟨H3, hdim⟩ := hasSNCParameters_rootRing (C := Γ(Z, U)) (m := m) (f := f) hm hmu
    Finset.univ q.asIdeal H2
  obtain ⟨n', zz', c', hrsop, -, -⟩ := H3
  haveI : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
    MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hrsop
  -- the stalk of the fibre product
  letI : Algebra RR ((Spec (CommRingCat.of RR)).presheaf.stalk q) :=
    StructureSheaf.stalkAlgebra RR q
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of RR)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk RR q
  let eq := IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
    ((Spec (CommRingCat.of RR)).presheaf.stalk q)
  have hΘ : IsOpenImmersion Θ := by rw [hΘdef]; infer_instance
  clear_value Θ
  haveI hΘq : IsIso (Θ.stalkMap q) := (IsOpenImmersion.iff_isIso_stalkMap.1 hΘ).2 q
  let eW := (asIso (Θ.stalkMap q)).commRingCatIsoToRingEquiv
  let e := eq.toRingEquiv.trans eW.symm
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv e, hdim, ringKrullDim_atPrime_congr hqP,
    ringKrullDim_eq_of_ringEquiv ez.toRingEquiv]

open Order in
/-- On a scheme smooth and quasi-compact over a field, the dimension of an irreducible component
is the dimension of the local ring at any of its closed points. -/
private theorem topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed.{u} {k : Type u} [Field k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [Smooth s] [QuasiCompact s] {C : Set Y}
    (hC : C ∈ irreducibleComponents Y) {y : Y} (hyC : y ∈ C) (hy : IsClosed ({y} : Set Y)) :
    topologicalKrullDim C = ringKrullDim (Y.presheaf.stalk y) := by
  obtain ⟨U, rfl, hU, hUc⟩ := exists_opens_isIntegral_of_mem_irreducibleComponents s hC
  haveI : QuasiCompact U.ι :=
    quasiCompact_iff_forall_isAffineOpen.mpr fun _ hV ↦ (hV.preimage U.ι).isCompact
  haveI : Nonempty U.toScheme := ⟨⟨y, hyC⟩⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_eq_natCast k (U.ι ≫ s)
  have hdC : topologicalKrullDim (U : Set Y) = d := by
    rw [← hd]
    rfl
  have hwcl : IsClosed ({(⟨y, hyC⟩ : U.toScheme)} : Set U.toScheme) := by
    convert hy.preimage U.ι.continuous using 1
    ext v
    exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
  have hcoU := coheight_eq_of_isClosed_singleton k (U.ι ≫ s) d hd _ hwcl
  have hr := ringKrullDim_stalk_eq_coheight (X := U.toScheme) ⟨y, hyC⟩
  rw [hcoU, ringKrullDim_eq_of_ringEquiv (U.stalkIso ⟨y, hyC⟩).commRingCatIsoToRingEquiv] at hr
  rw [hdC, hr]
  rfl

/-- **Transversal pullbacks of the power map are smooth.** Let `g : Z ⟶ ℙᴺ` be
a morphism from a smooth separated quasi-compact `k`-scheme along which the coordinate
hyperplanes pull back to a simple normal crossing family. Over the chart `xᵢ ≠ 0` the fibre
product `Z ×_{g, p} ℙᴺ` is `Spec 𝒪_Z[tⱼ]/(tⱼᵐ - fⱼ)` with `fⱼ = g^*(xⱼ/xᵢ)`; at a point where the
vanishing `fⱼ` are part of a regular system of parameters its local ring is regular of the same
dimension (the `tⱼ` replace the `fⱼ`), and where `fⱼ` is a unit the factor is étale since `m` is
invertible in `k` (`isRegularLocalRing_stalk_pullback_of_isPowerMapChartwise`). So the fibre
product is smooth over `k`, and pure of dimension `d` if `Z` is: the dimension of a component is
that of the local ring at a closed point, and closed points lie over closed points. -/
private theorem smooth_pullback_of_isPowerMapChartwise.{u} (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] (N m : ℕ) (hm : 0 < m)
    (p : ProjSpace k (ULift.{u} (Fin (N + 1))) ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (hp : IsPowerMapChartwise k N m p)
    (Z : Scheme.{u}) (g : Z ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    [Smooth (g ≫ ProjSpace.toSpec k _)] [QuasiCompact (g ≫ ProjSpace.toSpec k _)]
    [IsSeparated (g ≫ ProjSpace.toSpec k _)]
    (hg : MMP.Resolution.IsSNCFamily (g ≫ ProjSpace.toSpec k _)
      (fun i => (coordinateHyperplane k N i).comap g)) :
    Smooth (pullback.fst g p ≫ g ≫ ProjSpace.toSpec k _) ∧
      ∀ d : ℤ, MMP.IsPureDimensional Z d →
        MMP.IsPureDimensional (pullback g p) d := by
  have KP := isRegularLocalRing_stalk_pullback_of_isPowerMapChartwise k N m hm p hp Z g hg
  obtain ⟨hpf, -⟩ := isFinite_surjective_of_isPowerMapChartwise k N m hm p hp
  obtain ⟨sZ, hsZ⟩ : ∃ sZ, sZ = g ≫ ProjSpace.toSpec k (ULift.{u} (Fin (N + 1))) := ⟨_, rfl⟩
  haveI : Smooth sZ := hsZ ▸ ‹_›
  haveI : QuasiCompact sZ := hsZ ▸ ‹_›
  haveI : IsFinite (pullback.fst g p) := inferInstance
  obtain ⟨sW, hsW⟩ : ∃ sW, sW = pullback.fst g p ≫ sZ := ⟨_, rfl⟩
  haveI : LocallyOfFiniteType sW := by
    haveI : LocallyOfFiniteType (pullback.fst g p) := inferInstance
    rw [hsW]; infer_instance
  haveI : QuasiCompact sW := by
    haveI : QuasiCompact (pullback.fst g p) := inferInstance
    rw [hsW]; infer_instance
  have hsmooth : Smooth sW :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sW).2
      fun w => (KP w).1
  refine ⟨by rw [← hsZ, ← hsW]; exact hsmooth, fun d hd C hC => ?_⟩
  haveI : CompactSpace ↥(pullback g p) := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨w, hwC, hwcl⟩ :=
    (isClosed_of_mem_irreducibleComponents C hC).exists_closed_singleton hC.1.nonempty
  have h1 := topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed sW hC hwC hwcl
  have hzcl : IsClosed ({pullback.fst g p w} : Set Z) := by
    rw [← Set.image_singleton]
    exact (pullback.fst g p).isClosedMap _ hwcl
  have h2 := topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed sZ
    (irreducibleComponent_mem_irreducibleComponents (pullback.fst g p w))
    mem_irreducibleComponent hzcl
  obtain ⟨n, hn, hdim⟩ := hd _ (irreducibleComponent_mem_irreducibleComponents _)
  exact ⟨n, hn, by rw [h1, (KP w).2, ← h2, hdim]⟩

section LinearAutomorphism

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousIdeal AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {k : Type u} [Field k] {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The linear substitution `xᵢ ↦ ∑ⱼ Aᵢⱼ xⱼ`, a graded endomorphism of `k[xᵢ]`. -/
private noncomputable def linSubst (A : Matrix ι ι k) :
    MvPolynomial.homogeneousSubmodule ι k →+*ᵍ MvPolynomial.homogeneousSubmodule ι k where
  toRingHom := (MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) :
    MvPolynomial ι k →ₐ[k] MvPolynomial ι k).toRingHom
  map_mem {n x} hx := by
    have h := ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hx).aeval
      (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) (n := 1) (fun i =>
        MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
          (MvPolynomial.isHomogeneous_X k j).C_mul _)
    rw [one_mul] at h
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 h

/-- `linSubst A` is evaluation at the linear forms `∑ⱼ Aᵢⱼ xⱼ`. -/
private theorem linSubst_apply (A : Matrix ι ι k) (p : MvPolynomial ι k) :
    linSubst A p = MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) p :=
  rfl

/-- Substitutions compose by multiplying matrices. -/
private theorem linSubst_comp (A B : Matrix ι ι k) :
    (linSubst A).comp (linSubst B) = linSubst (B * A) := by
  refine GradedRingHom.ext fun p => ?_
  rw [GradedRingHom.comp_apply, linSubst_apply, linSubst_apply, linSubst_apply,
    ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The identity matrix gives the identity substitution. -/
private theorem linSubst_one : linSubst (1 : Matrix ι ι k) = GradedRingHom.id _ := by
  refine GradedRingHom.ext fun p => ?_
  change MvPolynomial.aeval _ p = p
  have : (fun i => ∑ j, MvPolynomial.C ((1 : Matrix ι ι k) i j) * MvPolynomial.X j) =
      (MvPolynomial.X : ι → MvPolynomial ι k) := by
    funext i
    simp [Matrix.one_apply]
  rw [this, MvPolynomial.aeval_X_left_apply]

variable (k) in
/-- The irrelevant-ideal condition of `Proj.map` for an invertible substitution. -/
private theorem irrelevant_le_linSubst (A : Matrix ι ι k) [Invertible A] :
    (MvPolynomial.homogeneousSubmodule ι k)₊ ≤
      (MvPolynomial.homogeneousSubmodule ι k)₊.map (linSubst A) :=
  Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse _ (linSubst (⅟A))
    (by rw [linSubst_comp, invOf_mul_self, linSubst_one])

/-- The linear automorphism of `ℙ^ι_k` of an invertible matrix. -/
private noncomputable def linAut (A : Matrix ι ι k) [Invertible A] :
    ProjSpace k ι ≅ ProjSpace k ι where
  hom := Proj.map (linSubst (⅟A)) (irrelevant_le_linSubst k (⅟A))
  inv := Proj.map (linSubst A) (irrelevant_le_linSubst k A)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact (MMP.Intersection.projMap_congr _ _ _ _
      (by rw [linSubst_comp, mul_invOf_self, linSubst_one])).trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact (MMP.Intersection.projMap_congr _ _ _ _
      (by rw [linSubst_comp, invOf_mul_self, linSubst_one])).trans Proj.map_id

/-- `Proj` of a linear substitution lies over `k`. -/
private theorem projMap_linSubst_toSpec (A : Matrix ι ι k) [Invertible A] :
    Proj.map (linSubst A) (irrelevant_le_linSubst k A) ≫ ProjSpace.toSpec k ι =
      ProjSpace.toSpec k ι := by
  rw [ProjSpace.toSpec, Proj.map_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 3
  refine RingHom.ext fun a => Subtype.ext ?_
  change linSubst A (MvPolynomial.C a) = MvPolynomial.C a
  rw [linSubst_apply, MvPolynomial.aeval_C]
  rfl

/-- The linear automorphism lies over `k`. -/
private theorem linAut_hom_toSpec (A : Matrix ι ι k) [Invertible A] :
    (linAut A).hom ≫ ProjSpace.toSpec k ι =
      ProjSpace.toSpec k ι :=
  projMap_linSubst_toSpec (⅟A)

/-- `σ⁻¹^* 𝒪(1) ≅ 𝒪(1)` for a linear automorphism `σ`. -/
private noncomputable def linAutInvTwistOneIso (A : Matrix ι ι k) [Invertible A] :
    (Scheme.Modules.pullback (linAut A).inv).obj (ProjSpace.twistOne k ι) ≅
      ProjSpace.twistOne k ι :=
  @asIso _ _ _ _ (Stacks.ProjTwistComparison.twistMap (linSubst A) (irrelevant_le_linSubst k A) 1)
    (Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id (linSubst A)
      (irrelevant_le_linSubst k A) 1 (linSubst (⅟A))
      (by rw [linSubst_comp, invOf_mul_self, linSubst_one])
      (by rw [linSubst_comp, mul_invOf_self, linSubst_one]))

/-- `linSubst A` is surjective for invertible `A`: `linSubst A ∘ linSubst A⁻¹ = id`. -/
private theorem linSubst_surjective (A : Matrix ι ι k) [Invertible A] :
    Function.Surjective (linSubst A) := fun p => ⟨linSubst (⅟A) p, by
  rw [← GradedRingHom.comp_apply, linSubst_comp, invOf_mul_self, linSubst_one]; rfl⟩

/-- `σ_A⁻¹ Hᵢ` is the hyperplane of the linear form `∑ⱼ (A⁻¹)ᵢⱼ xⱼ`. -/
private theorem formZero_X_comap_linAut (A : Matrix ι ι k) [Invertible A] (i : ι)
    (hX : (MvPolynomial.X i : MvPolynomial ι k) ∈ MvPolynomial.homogeneousSubmodule ι k 1)
    (hb : ∑ j, MvPolynomial.C ((⅟A) i j) * MvPolynomial.X j ∈
      MvPolynomial.homogeneousSubmodule ι k 1) :
    (formZero k ι ⟨MvPolynomial.X i, hX⟩).comap (linAut A).hom = formZero k ι ⟨_, hb⟩ := by
  refine (formZero_comap_projMap (linSubst (⅟A)) (irrelevant_le_linSubst k (⅟A))
    (linSubst_surjective (⅟A)) ⟨MvPolynomial.X i, hX⟩).trans ?_
  congr 2
  simp [linSubst_apply]

end LinearAutomorphism

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **The pulled-back coordinate hyperplanes are members of the pulled-back system.** For
`t : X ⟶ ℙᴺ_k` over `k` and any `j : Y ⟶ X`, the inverse image of the coordinate
hyperplane `Hᵢ` along `j ≫ t ≫ σ_A` is the trace on `Y` of the zero scheme of the section
`∑ₗ (A⁻¹)ᵢₗ t^* xₗ` of `t^* 𝒪(1)`. -/
private theorem coordinateHyperplane_comap_linAut_eq.{u} {k : Type u} [Field k] {N : ℕ}
    (A : Matrix (ULift.{u} (Fin (N + 1))) (ULift.{u} (Fin (N + 1))) k) [Invertible A]
    (i : Fin (N + 1)) {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (t : X ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (ht : t ≫ ProjSpace.toSpec k _ = X ↘ Spec (.of k)) {Y : Scheme.{u}} (j : Y ⟶ X) :
    letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (N + 1))) (R := k)
    letI := globalSectionsModule (k := k) (X := X)
    (coordinateHyperplane k N i).comap (j ≫ t ≫ (linAut A).hom) =
      (Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback t).obj
        (ProjectiveSpectrum.Proj.twistingSheafModule
          (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) ((1 : ℕ) : ℤ)))
        (MMP.Threefold.Bridges.systemSection
          (fun l : Fin (N + 1) => pullbackGlobalSections t
            (ProjectiveSpectrum.Proj.twistingSheafModule
              (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) ((1 : ℕ) : ℤ))
            (ProjectiveSpectrum.Proj.degreeSection _ 1 ⟨MvPolynomial.X (ULift.up l),
              (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X k _)⟩))
          (fun l => (⅟A) (ULift.up i) (ULift.up l)))).comap j := by
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (N + 1))) (R := k)
  letI := globalSectionsModule (k := k) (X := X)
  have hb : ∑ l, MvPolynomial.C ((⅟A) (ULift.up i) l) * MvPolynomial.X l ∈
      MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k 1 :=
    Submodule.sum_mem _ fun l _ =>
      (MvPolynomial.mem_homogeneousSubmodule _ _).2 ((MvPolynomial.isHomogeneous_X k l).C_mul _)
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, coordinateHyperplane,
    formZero_X_comap_linAut A _ _ hb]
  congr 1
  refine (Stacks.Divisors.zeroScheme_pullback _ _ _).symm.trans ?_
  congr 1
  rw [pullback_degreeSection_linearForm t ht _ hb (fun l =>
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X k l)),
    MMP.Threefold.Bridges.systemSection_apply]
  exact (Fintype.sum_equiv Equiv.ulift _ _ fun l => rfl)

section BertiniChoice

/-! ### Choosing the rows of the change of coordinates one at a time -/

universe u

open MMP.Threefold.Bridges Stacks.NonvanishingOpen

variable {k : Type u} [Field k]

/-- An invertible module in the `Stacks.Ample` spelling is invertible in the spelling of zero
schemes. -/
private local instance isInvertible_of_isInvertibleModule {X : Scheme.{u}} {L : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-- An empty family on a smooth scheme over a field is a simple normal crossing family: every
local ring is regular, hence has a regular system of parameters. -/
private theorem isSNCFamily_of_isEmpty {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [Smooth f]
    {Λ : Type*} [IsEmpty Λ] (E : Λ → Y.IdealSheafData) : MMP.Resolution.IsSNCFamily f E := by
  refine ⟨isEmptyElim, fun x => ?_⟩
  have := isRegularLocalRing_stalk_of_smooth_over_field f x
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk x)
  exact ⟨n, z, fun i => isEmptyElim i.1, hz, fun i => isEmptyElim i.1, fun i => isEmptyElim i.1⟩

/-- An snc family stays an snc family along an injective reindexing. -/
private theorem isSNCFamily_comp {Y : Scheme.{u}} {f : Y ⟶ Spec (.of k)} {Λ Λ' : Type*}
    {E : Λ → Y.IdealSheafData} (hE : MMP.Resolution.IsSNCFamily f E) (e : Λ' → Λ)
    (he : Function.Injective e) : MMP.Resolution.IsSNCFamily f (E ∘ e) := by
  refine ⟨fun i => hE.1 (e i), fun x => ?_⟩
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hE.2 x
  refine ⟨n, z, fun i => c ⟨e i.1, i.2⟩, hz, fun i => hc ⟨e i.1, i.2⟩, fun i i' h => ?_⟩
  exact Subtype.ext (he (congrArg Subtype.val (hinj h)))

/-- A dense open of `𝔸ᴺ⁺¹_k` contains the points where some nonzero polynomial does not vanish. -/
private theorem exists_ne_zero_eval_ne_zero_imp_mem {N : ℕ} (U : (coefficientSpace k N).Opens)
    (hU : Dense (U : Set (coefficientSpace k N))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧
      ∀ c : Fin (N + 1) → k, MvPolynomial.eval c Q ≠ 0 → coefficientPoint c ∈ U := by
  obtain ⟨x, hx⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨f, fun h => ?_, fun c hc => hfU ?_⟩
  · subst h
    exact hxf (by simp)
  · change f ∉ RingHom.ker (MvPolynomial.eval c)
    exact fun h => hc ((RingHom.mem_ker).mp h)

/-- The linear form `∑ₗ f(eₗ) xₗ` of a functional `f`, evaluated at `b`, is `f b`. -/
private theorem eval_linearForm {N : ℕ} (f : Module.Dual k (Fin (N + 1) → k))
    (b : Fin (N + 1) → k) :
    MvPolynomial.eval b (∑ l, MvPolynomial.C (f (Pi.single l 1)) * MvPolynomial.X l) = f b := by
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  conv_rhs => rw [← Finset.univ_sum_single b]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (Pi.single l (b l) : Fin (N + 1) → k) = b l • Pi.single l 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

/-- **One more row.** For a free system `s` of an invertible sheaf on a variety and finitely many
smooth `Z c ⟶ X` carrying snc families `G c`, and a proper subspace `W` of coefficients, there is a
coefficient vector `b ∉ W` whose trace on every `Z c` extends `G c` to an snc family. Bertini gives
for each `c` a nonzero polynomial `Q_c` off whose zeros the extension is snc; a nonzero linear form
`ℓ` vanishes on `W`; and `ℓ · ∏ Q_c` is nonzero on some point of the infinite field. -/
private theorem exists_not_mem_isSNCFamily_option [IsAlgClosed k] [CharZero k] {N : ℕ}
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [AlgebraicGeometry.IsVariety k (X ↘ Spec (.of k))]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    {κ : Type*} [Finite κ] (Z : κ → Scheme.{u}) (j : ∀ c, Z c ⟶ X) [∀ c, IsImmersion (j c)]
    [∀ c, Smooth (j c ≫ X ↘ Spec (.of k))] {Λ : Type u} [Finite Λ]
    (G : ∀ c, Λ → (Z c).IdealSheafData)
    (hG : ∀ c, MMP.Resolution.IsSNCFamily (j c ≫ X ↘ Spec (.of k)) (G c))
    (W : Submodule k (Fin (N + 1) → k)) (hW : W < ⊤) :
    ∃ b : Fin (N + 1) → k, b ∉ W ∧ ∀ c, MMP.Resolution.IsSNCFamily (j c ≫ X ↘ Spec (.of k))
      (fun o : Option Λ =>
        o.elim ((Stacks.Divisors.zeroScheme X L (systemSection s b)).comap (j c)) (G c)) := by
  classical
  have := Fintype.ofFinite κ
  have hQ : ∀ c, ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ b : Fin (N + 1) → k,
      MvPolynomial.eval b Q ≠ 0 → MMP.Resolution.IsSNCFamily (j c ≫ X ↘ Spec (.of k))
        (fun o : Option Λ =>
          o.elim ((Stacks.Divisors.zeroScheme X L (systemSection s b)).comap (j c)) (G c)) := by
    intro c
    obtain ⟨⟨U, hU, hUc⟩, -⟩ := exists_dense_open_isSNCFamily_zeroScheme s hs (j c) (G c) (hG c)
    obtain ⟨Q, hQ0, hQU⟩ := exists_ne_zero_eval_ne_zero_imp_mem U hU
    exact ⟨Q, hQ0, fun b hb => (hUc b (hQU b hb)).2.2⟩
  choose Q hQ0 hQ using hQ
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W hW
  set P : MvPolynomial (Fin (N + 1)) k :=
    ∑ l, MvPolynomial.C (f (Pi.single l 1)) * MvPolynomial.X l with hPdef
  have hP0 : P ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun b => ?_
    rw [← eval_linearForm f b, ← hPdef, h, map_zero]
    rfl
  have hF0 : P * ∏ c, Q c ≠ 0 :=
    mul_ne_zero hP0 (Finset.prod_ne_zero_iff.mpr fun c _ => hQ0 c)
  obtain ⟨b, hb⟩ : ∃ b, MvPolynomial.eval b (P * ∏ c, Q c) ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_mul, map_prod] at hb
  refine ⟨b, fun hbW => ?_, fun c => hQ c b ?_⟩
  · refine left_ne_zero_of_mul hb ?_
    rw [hPdef, eval_linearForm]
    exact hWf hbW
  · exact Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hb) c (Finset.mem_univ c)

/-- **The rows, one at a time.** In the setting of `exists_not_mem_isSNCFamily_option`, for every
`t ≤ N + 1` there are `t` linearly independent coefficient vectors whose traces form an snc family
on every `Z c`. -/
private theorem exists_linearIndependent_isSNCFamily [IsAlgClosed k] [CharZero k] {N : ℕ}
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [AlgebraicGeometry.IsVariety k (X ↘ Spec (.of k))]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    {κ : Type*} [Finite κ] (Z : κ → Scheme.{u}) (j : ∀ c, Z c ⟶ X) [∀ c, IsImmersion (j c)]
    [∀ c, Smooth (j c ≫ X ↘ Spec (.of k))] :
    ∀ t ≤ N + 1, ∃ b : Fin t → Fin (N + 1) → k, LinearIndependent k b ∧
      ∀ c, MMP.Resolution.IsSNCFamily (j c ≫ X ↘ Spec (.of k))
        (fun i : ULift.{u} (Fin t) =>
          (Stacks.Divisors.zeroScheme X L (systemSection s (b i.down))).comap (j c)) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun c => isSNCFamily_of_isEmpty _ _⟩
  | succ t ih =>
    intro ht
    obtain ⟨b, hb, hsnc⟩ := ih (by omega)
    have hW : Submodule.span k (Set.range b) < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun h => ?_
      have h1 := finrank_range_le_card (R := k) b
      rw [Set.finrank, h, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
      omega
    let G : ∀ c, ULift.{u} (Fin t) → (Z c).IdealSheafData := fun c i =>
      (Stacks.Divisors.zeroScheme X L (systemSection s (b i.down))).comap (j c)
    obtain ⟨b', hb'W, hb'⟩ := exists_not_mem_isSNCFamily_option (Λ := ULift.{u} (Fin t)) s hs Z j
      G hsnc _ hW
    refine ⟨Fin.snoc b b', linearIndependent_fin_snoc.mpr ⟨hb, hb'W⟩, fun c => ?_⟩
    let e : ULift.{u} (Fin (t + 1)) → Option (ULift.{u} (Fin t)) :=
      fun i => (finSuccEquivLast i.down).map ULift.up
    have he : Function.Injective e := fun i i' h =>
      ULift.ext (finSuccEquivLast.injective (Option.map_injective ULift.up_injective h))
    refine (congrArg _ (funext fun i => ?_)).mp (isSNCFamily_comp (hb' c) e he)
    obtain ⟨i⟩ := i
    induction i using Fin.lastCases with
    | last =>
      change Option.elim (Option.map ULift.up (finSuccEquivLast (Fin.last t))) _ (G c) = _
      rw [finSuccEquivLast_last, Option.map_none, Option.elim_none, Fin.snoc_last]
    | cast i =>
      change Option.elim (Option.map ULift.up (finSuccEquivLast (Fin.castSucc i))) _ (G c) = _
      rw [finSuccEquivLast_castSucc, Option.map_some, Option.elim_some, Fin.snoc_castSucc]

end BertiniChoice

/-- **A change of coordinates puts finitely many smooth closed subschemes of a variety in
general position with the coordinate hyperplanes.** Let `X` be a variety over
`k` with `h : X ⟶ ℙᴺ_k` over `k`, and `j c : Z c ⟶ X` finitely many closed immersions with `Z c`
smooth. There is an invertible matrix `A` such that the coordinate hyperplanes pull back along
every `j c ≫ h ≫ σ_A`, `σ_A` the linear automorphism `linAut A`, to a simple normal crossing
family on `Z c`. These pullbacks are the zero schemes of the sections `ℓᵢ = ∑ⱼ (A⁻¹)ᵢⱼ h^* xⱼ`
of `h^* 𝒪(1)` restricted to `Z c`; the rows are chosen one at a time, by Bertini for the free
system spanned by the `h^* xⱼ` and the snc family already chosen
(`MMP.Threefold.Bridges.exists_dense_open_isSNCFamily_zeroScheme`, applied with the immersion
`j c`), intersected with the dense open of rows outside the span of the earlier ones; a finite
intersection of dense opens of `𝔸^{N+1}_k` has a `k`-point. -/
private theorem exists_linAut_isSNCFamily_coordinateHyperplane.{u} (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] (N : ℕ) {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k sX] (h : X ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (hh : h ≫ ProjSpace.toSpec k _ = sX) {κ : Type*} [Finite κ] (Z : κ → Scheme.{u})
    (j : ∀ c, Z c ⟶ X) [∀ c, IsClosedImmersion (j c)] [∀ c, Smooth (j c ≫ sX)] :
    ∃ (A : Matrix (ULift.{u} (Fin (N + 1))) (ULift.{u} (Fin (N + 1))) k) (_ : Invertible A),
      ∀ c, MMP.Resolution.IsSNCFamily ((j c ≫ h ≫ (linAut A).hom) ≫ ProjSpace.toSpec k _)
        (fun i => (coordinateHyperplane k N i).comap (j c ≫ h ≫ (linAut A).hom)) := by
  classical
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (N + 1))) (R := k)
  letI := Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule
    (k := k) (X := X)
  have hX1 : ∀ l : Fin (N + 1), (MvPolynomial.X (ULift.up l) :
      MvPolynomial (ULift.{u} (Fin (N + 1))) k) ∈
        MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k 1 := fun l =>
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X k _)
  haveI : Stacks.Ample.IsInvertibleModule (ProjSpace k (ULift.{u} (Fin (N + 1))))
      (ProjectiveSpectrum.Proj.twistingSheafModule
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) ((1 : ℕ) : ℤ)) :=
    isInvertible_twistingSheafModule_one k _
  haveI : Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback h).obj
      (ProjectiveSpectrum.Proj.twistingSheafModule
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) ((1 : ℕ) : ℤ))) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback h _
  haveI : AlgebraicGeometry.IsVariety k (X ↘ Spec (.of k)) := ‹MMP.Mori.IsVariety k sX›
  haveI : ∀ c, Smooth (j c ≫ X ↘ Spec (.of k)) := fun c => ‹∀ c, Smooth (j c ≫ sX)› c
  let s : Fin (N + 1) → Γ((Scheme.Modules.pullback h).obj
      (ProjectiveSpectrum.Proj.twistingSheafModule
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) ((1 : ℕ) : ℤ)), ⊤) :=
    fun l => pullbackGlobalSections h
      (ProjectiveSpectrum.Proj.twistingSheafModule
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) ((1 : ℕ) : ℤ))
      (ProjectiveSpectrum.Proj.degreeSection _ 1 ⟨_, hX1 l⟩)
  have hs : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen X _
      (MMP.Threefold.Bridges.systemSection s c) = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    have hx : h x ∈ (⨆ i : ULift.{u} (Fin (N + 1)), Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) (MvPolynomial.X i)) := by
      rw [Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top]
      trivial
    obtain ⟨⟨l⟩, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨(Pi.single l (1 : k) : Fin (N + 1) → k), ?_⟩
    have hsl : MMP.Threefold.Bridges.systemSection s (Pi.single l (1 : k)) = s l := by
      rw [MMP.Threefold.Bridges.systemSection_apply, Finset.sum_eq_single l
        (fun l' _ hl' => by rw [Pi.single_eq_of_ne hl', zero_smul]) (by simp),
        Pi.single_eq_same, one_smul]
    rw [hsl]
    have e :=
      Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections
      h (ProjectiveSpectrum.Proj.twistingSheafModule
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) ((1 : ℕ) : ℤ))
      (ProjectiveSpectrum.Proj.degreeSection _ 1 ⟨_, hX1 l⟩)
    refine (SetLike.ext_iff.mp e x).mpr ?_
    change h x ∈ Stacks.Ample.nonvanishingLocus _ _
    have :=
      Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen
      (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) (adjoin_one_eq_top k _)
      one_pos 1 ⟨_, hX1 l⟩
    exact this.symm ▸ hl
  obtain ⟨b, hb, hsnc⟩ := exists_linearIndependent_isSNCFamily s hs Z j (N + 1) le_rfl
  let B : Matrix (ULift.{u} (Fin (N + 1))) (ULift.{u} (Fin (N + 1))) k :=
    Matrix.of fun i l => b i.down l.down
  have hB : IsUnit B := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    have h1 : LinearIndependent k (fun i : ULift.{u} (Fin (N + 1)) => b i.down) :=
      hb.comp _ ULift.down_injective
    exact h1.map' (LinearEquiv.funCongrLeft k k Equiv.ulift).toLinearMap (LinearEquiv.ker _)
  letI := hB.invertible
  refine ⟨⅟B, invertibleInvOf, fun c => ?_⟩
  have e1 : (j c ≫ h ≫ (linAut (⅟B)).hom) ≫ ProjSpace.toSpec k _ = j c ≫ X ↘ Spec (.of k) := by
    rw [Category.assoc, Category.assoc, linAut_hom_toSpec, hh]
    rfl
  rw [e1]
  have e2 : (fun i => (coordinateHyperplane k N i).comap (j c ≫ h ≫ (linAut (⅟B)).hom)) =
      (fun i : ULift.{u} (Fin (N + 1)) =>
        (Stacks.Divisors.zeroScheme X _
          (MMP.Threefold.Bridges.systemSection s (b i.down))).comap (j c)) ∘
          ULift.up := by
    funext i
    refine (coordinateHyperplane_comap_linAut_eq (⅟B) i h hh (j c)).trans ?_
    have : (fun l => (⅟(⅟B)) (ULift.up i) (ULift.up l)) = b i :=
      funext fun l => by rw [invOf_invOf]; rfl
    rw [this]
    rfl
  rw [e2]
  exact isSNCFamily_comp (hsnc c) _ ULift.up_injective

/-- Base change along `p ≫ σ⁻¹` is base change of `s ≫ σ` along `p`, compatibly with the first
projections. -/
private theorem pullback_comp_inv_iso.{u} {Z T T' : Scheme.{u}} (s : Z ⟶ T) (σ : T ≅ T')
    (p : T ⟶ T') :
    ∃ e : pullback s (p ≫ σ.inv) ≅ pullback (s ≫ σ.hom) p,
      e.hom ≫ pullback.fst (s ≫ σ.hom) p = pullback.fst s (p ≫ σ.inv) := by
  refine ⟨asIso (pullback.map s (p ≫ σ.inv) (s ≫ σ.hom) p (𝟙 _) (𝟙 _) σ.hom
    (by simp) (by simp)), ?_⟩
  simp

/-- **Kleiman–Bertini for a general translate of the power map.** Let `p` be the `m`-th power map
of `ℙᴺ` and `σ` a linear change of coordinates putting `X` and the closed subschemes `Z c`, `Z' c`
in general position with the coordinate hyperplanes
(`exists_linAut_isSNCFamily_coordinateHyperplane`). Then `π = σ⁻¹ ∘ p` is finite and surjective
with `π^* 𝒪(1) ≅ p^* 𝒪(1) ≅ L^{⊗ m}`, and each `Z ×_{h, π} ℙᴺ ≅ Z ×_{σ h, p} ℙᴺ` is smooth of the
same pure dimension (`smooth_pullback_of_isPowerMapChartwise`). -/
private theorem exists_projSpace_endo_transversal.{u} (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] (N m : ℕ) (hm : 0 < m) {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k sX] [Smooth sX] (h : X ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (hh : h ≫ ProjSpace.toSpec k _ = sX) (d₀ : ℤ)
    (hd₀ : MMP.IsPureDimensional X d₀)
    {κ : Type*} [Finite κ] (Z : κ → Scheme.{u}) (j : ∀ c, Z c ⟶ X)
    [∀ c, IsClosedImmersion (j c)] [∀ c, Smooth (j c ≫ sX)] (d : κ → ℤ)
    (hd : ∀ c, MMP.IsPureDimensional (Z c) (d c))
    {κ' : Type*} [Finite κ'] (Z' : κ' → Scheme.{u}) (j' : ∀ c, Z' c ⟶ X)
    [∀ c, IsClosedImmersion (j' c)] [∀ c, Smooth (j' c ≫ sX)] :
    ∃ π : ProjSpace k (ULift.{u} (Fin (N + 1))) ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))),
      π ≫ ProjSpace.toSpec k _ = ProjSpace.toSpec k _ ∧ IsFinite π ∧ Surjective π ∧
      (∃ L : (ProjSpace k (ULift.{u} (Fin (N + 1)))).Modules,
        AlgebraicGeometry.SheafOfModules.IsInvertible
          (ProjSpace k (ULift.{u} (Fin (N + 1)))).sheaf.obj
          (ProjSpace k (ULift.{u} (Fin (N + 1)))).ringCatSheaf.property L ∧
        Nonempty ((Scheme.Modules.pullback π).obj (ProjSpace.twistOne k _) ≅ tensorPow L m)) ∧
      (Smooth (pullback.fst h π ≫ h ≫ ProjSpace.toSpec k _) ∧
        MMP.IsPureDimensional (pullback h π) d₀) ∧
      (∀ c, Smooth (pullback.fst (j c ≫ h) π ≫ (j c ≫ h) ≫ ProjSpace.toSpec k _) ∧
        MMP.IsPureDimensional (pullback (j c ≫ h) π) (d c)) ∧
      ∀ c, Smooth (pullback.fst (j' c ≫ h) π ≫ (j' c ≫ h) ≫ ProjSpace.toSpec k _) := by
  obtain ⟨p, hpk, ⟨L, hL, ⟨eL⟩⟩, hp⟩ := exists_powerMap k N m hm
  obtain ⟨hpf, hps⟩ := isFinite_surjective_of_isPowerMapChartwise k N m hm p hp
  have hsm := smooth_pullback_of_isPowerMapChartwise k N m hm p hp
  let W : Option κ ⊕ κ' → Scheme.{u} := Sum.elim (fun o => o.elim X Z) Z'
  let w : ∀ o, W o ⟶ X := fun o =>
    match o with
    | .inl none => 𝟙 X
    | .inl (some c) => j c
    | .inr c => j' c
  haveI : ∀ o, IsClosedImmersion (w o) := fun o => by
    rcases o with (_ | _) | _
    · exact (inferInstance : IsClosedImmersion (𝟙 X))
    · exact (inferInstance : IsClosedImmersion (j _))
    · exact (inferInstance : IsClosedImmersion (j' _))
  haveI : ∀ o, Smooth (w o ≫ sX) := fun o => by
    rcases o with (_ | _) | _
    · exact (inferInstance : Smooth (𝟙 X ≫ sX))
    · exact (inferInstance : Smooth (j _ ≫ sX))
    · exact (inferInstance : Smooth (j' _ ≫ sX))
  obtain ⟨A, _, hsnc⟩ := exists_linAut_isSNCFamily_coordinateHyperplane k N sX h hh W w
  let σ := linAut (k := k) A
  have hσk : σ.hom ≫ ProjSpace.toSpec k _ = ProjSpace.toSpec k _ := linAut_hom_toSpec A
  have eσ := linAutInvTwistOneIso (k := k) A
  have hσk' : σ.inv ≫ ProjSpace.toSpec k _ = ProjSpace.toSpec k _ := by
    calc σ.inv ≫ ProjSpace.toSpec k _ = σ.inv ≫ σ.hom ≫ ProjSpace.toSpec k _ := by rw [hσk]
      _ = ProjSpace.toSpec k _ := Iso.inv_hom_id_assoc _ _
  have hvar : MMP.Mori.IsVariety k sX := inferInstance
  haveI : QuasiCompact sX := hvar.toQuasiCompact
  haveI : IsSeparated sX := hvar.toIsSeparated
  -- the transversal pullback along `p ≫ σ⁻¹`
  have key : ∀ {Y : Scheme.{u}} (t : Y ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
      [Smooth (t ≫ ProjSpace.toSpec k _)] [QuasiCompact (t ≫ ProjSpace.toSpec k _)]
      [IsSeparated (t ≫ ProjSpace.toSpec k _)],
      MMP.Resolution.IsSNCFamily ((t ≫ σ.hom) ≫ ProjSpace.toSpec k _)
        (fun i => (coordinateHyperplane k N i).comap (t ≫ σ.hom)) →
      Smooth (pullback.fst t (p ≫ σ.inv) ≫ t ≫ ProjSpace.toSpec k _) ∧
        ∀ e : ℤ, MMP.IsPureDimensional Y e →
          MMP.IsPureDimensional (pullback t (p ≫ σ.inv)) e := by
    intro Y t _ _ _ hY
    have h1 : t ≫ σ.hom ≫ ProjSpace.toSpec k _ = t ≫ ProjSpace.toSpec k _ := by rw [hσk]
    haveI : Smooth ((t ≫ σ.hom) ≫ ProjSpace.toSpec k _) := by
      rw [Category.assoc, h1]; infer_instance
    haveI : QuasiCompact ((t ≫ σ.hom) ≫ ProjSpace.toSpec k _) := by
      rw [Category.assoc, h1]; infer_instance
    haveI : IsSeparated ((t ≫ σ.hom) ≫ ProjSpace.toSpec k _) := by
      rw [Category.assoc, h1]; infer_instance
    obtain ⟨hs1, hd1⟩ := hsm Y (t ≫ σ.hom) hY
    obtain ⟨e', he'⟩ := pullback_comp_inv_iso t σ p
    refine ⟨?_, fun e he => isPureDimensional_of_isOpenImmersion_of_isClosedImmersion e'.hom
      (hd1 e he)⟩
    have : pullback.fst t (p ≫ σ.inv) ≫ t ≫ ProjSpace.toSpec k _ =
        e'.hom ≫ pullback.fst (t ≫ σ.hom) p ≫ (t ≫ σ.hom) ≫ ProjSpace.toSpec k _ := by
      rw [← Category.assoc e'.hom, he', Category.assoc t, h1]
    rw [this]
    infer_instance
  -- the instances for the closed subschemes
  have inst : ∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [Smooth (i ≫ sX)],
      Smooth ((i ≫ h) ≫ ProjSpace.toSpec k _) ∧ QuasiCompact ((i ≫ h) ≫ ProjSpace.toSpec k _) ∧
        IsSeparated ((i ≫ h) ≫ ProjSpace.toSpec k _) := by
    intro Y i _ _
    have h0 : (i ≫ h) ≫ ProjSpace.toSpec k _ = i ≫ sX := by rw [Category.assoc, hh]
    haveI : QuasiCompact i := inferInstance
    haveI : IsSeparated i := inferInstance
    rw [h0]
    exact ⟨inferInstance, quasiCompact_comp _ _, MorphismProperty.comp_mem @IsSeparated _ _ ‹_› ‹_›⟩
  have keyi : ∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [Smooth (i ≫ sX)],
      MMP.Resolution.IsSNCFamily ((i ≫ h ≫ σ.hom) ≫ ProjSpace.toSpec k _)
        (fun l => (coordinateHyperplane k N l).comap (i ≫ h ≫ σ.hom)) →
      Smooth (pullback.fst (i ≫ h) (p ≫ σ.inv) ≫ (i ≫ h) ≫ ProjSpace.toSpec k _) ∧
        ∀ e : ℤ, MMP.IsPureDimensional Y e →
          MMP.IsPureDimensional (pullback (i ≫ h) (p ≫ σ.inv)) e := by
    intro Y i _ _ hY
    obtain ⟨i1, i2, i3⟩ := inst i
    exact key (i ≫ h) (by simpa only [Category.assoc] using hY)
  haveI : Smooth (h ≫ ProjSpace.toSpec k _) := by rw [hh]; infer_instance
  haveI : QuasiCompact (h ≫ ProjSpace.toSpec k _) := by rw [hh]; infer_instance
  haveI : IsSeparated (h ≫ ProjSpace.toSpec k _) := by rw [hh]; infer_instance
  have hsnc0 : MMP.Resolution.IsSNCFamily ((𝟙 X ≫ h ≫ σ.hom) ≫ ProjSpace.toSpec k _)
      (fun l => (coordinateHyperplane k N l).comap (𝟙 X ≫ h ≫ σ.hom)) := hsnc (.inl none)
  have k0 := key h (by simpa only [Category.id_comp, Category.assoc] using hsnc0)
  haveI := hpf
  haveI := hps
  refine ⟨p ≫ σ.inv, by rw [Category.assoc, hσk', hpk], inferInstance, inferInstance,
    ⟨L, hL, ⟨((Scheme.Modules.pullbackComp p σ.inv).app _).symm ≪≫
      (Scheme.Modules.pullback p).mapIso eσ ≪≫ eL⟩⟩,
    ⟨k0.1, k0.2 d₀ hd₀⟩,
    fun c => ⟨(keyi (j c) (hsnc (.inl (some c)))).1,
      (keyi (j c) (hsnc (.inl (some c)))).2 _ (hd c)⟩,
    fun c => (keyi (j' c) (hsnc (.inr c))).1⟩

/-- A variety of dimension `n` is pure of dimension `n`. -/
private theorem isPureDimensional_of_irreducibleSpace.{u} {X : Scheme.{u}} [IrreducibleSpace X]
    (n : ℕ) (hn : topologicalKrullDim X = n) : MMP.IsPureDimensional X n := by
  intro C hC
  rw [irreducibleComponents_eq_singleton] at hC
  obtain rfl : C = Set.univ := hC
  exact ⟨n, rfl, (IsHomeomorph.topologicalKrullDim_eq _
    (Homeomorph.Set.univ X).isHomeomorph).trans hn⟩

/-- **Inverse images along a base change.** The inverse image of a closed subscheme `G ⊆ X` along
the first projection of `X ×_{h, T, π} T'` is `G ×_{h, T, π} T'`, compatibly with the maps to
`T`. -/
private theorem exists_iso_comap_pullback_fst.{u} {X T T' S : Scheme.{u}} (h : X ⟶ T)
    (π : T' ⟶ T) (G : X.IdealSheafData) (sT : T ⟶ S) :
    ∃ e : (G.comap (pullback.fst h π)).subscheme ≅ pullback (G.subschemeι ≫ h) π,
      (G.comap (pullback.fst h π)).subschemeι ≫ pullback.fst h π ≫ h ≫ sT =
        e.hom ≫ pullback.fst (G.subschemeι ≫ h) π ≫ (G.subschemeι ≫ h) ≫ sT := by
  refine ⟨G.comapIso (pullback.fst h π) ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso h π G.subschemeι, ?_⟩
  simp only [Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_fst_assoc,
    pullbackSymmetry_hom_comp_fst_assoc]
  rw [← pullback.condition_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- **The transversal cover before choosing a component.** With `π'` as in
`exists_projSpace_endo_transversal`, the fibre product `X₁ = X ×_{h, ℙᴺ, π'} ℙᴺ` with its first
projection `q` is finite and surjective over `X` (base change of `π'`), smooth of pure dimension
`n` over `k`, carries the `m`-th root `pr₂^* L` of `q^* h^* 𝒪(1)`, and for every non-empty `J` the
scheme-theoretic intersection `⋂_{j ∈ J} q⁻¹ F_j ≅ F_J ×_{ℙᴺ, π'} ℙᴺ` is smooth of pure dimension
`n - |J|`. -/
private theorem exists_finite_cover_transversal_strata.{u}
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX] [Smooth sX]
    (N : ℕ) (h : X ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (hh : h ≫ ProjSpace.toSpec k _ = sX) (m : ℕ) (hm : 0 < m)
    {ι : Type*} [Fintype ι] (F : ι → X.IdealSheafData)
    (n : ℕ) (hn : topologicalKrullDim X = n)
    (hstrata : ∀ J : Finset ι, J.Nonempty →
      Smooth ((⨆ j ∈ J, F j).subschemeι ≫ sX) ∧
        MMP.IsPureDimensional (⨆ j ∈ J, F j).subscheme ((n : ℤ) - J.card))
    {ι' : Type*} [Finite ι'] (F' : ι' → X.IdealSheafData) :
    ∃ (X₁ : Scheme.{u}) (q : X₁ ⟶ X), IsFinite q ∧ Surjective q ∧ Smooth (q ≫ sX) ∧
      MMP.IsPureDimensional X₁ n ∧
      (∃ L₁ : X₁.Modules,
        AlgebraicGeometry.SheafOfModules.IsInvertible X₁.sheaf.obj X₁.ringCatSheaf.property L₁ ∧
        Nonempty ((Scheme.Modules.pullback q).obj
            ((Scheme.Modules.pullback h).obj (ProjSpace.twistOne k _)) ≅ tensorPow L₁ m)) ∧
      (∀ J : Finset ι, J.Nonempty →
        Smooth ((⨆ j ∈ J, (F j).comap q).subschemeι ≫ q ≫ sX) ∧
          MMP.IsPureDimensional (⨆ j ∈ J, (F j).comap q).subscheme
            ((n : ℤ) - J.card)) ∧
      ∀ j, Smooth ((F' j).subschemeι ≫ sX) → Smooth (((F' j).comap q).subschemeι ≫ q ≫ sX) := by
  subst hh
  let κ := {J : Finset ι // J.Nonempty}
  let G : κ → X.IdealSheafData := fun J => ⨆ j ∈ J.1, F j
  haveI : ∀ c : κ, Smooth ((G c).subschemeι ≫ h ≫ ProjSpace.toSpec k _) := fun c =>
    (hstrata c.1 c.2).1
  let κ' := {j : ι' // Smooth ((F' j).subschemeι ≫ h ≫ ProjSpace.toSpec k _)}
  haveI : ∀ c : κ', Smooth ((F' c.1).subschemeι ≫ h ≫ ProjSpace.toSpec k _) := fun c => c.2
  obtain ⟨π, -, hπf, hπs, ⟨L, hL, ⟨eπ⟩⟩, ⟨hsm₀, hd₀⟩, hT, hT'⟩ :=
    exists_projSpace_endo_transversal k N m hm (h ≫ ProjSpace.toSpec k _) h rfl n
      (isPureDimensional_of_irreducibleSpace n hn)
      (fun c : κ => (G c).subscheme) (fun c => (G c).subschemeι)
      (fun c => (n : ℤ) - c.1.card) (fun c => (hstrata c.1 c.2).2)
      (fun c : κ' => (F' c.1).subscheme) (fun c => (F' c.1).subschemeι)
  haveI := hπf
  haveI := hπs
  haveI : Stacks.Ample.IsInvertibleModule _ L := hL
  obtain ⟨t⟩ := nonempty_pullback_tensorPow_iso (pullback.snd h π) L m
  refine ⟨pullback h π, pullback.fst h π, inferInstance, inferInstance, hsm₀, hd₀,
    ⟨(Scheme.Modules.pullback (pullback.snd h π)).obj L, inferInstance,
      ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫
        (Scheme.Modules.pullbackCongr pullback.condition).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
        (Scheme.Modules.pullback (pullback.snd h π)).mapIso eπ ≪≫ t⟩⟩, fun J hJ => ?_,
      fun j hj => ?_⟩
  swap
  · obtain ⟨e, he⟩ := exists_iso_comap_pullback_fst h π (F' j) (ProjSpace.toSpec k _)
    haveI : Smooth (pullback.fst ((F' j).subschemeι ≫ h) π ≫
        ((F' j).subschemeι ≫ h) ≫ ProjSpace.toSpec k _) := hT' ⟨j, hj⟩
    rw [he]
    infer_instance
  obtain ⟨hsJ, hdJ⟩ := hT ⟨J, hJ⟩
  rw [show (⨆ j ∈ J, (F j).comap (pullback.fst h π)) = (G ⟨J, hJ⟩).comap (pullback.fst h π) from
    ((Scheme.IdealSheafData.map_gc (pullback.fst h π)).l_iSup₂).symm]
  obtain ⟨e, he⟩ := exists_iso_comap_pullback_fst h π (G ⟨J, hJ⟩) (ProjSpace.toSpec k _)
  exact ⟨he ▸ inferInstance, isPureDimensional_of_isOpenImmersion_of_isClosedImmersion e.hom hdJ⟩

/-- **The Bloch–Gieseker cover of a transversal family.** If every non-empty intersection
`F_J = ⋂_{j ∈ J} F_j` is smooth of pure dimension `n - |J|`, a component `Y` of
`X ×_{h, ℙᴺ, σπ} ℙᴺ` mapping onto `X`, with `π` the `m`-th power map and `σ` a general element of
`PGL_{N+1}`, is a smooth variety finite over `X` on which `h^* 𝒪(1)` has an `m`-th root and every
`⋂_{j ∈ J} g⁻¹ F_j` is empty or smooth of pure dimension `n - |J|`.

The strata hypothesis is needed: for `F₁ = {xy = 0}` on `ℙ²` (snc, coefficients `1`), the
inverse image of `F₁` under any finite surjective `g` from a smooth variety is singular over the
node. This is why the prime components of `D`, not the `F_j`, are pulled back. -/
private theorem exists_cover_transversal.{u}
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX] [Smooth sX]
    (N : ℕ) (h : X ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (hh : h ≫ ProjSpace.toSpec k _ = sX) (m : ℕ) (hm : 0 < m)
    {ι : Type*} [Fintype ι] (F : ι → X.IdealSheafData)
    [∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (F j)]
    (n : ℕ) (hn : topologicalKrullDim X = n)
    (hstrata : ∀ J : Finset ι, J.Nonempty →
      Smooth ((⨆ j ∈ J, F j).subschemeι ≫ sX) ∧
        MMP.IsPureDimensional (⨆ j ∈ J, F j).subscheme ((n : ℤ) - J.card))
    {ι' : Type*} [Finite ι'] (F' : ι' → X.IdealSheafData) :
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (g : Y ⟶ X),
      MMP.Mori.IsVariety k sY ∧ Smooth sY ∧ g ≫ sX = sY ∧ IsFinite g ∧ Surjective g ∧
      (∃ L' : Y.Modules,
        AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L' ∧
        Nonempty ((Scheme.Modules.pullback g).obj
            ((Scheme.Modules.pullback h).obj (ProjSpace.twistOne k _)) ≅ tensorPow L' m)) ∧
      (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((F j).comap g)) ∧
      (∀ j, Smooth ((F' j).subschemeι ≫ sX) → Smooth (((F' j).comap g).subschemeι ≫ sY)) ∧
      ∃ n : ℕ, topologicalKrullDim Y = n ∧
        ∀ J : Finset ι, J.Nonempty →
          IsEmpty (⨆ j ∈ J, (F j).comap g).subscheme ∨
            (Smooth ((⨆ j ∈ J, (F j).comap g).subschemeι ≫ sY) ∧
              ∀ C ∈ irreducibleComponents (Set.univ : Set (⨆ j ∈ J, (F j).comap g).subscheme),
                topologicalKrullDim C + J.card = n) := by
  obtain ⟨X₁, q, hqf, hqs, hsm, hpure, ⟨L₁, hL₁, ⟨e₁⟩⟩, hJ, hF'⟩ :=
    exists_finite_cover_transversal_strata k sX N h hh m hm F n hn hstrata F'
  haveI := hqf
  haveI := hqs
  haveI := hsm
  obtain ⟨Y, i, hio, hic, hY, hsurj⟩ := exists_isVariety_isOpenImmersion_isClosedImmersion k sX q
  haveI := hio
  haveI := hic
  haveI := hY
  haveI := hsurj
  have hiSup : ∀ J : Finset ι,
      (⨆ j ∈ J, (F j).comap (i ≫ q)) = (⨆ j ∈ J, (F j).comap q).comap i := by
    intro J
    simp only [Scheme.IdealSheafData.comap_comp]
    exact ((Scheme.IdealSheafData.map_gc i).l_iSup₂).symm
  haveI : Stacks.Ample.IsInvertibleModule X₁ L₁ := hL₁
  have hiL : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback i).obj L₁) :=
    inferInstance
  obtain ⟨t⟩ := nonempty_pullback_tensorPow_iso i L₁ m
  refine ⟨Y, i ≫ q ≫ sX, i ≫ q, hY, inferInstance, Category.assoc _ _ _, inferInstance, hsurj,
    ⟨(Scheme.Modules.pullback i).obj L₁, hiL,
      ⟨((Scheme.Modules.pullbackComp i q).app _).symm ≪≫
        (Scheme.Modules.pullback i).mapIso e₁ ≪≫ t⟩⟩,
    fun j => isEffectiveCartierDivisor_comap_of_surjective (i ≫ q) (F j), fun j hj => ?_, n, ?_,
    fun J hJne => ?_⟩
  · rw [Scheme.IdealSheafData.comap_comp]
    exact smooth_comap_of_isOpenImmersion i (q ≫ sX) _ (hF' j hj)
  · haveI : Nonempty Y := inferInstance
    obtain ⟨n', hn', hd⟩ := (isPureDimensional_of_isOpenImmersion_of_isClosedImmersion i
      hpure).hasDim_of_nonempty
    rw [hd, show n' = n by exact_mod_cast hn']
  · obtain ⟨hJs, hJd⟩ := hJ J hJne
    rw [hiSup J]
    exact Or.inr ⟨smooth_comap_of_isOpenImmersion i (q ≫ sX) _ hJs,
      forall_topologicalKrullDim_add_card_of_isPureDimensional n J.card
        (isPureDimensional_of_isOpenImmersion_of_isClosedImmersion
          (((⨆ j ∈ J, (F j).comap q).comapIso i).hom ≫ pullback.snd i _) hJd)⟩

/-- On a variety, the Weil divisor `∑ⱼ G j` of a finite family of effective Cartier divisors
exists: its coefficient at `P` is `∑ⱼ length (𝒪_{Y,P} / (G j)_P)`. Only finitely many prime
divisors have their generic point in the support of `G j`, since that support misses the generic
point of `Y`, and off the support the summand vanishes. -/
private theorem exists_divisor_coeff_eq_sum_length.{u} (k : Type u) [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY) {ι : Type*} [Fintype ι]
    (G : ι → Y.IdealSheafData) [hG : ∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (G j)] :
    ∃ E : MMP.Mori.Divisor Y, ∀ P : MMP.Mori.PrimeDivisor Y, E.coeff P = ∑ j,
      ((Module.length (Y.presheaf.stalk P.genericPoint)
        (Y.presheaf.stalk P.genericPoint ⧸
          IdealSheafData.stalk (G j) P.genericPoint)).toNat : ℤ) := by
  haveI := hY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := ⟨⟩
  set c : MMP.Mori.PrimeDivisor Y → ℤ := fun P => ∑ j,
      ((Module.length (Y.presheaf.stalk P.genericPoint)
        (Y.presheaf.stalk P.genericPoint ⧸ IdealSheafData.stalk (G j) P.genericPoint)).toNat : ℤ)
  have hfin : (Function.support c).Finite := by
    refine (Set.finite_iUnion fun j => MMP.Mori.finite_setOf_genericPoint_mem
      (G j).support.isClosed fun s hs h0 => ?_).subset ?_
    · have hmax : IsMax s := Order.coheight_eq_zero.mp h0
      have hgen : genericPoint Y ⤳ s := (genericPoint_spec Y).specializes trivial
      have hgs : genericPoint Y = s := (hgen.antisymm (hmax (show s ≤ genericPoint Y from hgen))).eq
      refine notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor (G j) (hG j)
        (x := genericPoint Y) ?_ (hgs ▸ hs)
      show closure ({genericPoint Y} : Set Y) ∈ irreducibleComponents Y
      rw [show closure ({genericPoint Y} : Set Y) = Set.univ from genericPoint_spec Y,
        irreducibleComponents_eq_singleton]
      rfl
    · intro P hP
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      by_contra hn
      apply hj
      rw [(IdealSheafData.stalk_eq_top_iff_not_mem_support _ _).mpr hn,
        Module.length_eq_zero_iff.mpr inferInstance]
      rfl
  exact ⟨Finsupp.ofSupportFinite c hfin, fun P => rfl⟩

/-- At a point of `⋂_{P ∈ J} P`, the stalk of the intersection is generated by the members
`z_{j(P)}`, `P ∈ J`, of a regular system of parameters. -/
private theorem exists_stalk_iSup_idealSheaf_eq_span.{u} {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {D : MMP.Mori.Divisor X} (hsnc : D.IsSNC sX) (J : Finset D.support) (x : X)
    (hx : x ∈ (⨆ P ∈ J, P.1.idealSheaf).support) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (s : Finset (Fin n)),
      MMP.Mori.IsRegularSystemOfParameters z ∧ s.card = J.card ∧
      IdealSheafData.stalk (⨆ P ∈ J, P.1.idealSheaf) x = Ideal.span (z '' s) := by
  classical
  obtain ⟨n, z, j, hz, hj, hI⟩ := hsnc.2 x
  have hxP : ∀ P ∈ J, x ∈ P.1.support := fun P hP =>
    Scheme.IdealSheafData.support_antitone
      (le_iSup₂ (f := fun P (_ : P ∈ J) => P.1.idealSheaf) P hP) hx
  let j' : J → Fin n := fun P => j ⟨P.1.1, P.1.2, hxP P.1 P.2⟩
  have hj' : Function.Injective j' := by
    intro P Q h
    have := congrArg (fun E => E.1) (hj h)
    exact Subtype.ext (Subtype.ext this)
  refine ⟨n, z, Finset.univ.map ⟨j', hj'⟩, hz,
    by rw [Finset.card_map, Finset.card_univ, Fintype.card_coe], ?_⟩
  have key : IdealSheafData.stalk (⨆ P ∈ J, P.1.idealSheaf) x =
      ⨆ P : J, IdealSheafData.stalk P.1.1.idealSheaf x := by
    rw [iSup_subtype' (p := fun P => P ∈ J) (f := fun P _ => P.1.idealSheaf)]
    exact MMP.Resolution.stalk_iSup (fun P : J => P.1.1.idealSheaf) x
  rw [key]
  apply le_antisymm
  · refine iSup_le fun P => ?_
    rw [hI ⟨P.1.1, P.1.2, hxP P.1 P.2⟩]
    refine Ideal.span_mono ?_
    rw [Set.singleton_subset_iff]
    exact ⟨j' P, by simp, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at hi
    obtain ⟨P, rfl⟩ := hi
    refine Ideal.mem_iSup_of_mem P ?_
    rw [hI ⟨P.1.1, P.1.2, hxP P.1 P.2⟩]
    exact Ideal.subset_span rfl

/-- The intersection of the prime components `P ∈ J` of an snc divisor is smooth: its local rings
are quotients of regular local rings by part of a regular system of parameters. -/
private theorem smooth_iSup_idealSheaf_of_isSNC.{u} (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX] [Smooth sX]
    (D : MMP.Mori.Divisor X) (hsnc : D.IsSNC sX) (J : Finset D.support) :
    Smooth ((⨆ P ∈ J, P.1.idealSheaf).subschemeι ≫ sX) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨G, hG⟩ : ∃ G, G = ⨆ P ∈ J, P.1.idealSheaf := ⟨_, rfl⟩
  rw [← hG, MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  intro w
  have hx : G.subschemeι w ∈ G.support := by
    rw [← SetLike.mem_coe, ← G.range_subschemeι]; exact ⟨w, rfl⟩
  obtain ⟨n, z, s, hz, -, hst⟩ :=
    exists_stalk_iSup_idealSheaf_eq_span hsnc J (G.subschemeι w) (by rw [← hG]; exact hx)
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
  rw [← hst, ← hG] at hreg
  exact IsRegularLocalRing.of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv G w)

open Order in
/-- The intersection of the prime components `P ∈ J` of an snc divisor on a variety of dimension
`n` is pure of dimension `n - |J|`: at a closed point of a component `C`, the local ring of `C`
is the quotient of the `n`-dimensional regular local ring of `X` by `|J|` parameters. -/
private theorem isPureDimensional_iSup_idealSheaf_of_isSNC.{u} (k : Type u) [Field k]
    [IsAlgClosed k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX] [Smooth sX]
    (D : MMP.Mori.Divisor X) (hsnc : D.IsSNC sX) (n : ℕ) (hn : topologicalKrullDim X = n)
    (J : Finset D.support) :
    MMP.IsPureDimensional (⨆ P ∈ J, P.1.idealSheaf).subscheme
      ((n : ℤ) - J.card) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hsm := smooth_iSup_idealSheaf_of_isSNC k sX D hsnc J
  obtain ⟨G, hG⟩ : ∃ G, G = ⨆ P ∈ J, P.1.idealSheaf := ⟨_, rfl⟩
  rw [← hG] at hsm ⊢
  intro C hC
  have hCcl : IsClosed (G.subschemeι '' C) :=
    G.subschemeι.isClosedEmbedding.isClosedMap _ (isClosed_of_mem_irreducibleComponents C hC)
  obtain ⟨_, ⟨w, hwC, rfl⟩, hxcl⟩ := hCcl.exists_closed_singleton (hC.1.nonempty.image _)
  -- the dimension of `X` at the closed point
  have hcoX : coheight (G.subschemeι w) = n := coheight_eq_of_isClosed_singleton k sX n hn _ hxcl
  have hx : G.subschemeι w ∈ G.support := by
    rw [← SetLike.mem_coe, ← G.range_subschemeι]; exact ⟨w, rfl⟩
  obtain ⟨m, z, s, hz, hs, hst⟩ :=
    exists_stalk_iSup_idealSheaf_eq_span hsnc J (G.subschemeι w) (by rw [← hG]; exact hx)
  have hm : m = n := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, hcoX] at h
    exact_mod_cast h.symm
  subst hm
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨-, hqdim, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
  rw [← hst, ← hG, ringKrullDim_eq_of_ringEquiv
    (MMP.Flips.ResolutionInputs.stalkQuotientEquiv G w)] at hqdim
  have hsle : s.card ≤ m := by simpa using s.card_le_univ
  have hwcl : IsClosed ({w} : Set G.subscheme) := by
    rw [← G.subschemeι.isClosedEmbedding.injective.preimage_image {w}, Set.image_singleton]
    exact hxcl.preimage G.subschemeι.continuous
  have hdim := topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed (G.subschemeι ≫ sX) hC hwC
    hwcl
  rw [hqdim] at hdim
  refine ⟨m - s.card, by rw [Nat.cast_sub hsle, hs], ?_⟩
  exact_mod_cast hdim

/-- Local equations of an effective Cartier divisor `I` at `g y` and of `I.comap g` at `y`, the
second the image of the first under the stalk map. -/
private theorem exists_stalk_eq_span_and_stalk_comap_eq_span.{u} {X Y : Scheme.{u}} (g : Y ⟶ X)
    (I : X.IdealSheafData) [hI : Stacks.Divisors.IsEffectiveCartierDivisor I] (y : Y) :
    ∃ t : X.presheaf.stalk (g y), IdealSheafData.stalk I (g y) = Ideal.span {t} ∧
      IdealSheafData.stalk (I.comap g) y = Ideal.span {g.stalkMap y t} := by
  obtain ⟨W, hyW, -, s, -, hgen⟩ :=
    Stacks.Blowup.exists_affineOpens_ideal_eq_span_le I hI (g y) ⊤ trivial
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ g ⁻¹ᵁ (W : X.Opens) from hyW) (g ⁻¹ᵁ (W : X.Opens)).isOpen
  have hVW : (V : Y.Opens) ≤ g ⁻¹ᵁ (W : X.Opens) := hVsub
  refine ⟨X.presheaf.germ W.1 (g y) hyW s, ?_, ?_⟩
  · rw [IdealSheafData.stalk_eq_map_germ I (g y) W hyW, hgen, Ideal.map_span,
      Set.image_singleton]
  · rw [IdealSheafData.stalk_eq_map_germ _ y ⟨V, hV⟩ hyV,
      Stacks.IdealSheaf.ideal_comap_eq_span I g W ⟨V, hV⟩ hVW hgen, Ideal.map_span,
      Set.image_singleton, Scheme.Hom.germ_stalkMap_apply]
    congr 2
    exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hVW) y hyV _

private theorem stalk_eq_map_stalkSpecializes.{u} {X : Scheme.{u}} (I : X.IdealSheafData) {y x : X}
    (h : y ⤳ x) : IdealSheafData.stalk I y =
      Ideal.map (X.presheaf.stalkSpecializes h).hom (IdealSheafData.stalk I x) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  have hyU : y ∈ U := h.mem_open U.isOpen hxU
  rw [IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ I y ⟨U, hU⟩ hyU, Ideal.map_map, ← CommRingCat.hom_comp,
    TopCat.Presheaf.germ_stalkSpecializes]

/-- The order of a local equation at a generization is the length of the stalk quotient. -/
private theorem ord_stalkSpecializes_eq_length.{u} {X : Scheme.{u}} (I : X.IdealSheafData) {y x : X}
    (h : y ⤳ x) {t : X.presheaf.stalk x} (ht : IdealSheafData.stalk I x = Ideal.span {t}) :
    Ring.ord (X.presheaf.stalk y) (X.presheaf.stalkSpecializes h t) =
      Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸ IdealSheafData.stalk I y) := by
  rw [stalk_eq_map_stalkSpecializes I h, ht, Ideal.map_span, Set.image_singleton]
  rfl

/-- A local equation of an effective Cartier divisor on an integral scheme is non-zero. -/
private theorem ne_zero_of_stalk_eq_span.{u} {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData)
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I] {x : X} {t : X.presheaf.stalk x}
    (ht : IdealSheafData.stalk I x = Ideal.span {t}) : t ≠ 0 := by
  rintro rfl
  obtain ⟨W, hxW, -, s, hs, hgen⟩ :=
    Stacks.Blowup.exists_affineOpens_ideal_eq_span_le I hI x ⊤ trivial
  rw [IdealSheafData.stalk_eq_map_germ I x W hxW, hgen, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton] at ht
  haveI : Nonempty (W.1 : X.Opens) := ⟨⟨x, hxW⟩⟩
  have h0 : X.presheaf.germ W.1 x hxW s = 0 := by
    obtain ⟨u, hu⟩ := ht
    exact (Units.mul_left_eq_zero u).mp hu
  exact hs.ne_zero ((germ_injective_of_isIntegral X (U := W.1) x hxW)
    (h0.trans (map_zero _).symm))

open Order Classical in
/-- At a generization `y` of `x` of codimension at most one, the order of a local equation `π`
of a prime divisor `P` is `1` if `y` is the generic point of `P` and `0` otherwise. -/
private theorem ord_stalkSpecializes_idealSheaf.{u} {X : Scheme.{u}} (P : MMP.Mori.PrimeDivisor X)
    {y x : X} (h : y ⤳ x) (hy : coheight y ≤ 1) {π : X.presheaf.stalk x}
    (hπ : IdealSheafData.stalk P.idealSheaf x = Ideal.span {π}) :
    Ring.ord (X.presheaf.stalk y) (X.presheaf.stalkSpecializes h π) =
      if y = P.genericPoint then 1 else 0 := by
  split_ifs with hyP
  · subst hyP
    refine MMP.Intersection.ord_stalkSpecializes_eq_one h ?_
    have hxP : x ∈ P.support := h.mem_closed P.idealSheaf.support.isClosed
      (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
    obtain ⟨q, hq, hst, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hxP
    rw [← hπ, hst]
    have := (MMP.Intersection.fromSpecStalk_primeOfSpecializes h).trans hq.symm
    have heq := (X.fromSpecStalk x).isEmbedding.injective this
    rw [← heq]
  · have hnot : y ∉ P.support := by
      intro hyS
      have hsp : P.genericPoint ⤳ y := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hyS
      have hlt : y < P.genericPoint := MMP.Intersection.lt_of_specializes_of_ne hsp hyP
      have h1 := coheight_add_one_le hlt
      rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h1
      have h2 := h1.trans hy
      norm_num at h2
    rw [ord_stalkSpecializes_eq_length _ h hπ,
      MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support P hnot]
    exact Module.length_eq_zero_iff.mpr inferInstance

/-- The order of a product of non-zero elements at a generization is the sum of the orders. -/
private theorem ord_stalkSpecializes_prod.{u} {X : Scheme.{u}} {y x : X}
    [IsDomain (X.presheaf.stalk x)]
    (h : y ⤳ x) {κ : Type*} (s : Finset κ) (f : κ → X.presheaf.stalk x) (hf : ∀ i, f i ≠ 0) :
    Ring.ord (X.presheaf.stalk y) (X.presheaf.stalkSpecializes h (∏ i ∈ s, f i)) =
      ∑ i ∈ s, Ring.ord (X.presheaf.stalk y) (X.presheaf.stalkSpecializes h (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, map_one]
    exact Ring.ord_one _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      MMP.Intersection.ord_stalkSpecializes_mul h _ (Finset.prod_ne_zero_iff.mpr fun i _ => hf i),
      ih]

open Order Classical in
/-- **An effective Cartier divisor is the sum of its prime components, locally.** On a smooth
variety, if the Weil divisor `∑ⱼ F_j` has all coefficients in `{0, 1}` (pinned by `D`), then at
every point `x` a local equation of `F_j` is associated to the product of the local equations of
the prime divisors `P` of `D` occurring in `F_j`. -/
private theorem associated_localEquation_prod.{u} (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX] [Smooth sX]
    {ι : Type*} [Fintype ι] (F : ι → X.IdealSheafData)
    [∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (F j)]
    (D : MMP.Mori.Divisor X)
    (hD : ∀ P : MMP.Mori.PrimeDivisor X, D.coeff P = ∑ j,
      ((Module.length (X.presheaf.stalk P.genericPoint)
      (X.presheaf.stalk P.genericPoint ⧸ IdealSheafData.stalk (F j) P.genericPoint)).toNat : ℤ))
    (hD1 : ∀ P ∈ D.support, D.coeff P = 1)
    (x : X) (t : ι → X.presheaf.stalk x) (ht : ∀ j, IdealSheafData.stalk (F j) x = Ideal.span {t j})
    (π : D.support → X.presheaf.stalk x)
    (hπ : ∀ P, IdealSheafData.stalk P.1.idealSheaf x = Ideal.span {π P}) (j : ι) :
    Associated (t j) (∏ P ∈ Finset.univ.filter (fun P : D.support =>
      (Module.length (X.presheaf.stalk P.1.genericPoint) (X.presheaf.stalk P.1.genericPoint ⧸
        IdealSheafData.stalk (F j) P.1.genericPoint)).toNat ≠ 0), π P) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsDomain (X.presheaf.stalk x) := by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
    exact IsRegularLocalRing.isDomain _
  haveI : UniqueFactorizationMonoid (X.presheaf.stalk x) := by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
    exact IsRegularLocalRing.uniqueFactorizationMonoid _
  haveI : ∀ P : MMP.Mori.PrimeDivisor X, Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf :=
    fun P => AlgebraicGeometry.PrimeDivisor.isEffectiveCartierDivisor_idealSheaf (fun z => by
      haveI := isRegularLocalRing_stalk_of_smooth_over_field sX z
      exact IsRegularLocalRing.uniqueFactorizationMonoid _) P
  have htne : ∀ j, t j ≠ 0 := fun j => ne_zero_of_stalk_eq_span (F j) (ht j)
  have hπne : ∀ P, π P ≠ 0 := fun P => ne_zero_of_stalk_eq_span P.1.idealSheaf (hπ P)
  set S := Finset.univ.filter (fun P : D.support =>
      (Module.length (X.presheaf.stalk P.1.genericPoint) (X.presheaf.stalk P.1.genericPoint ⧸
        IdealSheafData.stalk (F j) P.1.genericPoint)).toNat ≠ 0) with hS
  refine MMP.Intersection.associated_of_forall_ord_stalkSpecializes_eq x (htne j)
    (Finset.prod_ne_zero_iff.mpr fun P _ => hπne P) fun y hy hc => ?_
  rw [ord_stalkSpecializes_prod hy S π hπne, ord_stalkSpecializes_eq_length (F j) hy (ht j)]
  have hterm : ∀ P : D.support, Ring.ord (X.presheaf.stalk y)
      (X.presheaf.stalkSpecializes hy (π P)) = if y = P.1.genericPoint then 1 else 0 :=
    fun P => ord_stalkSpecializes_idealSheaf P.1 hy hc (hπ P)
  simp only [hterm]
  rcases (show coheight y = 0 ∨ coheight y = 1 by
    generalize coheight y = c at hc
    induction c using ENat.recTopCoe with
    | top => exact absurd hc (by simp)
    | coe c => norm_cast at hc ⊢; omega) with h0 | h1
  · -- the generic point: no divisor passes through it
    have hmax : IsMax y := Order.coheight_eq_zero.mp h0
    have hgen : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
    have hgs : genericPoint X = y := (hgen.antisymm (hmax (show y ≤ genericPoint X from hgen))).eq
    have hyF : y ∉ (F j).support := by
      rw [← hgs]
      refine notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor (F j) inferInstance
        (x := genericPoint X) ?_
      show closure ({genericPoint X} : Set X) ∈ irreducibleComponents X
      rw [show closure ({genericPoint X} : Set X) = Set.univ from genericPoint_spec X,
        irreducibleComponents_eq_singleton]
      rfl
    rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).mpr hyF,
      Module.length_eq_zero_iff.mpr inferInstance]
    refine (Finset.sum_eq_zero fun P _ => ?_).symm
    rw [if_neg]
    rintro rfl
    rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h0
    exact one_ne_zero h0
  · -- a prime divisor `P'`
    obtain ⟨P', rfl⟩ : ∃ P' : MMP.Mori.PrimeDivisor X, y = P'.genericPoint :=
      ⟨_, (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y h1).symm⟩
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk P'.genericPoint) :=
      krullDimLE_of_coheight_le (by rw [h1]; rfl)
    haveI : IsDomain (X.presheaf.stalk P'.genericPoint) := by
      haveI := isRegularLocalRing_stalk_of_smooth_over_field sX P'.genericPoint
      exact IsRegularLocalRing.isDomain _
    have hfin : Module.length (X.presheaf.stalk P'.genericPoint) (X.presheaf.stalk P'.genericPoint ⧸
        IdealSheafData.stalk (F j) P'.genericPoint) ≠ ⊤ := by
      rw [← ord_stalkSpecializes_eq_length (F j) hy (ht j)]
      exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero
        (MMP.Intersection.stalkSpecializes_ne_zero hy (htne j)))
    rw [← ENat.coe_toNat hfin]
    have hiff : ∀ P : D.support, P'.genericPoint = P.1.genericPoint ↔ P.1 = P' := fun P =>
      ⟨fun h => (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h).symm,
        fun h => h ▸ rfl⟩
    simp only [hiff]
    have hsum := hD P'
    have hle : ∀ i, ((Module.length (X.presheaf.stalk P'.genericPoint)
        (X.presheaf.stalk P'.genericPoint ⧸ IdealSheafData.stalk (F i) P'.genericPoint)).toNat : ℤ)
          ≤ D.coeff P' := fun i => hsum ▸
      Finset.single_le_sum (f := fun i' => ((Module.length (X.presheaf.stalk P'.genericPoint)
        (X.presheaf.stalk P'.genericPoint ⧸
          IdealSheafData.stalk (F i') P'.genericPoint)).toNat : ℤ))
        (fun _ _ => Int.natCast_nonneg _) (Finset.mem_univ i)
    by_cases hP'D : P' ∈ D.support
    · have hiff2 : ∀ P : D.support, P.1 = P' ↔ (⟨P', hP'D⟩ : D.support) = P :=
        fun P => ⟨fun h => Subtype.ext h.symm, fun h => h ▸ rfl⟩
      simp only [hiff2]
      rw [Finset.sum_ite_eq]
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1' := hle j
      rw [hD1 P' hP'D] at h1'
      split_ifs with hne
      · have : (Module.length (X.presheaf.stalk P'.genericPoint) (X.presheaf.stalk P'.genericPoint ⧸
          IdealSheafData.stalk (F j) P'.genericPoint)).toNat = 1 := by omega
        rw [this]
        rfl
      · rw [not_not.mp hne]
        rfl
    · have hz : D.coeff P' = 0 := Finsupp.notMem_support_iff.mp hP'D
      have h1' := hle j
      rw [hz] at h1'
      have : (Module.length (X.presheaf.stalk P'.genericPoint) (X.presheaf.stalk P'.genericPoint ⧸
          IdealSheafData.stalk (F j) P'.genericPoint)).toNat = 0 := by omega
      rw [this]
      refine (Finset.sum_eq_zero fun P _ => ?_).symm
      rw [if_neg]
      rintro rfl
      exact hP'D P.2

/-- The order of a product of non-zero elements of a domain is the sum of the orders. -/
private theorem ord_prod {R : Type*} [CommRing R] [IsDomain R] {κ : Type*} (s : Finset κ)
    (f : κ → R)
    (hf : ∀ i ∈ s, f i ≠ 0) : Ring.ord R (∏ i ∈ s, f i) = ∑ i ∈ s, Ring.ord R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact Ring.ord_one _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_comm,
      Ring.ord_mul R (mem_nonZeroDivisors_of_ne_zero (hf a (Finset.mem_insert_self _ _))),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi), add_comm]

/-- **The divisors `F_j` are the sums of their prime components**. Since all
coefficients of `D = ∑ⱼ F_j` are `1`, every prime divisor `P` of `D` occurs in exactly one `F_j`,
with multiplicity one, so on the regular scheme `X` (where an effective Cartier divisor is
determined by its Weil divisor) `F_j = ∑_{P ⊆ F_j} P`. Pulling back along the dominant `g` is
additive, and so is the order of vanishing along a prime divisor `Q` of `Y` (the local ring
`𝒪_{Y,Q}` being a discrete valuation ring): the multiplicity of `∑ⱼ g⁻¹ F_j` along `Q` is that of
`∑_{P ∈ D} g⁻¹ P`. -/
private theorem sum_length_comap_eq_sum_length_comap_idealSheaf.{u}
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX] [Smooth sX]
    {ι : Type*} [Fintype ι] (F : ι → X.IdealSheafData)
    [∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (F j)]
    (D : MMP.Mori.Divisor X)
    (hD : ∀ P : MMP.Mori.PrimeDivisor X, D.coeff P = ∑ j,
      ((Module.length (X.presheaf.stalk P.genericPoint)
      (X.presheaf.stalk P.genericPoint ⧸ IdealSheafData.stalk (F j) P.genericPoint)).toNat : ℤ))
    (hsnc : D.IsSNC sX) (hD1 : ∀ P ∈ D.support, D.coeff P = 1)
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sY] [Smooth sY]
    (g : Y ⟶ X) [Surjective g] (Q : MMP.Mori.PrimeDivisor Y) :
    ∑ j, ((Module.length (Y.presheaf.stalk Q.genericPoint) (Y.presheaf.stalk Q.genericPoint ⧸
        IdealSheafData.stalk ((F j).comap g) Q.genericPoint)).toNat : ℤ) =
      ∑ P : D.support, ((Module.length (Y.presheaf.stalk Q.genericPoint)
        (Y.presheaf.stalk Q.genericPoint ⧸
          IdealSheafData.stalk (P.1.idealSheaf.comap g) Q.genericPoint)).toNat : ℤ) := by
  classical
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI hcartP : ∀ P : MMP.Mori.PrimeDivisor X,
      Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf :=
    fun P => AlgebraicGeometry.PrimeDivisor.isEffectiveCartierDivisor_idealSheaf (fun z => by
      haveI := isRegularLocalRing_stalk_of_smooth_over_field sX z
      exact IsRegularLocalRing.uniqueFactorizationMonoid _) P
  set y := Q.genericPoint
  choose t ht htc using fun j => exists_stalk_eq_span_and_stalk_comap_eq_span g (F j) y
  choose π hπ hπc using fun P : D.support =>
    exists_stalk_eq_span_and_stalk_comap_eq_span g P.1.idealSheaf y
  haveI : IsDomain (Y.presheaf.stalk y) := by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sY y
    exact IsRegularLocalRing.isDomain _
  haveI : Ring.KrullDimLE 1 (Y.presheaf.stalk y) :=
    krullDimLE_of_coheight_le (by rw [MMP.Mori.PrimeDivisor.coheight_genericPoint]; rfl)
  set φ := (g.stalkMap y).hom
  have hπne : ∀ P : D.support, φ (π P) ≠ 0 := fun P => by
    haveI := isEffectiveCartierDivisor_comap_of_surjective g P.1.idealSheaf
    exact ne_zero_of_stalk_eq_span _ (hπc P)
  have hfin : ∀ P : D.support, Ring.ord (Y.presheaf.stalk y) (φ (π P)) ≠ ⊤ := fun P =>
    Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero (hπne P))
  set o : D.support → ℕ := fun P => (Ring.ord (Y.presheaf.stalk y) (φ (π P))).toNat with ho
  set a : ι → D.support → ℕ := fun j P => (Module.length (X.presheaf.stalk P.1.genericPoint)
    (X.presheaf.stalk P.1.genericPoint ⧸ IdealSheafData.stalk (F j) P.1.genericPoint)).toNat
  have hlhs : ∀ j, ((Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y ⧸
      IdealSheafData.stalk ((F j).comap g) y)).toNat : ℤ) =
        ∑ P : D.support, if a j P ≠ 0 then (o P : ℤ) else 0 := by
    intro j
    have hass := (associated_localEquation_prod k sX F D hD hD1 (g y) t ht π hπ j).map
      (g.stalkMap y).hom
    rw [map_prod] at hass
    have e : Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y ⧸
        IdealSheafData.stalk ((F j).comap g) y) =
          ∑ P ∈ Finset.univ.filter (fun P => a j P ≠ 0), ((o P : ℕ) : ℕ∞) := by
      rw [htc j]
      change Ring.ord _ _ = _
      rw [Ring.ord_eq_of_associated hass, ord_prod _ _ fun i _ => hπne i]
      exact Finset.sum_congr rfl fun P _ => (ENat.coe_toNat (hfin P)).symm
    rw [e, ← Nat.cast_sum, ENat.toNat_coe, Nat.cast_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun j _ => hlhs j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hr : ((Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y ⧸
      IdealSheafData.stalk (P.1.idealSheaf.comap g) y)).toNat : ℤ) = o P := by
    rw [hπc P]
    rfl
  rw [hr]
  -- `P` occurs in exactly one `F_j`, with multiplicity one
  have hs : ∑ j, (a j P : ℤ) = 1 := (hD P.1).symm.trans (hD1 P.1 P.2)
  have hle : ∀ j, (a j P : ℤ) ≤ 1 := fun j => hs ▸
    Finset.single_le_sum (f := fun j => (a j P : ℤ)) (fun _ _ => Int.natCast_nonneg _)
      (Finset.mem_univ j)
  calc (∑ j, if a j P ≠ 0 then (o P : ℤ) else 0) = ∑ j, (a j P : ℤ) * o P := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have := hle j
        split_ifs with h
        · rw [show (a j P : ℤ) = 1 by omega, one_mul]
        · simp [not_not.mp h]
    _ = o P := by rw [← Finset.sum_mul, hs, one_mul]

end BlochGiesekerGloballyGenerated

section

open CategoryTheory AlgebraicGeometry MMP.Intersection MMP.Intersection.Scheme.Modules

universe u

/-- **Bloch–Gieseker covers, globally generated case.** Let `sX : X ⟶ Spec k` be a smooth variety
over an algebraically closed field of characteristic zero, `h : X ⟶ ℙᴺ_k` a `k`-morphism,
`0 < m`, and `F j`, `j ∈ ι`, finitely many effective Cartier divisors on `X` whose sum `D` is snc
with all coefficients `1`. Then there are a smooth variety `sY : Y ⟶ Spec k`, a finite surjective
`k`-morphism `g : Y ⟶ X` and an invertible sheaf `L'` on `Y` with
`g^* h^* 𝒪(1) ≅ L'^{⊗m}`, such that each `(F j).comap g` is an effective Cartier divisor, smooth
whenever `F j` is, and their sum is snc with all coefficients `1`. -/
@[mmp "prop_km2c_bloch_gieseker_globally_generated_smooth"]
public theorem exists_isFinite_surjective_pullback_twistOne_iso_tensorPow_of_isSNC
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsVariety k sX] [Smooth sX]
    {N : ℕ} (h : X ⟶ ProjSpace k (ULift.{u} (Fin (N + 1))))
    (hh : h ≫ ProjSpace.toSpec k _ = sX) (m : ℕ) (hm : 0 < m)
    {ι : Type*} [Fintype ι] (F : ι → X.IdealSheafData)
    [∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (F j)]
    (D : Divisor X)
    (hD : ∀ P : PrimeDivisor X, D.coeff P = ∑ j, ((Module.length (X.presheaf.stalk P.genericPoint)
      (X.presheaf.stalk P.genericPoint ⧸ IdealSheafData.stalk (F j) P.genericPoint)).toNat : ℤ))
    (hsnc : D.IsSNC sX) (hD1 : ∀ P ∈ D.support, D.coeff P = 1) :
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (g : Y ⟶ X),
      IsVariety k sY ∧ Smooth sY ∧ g ≫ sX = sY ∧ IsFinite g ∧ Surjective g ∧
      (∃ L' : Y.Modules,
        AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L' ∧
        Nonempty ((Scheme.Modules.pullback g).obj
            ((Scheme.Modules.pullback h).obj (ProjSpace.twistOne k _)) ≅ tensorPow L' m)) ∧
      (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((F j).comap g)) ∧
      (∀ j, Smooth ((F j).subschemeι ≫ sX) → Smooth (((F j).comap g).subschemeι ≫ sY)) ∧
      ∃ E : Divisor Y,
        (∀ P : PrimeDivisor Y, E.coeff P = ∑ j,
          ((Module.length (Y.presheaf.stalk P.genericPoint)
            (Y.presheaf.stalk P.genericPoint ⧸
              IdealSheafData.stalk ((F j).comap g) P.genericPoint)).toNat : ℤ)) ∧
        E.IsSNC sY ∧ ∀ P ∈ E.support, E.coeff P = 1 := by
  classical
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x => by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
    exact IsRegularLocalRing.uniqueFactorizationMonoid _
  have hcartP : ∀ P : D.support, Stacks.Divisors.IsEffectiveCartierDivisor P.1.idealSheaf :=
    fun P => AlgebraicGeometry.PrimeDivisor.isEffectiveCartierDivisor_idealSheaf hufd P.1
  haveI : Nonempty X := inferInstance
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast k sX
  obtain ⟨Y, sY, g, hY, hsm, hg, hfin, hsurj, hL, hcartG, hFsm, n', hn', hJ⟩ :=
    exists_cover_transversal k sX N h hh m hm (fun P : D.support => P.1.idealSheaf) n hn
      (fun J _ => ⟨smooth_iSup_idealSheaf_of_isSNC k sX D hsnc J,
        isPureDimensional_iSup_idealSheaf_of_isSNC k sX D hsnc n hn J⟩) F
  haveI := hsm
  haveI := hY
  haveI := hsurj
  haveI := hcartG
  have hcartF : ∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((F j).comap g) :=
    fun j => isEffectiveCartierDivisor_comap_of_surjective g (F j)
  haveI := hcartF
  obtain ⟨E, hE⟩ := exists_divisor_coeff_eq_sum_length k sY hY (fun j => (F j).comap g)
  obtain ⟨E', hE'⟩ := exists_divisor_coeff_eq_sum_length k sY hY
    (fun P : D.support => P.1.idealSheaf.comap g)
  obtain ⟨hsncE', hE'1⟩ :=
    MMP.Mori.DivisorWithCoeffs.isSNC_of_forall_smooth_iSup k sY hY n' hn' _ hJ E' hE'
  have hEE : E = E' := Finsupp.ext fun Q => (hE Q).trans
    ((sum_length_comap_eq_sum_length_comap_idealSheaf k sX F D hD hsnc hD1 sY g Q).trans
      (hE' Q).symm)
  subst hEE
  exact ⟨Y, sY, g, hY, hsm, hg, hfin, hsurj, hL, hcartF, hFsm, E, hE, hsncE', hE'1⟩

end

section BlochGieseker

open CategoryTheory MonoidalCategory MMP.Intersection MMP.Intersection.Scheme.Modules Stacks.Ample
  Stacks.RelativeVeryAmple MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor IsVariety

/-- An immersion into projective space over `Spec k` pinning `M` to the hyperplane sheaf gives a
`k`-morphism to `MMP.Intersection.ProjSpace` pulling `𝒪(1)` back to `M`. -/
private theorem exists_hom_projSpace_of_hasImmersionTwistOver.{u} (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (M : X.Modules)
    (h : Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver sX M) :
    ∃ (N : ℕ) (h : X ⟶ ProjSpace k (ULift.{u} (Fin (N + 1)))),
      h ≫ ProjSpace.toSpec k _ = sX ∧
        Nonempty (M ≅ (AlgebraicGeometry.Scheme.Modules.pullback h).obj
          (ProjSpace.twistOne k _)) := by
  obtain ⟨n, i, -, hover, ⟨e'⟩⟩ := h
  set E := ProjSpace.isoProjectiveSpaceOver k n
  refine ⟨n, i ≫ E.inv, ?_, ⟨?_⟩⟩
  · rw [Category.assoc, (Iso.inv_comp_eq _).2 (ProjSpace.isoProjectiveSpaceOver_hom_fst k n).symm,
      hover]
  have t1 : (AlgebraicGeometry.Scheme.Modules.pullback E.inv).obj
      (ProjSpace.twistOne k (ULift.{u} (Fin (n + 1)))) ≅
      Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k)) :=
    (AlgebraicGeometry.Scheme.Modules.pullback E.inv).mapIso
        (ProjSpace.twistOneIsoPullback k n).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp E.inv E.hom).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr E.inv_hom_id).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId _).app _
  exact e' ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback i).mapIso t1.symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp i E.inv).app _

/-- If `L ≅ L₁ ⊗ L₂⁻¹` and `g^* L₁ ≅ C^{⊗ m}`, `g^* L₂ ≅ B^{⊗ m}` with `C`, `B` invertible, then
`g^* L ≅ (C ⊗ B⁻¹)^{⊗ m}`. -/
private theorem nonempty_pullback_iso_tensorPow_tensor_inv.{u} {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L L₁ L₂ : X.Modules) [IsInvertibleModule X L₁] [IsInvertibleModule X L₂]
    (eL : L ≅ L₁ ⊗ tensorPowModule X L₂ (-1)) (C B : Y.Modules) [IsInvertibleModule Y C]
    [IsInvertibleModule Y B] (m : ℕ)
    (e₁ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj L₁ ≅ tensorPow C m)
    (e₂ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj L₂ ≅ tensorPow B m) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L ≅
      tensorPow (C ⊗ tensorPowModule Y B (-1)) m) := by
  obtain ⟨tC⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule Y C m
  obtain ⟨tB⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule Y B m
  haveI : IsInvertibleModule Y (C ⊗ tensorPowModule Y B (-1)) :=
    (inferInstance : IsInvertibleModule Y (tensorModules Y C (tensorPowModule Y B (-1))))
  obtain ⟨tL⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule Y
    (C ⊗ tensorPowModule Y B (-1)) m
  have e : (tensorPowModule Y (tensorPowModule Y B (m : ℤ)) (-1) ⊗
      tensorPowModule Y B (m : ℤ) : Y.Modules) ≅ 𝟙_ _ :=
    whiskerLeftIso _ (tensorPowModuleOneIso Y (tensorPowModule Y B (m : ℤ))).symm ≪≫
      tensorPowModuleAddIso Y _ (-1) 1 ≪≫ tensorPowModuleCongr Y _ (by norm_num) ≪≫
      tensorPowModuleZeroIso Y _
  have e' : (tensorPowModule Y (tensorPowModule Y B (-1)) (m : ℤ) ⊗
      tensorPowModule Y B (m : ℤ) : Y.Modules) ≅ 𝟙_ _ :=
    whiskerRightIso (Stacks.RelativeVeryAmple.tensorPowModulePowIso Y B (-1) m) _ ≪≫
      tensorPowModuleAddIso Y B _ _ ≪≫ tensorPowModuleCongr Y B (by ring) ≪≫
      tensorPowModuleZeroIso Y B
  have iInv := Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso Y
    (tensorPowModule Y (tensorPowModule Y B (m : ℤ)) (-1))
    (tensorPowModule Y (tensorPowModule Y B (-1)) (m : ℤ)) (tensorPowModule Y B (m : ℤ)) e e'
  exact ⟨(AlgebraicGeometry.Scheme.Modules.pullback g).mapIso eL ≪≫
    Stacks.ProjectiveBundleConormal.pullbackTensorComparisonIso g L₁
      (tensorPowModule X L₂ (-1)) ≪≫
    tensorIso e₁ (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso
      g L₂ (-1)) ≪≫
    tensorIso tC (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorPowModuleIsoOfIsoInt Y
      _ _ (e₂ ≪≫ tB) (-1) ≪≫ iInv) ≪≫
    (Stacks.AmplePullbackPart1.tensorPowModuleTensorIso Y C _ m).symm ≪≫ tL.symm⟩

end BlochGieseker

section

open CategoryTheory AlgebraicGeometry MMP.Intersection MMP.Intersection.Scheme.Modules

universe u

/-- **Bloch–Gieseker covers.** Let `sX : X ⟶ Spec k` be a smooth quasi-projective variety over an
algebraically closed field of characteristic zero, `L` an invertible sheaf on `X`, `0 < m`, and
`F j`, `j ∈ ι`, finitely many effective Cartier divisors on `X` whose sum `D` is snc with all
coefficients `1`. Then there are a smooth variety `sY : Y ⟶ Spec k`, a finite surjective
`k`-morphism `g : Y ⟶ X` and an invertible sheaf `L'` on `Y` with `g^* L ≅ L'^{⊗m}`, such that
each `(F j).comap g` is an effective Cartier divisor, smooth whenever `F j` is, and their sum is
snc with all coefficients `1`. -/
@[mmp "prop_km2c_bloch_gieseker_cover_smooth"]
public theorem exists_isFinite_surjective_pullback_iso_tensorPow_of_isSNC
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sX] [Smooth sX]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (m : ℕ) (hm : 0 < m)
    {ι : Type*} [Fintype ι] (F : ι → X.IdealSheafData)
    [∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (F j)]
    (D : Divisor X)
    (hD : ∀ P : PrimeDivisor X, D.coeff P = ∑ j, ((Module.length (X.presheaf.stalk P.genericPoint)
      (X.presheaf.stalk P.genericPoint ⧸ IdealSheafData.stalk (F j) P.genericPoint)).toNat : ℤ))
    (hsnc : D.IsSNC sX) (hD1 : ∀ P ∈ D.support, D.coeff P = 1) :
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (g : Y ⟶ X),
      IsVariety k sY ∧ Smooth sY ∧ g ≫ sX = sY ∧ IsFinite g ∧ Surjective g ∧
      (∃ L' : Y.Modules,
        AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L' ∧
        Nonempty ((Scheme.Modules.pullback g).obj L ≅ tensorPow L' m)) ∧
      (∀ j, Stacks.Divisors.IsEffectiveCartierDivisor ((F j).comap g)) ∧
      (∀ j, Smooth ((F j).subschemeι ≫ sX) → Smooth (((F j).comap g).subschemeι ≫ sY)) ∧
      ∃ E : Divisor Y,
        (∀ P : PrimeDivisor Y, E.coeff P = ∑ j,
          ((Module.length (Y.presheaf.stalk P.genericPoint)
            (Y.presheaf.stalk P.genericPoint ⧸
              IdealSheafData.stalk ((F j).comap g) P.genericPoint)).toNat : ℤ)) ∧
        E.IsSNC sY ∧ ∀ P ∈ E.support, E.coeff P = 1 := by
  haveI : Stacks.Ample.IsInvertibleModule X L := ‹_›
  obtain ⟨L₁, L₂, _, _, hv₁, hv₂, ⟨eL⟩⟩ :=
    MMP.Foundation.exists_isRelativelyVeryAmple_iso_tensor_inv k sX L
  obtain ⟨N₁, h₁, hh₁, ⟨e₁⟩⟩ := exists_hom_projSpace_of_hasImmersionTwistOver k sX L₁
    (Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple sX L₁ hv₁)
  obtain ⟨N₂, h₂, hh₂, ⟨e₂⟩⟩ := exists_hom_projSpace_of_hasImmersionTwistOver k sX L₂
    (Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple sX L₂ hv₂)
  obtain ⟨Y₁, s₁, g₁, _, _, hg₁, _, _, ⟨A, hA, ⟨eA⟩⟩, _, hsm₁, E₁, hE₁, hsnc₁, hE₁1⟩ :=
    MMP.Mori.exists_isFinite_surjective_pullback_twistOne_iso_tensorPow_of_isSNC k sX h₁ hh₁
      m hm F D hD hsnc hD1
  obtain ⟨Y, sY, g₂, hVY, hSY, hg₂, _, _, ⟨B, hB, ⟨eB⟩⟩, hC₂, hsm₂, E, hE, hsncE, hE1⟩ :=
    MMP.Mori.exists_isFinite_surjective_pullback_twistOne_iso_tensorPow_of_isSNC k s₁
      (g₁ ≫ h₂) (by rw [Category.assoc, hh₂, hg₁]) m hm (fun j => (F j).comap g₁) E₁ hE₁
      hsnc₁ hE₁1
  haveI : Stacks.Ample.IsInvertibleModule Y₁ A := hA
  haveI : Stacks.Ample.IsInvertibleModule Y B := hB
  obtain ⟨tA⟩ := nonempty_pullback_tensorPow_iso g₂ A m
  have f₁ : (AlgebraicGeometry.Scheme.Modules.pullback (g₂ ≫ g₁)).obj L₁ ≅
      tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback g₂).obj A) m :=
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp g₂ g₁).app L₁).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback g₂).mapIso
        ((AlgebraicGeometry.Scheme.Modules.pullback g₁).mapIso e₁ ≪≫ eA) ≪≫ tA
  have f₂ : (AlgebraicGeometry.Scheme.Modules.pullback (g₂ ≫ g₁)).obj L₂ ≅ tensorPow B m :=
    (AlgebraicGeometry.Scheme.Modules.pullback (g₂ ≫ g₁)).mapIso e₂ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp (g₂ ≫ g₁) h₂).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr (Category.assoc g₂ g₁ h₂)).app _ ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp g₂ (g₁ ≫ h₂)).app _).symm ≪≫ eB
  refine ⟨Y, sY, g₂ ≫ g₁, hVY, hSY, by rw [Category.assoc, hg₁, hg₂], inferInstance,
    inferInstance, ⟨_, (inferInstance : Stacks.Ample.IsInvertibleModule Y
      (Stacks.RelativeVeryAmple.tensorModules Y
        ((AlgebraicGeometry.Scheme.Modules.pullback g₂).obj A)
        (Stacks.Ample.tensorPowModule Y B (-1)))),
      nonempty_pullback_iso_tensorPow_tensor_inv (g₂ ≫ g₁) L L₁ L₂ eL _ B m f₁ f₂⟩,
    by simpa only [Scheme.IdealSheafData.comap_comp] using hC₂,
    fun j hj => by
      rw [Scheme.IdealSheafData.comap_comp]
      exact hsm₂ j (hsm₁ j hj), E,
    fun P => (hE P).trans <| Finset.sum_congr rfl fun j _ => by
      rw [Scheme.IdealSheafData.comap_comp], hsncE, hE1⟩

end

end MMP.Mori
