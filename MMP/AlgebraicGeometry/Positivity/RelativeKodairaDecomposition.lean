module
public import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
public import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
public import MMP.AlgebraicGeometry.Positivity.BigAmplePlusEffective
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Divisor.InvertibleSheafOfEffective
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafSpelling
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecQuotientInSite
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBaseFunctor
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Relative Kodaira decomposition, and positivity over a birational image

Let `f : Y ⟶ S` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, with `Y` normal and `ℚ`-factorial. An `f`-big `ℚ`-divisor `G` on `Y` is
`ℚ`-linearly equivalent to `H + E - f^*T`, with `H` an ample effective `ℚ`-divisor on `Y`, `E` an
effective `ℚ`-divisor on `Y`, and `T` a `ℚ`-Cartier divisor on `S`. The proof writes a multiple of
`G` as `A + E` with `A` `f`-ample, takes a section `φ` of `jA - H₀` over a neighbourhood of the
generic point of `f(Y)` for an effective ample `H₀`, and observes that the poles of
`div φ + nG - H₀` are vertical; they are cancelled by the pull-back of a multiple of a
hypersurface section of `S` that does not contain `f(Y)`.

If moreover `k = ℂ` and `f` is birational onto its scheme-theoretic image, the generic fibre of `Y`
over `f(Y)` is a point. Every invertible sheaf then has non-zero generic rank, so every Cartier
divisor `L` is `f`-big; writing `mL ∼ A + E` and twisting `A` by the pull-back of an ample divisor
of `S`, which has degree zero on the curves contracted by `f`, puts `±[L]` in the relative
effective cone. Hence every `ℝ`-Cartier divisor on `Y` is pseudo-effective over `S`, and every
`ℚ`-Cartier `ℚ`-divisor, in particular the zero one, is `f`-big.

## Main results

* `MMP.Mori.exists_isCartier_isEffective_isAmple`: a normal projective variety carries an
  effective ample Cartier Weil divisor.
* `MMP.Mori.QDivisor.IsRelativelyBig.exists_qLinearlyEquivalent_add_sub_pullback`: the
  decomposition `G ∼_ℚ H + E - f^*T`.
* `MMP.Mori.relativeGenericRank_ne_zero_of_isBirationalMorphism_toImage`: over a base onto
  which `f` is birational, every invertible sheaf has non-zero generic rank.
* `MMP.Mori.Divisor.isRelativelyBig_of_isBirationalMorphism_toImage`,
  `MMP.Mori.QDivisor.isRelativelyBig_of_isBirationalMorphism_toImage`: over a base onto which `f`
  is birational, every Cartier divisor and every `ℚ`-Cartier `ℚ`-divisor is `f`-big.
* `MMP.Fourfold.exists_isEffective_degree_eq_nsmul_of_isRelativelyAmple`: an `f`-ample Cartier
  divisor has a positive multiple with the degrees, on the curves contracted by `f`, of an
  effective Cartier divisor.
* positivity over a birational image:
`MMP.Fourfold.isRelativelyPseudoEffective_and_isRelativelyBig_zero_of_isBirationalMorphism_toImage`

## Implementation notes

The `ℚ`-Cartier divisor `T` on `S` is written `c • T₀` with `c ∈ ℚ` and `T₀` a Cartier divisor
on `S`; its pull-back to `Y` is `c` times the Weil divisor `[f^*T₀]` of the Cartier pull-back
`f^*T₀` (`MMP.Intersection.IsPullback`, `MMP.Intersection.IsWeilDivisorOfCartier`). Since `S`
need not be normal, `T` is a Cartier and not a Weil divisor. Every `ℚ`-Cartier divisor
`∑ cⱼ Tⱼ` whose pull-back is defined is a sum of such terms, so the one-term form is the
stronger statement. The instance arguments `IsLocallyNoetherian Y` and `CompactSpace Y`
follow from projectivity of `Y` over `k`; they are stated so that the divisor-theoretic notions
elaborate.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold Opposite TopologicalSpace TensorProduct
open MonoidalCategory

namespace MMP.Mori

/-- A normal projective variety carries an effective Cartier Weil divisor `H` whose divisorial
sheaf `𝒪_Y(H)` is ample: a power of an ample invertible sheaf has a regular section, whose zero
scheme is an effective Cartier divisor, and its Weil divisor is `H`. -/
public theorem exists_isCartier_isEffective_isAmple {k : Type v} [Field k] {Y : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sY]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] :
    ∃ (H : Divisor Y) (hH : H.IsCartier), H.IsEffective ∧ H.IsAmple hH := by
  haveI hYi : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety k sY).toIsIntegral
  have hYqp : Stacks.HProjective.IsHQuasiProjective sY :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sY).isProjective.isHQuasiProjective
  obtain ⟨-, L, hLinv, hLamp⟩ :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sY hYqp
  have hL : Stacks.Ample.IsAmple Y L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sY L hLamp
  obtain ⟨IX, hIX, -, -, n, hn, ⟨eX⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint Y))
  obtain ⟨H, hH0, hHc, ⟨eH⟩, -⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor IX hIX
  haveI := hHc.isInvertibleModule_divisorialSheaf
  have hHamp : Stacks.Ample.IsAmple Y H.divisorialSheaf :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)
  exact ⟨H, hHc, hH0, hHamp⟩

end MMP.Mori

namespace Proof_lem_fourfold_relative_kodaira_core

/-- The Weil divisor `[D]` of a Cartier divisor. -/
private lemma isWeilDivisorOfCartier_cartierWeilDivisor {S : Scheme.{v}} [IsIntegral S]
    [IsNoetherian S] (D : S.CartierDivisor) :
    MMP.Intersection.IsWeilDivisorOfCartier D (weilDivisorEquivFinsupp (cartierWeilDivisor D)) := by
  intro P
  have hcoh : Order.coheight (MMP.Mori.PrimeDivisor.genericPoint P) = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  haveI : Ring.KrullDimLE 1
      (S.presheaf.stalk (MMP.Intersection.primeDivisorSubvariety P).genericPoint) :=
    krullDimLE_of_coheight_le hcoh.le
  obtain ⟨N, hN⟩ :=
    MMP.Intersection.exists_isOrderAlong D (MMP.Intersection.primeDivisorSubvariety P)
  convert hN using 1
  have hN' := hN
  unfold MMP.Intersection.IsOrderAlong at hN'
  dsimp only [MMP.Intersection.primeDivisorSubvariety_genericPoint] at hN'
  obtain ⟨a, b, ha, hb, ⟨g, hg, hgab⟩, la, lb, hla, hlb, rfl⟩ := hN'
  change cartierMultiplicity D (MMP.Mori.PrimeDivisor.genericPoint P) = _
  rw [MMP.Intersection.cartierMultiplicity_eq_ord_of_isLocalEquationAt hg]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (S.presheaf.stalk _) S.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : totalQuotientStalkToFunctionField _ g *
      algebraMap (S.presheaf.stalk _) S.functionField b =
      algebraMap (S.presheaf.stalk _) S.functionField a := by
    have := congrArg (totalQuotientStalkToFunctionField _) hgab.2
    rw [map_mul, MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    rw [mul_comm]
    exact this
  have hTg := MMP.Intersection.totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg
  have hord := S.ord_mul (x := MMP.Mori.PrimeDivisor.genericPoint P) hTg hbK
  rw [key, ord_algebraMap_stalk _ hcoh a ha0, ord_algebraMap_stalk _ hcoh b hb0] at hord
  erw [hla, hlb, ENat.toNat_coe, ENat.toNat_coe] at hord
  omega

/-- Key local computation: for an effective `T₀` and a pull-back `T₀'`, the order of `T₀'` along
a prime divisor is a natural number, positive when the image of its generic point lies in
`Supp T₀`. -/
private lemma exists_order_of_isPullback {Y S : Scheme.{v}} [IsIntegral Y]
    {f : Y ⟶ S} {T₀ : S.CartierDivisor} {T₀' : Y.CartierDivisor}
    (hT₀ : MMP.Intersection.IsEffective T₀) (hpb : MMP.Intersection.IsPullback f T₀ T₀')
    (P : MMP.Mori.PrimeDivisor Y) {N : ℤ}
    (hN : MMP.Intersection.IsOrderAlong T₀' (MMP.Intersection.primeDivisorSubvariety P) N) :
    ∃ n : ℕ, N = n ∧ (f P.genericPoint ∈ MMP.Intersection.cartierSupport T₀ → 1 ≤ n) := by
  set y := P.genericPoint with hy
  obtain ⟨U, hvU, s, hs, hsD⟩ := hT₀ (f y)
  set a : S.presheaf.stalk (f y) := S.presheaf.germ U (f y) hvU s with ha
  have hg : MMP.Intersection.IsLocalEquationAt T₀ (f y)
      (MMP.Intersection.stalkToTotalQuotient _ a) :=
    ⟨U, hvU, hs.unit, hsD, MMP.Intersection.germ_toTotalQuotient hvU s⟩
  have hab : MMP.Intersection.IsFraction (MMP.Intersection.stalkToTotalQuotient _ a) a 1 :=
    ⟨by rw [map_one]; exact isUnit_one, by rw [map_one, one_mul]⟩
  have h' : MMP.Intersection.IsFraction
      (MMP.Intersection.stalkToTotalQuotient y (f.stalkMap y a)) (f.stalkMap y a)
      (f.stalkMap y 1) :=
    ⟨by rw [map_one, map_one]; exact isUnit_one, by rw [map_one, map_one, one_mul]⟩
  have hloc := hpb.isLocalEquationAt hg hab h'
  obtain ⟨n, hn, rfl⟩ := hN.eq_length (V := MMP.Intersection.primeDivisorSubvariety P) hloc
  refine ⟨n, rfl, fun hsupp => ?_⟩
  have hna : ¬ IsUnit a := by
    intro hu
    apply MMP.Intersection.notMem_cartierSupport_of_isLocalEquationAt_one _ hsupp
    have h1 := hg.mul_units hu.unit⁻¹
    have e : MMP.Intersection.stalkToTotalQuotient _ a *
        MMP.Intersection.stalkToTotalQuotient _ ((hu.unit⁻¹ : (S.presheaf.stalk (f y))ˣ) :
          S.presheaf.stalk (f y)) = 1 := by
      rw [← map_mul]
      have : a * ((hu.unit⁻¹ : (S.presheaf.stalk (f y))ˣ) : S.presheaf.stalk (f y)) = 1 := by
        simp
      rw [this, map_one]
    rwa [e] at h1
  have hnu : ¬ IsUnit (f.stalkMap y a) := fun hu => hna (isUnit_of_map_unit (f.stalkMap y).hom a hu)
  by_contra hlt
  have h0 : n = 0 := by omega
  subst h0
  apply hnu
  have hsub := Module.length_eq_zero_iff.1 (by exact_mod_cast hn)
  exact (Ideal.span_singleton_eq_top).1 (Ideal.Quotient.subsingleton_iff.1 hsub)

/-- Pole-clearing step: for finitely many prime divisors of `Y` that are vertical over `S`,
there is a Cartier divisor `T₀` on `S` with a pull-back `T₀'` whose Weil divisor is effective and
positive along each of them. -/
private theorem exists_weilPullback_pos_of_vertical
    {k : Type v} [Field k] [IsAlgClosed k] [CharZero k] {Y S : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sS]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (f : Y ⟶ S)
    (s : Finset (MMP.Mori.PrimeDivisor Y))
    (hs : ∀ P ∈ s, f P.genericPoint ≠ f (genericPoint Y)) :
    ∃ (T₀ : S.CartierDivisor) (T₀' : Y.CartierDivisor) (w : Divisor Y),
      MMP.Intersection.IsPullback f T₀ T₀' ∧ MMP.Intersection.IsWeilDivisorOfCartier T₀' w ∧
      w.IsEffective ∧ ∀ P ∈ s, 0 < w.coeff P := by
  haveI hYi : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety k sY).toIsIntegral
  letI : IsNoetherian Y := ⟨⟩
  haveI hSln : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian sS
  have hSv : MMP.Mori.IsVariety k sS := inferInstance
  have hSq : Stacks.HProjective.IsHQuasiProjective sS :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sS).isProjective.isHQuasiProjective
  set T : Set S := ⋃ P ∈ s, closure {f P.genericPoint} with hT
  have hTc : IsClosed T := s.finite_toSet.isClosed_biUnion fun P _ => isClosed_closure
  have hy₀ : f (genericPoint Y) ∉ T := by
    intro h
    obtain ⟨P, hP, hmem⟩ := Set.mem_iUnion₂.1 h
    apply hs P hP
    have h1 : f P.genericPoint ⤳ f (genericPoint Y) := specializes_iff_mem_closure.2 hmem
    have h2 : f (genericPoint Y) ⤳ f P.genericPoint :=
      ((genericPoint_specializes P.genericPoint)).map f.continuous
    exact (h1.antisymm h2).eq
  obtain ⟨T₀, hT₀e, hTs, hy₀s⟩ :=
    MMP.Threefold.Resolution.exists_isEffective_subset_cartierSupport_of_notMem hSv hSq hTc hy₀
  have hpc : MMP.Intersection.PullbackCondition f T₀ := by
    intro η hη
    have hass : Stacks.Divisors.schemeAssociatedPoints Y = {genericPoint Y} :=
      calc Stacks.Divisors.schemeAssociatedPoints Y
          = Stacks.Divisors.schemeWeaklyAssociatedPoints Y :=
            AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints Y _
        _ = genericPoints Y := AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints Y
        _ = {genericPoint Y} := genericPoints_eq_singleton
    rw [hass] at hη
    rw [Set.mem_singleton_iff.1 hη]
    exact hy₀s
  obtain ⟨T₀', hpb⟩ := MMP.Intersection.exists_isPullback hpc
  have hw := isWeilDivisorOfCartier_cartierWeilDivisor T₀'
  refine ⟨T₀, T₀', _, hpb, hw, fun P => ?_, fun P hP => ?_⟩
  · obtain ⟨n, hn, -⟩ := exists_order_of_isPullback hT₀e hpb P (hw P)
    show 0 ≤ _
    rw [hn]; exact Int.natCast_nonneg n
  · obtain ⟨n, hn, h1⟩ := exists_order_of_isPullback hT₀e hpb P (hw P)
    have hmem : f P.genericPoint ∈ MMP.Intersection.cartierSupport T₀ :=
      hTs (Set.mem_iUnion₂.2 ⟨P, hP, subset_closure rfl⟩)
    have := h1 hmem
    show 0 < _
    rw [hn]; exact_mod_cast this

section SheafComparison

variable {S : Scheme.{v}} [IsIntegral S] [IsLocallyNoetherian S]

/-- On an integral scheme the generic point of the irreducible component is the generic point. -/
private lemma componentGenericPoint_specializes (Z : irreducibleComponents S) :
    componentGenericPoint S Z ⤳ genericPoint S := by
  rw [specializes_iff_mem_closure, (isGenericPoint_componentGenericPoint S Z).def]
  exact Z.2.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _) (Set.mem_univ _)

private lemma stalkSpecializes_algebraMap (Z : irreducibleComponents S)
    (a : S.presheaf.stalk (componentGenericPoint S Z)) :
    S.presheaf.stalkSpecializes (componentGenericPoint_specializes Z)
      (algebraMap (S.presheaf.stalk (componentGenericPoint S Z)) S.functionField a) = a := by
  change (S.presheaf.stalkSpecializes _) ((S.presheaf.stalkSpecializes _) a) = a
  rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

private lemma stalkSpecializes_stalkSpecializes_genericPoint (Z : irreducibleComponents S)
    (c : S.functionField) :
    (S.presheaf.stalkSpecializes ((genericPoint_spec S).specializes (Set.mem_univ _) :
      genericPoint S ⤳ componentGenericPoint S Z))
      (S.presheaf.stalkSpecializes (componentGenericPoint_specializes Z) c) = c := by
  rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- On a normal integral Noetherian scheme the Weil divisor of a Cartier divisor is Cartier. -/
private lemma isCartier_of_isWeilDivisorOfCartier [IsNormal S] [CompactSpace S]
    {D : S.CartierDivisor} {D' : Divisor S}
    (h : MMP.Intersection.IsWeilDivisorOfCartier D D') : D'.IsCartier := by
  let ι₀ : S.functionField →+* RationalFunctions S :=
    Pi.ringHom fun Z => (S.presheaf.stalkSpecializes (componentGenericPoint_specializes Z)).hom
  have hev : ∀ (Z : irreducibleComponents S) (c : S.functionField),
      MMP.Threefold.Mori.Helpers.evalFF Z (ι₀ c) = c :=
    stalkSpecializes_stalkSpecializes_genericPoint
  intro x
  obtain ⟨f, U, hxU, g, hg, rfl⟩ := MMP.Intersection.exists_isLocalEquationAt D x
  set c := totalQuotientStalkToFunctionField (genericPoint S)
    (S.totalQuotientSheaf.presheaf.germ U (genericPoint S)
      ((genericPoint_spec S).mem_open_set_iff U.isOpen |>.mpr ⟨x, Set.mem_univ _, hxU⟩)
      (g : _)) with hc
  have hc0 : c ≠ 0 :=
    MMP.Intersection.totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt
      ⟨U, _, g, hg, rfl⟩
  refine ⟨U, hxU, Units.map ι₀.toMonoidHom (Units.mk0 c hc0), fun E hE => ?_⟩
  have hη := MMP.Intersection.genericPoint_mem_of_support_inter_nonempty E hE
  rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  change _ = S.ord (MMP.Threefold.Mori.Helpers.evalFF E.component (ι₀ c)) _
  rw [hev, ← MMP.Intersection.ord_eq_coeff_of_isLocalEquationAt h E rfl ⟨U, hη, g, hg, rfl⟩, hc,
    ← MMP.Intersection.totalQuotientStalkToFunctionField_stalkSpecializes
      ((genericPoint_spec S).specializes (Set.mem_univ (MMP.Mori.PrimeDivisor.genericPoint E))),
    TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- The value in `K(X)` of a section of `𝓜_X` is the same at every point. -/
private lemma totalQuotientStalkToFunctionField_germ_eq {V : S.Opens}
    (σ : S.totalQuotientSheaf.obj.obj (op V)) {x y : S} (hx : x ∈ V) (hy : y ∈ V) :
    totalQuotientStalkToFunctionField x (S.totalQuotientSheaf.presheaf.germ V x hx σ) =
      totalQuotientStalkToFunctionField y (S.totalQuotientSheaf.presheaf.germ V y hy σ) := by
  have hg : genericPoint S ∈ V := (genericPoint_spec S).mem_open_set_iff V.isOpen |>.mpr
    ⟨x, Set.mem_univ _, hx⟩
  have key : ∀ z (hz : z ∈ V), totalQuotientStalkToFunctionField z
      (S.totalQuotientSheaf.presheaf.germ V z hz σ) = totalQuotientStalkToFunctionField
        (genericPoint S) (S.totalQuotientSheaf.presheaf.germ V (genericPoint S) hg σ) := by
    intro z hz
    rw [← MMP.Intersection.totalQuotientStalkToFunctionField_stalkSpecializes
      ((genericPoint_spec S).specializes (Set.mem_univ z)),
      TopCat.Presheaf.germ_stalkSpecializes_apply]
  rw [key x hx, key y hy]

/-- Every rational function is a section of `𝓜_X` over every open. -/
private lemma exists_totalQuotient_section (V : S.Opens) (c : S.functionField) :
    ∃ σ : S.totalQuotientSheaf.obj.obj (op V), ∀ (x : S) (hx : x ∈ V),
      totalQuotientStalkToFunctionField x (S.totalQuotientSheaf.presheaf.germ V x hx σ) = c := by
  have hloc : ∀ x : V, ∃ (W : S.Opens) (_ : W ≤ V) (_ : (x : S) ∈ W)
      (s : S.totalQuotientSheaf.obj.obj (op W)), ∀ (y : S) (hy : y ∈ W),
        totalQuotientStalkToFunctionField y (S.totalQuotientSheaf.presheaf.germ W y hy s) = c := by
    intro x
    obtain ⟨m, hm⟩ := (MMP.Intersection.totalQuotientStalkToFunctionField_bijective (x : S)).2 c
    obtain ⟨W, hxW, s, rfl⟩ := S.totalQuotientSheaf.presheaf.germ_exist m
    refine ⟨W ⊓ V, inf_le_right, ⟨hxW, x.2⟩,
      S.totalQuotientSheaf.obj.map (homOfLE inf_le_left).op s, fun y hy => ?_⟩
    rw [TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf, ← hm]
    exact totalQuotientStalkToFunctionField_germ_eq s _ _
  choose W hWV hxW s hs using hloc
  have hcover : V ≤ iSup W := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩
  have hc : TopCat.Presheaf.IsCompatible S.totalQuotientSheaf.obj W s := by
    intro i j
    refine TopCat.Presheaf.section_ext S.totalQuotientSheaf _ _ _ fun z hz => ?_
    apply (MMP.Intersection.totalQuotientStalkToFunctionField_bijective z).1
    rw [TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf,
      TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf, hs, hs]
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.totalQuotientSheaf W V
    (fun x => homOfLE (hWV x)) hcover s hc
  refine ⟨σ, fun x hx => ?_⟩
  have := hs ⟨x, hx⟩ x (hxW _)
  rw [← hσ ⟨x, hx⟩, TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf] at this
  exact this

/-- A section of `𝓜_X` over `V`, read in the sheaf of rational functions of `MMP.Mori`. -/
private noncomputable def toRationalFunctions (V : S.Opens)
    (σ : S.totalQuotientSheaf.obj.obj (op V)) :
    ToType ((MMP.Mori.rationalFunctionsPresheaf S).obj (op V)) :=
  fun Z => S.presheaf.stalkSpecializes (componentGenericPoint_specializes Z.1)
    (totalQuotientStalkToFunctionField _ (S.totalQuotientSheaf.presheaf.germ V _ Z.2 σ))

private lemma toRationalFunctions_add (V : S.Opens) (σ τ : S.totalQuotientSheaf.obj.obj (op V)) :
    toRationalFunctions V (σ + τ) = toRationalFunctions V σ + toRationalFunctions V τ := by
  funext Z
  simp only [toRationalFunctions, map_add]
  rfl

private lemma toRationalFunctions_smul [IsNormal S] (V : S.Opens) (r : Γ(S, V))
    (σ : S.totalQuotientSheaf.obj.obj (op V)) :
    toRationalFunctions V (r • σ) = r • toRationalFunctions V σ := by
  funext Z
  rw [MMP.Mori.rationalFunctions_smul_apply]
  simp only [toRationalFunctions, MMP.Intersection.smul_totalQuotient_def, map_mul,
    MMP.Intersection.germ_toTotalQuotient,
    MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient,
    stalkSpecializes_algebraMap]

private lemma toRationalFunctions_map {V W : S.Opens} (i : W ⟶ V)
    (σ : S.totalQuotientSheaf.obj.obj (op V)) :
    toRationalFunctions W (S.totalQuotientSheaf.obj.map i.op σ) =
      (MMP.Mori.rationalFunctionsPresheaf S).map i.op (toRationalFunctions V σ) := by
  funext Z
  rw [MMP.Mori.rationalFunctionsPresheaf_map_apply]
  simp only [toRationalFunctions]
  rw [TopCat.Presheaf.germ_res_apply' S.totalQuotientSheaf.presheaf]

/-- The valuation of the component of a unit of `K(X)` along a prime divisor is its order. -/
private lemma valuation_component_eq_exp_ord [IsNormal S] (E : MMP.Mori.PrimeDivisor S)
    (ψ : (MMP.Mori.RationalFunctions S)ˣ) :
    E.valuation (MMP.Mori.RationalFunctions.component S E.component ψ) =
      WithZero.exp (E.ord ψ) := by
  rw [MMP.Mori.PrimeDivisor.ord, MMP.Mori.PrimeDivisor.ordHom]
  change _ = ((WithZero.unitsWithZeroEquiv (Units.map E.valuation.toMonoidHom
    (Units.map (MMP.Mori.RationalFunctions.component S E.component).toMonoidHom ψ)) :
      Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  rfl

private lemma mem_lineBundleSections_iff_isDivisorialSection [IsNormal S]
    {D : S.CartierDivisor} {D' : Divisor S} (h : MMP.Intersection.IsWeilDivisorOfCartier D D')
    (V : S.Opens) (σ : S.totalQuotientSheaf.obj.obj (op V)) :
    σ ∈ MMP.Intersection.lineBundleSections D V ↔
      D'.IsDivisorialSection V (toRationalFunctions V σ) := by
  by_cases hV : genericPoint S ∈ V
  · set c := totalQuotientStalkToFunctionField (genericPoint S)
      (S.totalQuotientSheaf.presheaf.germ V (genericPoint S) hV σ) with hc
    have hT : ∀ (x : S) (hx : x ∈ V), totalQuotientStalkToFunctionField x
        (S.totalQuotientSheaf.presheaf.germ V x hx σ) = c :=
      fun x hx => totalQuotientStalkToFunctionField_germ_eq σ hx hV
    have hrat : ∀ Z, toRationalFunctions V σ Z =
        S.presheaf.stalkSpecializes (componentGenericPoint_specializes Z.1) c := by
      intro Z
      simp only [toRationalFunctions, hT]
    by_cases hc0 : c = 0
    · constructor
      · intro _ E hE
        rw [hrat, hc0, map_zero]
        exact MMP.Mori.PrimeDivisor.OrdGE.zero _
      · intro _
        show ∀ (x : S) (hx : x ∈ V) (f : S.totalQuotientSheaf.presheaf.stalk x),
          MMP.Intersection.IsLocalEquationAt D x f → _ ∈ _
        intro x hx f _
        have : S.totalQuotientSheaf.presheaf.germ V x hx σ = 0 :=
          (MMP.Intersection.totalQuotientStalkToFunctionField_bijective x).1
            (by rw [hT, hc0, map_zero])
        rw [this, zero_mul]
        exact zero_mem _
    · haveI : Nonempty V := ⟨⟨_, hV⟩⟩
      rw [MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add h V hc0 σ hT]
      unfold MMP.Mori.Divisor.IsDivisorialSection
      refine forall_congr' fun E => forall_congr' fun hE => ?_
      let ι₀ : S.functionField →+* MMP.Mori.RationalFunctions S :=
        Pi.ringHom fun Z => (S.presheaf.stalkSpecializes (componentGenericPoint_specializes Z)).hom
      set ψ := Units.map ι₀.toMonoidHom (Units.mk0 c hc0) with hψ
      have hv := valuation_component_eq_exp_ord E ψ
      rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at hv
      have hev : MMP.Threefold.Mori.Helpers.evalFF E.component (ψ : MMP.Mori.RationalFunctions S)
          = c := stalkSpecializes_stalkSpecializes_genericPoint E.component c
      rw [hev] at hv
      have hne : MMP.Mori.RationalFunctions.component S E.component ψ ≠ 0 :=
        (ψ.isUnit.map (MMP.Mori.RationalFunctions.component S E.component)).ne_zero
      have hcomp : S.presheaf.stalkSpecializes (componentGenericPoint_specializes E.component) c =
          MMP.Mori.RationalFunctions.component S E.component ψ := rfl
      rw [hrat ⟨E.component, _⟩, hcomp]
      unfold MMP.Mori.PrimeDivisor.OrdGE
      rw [hv, WithZero.exp_le_exp]
      simp only [hne, false_or]
      omega
  · have hempty : ∀ x, x ∉ V := fun x hx =>
      hV ((genericPoint_spec S).mem_open_set_iff V.isOpen |>.mpr ⟨x, Set.mem_univ _, hx⟩)
    constructor
    · rintro - E ⟨y, -, hy⟩
      exact absurd hy (hempty y)
    · intro _
      show ∀ (x : S) (hx : x ∈ V) (f : S.totalQuotientSheaf.presheaf.stalk x),
        MMP.Intersection.IsLocalEquationAt D x f → _ ∈ _
      intro x hx
      exact absurd hx (hempty x)

private lemma bijective_toRationalFunctions [IsNormal S] (V : S.Opens) :
    Function.Bijective (toRationalFunctions (S := S) V) := by
  constructor
  · intro σ τ hστ
    refine TopCat.Presheaf.section_ext S.totalQuotientSheaf V σ τ fun x hx => ?_
    obtain ⟨Z, hxZ⟩ := MMP.Mori.exists_mem_irreducibleComponents x
    have hZV : componentGenericPoint S Z ∈ V :=
      (MMP.Mori.genericPoint_mem_iff Z V).mpr ⟨x, hx, hxZ⟩
    have h1 := congrArg (fun φ => S.presheaf.stalkSpecializes ((genericPoint_spec S).specializes
      (Set.mem_univ _) : genericPoint S ⤳ componentGenericPoint S Z) (φ ⟨Z, hZV⟩)) hστ
    simp only [toRationalFunctions, stalkSpecializes_stalkSpecializes_genericPoint] at h1
    refine (MMP.Intersection.totalQuotientStalkToFunctionField_bijective x).1 ?_
    rwa [totalQuotientStalkToFunctionField_germ_eq σ hx hZV,
      totalQuotientStalkToFunctionField_germ_eq τ hx hZV]
  · intro φ
    by_cases hV : ∃ Z : irreducibleComponents S, componentGenericPoint S Z ∈ V
    · obtain ⟨Z₀, hZ₀⟩ := hV
      obtain ⟨σ, hσ⟩ := exists_totalQuotient_section V (S.presheaf.stalkSpecializes
        ((genericPoint_spec S).specializes (Set.mem_univ _) :
          genericPoint S ⤳ componentGenericPoint S Z₀) (φ ⟨Z₀, hZ₀⟩))
      refine ⟨σ, funext fun Z => ?_⟩
      have : Subsingleton (irreducibleComponents S) :=
        MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents
      obtain ⟨Z, hZ⟩ := Z
      obtain rfl : Z = Z₀ := Subsingleton.elim _ _
      simp only [toRationalFunctions, hσ]
      rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
        TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    · exact ⟨0, funext fun Z => absurd ⟨Z.1, Z.2⟩ hV⟩

/-- On a normal integral Noetherian scheme the sheaf `𝒪_X(D)` of a Cartier divisor is the
divisorial sheaf of its Weil divisor. -/
private lemma nonempty_sheaf_iso_divisorialSheaf [IsNormal S] {D : S.CartierDivisor}
    {D' : Divisor S} (h : MMP.Intersection.IsWeilDivisorOfCartier D D') :
    Nonempty (MMP.CartierDivisor.sheaf D ≅ D'.divisorialSheaf) := by
  let f : ∀ V : S.Opens, Γ(MMP.CartierDivisor.sheaf D, V) →ₗ[Γ(S, V)]
      D'.divisorialSubmodule V := fun V =>
    { toFun := fun σ => ⟨toRationalFunctions V (MMP.CartierDivisorSheaf.sectionVal σ),
        (mem_lineBundleSections_iff_isDivisorialSection h V (MMP.CartierDivisorSheaf.sectionVal
            σ)).1 (MMP.CartierDivisor.sectionVal_mem_lineBundleSections σ)⟩
      map_add' := fun σ τ => Subtype.ext (toRationalFunctions_add V
          (MMP.CartierDivisorSheaf.sectionVal σ) (MMP.CartierDivisorSheaf.sectionVal τ))
      map_smul' := fun r σ => Subtype.ext (toRationalFunctions_smul V r
          (MMP.CartierDivisorSheaf.sectionVal σ)) }
  have hf : ∀ V, Function.Bijective (f V) := fun V => by
    refine ⟨fun σ τ hστ => MMP.CartierDivisorSheaf.sectionVal_injective
      ((bijective_toRationalFunctions V).1 (congrArg Subtype.val hστ)), fun φ => ?_⟩
    obtain ⟨σ, hσ⟩ := (bijective_toRationalFunctions V).2 φ.1
    exact ⟨MMP.CartierDivisor.sectionOfMem
        ((mem_lineBundleSections_iff_isDivisorialSection h V σ).2 (hσ ▸ φ.2)),
      Subtype.ext hσ⟩
  exact ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (LinearEquiv.ofBijective (f V.unop) (hf V.unop)).toModuleIso)
      (fun V W i => by
        ext σ
        exact Subtype.ext (toRationalFunctions_map i.unop (MMP.CartierDivisorSheaf.sectionVal
            σ))))⟩

end SheafComparison

section FiberRankCongr

variable {X : Scheme.{v}} {F G : X.Modules}

private lemma germM_smul' (M : X.Modules) (y : X) (W : X.Opens) (hy : y ∈ W) (r : Γ(X, W))
    (m : Γ(M, W)) :
    TopCat.Presheaf.germ M.val.presheaf W y hy (r • m) =
      X.presheaf.germ W y hy r • TopCat.Presheaf.germ M.val.presheaf W y hy m :=
  PresheafOfModules.germ_smul M.val y W hy r m

/-- The map on stalks (as abelian groups) induced by a morphism of modules. -/
private noncomputable def stalkMapAb (φ : F ⟶ G) (y : X) :
    TopCat.Presheaf.stalk (C := Ab.{v}) F.val.presheaf y ⟶
      TopCat.Presheaf.stalk (C := Ab.{v}) G.val.presheaf y :=
  (TopCat.Presheaf.stalkFunctor Ab.{v} y).map φ.mapPresheaf

private lemma stalkMapAb_germ (φ : F ⟶ G) (y : X) {W : X.Opens} (hy : y ∈ W) (ξ : Γ(F, W)) :
    stalkMapAb φ y (TopCat.Presheaf.germ F.val.presheaf W y hy ξ) =
      TopCat.Presheaf.germ G.val.presheaf W y hy (φ.app W ξ) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy φ.mapPresheaf ξ

private lemma stalkMapAb_smul (φ : F ⟶ G) (y : X) (ρ : X.presheaf.stalk y)
    (n : TopCat.Presheaf.stalk (C := Ab.{v}) F.val.presheaf y) :
    stalkMapAb φ y (ρ • n) = ρ • stalkMapAb φ y n := by
  obtain ⟨V, hyV, ξ, hξ⟩ := X.presheaf.exists_germ_eq ρ
  obtain ⟨W, hWV, hyW, ζ, hζ⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf n hyV
  subst hξ
  subst hζ
  have key : ∀ (r : Γ(X, W)) (m : Γ(F, W)),
      stalkMapAb φ y (X.presheaf.germ W y hyW r •
          TopCat.Presheaf.germ F.val.presheaf W y hyW m) =
        X.presheaf.germ W y hyW r •
          stalkMapAb φ y (TopCat.Presheaf.germ F.val.presheaf W y hyW m) := by
    intro r m
    rw [← germM_smul' F y W hyW r m, stalkMapAb_germ φ y hyW,
      stalkMapAb_germ φ y hyW m, ← germM_smul' G y W hyW r (φ.app W m)]
    congr 1
    exact Scheme.Modules.Hom.app_smul φ r m
  rw [← X.presheaf.germ_res_apply (homOfLE hWV) y hyW ξ]
  exact key _ ζ

private lemma stalkMapAb_inv_hom (e : F ≅ G) (x : X)
    (n : TopCat.Presheaf.stalk (C := Ab.{v}) F.val.presheaf x) :
    stalkMapAb e.inv x (stalkMapAb e.hom x n) = n := by
  obtain ⟨W, hW, ζ, rfl⟩ := TopCat.Presheaf.germ_exist F.val.presheaf n
  have h1 := stalkMapAb_germ e.hom x hW (ζ : Γ(F, W))
  have h2 := stalkMapAb_germ e.inv x hW (e.hom.app W (ζ : Γ(F, W)))
  have h3 : e.inv.app W (e.hom.app W (ζ : Γ(F, W))) = ζ := by
    have := ConcreteCategory.congr_hom (show e.hom.app W ≫ e.inv.app W = 𝟙 _ from by
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id]; rfl) ζ
    exact this
  rw [h1, h2, h3]

/-- The fibre rank is invariant under isomorphism of modules. -/
private theorem fiberRank_congr (e : F ≅ G) (x : X) :
    Scheme.Modules.fiberRank F x = Scheme.Modules.fiberRank G x := by
  unfold Scheme.Modules.fiberRank
  let eS : TopCat.Presheaf.stalk (C := Ab.{v}) F.val.presheaf x ≃ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{v}) G.val.presheaf x :=
    { toFun := stalkMapAb e.hom x
      map_add' := map_add _
      map_smul' := fun ρ n => stalkMapAb_smul e.hom x ρ n
      invFun := stalkMapAb e.inv x
      left_inv := stalkMapAb_inv_hom e x
      right_inv := stalkMapAb_inv_hom e.symm x }
  exact (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (X.residueField x) _) eS).finrank_eq

end FiberRankCongr

section Rank

open MonoidalCategory in
/-- If `𝒪_X(D₀) ≅ 𝒪_X(Ec)` then `𝒪_X(m • Ec) ≅ 𝒪_X(m • D₀)` for `m ≥ 1`. -/
private theorem nonempty_sheaf_nsmul_iso {X : Scheme.{v}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D₀ : Divisor X} (hD₀ : D₀.IsCartier) {Ec : X.CartierDivisor}
    (e : D₀.divisorialSheaf ≅ MMP.CartierDivisor.sheaf Ec) (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (MMP.CartierDivisor.sheaf (m • Ec) ≅
      (m • D₀).divisorialSheaf) ∧ (m • D₀).IsCartier := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [one_nsmul, one_nsmul]
    exact ⟨⟨e.symm⟩, hD₀⟩
  | succ n hn ih =>
    obtain ⟨⟨ie⟩, hc⟩ := ih
    rw [succ_nsmul, succ_nsmul]
    refine ⟨⟨?_⟩, hc.add hD₀⟩
    exact (MMP.CartierDivisorSheaf.sheafMulIso (n • Ec) Ec).symm ≪≫
      MonoidalCategory.tensorIso ie e.symm ≪≫ hc.divisorialSheafTensorIso hD₀

/-- The generic rank only depends on the isomorphism class of the module. -/
private theorem relativeGenericRank_congr {X Y : Scheme.{v}} (f : X ⟶ Y) [IrreducibleSpace X]
    {F G : X.Modules} (e : F ≅ G) : relativeGenericRank f F = relativeGenericRank f G :=
  fiberRank_congr ((Scheme.Modules.pushforward f).mapIso e) _

end Rank

/-- Bigness of a Cartier Weil divisor `D₀` transfers to a Cartier divisor `Ec` with
`𝒪_X(D₀) ≅ 𝒪_X(Ec)`. -/
private theorem isRelativelyBigCartier_of_isRelativelyBig {X Y : Scheme.{v}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Y) {D₀ : Divisor X}
    (hD₀ : D₀.IsCartier) {Ec : X.CartierDivisor}
    (e : D₀.divisorialSheaf ≅ MMP.CartierDivisor.sheaf Ec)
    (hb : D₀.IsRelativelyBig f) : IsRelativelyBigCartier f Ec := by
  obtain ⟨a, b, ha, hb', c, hc, k₀, hk⟩ := hb
  refine ⟨a, b, ha, hb', c, hc, max k₀ 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hk0 : k₀ ≤ m := le_trans (le_max_left _ _) hm
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hn : 1 ≤ n := by omega
  obtain ⟨⟨ie⟩, -⟩ := nonempty_sheaf_nsmul_iso hD₀ e n hn
  have h := hk _ hk0
  rw [natCast_zsmul] at h ⊢
  rw [relativeGenericRank_congr f ie]
  exact h

/-- Divisors with isomorphic divisorial sheaves are linearly equivalent. -/
private theorem linearlyEquivalent_of_iso_divisorialSheaf {X : Scheme.{v}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D D' : Divisor X}
    (e : D.divisorialSheaf ≅ D'.divisorialSheaf) : D.LinearlyEquivalent D' :=
  MMP.Threefold.Mori.CanonUniq.linearlyEquivalent_of_iso (U := ⊤) (fun _ => trivial)
    ((Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).mapIso e)

/-- Cartier divisors linearly equivalent have isomorphic sheaves. -/
public theorem _root_.MMP.Fourfold.nonempty_sheaf_iso_of_linearlyEquivalent {X : Scheme.{v}}
    {B B' : X.CartierDivisor} (h : MMP.Intersection.LinearlyEquivalent B B') :
    Nonempty (MMP.CartierDivisor.sheaf B ≅
      MMP.CartierDivisor.sheaf B') := by
  obtain ⟨c, hc⟩ := (MMP.Intersection.mem_principalSubgroup_iff).1 h
  have hB : B = B' + MMP.Intersection.principalDivisor c := by rw [hc]; abel
  subst hB
  exact ⟨(MMP.CartierDivisor.sheafAddPrincipalIso B' c).symm⟩

/-- Relative ampleness depends only on the isomorphism class. -/
public theorem _root_.MMP.Fourfold.isRelativelyAmple_of_iso {X Y : Scheme.{v}} (f : X ⟶ Y)
    {L L' : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : IsRelativelyAmple f L) : IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1 hamp

/-- A non-zero section of `𝒪_X(B)` over an open `U` of an integral scheme is a rational function
`φ` with `div φ + B ≥ 0` at every prime divisor meeting `U`. -/
private theorem exists_unit_of_ne_zero_divisorialSection {X : Scheme.{v}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {B : Divisor X} {U : X.Opens}
    (ψ : B.divisorialSubmodule U) (hψ : ψ ≠ 0) :
    ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X,
      (E.support ∩ (U : Set X)).Nonempty → 0 ≤ (MMP.Mori.principalDivisor φ + B).coeff E := by
  classical
  haveI : Subsingleton (irreducibleComponents X) :=
    MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents
  have hne : ∃ Z0 : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      ψ.1 Z0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hψ (Subtype.ext (funext hcon))
  obtain ⟨Z0, hZ0⟩ := hne
  have hall : ∀ Z : irreducibleComponents X, Z = Z0.1 := fun Z => Subsingleton.elim _ _
  have hZU : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ∈ U := fun Z => by
    rw [hall Z]; exact Z0.2
  have hfield := RationalFunctions.isField_stalk (X := X)
  have hunit : ∀ Z : irreducibleComponents X, IsUnit (ψ.1 ⟨Z, hZU Z⟩) := fun Z => by
    obtain rfl : Z = Z0.1 := hall Z
    obtain ⟨b, hb⟩ := (hfield Z0.1).mul_inv_cancel hZ0
    exact IsUnit.of_mul_eq_one b hb
  refine ⟨(RationalFunctions.unitsEquiv X).symm (fun Z => (hunit Z).unit), fun E hE => ?_⟩
  have h1 := ψ.2 E hE
  have hcomp : (((RationalFunctions.unitsEquiv X).symm (fun Z => (hunit Z).unit) :
      (RationalFunctions X)ˣ) : RationalFunctions X) E.component = ψ.1 ⟨E.component, hZU _⟩ := rfl
  have h3 := E.valuation_component ((RationalFunctions.unitsEquiv X).symm
    (fun Z => (hunit Z).unit))
  rw [hcomp] at h3
  rcases h1 with h0 | hle
  · exact absurd h0 (hunit E.component).ne_zero
  · rw [h3, WithZero.exp_le_exp] at hle
    rw [DivisorWithCoeffs.coeff_add, MMP.Mori.coeff_principalDivisor]
    omega

section TwistIso

/-- `𝒪_X(nW + B) ≅ 𝒪_X(B) ⊗ 𝒪_X(W)^{⊗ n}` for Cartier divisors `W` and `B`. -/
private theorem nonempty_divisorialSheaf_nsmul_add_iso {X : Scheme.{v}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {W B : Divisor X} (hW : W.IsCartier)
    [Stacks.Ample.IsInvertibleModule X W.divisorialSheaf]
    (hB : B.IsCartier) (n : ℕ) :
    Nonempty ((n • W + B).divisorialSheaf ≅ B.divisorialSheaf ⊗
        Stacks.Ample.tensorPowModule X W.divisorialSheaf n) ∧ (n • W + B).IsCartier := by
  induction n with
  | zero =>
    have h : ((0 : ℕ) • W + B) = B := by simp
    rw [h]
    exact ⟨⟨(ρ_ _).symm ≪≫ whiskerLeftIso _
      (Stacks.Ample.tensorPowModuleZeroIso X W.divisorialSheaf).symm⟩, hB⟩
  | succ n ih =>
    obtain ⟨⟨e⟩, hc⟩ := ih
    have h : ((n + 1 : ℕ) • W + B) = (n • W + B) + W := by
      rw [succ_nsmul]; abel
    rw [h]
    refine ⟨⟨(hc.divisorialSheafTensorIso hW).symm ≪≫ ?_⟩, hc.add hW⟩
    refine (whiskerRightIso e _) ≪≫ (α_ _ _ _) ≪≫ ?_
    refine whiskerLeftIso _ ?_
    exact (whiskerLeftIso _ (Stacks.Ample.tensorPowModuleOneIso X W.divisorialSheaf).symm) ≪≫
      Stacks.Ample.tensorPowModuleAddIso X W.divisorialSheaf (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X W.divisorialSheaf
        (by push_cast; ring)

end TwistIso

/-- The fibre rank of a zero module is zero. -/
private theorem fiberRank_eq_zero_of_isZero {Y : Scheme.{v}} (G : Y.Modules)
    (hG : Limits.IsZero G) (y : Y) : Scheme.Modules.fiberRank G y = 0 := by
  have hsec : ∀ (U : Y.Opens) (m : Γ(G, U)), m = 0 := by
    intro U m
    have h := (SheafOfModules.evaluation Y.ringCatSheaf (op U)).map_isZero hG
    exact (ModuleCat.isZero_iff_subsingleton.1 h).elim m 0
  have hstalk : ∀ n : TopCat.Presheaf.stalk (C := Ab.{v}) G.val.presheaf y, n = 0 := by
    intro n
    obtain ⟨U, hU, m, rfl⟩ := TopCat.Presheaf.germ_exist G.val.presheaf n
    rw [hsec U m]
    exact map_zero _
  unfold Scheme.Modules.fiberRank
  letI : Module (Y.presheaf.stalk y) (G.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) G.val y
  letI : Algebra (Y.presheaf.stalk y) (Y.residueField y) := (Y.residue y).hom.toAlgebra
  haveI : Subsingleton (Y.residueField y ⊗[Y.presheaf.stalk y] G.presheaf.stalk y) := by
    refine ⟨fun a b => ?_⟩
    have : ∀ x : Y.residueField y ⊗[Y.presheaf.stalk y] G.presheaf.stalk y, x = 0 := fun x =>
      TensorProduct.inductionOn x
        (fun a n => by rw [hstalk n]; exact TensorProduct.tmul_zero _ a)
        (fun a b ha hb => by rw [ha, hb, add_zero])
    exact (this a).trans (this b).symm
  show Module.finrank (Y.residueField y)
    (Y.residueField y ⊗[Y.presheaf.stalk y] G.presheaf.stalk y) = 0
  exact Module.finrank_zero_of_subsingleton

/-- The tensor product of `𝒪_Y`-modules, at the monoidal structure of the Stacks library. -/
private noncomputable abbrev tensorS (Y : Scheme.{v}) (A B : Y.Modules) : Y.Modules :=
  @MonoidalCategoryStruct.tensorObj Y.Modules _
    (@MonoidalCategory.toMonoidalCategoryStruct _ _ (Stacks.SheafInternalHom.schemeMonoidalCategory
        Y)) A B

/-- A non-zero sheaf of modules generated by sections has a non-zero global section. -/
private theorem exists_ne_zero_global_of_generatingSections {Y : Scheme.{v}}
    {N : SheafOfModules.{v} Y.ringCatSheaf} (σ : N.GeneratingSections) (hN : ¬ Limits.IsZero N) :
    ∃ t : Γ(N, ⊤), t ≠ 0 := by
  by_contra h
  push Not at h
  apply hN
  have hπ : σ.π = 0 := by
    apply N.freeHomEquiv.injective
    funext i
    apply Subtype.ext
    funext X
    have e1 : N.freeHomEquiv σ.π i = σ.s i := by
      change (N.freeHomEquiv (N.freeHomEquiv.symm σ.s)) i = σ.s i
      rw [Equiv.apply_symm_apply]
    rw [e1]
    obtain ⟨U⟩ := X
    have hc := (σ.s i).2 (show op (⊤ : Y.Opens) ⟶ op U from (homOfLE (le_top : U ≤ ⊤)).op)
    have h0 := h ((σ.s i).1 (op ⊤))
    rw [← hc, h0]
    have hR : (N.freeHomEquiv (0 : SheafOfModules.free σ.I ⟶ N) i).1 (op U) = 0 := by
      show (N.unitHomEquiv (SheafOfModules.ιFree i ≫ 0)).val (op U) = 0
      rw [SheafOfModules.unitHomEquiv_apply_coe, Limits.comp_zero]
      have hz : SheafOfModules.Hom.val (0 : SheafOfModules.unit Y.ringCatSheaf ⟶ N) = 0 :=
        (SheafOfModules.forget _).map_zero _ _
      rw [hz]
      have h2 : PresheafOfModules.Hom.app (0 : (SheafOfModules.unit Y.ringCatSheaf).val ⟶ N.val)
          (op U) = 0 := (PresheafOfModules.evaluation _ (op U)).map_zero _ _
      rw [h2]
      first | rfl | exact LinearMap.zero_apply _ | simp [ModuleCat.hom_zero]
    rw [hR]
    exact (map_zero (ConcreteCategory.hom (N.val.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)))
  exact Limits.IsZero.of_epi_eq_zero σ.π hπ

section PullbackTwist

/-- The pull-back of `𝒪_X(nW + B)` along `i` is `i^*𝒪_X(B) ⊗ (i^*𝒪_X(W))^{⊗ n}`. -/
private theorem nonempty_pullback_divisorialSheaf_nsmul_add_iso {Z X : Scheme.{v}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (i : Z ⟶ X)
    {W B : Divisor X} (hW : W.IsCartier)
    [Stacks.Ample.IsInvertibleModule X W.divisorialSheaf]
    [Stacks.Ample.IsInvertibleModule Z ((Scheme.Modules.pullback i).obj W.divisorialSheaf)]
    (hB : B.IsCartier) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback i).obj (n • W + B).divisorialSheaf ≅
      (Scheme.Modules.pullback i).obj B.divisorialSheaf ⊗
        Stacks.Ample.tensorPowModule Z ((Scheme.Modules.pullback i).obj W.divisorialSheaf) n) := by
  obtain ⟨⟨e⟩, -⟩ := nonempty_divisorialSheaf_nsmul_add_iso hW hB n
  exact ⟨(Scheme.Modules.pullback i).mapIso e ≪≫
    Stacks.ProjectiveBundleConormal.pullbackTensorComparisonIso i _ _ ≪≫
    whiskerLeftIso _
        (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso i
      W.divisorialSheaf (n : ℤ))⟩

end PullbackTwist

/-- Over a relative ample divisor, a twist has a non-zero section over `f⁻¹(V)`. -/
private theorem exists_ne_zero_section_twist_over {Y S : Scheme.{v}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (f : Y ⟶ S) {W H : Divisor Y}
    (hW : W.IsCartier) (hH : H.IsCartier)
    (hA : haveI := hW.isInvertibleModule_divisorialSheaf;
      MMP.Mori.IsRelativelyAmple f W.divisorialSheaf) :
    ∃ j : ℕ, 0 < j ∧ ∃ V : S.Opens, f (genericPoint Y) ∈ V ∧
      ∃ ψ : (j • W + (-H)).divisorialSubmodule (f ⁻¹ᵁ V), ψ ≠ 0 := by
  haveI := hW.isInvertibleModule_divisorialSheaf
  haveI := hH.neg.isInvertibleModule_divisorialSheaf
  obtain ⟨V, hVaff, hηV, hamp⟩ := hA (f (genericPoint Y))
  set U : Y.Opens := f ⁻¹ᵁ V with hU
  have hηU : genericPoint Y ∈ U := hηV
  haveI : Nonempty U := ⟨⟨genericPoint Y, hηU⟩⟩
  have iP : ∀ F : Y.Modules,
      (RingedSpaceModuleAdjunction.modulePullback U.ι.toLRSHom.toShHom).obj F ≅
        (Scheme.Modules.pullback U.ι).obj F := fun F =>
    (Adjunction.leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction U.ι.toLRSHom.toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι)).app F
  set M : U.toScheme.Modules := (Scheme.Modules.pullback U.ι).obj W.divisorialSheaf with hM
  set G : U.toScheme.Modules := (Scheme.Modules.pullback U.ι).obj (-H).divisorialSheaf with hG
  haveI hMinv : Stacks.Ample.IsInvertibleModule U.toScheme M := inferInstance
  haveI hGinv : Stacks.Ample.IsInvertibleModule U.toScheme G := inferInstance
  have hamp' : Stacks.Ample.IsAmple U.toScheme M :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ (iP W.divisorialSheaf)).1 hamp
  haveI : IsLocallyNoetherian U.toScheme := inferInstance
  haveI hGcoh : SheafOfModules.IsCoherent G :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible U.toScheme G
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G
  have hGnz : ¬ Limits.IsZero G := by
    intro hz
    have h1 := fiberRank_eq_zero_of_isZero G hz ⟨genericPoint Y, hηU⟩
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank G 1 :=
      (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one
        U.toScheme G).mp inferInstance
    have h2 := Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank G 1
      ⟨genericPoint Y, hηU⟩
    omega
  obtain ⟨n₀, hn₀⟩ :=
    Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple M hamp' G hqc hft
  set N : ℕ := (max n₀ 1).toNat with hN
  have hNn₀ : n₀ ≤ (N : ℤ) := le_trans (le_max_left _ _) (Int.self_le_toNat _)
  have hN1 : 0 < N := by
    have h0 := Int.self_le_toNat (max n₀ 1)
    have h1 : (1 : ℤ) ≤ max n₀ 1 := le_max_right _ _
    omega
  obtain ⟨σ, -⟩ := hn₀ (N : ℤ) hNn₀
  have hNz : ¬ Limits.IsZero
      (tensorS U.toScheme G (Stacks.Ample.tensorPowModule U.toScheme M (N : ℤ))) := by
    intro hz
    haveI : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨U.toScheme.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (U.toScheme.presheaf) (forget₂ CommRingCat RingCat)
          (U.toScheme.ringCatSheaf.2)⟩).flip.obj
        (Stacks.Ample.tensorPowModule U.toScheme M (N : ℤ))).IsEquivalence :=
      (Stacks.SheafOfModules.Invertible.isInvertible_iff_tensorRightFunctor_isEquivalence
        U.toScheme.presheaf U.toScheme.ringCatSheaf.2 _).1 inferInstance
    exact hGnz (Limits.IsZero.of_full_of_faithful_of_isZero
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨U.toScheme.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (U.toScheme.presheaf) (forget₂ CommRingCat RingCat)
          (U.toScheme.ringCatSheaf.2)⟩).flip.obj
        (Stacks.Ample.tensorPowModule U.toScheme M (N : ℤ))) G
      (hz.of_iso (Stacks.SheafOfModules.tensorObjIso U.toScheme.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf U.toScheme) G
        (Stacks.Ample.tensorPowModule U.toScheme M (N : ℤ))).symm))
  obtain ⟨x0, hx0⟩ := exists_ne_zero_global_of_generatingSections σ hNz
  obtain ⟨e1⟩ := nonempty_pullback_divisorialSheaf_nsmul_add_iso U.ι hW hH.neg N
  have e2 := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (N • W + -H).divisorialSheaf
  have hU' : (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) = U := by simp
  refine ⟨N, hN1, V, hηV, ?_⟩
  let E : (Scheme.Modules.restrictFunctor U.ι).obj (N • W + -H).divisorialSheaf ≅
      tensorS U.toScheme G (Stacks.Ample.tensorPowModule U.toScheme M (N : ℤ)) :=
    e2 ≪≫ e1 ≪≫ (Stacks.SheafOfModules.tensorObjIso U.toScheme.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf U.toScheme) G
      (Stacks.Ample.tensorPowModule U.toScheme M (N : ℤ))).symm
  let y : Γ((Scheme.Modules.restrictFunctor U.ι).obj (N • W + -H).divisorialSheaf, ⊤) :=
    E.inv.app ⊤ x0
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    have h1 : E.hom.app ⊤ (E.inv.app ⊤ x0) = x0 :=
      ConcreteCategory.congr_hom (show E.inv.app ⊤ ≫ E.hom.app ⊤ = 𝟙 _ by
        rw [← Scheme.Modules.Hom.comp_app, E.inv_hom_id]
        rfl) x0
    rw [← h1]
    change E.hom.app ⊤ y = 0
    rw [h]
    exact map_zero _
  have key : ∀ (a b : Y.Opens) (h : a = b) (z : Γ((N • W + -H).divisorialSheaf, a)), z ≠ 0 →
      (h ▸ z : Γ((N • W + -H).divisorialSheaf, b)) ≠ 0 := by
    rintro a b rfl z hz
    exact hz
  exact (⟨hU' ▸ y, key _ _ hU' y hy0⟩ : ∃ ψ : (N • W + -H).divisorialSubmodule U, ψ ≠ 0)

/-- Relatively ample twists have generic sections: if `𝒪_Y(W)` is `f`-ample then, for every Cartier
divisor `H`, some multiple `jW - H` has a non-zero section over `f⁻¹(V)` for a neighbourhood `V` of
the generic point of `f(Y)`. -/
private theorem exists_section_twist_of_isRelativelyAmple {Y S : Scheme.{v}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (f : Y ⟶ S) {W H : Divisor Y}
    (hW : W.IsCartier) (hH : H.IsCartier)
    (hA : haveI := hW.isInvertibleModule_divisorialSheaf;
      MMP.Mori.IsRelativelyAmple f W.divisorialSheaf) :
    ∃ j : ℕ, 0 < j ∧ ∃ V : S.Opens, f (genericPoint Y) ∈ V ∧
      ∃ φ : (RationalFunctions Y)ˣ, ∀ E : MMP.Mori.PrimeDivisor Y,
        (E.support ∩ ((f ⁻¹ᵁ V : Y.Opens) : Set Y)).Nonempty →
          0 ≤ (principalDivisor φ + j • W - H).coeff E := by
  obtain ⟨j, hj, V, hV, ψ, hψ⟩ := exists_ne_zero_section_twist_over f hW hH hA
  obtain ⟨φ, hφ⟩ := exists_unit_of_ne_zero_divisorialSection ψ hψ
  refine ⟨j, hj, V, hV, φ, fun E hE => ?_⟩
  have h := hφ E hE
  have e : MMP.Mori.principalDivisor φ + (j • W + -H) = MMP.Mori.principalDivisor φ + j • W - H :=
      by
    abel
  rwa [e] at h

/-- The `f`-big divisor `D₀` has a multiple linearly equivalent to `W + E` with `W` Cartier,
`f`-ample and `E` effective. -/
private theorem exists_linearlyEquivalent_ample_add_effective
    {k : Type v} [Field k] [IsAlgClosed k] [CharZero k] {Y S : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sS]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (f : Y ⟶ S)
    (hf : f ≫ sS = sY) {D₀ : Divisor Y} (hD₀ : D₀.IsCartier) (hb : D₀.IsRelativelyBig f) :
    ∃ m : ℕ, 0 < m ∧ ∃ (W E : Divisor Y) (hW : W.IsCartier), 0 ≤ E ∧
      (haveI := hW.isInvertibleModule_divisorialSheaf;
        MMP.Mori.IsRelativelyAmple f W.divisorialSheaf) ∧
      (m • D₀).LinearlyEquivalent (W + E) := by
  haveI hYi : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety k sY).toIsIntegral
  letI : IsNoetherian Y := ⟨⟩
  haveI := hD₀.isInvertibleModule_divisorialSheaf
  obtain ⟨Ec, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D₀.divisorialSheaf
  have hbig := isRelativelyBigCartier_of_isRelativelyBig f hD₀ e hb
  obtain ⟨m, hm, A, E, hA, hE, hlin⟩ :=
    (MMP.Mori.isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sY sS f hf Ec).1 hbig
  obtain ⟨⟨ie⟩, hmc⟩ := nonempty_sheaf_nsmul_iso hD₀ e m hm
  have hwA := isWeilDivisorOfCartier_cartierWeilDivisor A
  have hwE := isWeilDivisorOfCartier_cartierWeilDivisor E
  set wA : Divisor Y := weilDivisorEquivFinsupp (cartierWeilDivisor A) with hwAdef
  set wE : Divisor Y := weilDivisorEquivFinsupp (cartierWeilDivisor E) with hwEdef
  have hwAE : MMP.Intersection.IsWeilDivisorOfCartier (A + E) (wA + wE) := fun P => by
    have := (hwA P).add (hwE P)
    simpa [DivisorWithCoeffs.coeff_add] using this
  obtain ⟨eA⟩ := nonempty_sheaf_iso_divisorialSheaf hwA
  obtain ⟨eAE⟩ := nonempty_sheaf_iso_divisorialSheaf hwAE
  obtain ⟨eL⟩ := nonempty_sheaf_iso_of_linearlyEquivalent hlin
  have hcA : wA.IsCartier := isCartier_of_isWeilDivisorOfCartier hwA
  refine ⟨m, hm, wA, wE, hcA, ?_, ?_, ?_⟩
  · intro P
    exact (hwE P).nonneg_of_isEffective hE
  · haveI := hcA.isInvertibleModule_divisorialSheaf
    exact isRelativelyAmple_of_iso f eA hA
  · exact linearlyEquivalent_of_iso_divisorialSheaf (ie.symm ≪≫ eL ≪≫ eAE)

/-- Generic-fibre step: for an `f`-big `G` there are `n > 0`, an integral `D = n G`, an
effective ample Cartier `H₀` and a rational function `φ` such that every negative coefficient
of `div φ + D - H₀` sits on a prime divisor whose generic point does not map to the generic
point of `f(Y)`. -/
private theorem exists_section_sub_ample_neg_vertical
    {k : Type v} [Field k] [IsAlgClosed k] [CharZero k] {Y S : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sS]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (hY : IsQFactorial sY) (f : Y ⟶ S)
    (hf : f ≫ sS = sY) {G : QDivisor Y} (hG : G.IsRelativelyBig f) :
    ∃ n : ℕ, 0 < n ∧ ∃ D H₀ : Divisor Y, Divisor.toQDivisor D = (n : ℚ) • G ∧
      (∃ hH : H₀.IsCartier, H₀.IsAmple hH) ∧ H₀.IsEffective ∧
      ∃ φ : (RationalFunctions Y)ˣ, ∀ P : MMP.Mori.PrimeDivisor Y,
        (principalDivisor φ + D - H₀).coeff P < 0 →
          f P.genericPoint ≠ f (genericPoint Y) := by
  haveI hYi : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety k sY).toIsIntegral
  obtain ⟨m₀, hm₀, D₀, hD₀, hD₀c, hD₀b⟩ := hG
  obtain ⟨m, hm, W, E, hW, hE, hWa, hlin⟩ :=
    exists_linearlyEquivalent_ample_add_effective sY sS f hf hD₀c hD₀b
  obtain ⟨H, hHc, hHe, hHa⟩ := exists_isCartier_isEffective_isAmple sY
  obtain ⟨j, hj, V, hV, φ₀, hφ₀⟩ := exists_section_twist_of_isRelativelyAmple f hW hHc hWa
  obtain ⟨ρ, hρ⟩ := hlin
  refine ⟨m₀ * (j * m), Nat.mul_pos hm₀ (Nat.mul_pos hj hm), (j * m) • D₀, H,
    ?_, ⟨hHc, hHa⟩, hHe, φ₀ * (ρ ^ j)⁻¹, fun P hP => ?_⟩
  · rw [map_nsmul, hD₀, ← Nat.cast_smul_eq_nsmul ℚ (j * m), smul_smul]
    congr 1
    push_cast
    ring
  · by_contra heq
    have hηV : genericPoint Y ∈ ((f ⁻¹ᵁ V : Y.Opens) : Set Y) := hV
    have hPV : P.genericPoint ∈ ((f ⁻¹ᵁ V : Y.Opens) : Set Y) := by
      change f P.genericPoint ∈ (V : Set S)
      rw [heq]; exact hV
    have hne : (P.support ∩ ((f ⁻¹ᵁ V : Y.Opens) : Set Y)).Nonempty :=
      ⟨P.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl, hPV⟩
    have h1 := hφ₀ P hne
    have hpow : ∀ n : ℕ, principalDivisor (ρ ^ n) = n • principalDivisor ρ := by
      intro n
      induction n with
      | zero => simp [MMP.Mori.principalDivisor_one]
      | succ n ih => rw [pow_succ, MMP.Mori.principalDivisor_mul, ih, succ_nsmul]
    have key : principalDivisor (φ₀ * (ρ ^ j)⁻¹) + (j * m) • D₀ - H =
        (principalDivisor φ₀ + j • W - H) + j • E := by
      rw [MMP.Mori.principalDivisor_mul, MMP.Mori.principalDivisor_inv, hpow, mul_smul]
      have h2 : m • D₀ = W + E + principalDivisor ρ := by rw [← hρ]; abel
      rw [h2, smul_add, smul_add]
      abel
    rw [key, DivisorWithCoeffs.coeff_add] at hP
    have h3 : 0 ≤ (j • E).coeff P := by
      have h4 : (j • E).coeff P = j • E.coeff P := by
        simp [DivisorWithCoeffs.coeff_apply]
      rw [h4]
      exact nsmul_nonneg (hE P) j
    omega

/-- A non-negative rational multiple of an effective divisor is effective. -/
private lemma isEffective_smul_toQDivisor {X : Scheme.{v}} {D : Divisor X} (hD : D.IsEffective)
    {q : ℚ} (hq : 0 ≤ q) : (q • Divisor.toQDivisor D).IsEffective := fun P => by
  change 0 ≤ q * (D P : ℚ)
  have : (0 : ℚ) ≤ D P := by exact_mod_cast hD P
  positivity

/-- If `w ≥ 0` is positive on every prime where `D` is negative, then `D + N w ≥ 0` for
`N = ∑ |dᵢ|`. -/
private theorem isEffective_add_smul {X : Scheme.{v}} (D w : Divisor X) (hw : w.IsEffective)
    (hpos : ∀ P ∈ D.support.filter (fun P => D P < 0), 0 < w.coeff P) :
    (D + (∑ P ∈ D.support, (D P).natAbs : ℕ) • w).IsEffective := by
  intro P
  set N : ℕ := ∑ P ∈ D.support, (D P).natAbs
  change 0 ≤ D P + (N : ℤ) * w P
  have hwP : 0 ≤ w P := hw P
  by_cases hDP : D P < 0
  · have hmem : P ∈ D.support := Finsupp.mem_support_iff.2 hDP.ne
    have hw1 : 1 ≤ w P := hpos P (Finset.mem_filter.2 ⟨hmem, hDP⟩)
    have hle : (D P).natAbs ≤ N := Finset.single_le_sum (f := fun P => (D P).natAbs)
      (fun _ _ => Nat.zero_le _) hmem
    have : -(D P) ≤ (N : ℤ) := by omega
    nlinarith
  · push Not at hDP
    positivity

end Proof_lem_fourfold_relative_kodaira_core

namespace MMP.Mori

open Proof_lem_fourfold_relative_kodaira_core

/-- **Relative Kodaira decomposition.** Let `f : Y ⟶ S` be a morphism of projective varieties
over an algebraically closed field `k` of characteristic zero, with `Y` normal and
`ℚ`-factorial. If `G` is an `f`-big `ℚ`-divisor on `Y`, there are an ample effective
`ℚ`-divisor `H` on `Y`, an effective `ℚ`-divisor `E` on `Y` and a `ℚ`-Cartier divisor
`T = c • T₀` on `S` such that `G ∼_ℚ H + E - f^*T`. -/
@[mmp "lem_fourfold_relative_kodaira_core"]
public theorem QDivisor.IsRelativelyBig.exists_qLinearlyEquivalent_add_sub_pullback
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {Y S : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sS]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (hY : IsQFactorial sY) (f : Y ⟶ S)
    (hf : f ≫ sS = sY) {G : QDivisor Y} (hG : G.IsRelativelyBig f) :
    ∃ H E : QDivisor Y, H.IsAmple ∧ H.IsEffective ∧ E.IsEffective ∧
      ∃ (c : ℚ) (T₀ : S.CartierDivisor) (T₀' : Y.CartierDivisor) (w : Divisor Y),
        MMP.Intersection.IsPullback f T₀ T₀' ∧ MMP.Intersection.IsWeilDivisorOfCartier T₀' w ∧
        G.QLinearlyEquivalent (H + E - c • Divisor.toQDivisor w) := by
  obtain ⟨n, hn, D, H₀, hD, hH₀, hH₀e, φ, hneg⟩ :=
    exists_section_sub_ample_neg_vertical sY sS hY f hf hG
  set D₀ : Divisor Y := principalDivisor φ + D - H₀
  obtain ⟨T₀, T₀', w, hT, hw, hwe, hwpos⟩ :=
    exists_weilPullback_pos_of_vertical sY sS f (D₀.support.filter (fun P => D₀ P < 0))
      (fun P hP => hneg P (Finset.mem_filter.1 hP).2)
  set N : ℕ := ∑ P ∈ D₀.support, (D₀ P).natAbs
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨(n : ℚ)⁻¹ • Divisor.toQDivisor H₀, (n : ℚ)⁻¹ • Divisor.toQDivisor (D₀ + N • w),
    ⟨n, hn, H₀, by rw [smul_smul, mul_inv_cancel₀ hn', one_smul], hH₀⟩,
    isEffective_smul_toQDivisor hH₀e (by positivity),
    isEffective_smul_toQDivisor (isEffective_add_smul D₀ w hwe hwpos) (by positivity),
    (N : ℚ) / n, T₀, T₀', w, hT, hw, n, hn, φ⁻¹, ?_⟩
  · rw [MMP.Mori.principalDivisor_inv]
    ext P
    have hDP : (D P : ℚ) = n * G P := by
      have h := congrArg (fun F : QDivisor Y => F P) hD
      simp only [Finsupp.smul_apply, smul_eq_mul] at h
      exact h
    change (n : ℤ) • (G P - ((n : ℚ)⁻¹ * H₀ P + (n : ℚ)⁻¹ * ((D₀ + N • w) P : ℤ)
      - (N : ℚ) / n * w P)) = ((-principalDivisor φ) P : ℤ)
    simp only [D₀, Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_smul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Finsupp.coe_neg, Pi.neg_apply, smul_eq_mul, zsmul_eq_mul,
      nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    push_cast
    rw [hDP]
    field_simp
    ring

end MMP.Mori

section BirationalImage

open Limits Stacks.SheafOfModules.Invertible MMP.CartierDivisorSheaf MMP.Intersection
open Proof_lem_fourfold_relative_kodaira_core

namespace MMP.Proof_lem_fourfold_birational_relative_pseudoeffective

section GenericFibre

/-- The prime `𝔭 = g(ξ)` of the image of the generic point kills the image of `R` in the global
sections of an integral scheme. -/
private theorem ker_le {R : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Spec R) :
    ∀ a ∈ (g (genericPoint X)).asIdeal, ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom a = 0 := by
  intro a ha
  have hb : (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv.hom a) = PrimeSpectrum.basicOpen a := by
    rw [basicOpen_eq_of_affine]
  apply eq_zero_of_basicOpen_eq_bot
  have h1 := Scheme.preimage_basicOpen g ((Scheme.ΓSpecIso R).inv.hom a)
  rw [hb] at h1
  have h2 : X.basicOpen (((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom a) =
      g ⁻¹ᵁ PrimeSpectrum.basicOpen a := h1.symm
  rw [h2]
  by_contra hne
  have hne' : ((g ⁻¹ᵁ PrimeSpectrum.basicOpen a : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h; apply hne; exact TopologicalSpace.Opens.ext h
  have := (genericPoint_spec X).mem_open_set_iff
    (U := (g ⁻¹ᵁ PrimeSpectrum.basicOpen a : X.Opens)) (g ⁻¹ᵁ PrimeSpectrum.basicOpen a).isOpen
  have hm := this.mpr (by simpa using hne')
  exact hm ha

/-- A morphism from an integral scheme to `Spec R` factors through `Spec (R ⧸ 𝔭)`, `𝔭` the
image of the generic point. -/
private noncomputable def toSpecQuot {R : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec R) : X ⟶ Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)) :=
  (ΓSpec.adjunction.homEquiv X (op (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal))))
    (CommRingCat.ofHom (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
      (ker_le g))).op

private theorem toSpecQuot_comp {R : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec R) :
    toSpecQuot g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal)) =
      g := by
  apply ext_to_Spec
  have h := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := X)
    (B := CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal))
    (CommRingCat.ofHom (Ideal.Quotient.lift _ ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
      (ker_le g)))
  have h2 := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal))
  change _ ≫ (toSpecQuot g ≫ _).appTop = _ ≫ g.appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← h2, Category.assoc]
  change _ ≫ (toSpecQuot g).appTop = _ at h
  rw [h]
  ext a
  rfl

/-- The prime ideal of a point of `Spec R` is prime. -/
local instance specPrime {R : CommRingCat.{u}} (x : Spec R) : x.asIdeal.IsPrime :=
  PrimeSpectrum.isPrime x

/-- The map `R ⟶ κ(x)` to the residue field of the point `x` of `Spec R`. -/
private noncomputable def resMap (R : CommRingCat.{u}) (x : Spec R) :
    R ⟶ (Spec R).residueField x :=
  CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField) ≫
    (Scheme.Spec.residueFieldIso R x).inv

private theorem map_resMap (R : CommRingCat.{u}) (x : Spec R) :
    Spec.map (resMap R x) = (Spec R).fromSpecResidueField x := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R x, resMap, Spec.map_comp]

private theorem ker_resMap (R : CommRingCat.{u}) (x : Spec R) :
    RingHom.ker (resMap R x).hom = x.asIdeal := by
  have hk := Ideal.ker_algebraMap_residueField x.asIdeal
  have h1 : ∀ a : R, a ∈ x.asIdeal ↔ algebraMap R x.asIdeal.ResidueField a = 0 :=
    fun a => by rw [← RingHom.mem_ker, hk]
  let e := ((Scheme.Spec.residueFieldIso R x).symm.commRingCatIsoToRingEquiv)
  ext a
  rw [h1 a, RingHom.mem_ker]
  change e (algebraMap R _ a) = 0 ↔ _
  exact map_eq_zero_iff e e.injective

/-- The map `R ⧸ 𝔭 ⟶ κ(𝔭)`. -/
private noncomputable def resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    CommRingCat.of (R ⧸ x.asIdeal) ⟶ (Spec R).residueField x :=
  CommRingCat.ofHom (Ideal.Quotient.lift _ (resMap R x).hom (fun a ha => by
    rw [← ker_resMap R x] at ha; exact ha))

private theorem mk_comp_resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal) ≫ resMapQuot R x = resMap R x := by
  ext a; rfl

private theorem spec_resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    Spec.map (resMapQuot R x) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal)) =
      (Spec R).fromSpecResidueField x := by
  rw [← Spec.map_comp, mk_comp_resMapQuot]
  exact map_resMap R x

private theorem flat_resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    RingHom.Flat (resMapQuot R x).hom := by
  have : (resMapQuot R x).hom =
      ((Scheme.Spec.residueFieldIso R x).symm.commRingCatIsoToRingEquiv :
        x.asIdeal.ResidueField →+* _).comp
        (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField) := by
    refine RingHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  rw [this]
  have h1 : RingHom.Flat (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField) := by
    have := IsLocalization.flat x.asIdeal.ResidueField (nonZeroDivisors (R ⧸ x.asIdeal))
    exact this
  exact RingHom.Flat.comp h1 (RingHom.Flat.of_bijective
    ((Scheme.Spec.residueFieldIso R x).symm.commRingCatIsoToRingEquiv).bijective)

/-- Tensoring over `R` or over a quotient ring `A` of `R` gives the same `K`-module, `A` acting
compatibly on `K` and `M`. -/
private theorem tensor_quot_equiv {R A K M : Type*} [CommRing R] [CommRing A] [CommRing K]
    [AddCommGroup M] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
    [Module R M] [Module A M] [IsScalarTower R A M] (h : Function.Surjective (algebraMap R A)) :
    Nonempty ((K ⊗[R] M) ≃ₗ[K] (K ⊗[A] M)) := by
  haveI : TensorProduct.CompatibleSMul R A K M := ⟨fun a k m => by
    obtain ⟨r, rfl⟩ := h a
    rw [algebraMap_smul, algebraMap_smul, TensorProduct.smul_tmul]⟩
  haveI : TensorProduct.CompatibleSMul A R K M := ⟨fun r k m => by
    rw [← algebraMap_smul A r k, ← algebraMap_smul A r m, TensorProduct.smul_tmul]⟩
  exact ⟨(TensorProduct.equivOfCompatibleSMul R A K K M).symm⟩

/-- The fibre rank of `M^~` at `x` is the dimension of `κ(x) ⊗_R M`. -/
private theorem fiberRank_tilde (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (x : PrimeSpectrum.Top R) :
    letI : Algebra ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
      ((Spec R).residue x).hom.toAlgebra
    letI : Algebra R ((Spec R).residueField x) :=
      ((algebraMap ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)).comp
        (algebraMap R ((structurePresheafInCommRingCat R).stalk x))).toAlgebra
    Scheme.Modules.fiberRank (tilde M) x =
      Module.finrank ((Spec R).residueField x) (((Spec R).residueField x) ⊗[R] M) := by
  letI : Algebra ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
      ((Spec R).residue x).hom.toAlgebra
  letI : Algebra R ((Spec R).residueField x) :=
      ((algebraMap ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)).comp
        (algebraMap R ((structurePresheafInCommRingCat R).stalk x))).toAlgebra
  haveI : IsScalarTower R ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Module ((structurePresheafInCommRingCat R).stalk x) ((tilde M).presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (Spec R).presheaf) (tilde M).val x
  haveI : IsScalarTower R ((structurePresheafInCommRingCat R).stalk x) ((tilde M).presheaf.stalk x)
      :=
    (inferInstance : IsScalarTower R ((structurePresheafInCommRingCat R).stalk x)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))
  have hbc : IsBaseChange ((structurePresheafInCommRingCat R).stalk x) (tilde.toStalk M x).hom :=
    IsLocalizedModule.isBaseChange x.asIdeal.primeCompl _ _
  unfold Scheme.Modules.fiberRank
  let e1 := hbc.equiv
  let e2 := (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ((Spec R).residueField x) _)
    e1.symm) ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange R
      ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)
      ((Spec R).residueField x) M)
  exact e2.finrank_eq

/-- The fibre rank at `x` of a quasi-coherent module `G` on `Spec R` is the dimension of
`κ(x) ⊗_R Γ(G, ⊤)`. -/
private theorem fiberRank_of_isQuasicoherent (R : CommRingCat.{u}) (G : (Spec R).Modules)
    [G.IsQuasicoherent] (x : PrimeSpectrum.Top R) :
    letI : Algebra ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
      ((Spec R).residue x).hom.toAlgebra
    letI : Algebra R ((Spec R).residueField x) :=
      ((algebraMap ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)).comp
        (algebraMap R ((structurePresheafInCommRingCat R).stalk x))).toAlgebra
    Scheme.Modules.fiberRank G x =
      Module.finrank ((Spec R).residueField x) (((Spec R).residueField x) ⊗[R]
        ((modulesSpecToSheaf.obj G).presheaf.obj (op ⊤))) := by
  have := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  rw [← fiberRank_congr (asIso G.fromTildeΓ) x]
  exact fiberRank_tilde R _ x

private theorem finrank_eq_of_ringEquiv_addEquiv {K L : Type*} {M N : Type v} [Semiring K]
    [Semiring L] [AddCommMonoid M] [AddCommMonoid N] [Module K M] [Module L N] (i : K ≃+* L)
    (j : M ≃+ N) (hc : ∀ (r : K) (m : M), j (r • m) = i r • j m) :
    Module.finrank K M = Module.finrank L N := by
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv i j i.bijective hc]

private theorem finrank_tensor_congr {R : Type*} {K L M : Type v} [CommRing R] [CommRing K]
    [CommRing L] [Algebra R K] [Algebra R L] (τ : K ≃ₐ[R] L) [AddCommGroup M] [Module R M] :
    Module.finrank K (K ⊗[R] M) = Module.finrank L (L ⊗[R] M) := by
  refine finrank_eq_of_ringEquiv_addEquiv τ.toRingEquiv
    (TensorProduct.congr τ.toLinearEquiv (LinearEquiv.refl R M)).toAddEquiv ?_
  intro k x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem appLE_top_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appLE]
  have : (homOfLE h).op = 𝟙 _ := rfl
  rw [this]; simp [Scheme.Hom.appTop]
  exact Category.comp_id _

private theorem baseModule_top_smul {Z W : Scheme.{u}} (h : Z ⟶ W) (M : Z.Modules)
    (b : Γ(W, ⊤)) (m : Γ(M, ⊤)) :
    letI := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule h M ⊤
    b • m = (h.appTop.hom b) • m := by
  show (h.appLE ⊤ ⊤ _).hom b • m = _
  rw [appLE_top_eq]

private theorem surjective_mk_appTop (R : CommRingCat.{u}) (x : Spec R) :
    Function.Surjective ((Scheme.ΓSpecIso R).inv ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal))).appTop).hom := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal))
  have hs : Function.Surjective (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ x.asIdeal))).inv).hom :=
    (((Scheme.ΓSpecIso (CommRingCat.of (R ⧸
        x.asIdeal))).symm.commRingCatIsoToRingEquiv).surjective).comp
      (Ideal.Quotient.mk_surjective)
  rw [h] at hs
  exact hs

private theorem algebraMap_chain {R S : CommRingCat.{u}} (I : Ideal R) (ψ : CommRingCat.of (R ⧸ I)
    ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop ≫
      (Spec.map ψ).appTop = (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ) ≫
        (Scheme.ΓSpecIso S).inv := by
  rw [← Scheme.Hom.comp_appTop, ← Spec.map_comp]
  exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ)).symm

/-- For any flat field extension `ψ : R ⧸ 𝔭 → K` and any cartesian square over `Spec ψ`, the
sections of `F` pulled back to the corner have `K`-dimension `K ⊗_R Γ(X, F)`. -/
private theorem finrank_fibre_sections {R : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [QuasiSeparatedSpace X] (g : X ⟶ Spec R) (F : X.Modules)
    [F.IsQuasicoherent] {K : Type u} [Field K]
    (ψ : CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal) ⟶ CommRingCat.of K)
    (hψ : RingHom.Flat ψ.hom) {Fib : Scheme.{u}} (p : Fib ⟶ X)
    (k : Fib ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p k (toSpecQuot g) (Spec.map ψ)) :
    letI : Algebra R K :=
      (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal) ≫ ψ).hom.toAlgebra
    letI : Module R Γ(F, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
    Module.finrank K (cohomologyOverField K k ((Scheme.Modules.pullback p).obj F) 0) =
    Module.finrank K (K ⊗[R] Γ(F, ⊤)) := by
  have hflat : Flat (Spec.map ψ) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hψ
  obtain ⟨e, he⟩ :=
      Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange
    H F
  have P1 : Module.finrank (CommRingCat.of K)
      (cohomologyOverField (CommRingCat.of K)
        k
        ((Scheme.Modules.pullback p).obj F) 0) =
      letI := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule
          k
          ((Scheme.Modules.pullback p).obj F) ⊤
      Module.finrank Γ(Spec (CommRingCat.of K), ⊤)
        Γ((Scheme.Modules.pullback p).obj F, ⊤) := by
    refine ((cohomologyOverFieldZeroIsoSections _ _ _).toLinearEquiv.finrank_eq).trans ?_
    letI := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule
          k
          ((Scheme.Modules.pullback p).obj F) ⊤
    refine finrank_eq_of_ringEquiv_addEquiv
      ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
      (AddEquiv.refl _) ?_
    intro r m
    simp only [AddEquiv.refl_apply]
    refine Eq.trans ?_ (baseModule_top_smul k _ _ m).symm
    rfl
  letI algκ : Algebra R (CommRingCat.of K) :=
    (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal) ≫ ψ).hom.toAlgebra
  letI algRB : Algebra R Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤) :=
    ((Scheme.ΓSpecIso R).inv ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint
          X)).asIdeal))).appTop).hom.toAlgebra
  letI algBL := Stacks.AlgebraicGeometry.SectionsBaseChange.baseAlgebra
    (Spec.map ψ)
  letI algRL : Algebra R Γ(Spec (CommRingCat.of K), ⊤) :=
    ((algebraMap _ Γ(Spec (CommRingCat.of K), ⊤)).comp
      (algebraMap R Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤))).toAlgebra
  haveI : IsScalarTower R Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤)
      Γ(Spec (CommRingCat.of K), ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI modBF := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule (toSpecQuot g) F ⊤
  letI modRF : Module R Γ(F, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom
  have key : (Scheme.ΓSpecIso R).inv ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (g (genericPoint X)).asIdeal))).appTop ≫
        (toSpecQuot g).appTop = (Scheme.ΓSpecIso R).inv ≫ g.appTop := by
    rw [← Scheme.Hom.comp_appTop, toSpecQuot_comp]
  haveI tower : IsScalarTower R Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤)
      Γ(F, ⊤) := ⟨fun r b m => by
    have h1 := baseModule_top_smul (toSpecQuot g) F (r • b) m
    have h2 := baseModule_top_smul (toSpecQuot g) F b m
    have hr : (toSpecQuot g).appTop.hom (algebraMap R _ r) =
        ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom r := by
      rw [← key]; rfl
    rw [h1, h2, Algebra.smul_def, map_mul, mul_smul, hr]
    rfl⟩
  obtain ⟨eq⟩ := tensor_quot_equiv (R := R)
    (A := Γ(Spec (CommRingCat.of (R ⧸ (g (genericPoint X)).asIdeal)), ⊤))
    (K := Γ(Spec (CommRingCat.of K), ⊤)) (M := Γ(F, ⊤))
    (surjective_mk_appTop R (g (genericPoint X)))
  have hcomm : ∀ r : R,
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
        (algebraMap R (CommRingCat.of K) r) =
      algebraMap R Γ(Spec (CommRingCat.of K), ⊤) r := by
    intro r
    have h := congrArg (fun φ => φ.hom r) (algebraMap_chain (g (genericPoint X)).asIdeal ψ)
    show _ = ((Spec.map ψ).appLE ⊤ ⊤ _).hom _
    rw [appLE_top_eq]
    exact h.symm
  let τ : (CommRingCat.of K) ≃ₐ[R]
      Γ(Spec (CommRingCat.of K), ⊤) :=
    AlgEquiv.ofRingEquiv hcomm
  letI modLG := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule
    k
    ((Scheme.Modules.pullback p).obj F) ⊤
  exact P1.trans (e.finrank_eq.symm.trans (eq.finrank_eq.symm.trans
    (finrank_tensor_congr τ).symm))

private theorem finrank_tensor_inst_congr {R K N : Type*} [CommRing R] [CommRing K]
    [AddCommGroup N] (alg1 alg2 : Algebra R K) (m1 m2 : Module R N) (hA : alg1 = alg2)
    (hM : m1 = m2) :
    (letI := alg1; letI := m1; Module.finrank K (K ⊗[R] N)) =
      (letI := alg2; letI := m2; Module.finrank K (K ⊗[R] N)) := by
  subst hA hM
  rfl

private theorem alg_eq (R : CommRingCat.{u}) (x : PrimeSpectrum.Top R) :
    letI : Algebra ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x) :=
      ((Spec R).residue x).hom.toAlgebra
    ((algebraMap ((structurePresheafInCommRingCat R).stalk x) ((Spec R).residueField x)).comp
        (algebraMap R ((structurePresheafInCommRingCat R).stalk x))) = (resMap R x).hom := by
  ext r
  have := congrArg (fun φ => φ.hom r) (Scheme.Spec.algebraMap_residueFieldIso_inv R x)
  exact this.symm

private theorem isPullback_of_factor {C : Type*} [Category C] {P X' T S R' : C} (ι : S ⟶ R')
    [Mono ι] (g' : X' ⟶ S) (p : P ⟶ X') (k : P ⟶ T) (q : T ⟶ S)
    (H : IsPullback p k (g' ≫ ι) (q ≫ ι)) : IsPullback p k g' q := by
  have hmono : IsPullback (𝟙 X') g' (g' ≫ ι) ι := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  refine IsPullback.of_right (h₁₂ := 𝟙 X') (v₁₂ := g') (v₁₃ := g' ≫ ι) (h₂₂ := ι) ?_ ?_ hmono
  · simpa using H
  · refine (cancel_mono ι).1 ?_
    simpa using H.w

/-- The map `Spec κ(j z) ⟶ Spec R` through the open immersion `j : Spec R ⟶ Y`. -/
private noncomputable def resGamma {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) : Spec (Y.residueField (j z)) ⟶ Spec R :=
  Spec.map (inv (j.residueFieldMap z)) ≫ (Spec R).fromSpecResidueField z

private theorem resGamma_comp {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) : resGamma j z ≫ j = Y.fromSpecResidueField (j z) := by
  rw [resGamma, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc]
  simp

/-- The generic fibre of `f` over `j z` is the fibre over `z` of the base change of `f` along the
open immersion `j`. -/
private theorem isPullback_fiber_open {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (z : Spec R) :
    IsPullback (pullback.lift (f.fiberι (j z)) (f.fiberToSpecResidueField (j z) ≫ resGamma j z)
        (by rw [Category.assoc, resGamma_comp]; exact Scheme.Hom.fiber_fac f (j z)))
      (f.fiberToSpecResidueField (j z)) (pullback.snd f j) (resGamma j z) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f j) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f j)
  rw [pullback.lift_fst, resGamma_comp]
  exact IsPullback.of_hasPullback f _

/-- The ring map `R ⧸ 𝔭 ⟶ κ(j z)`. -/
private noncomputable def psiK {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) :
    CommRingCat.of (R ⧸ z.asIdeal) ⟶ Y.residueField (j z) :=
  resMapQuot R z ≫ inv (j.residueFieldMap z)

private theorem spec_psiK {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) :
    Spec.map (psiK j z) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal)) =
      resGamma j z := by
  rw [psiK, Spec.map_comp, Category.assoc, spec_resMapQuot]
  rfl

private theorem flat_psiK {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) : RingHom.Flat (psiK j z).hom := by
  rw [psiK]
  exact RingHom.Flat.comp (flat_resMapQuot R z)
    (RingHom.Flat.of_bijective (asIso (inv (j.residueFieldMap
        z))).commRingCatIsoToRingEquiv.bijective)

/-- `cohomologyOverField` only depends on the module up to isomorphism. -/
private theorem finrank_cohomologyOverField_congr {K : Type u} [Field K] {Z : Scheme.{u}}
    (k : Z ⟶ Spec (CommRingCat.of K)) {M N : Z.Modules} (e : M ≅ N) (n : ℕ) :
    Module.finrank K (cohomologyOverField K k M n) =
      Module.finrank K (cohomologyOverField K k N n) := by
  unfold cohomologyOverField
  exact (((ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ k.appLE ⊤ ⊤ (by simp)).hom).mapIso
    (((SheafOfModules.evaluation Z.ringCatSheaf (op (⊤ : Z.Opens))).rightDerived n).mapIso e))
    ).toLinearEquiv.finrank_eq

/-- The base change of `f` along `j`, as a scheme. -/
private noncomputable abbrev bcScheme {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Z ⟶ Y) : Scheme.{u} :=
    pullback f j

/-- The generic fibre of `f` over `j z`, `z` the image of the generic point of `X ×_Y Spec R`, is
the base change of the factorisation of `X ×_Y Spec R ⟶ Spec R` through `Spec (R ⧸ 𝔭)` along the
flat map `Spec κ(j z) ⟶ Spec (R ⧸ 𝔭)`. -/
private theorem isPullback_fiber_toSpecQuot {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] [IsIntegral (bcScheme f j)] :
    IsPullback
      (pullback.lift (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))
        (f.fiberToSpecResidueField (j ((pullback.snd f j) (genericPoint (bcScheme f j)))) ≫
          resGamma j ((pullback.snd f j) (genericPoint (bcScheme f j))))
        (by rw [Category.assoc, resGamma_comp]; exact Scheme.Hom.fiber_fac f _))
      (f.fiberToSpecResidueField (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))
      (toSpecQuot (pullback.snd f j))
      (Spec.map (psiK j ((pullback.snd f j) (genericPoint (bcScheme f j))))) := by
  refine isPullback_of_factor (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    ((pullback.snd f j) (genericPoint (bcScheme f j))).asIdeal))) _ _ _ _ ?_
  rw [toSpecQuot_comp, spec_psiK]
  exact isPullback_fiber_open f j _

/-- The dimension of the sections on the generic fibre of `f` over `j z`, computed on the base
change `X' = X ×_Y Spec R` along an affine open immersion `j`. -/
private theorem finrank_fibre_via_open {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] [IsIntegral (bcScheme f j)]
    [CompactSpace (bcScheme f j)] [QuasiSeparatedSpace (bcScheme f j)]
    (F : X.Modules) [F.IsQuasicoherent] :
    letI z := (pullback.snd f j) (genericPoint (bcScheme f j))
    letI : Algebra R (Y.residueField (j z)) :=
      (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal) ≫ psiK j z).hom.toAlgebra
    letI : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
    Module.finrank (Y.residueField (j z))
      (cohomologyOverField (Y.residueField (j z)) (f.fiberToSpecResidueField (j z))
        ((Scheme.Modules.pullback (f.fiberι (j z))).obj F) 0) =
    Module.finrank (Y.residueField (j z))
      (Y.residueField (j z) ⊗[R] Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤))
          := by
  haveI : ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F).IsQuasicoherent :=
    inferInstance
  have H := isPullback_fiber_toSpecQuot f j
  have h := finrank_fibre_sections (pullback.snd f j)
    ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F) (psiK j _) (flat_psiK j _) _ _ H
  have hobj : (Scheme.Modules.pullback (pullback.lift
      (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))
      (f.fiberToSpecResidueField (j ((pullback.snd f j) (genericPoint (bcScheme f j)))) ≫
        resGamma j ((pullback.snd f j) (genericPoint (bcScheme f j))))
      (by rw [Category.assoc, resGamma_comp]; exact Scheme.Hom.fiber_fac f _) ≫
        pullback.fst f j)).obj F =
      (Scheme.Modules.pullback
        (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))).obj F := by
    rw [pullback.lift_fst]
  let e : (Scheme.Modules.pullback (pullback.lift
      (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))
      (f.fiberToSpecResidueField (j ((pullback.snd f j) (genericPoint (bcScheme f j)))) ≫
        resGamma j ((pullback.snd f j) (genericPoint (bcScheme f j))))
      (by rw [Category.assoc, resGamma_comp]; exact Scheme.Hom.fiber_fac f _))).obj
      ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F) ≅
      (Scheme.Modules.pullback
        (f.fiberι (j ((pullback.snd f j) (genericPoint (bcScheme f j)))))).obj F :=
    ((Scheme.Modules.pullback _).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (pullback.fst f j)).app F)) ≪≫
      ((Scheme.Modules.pullbackComp _ _).app F) ≪≫ eqToIso hobj
  exact (finrank_cohomologyOverField_congr _ e.symm 0).trans h

/-- `finrank` of a base change `K' ⊗_{S'} N` is invariant under compatible ring isomorphisms and a
semilinear additive isomorphism of the modules. -/
private theorem finrank_tensor_semilinear {S' S K' K N N' : Type v} [CommRing S'] [CommRing S]
    [CommRing K'] [CommRing K] [Algebra S' K'] [Algebra S K] [AddCommGroup N] [Module S' N]
    [AddCommGroup N'] [Module S N'] (σ : S' ≃+* S) (ρ : K' ≃+* K)
    (hσρ : ∀ s, ρ (algebraMap S' K' s) = algebraMap S K (σ s)) (ν : N ≃+ N')
    (hν : ∀ (s : S') (n : N), ν (s • n) = σ s • ν n) :
    Module.finrank K' (K' ⊗[S'] N) = Module.finrank K (K ⊗[S] N') := by
  have hρ : ∀ (s : S') (k : K'), ρ (s • k) = σ s • ρ k := fun s k => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hσρ]
  have hρ' : ∀ (s : S) (k : K), ρ.symm (s • k) = σ.symm s • ρ.symm k := fun s k => by
    have := hρ (σ.symm s) (ρ.symm k)
    simp at this
    apply ρ.injective
    simpa using this.symm
  have hν' : ∀ (s : S) (n : N'), ν.symm (s • n) = σ.symm s • ν.symm n := fun s n => by
    apply ν.injective
    have := hν (σ.symm s) (ν.symm n)
    simpa using this.symm
  let Φ : K' ⊗[S'] N →+ K ⊗[S] N' :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun k' => ((TensorProduct.mk S K N') (ρ k')).toAddMonoidHom.comp
          ν.toAddMonoidHom)
        (fun a b => by ext n; simp [TensorProduct.add_tmul]))
      (fun s k n => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply]
        simp [hρ, hν, TensorProduct.smul_tmul])
  let Ψ : K ⊗[S] N' →+ K' ⊗[S'] N :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun k => ((TensorProduct.mk S' K' N) (ρ.symm k)).toAddMonoidHom.comp
          ν.symm.toAddMonoidHom)
        (fun a b => by ext n; simp [TensorProduct.add_tmul]))
      (fun s k n => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply]
        simp [hρ', hν', TensorProduct.smul_tmul])
  have hΦ : ∀ a n, Φ (a ⊗ₜ n) = ρ a ⊗ₜ ν n := fun a n => rfl
  have hΨ : ∀ a n, Ψ (a ⊗ₜ n) = ρ.symm a ⊗ₜ ν.symm n := fun a n => rfl
  let e : K' ⊗[S'] N ≃+ K ⊗[S] N' :=
    { toFun := Φ
      invFun := Ψ
      map_add' := Φ.map_add
      left_inv := fun x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a n => simp [hΦ, hΨ]
        | add x y hx hy => simp only [map_add, hx, hy]
      right_inv := fun x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a n => simp [hΦ, hΨ]
        | add x y hx hy => simp only [map_add, hx, hy] }
  refine finrank_eq_of_ringEquiv_addEquiv ρ e ?_
  intro k x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => simp [e, hΦ, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

section RestrictStalk

variable {X : Scheme.{u}} {X' : Scheme.{u}} (h : X' ⟶ X) [IsOpenImmersion h] (M : X.Modules) (x' :
    X')

/-- The comparison of the stalk of a module at `h x'` with the stalk at `x'` of its restriction
along the open immersion `h`, at the spelling at which both stalks carry their module
structures. -/
private noncomputable def restrictStalkInv :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (h.base x') ⟶
      TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.restrictFunctor h).obj M).val.presheaf x' :=
  (Scheme.Modules.restrictStalkNatIso h x').inv.app M

private lemma isIso_restrictStalkInv : IsIso (restrictStalkInv h M x') :=
  inferInstanceAs (IsIso ((Scheme.Modules.restrictStalkNatIso h x').inv.app M))

/-- The action of a section of `𝒪_{X'}` on a section of the restriction of `M` is the action of
its image under `h.appIso` on the corresponding section of `M`. -/
private lemma restrict_smul {U : X'.Opens} (r : Γ(X', U)) (m : Γ(M, h ''ᵁ U)) :
    HSMul.hSMul (α := Γ(X', U))
        (β := Γ((Scheme.Modules.restrictFunctor h).obj M, U)) r m =
      (h.appIso U).inv r • m :=
  rfl

/-- `restrictStalkInv` sends the germ of a section over `h ''ᵁ U` to its germ over `U`. -/
private lemma restrictStalkInv_germ {U : X'.Opens} (hxU : x' ∈ U)
    (hmem : h.base x' ∈ (h ''ᵁ U : X.Opens)) (ξ : Γ(M, h ''ᵁ U)) :
    restrictStalkInv h M x'
        (TopCat.Presheaf.germ M.val.presheaf (h ''ᵁ U) (h.base x') hmem ξ) =
      TopCat.Presheaf.germ
        ((Scheme.Modules.restrictFunctor h).obj M).val.presheaf U x' hxU ξ :=
  ConcreteCategory.congr_hom
    (Scheme.Modules.germ_restrictStalkNatIso_inv_app h x' M hxU) ξ

/-- The stalk map of an open immersion, on the germ of a section transported by `h.appIso`. -/
private lemma stalkMap_germ_appIso {U : X'.Opens} (hxU : x' ∈ U)
    (hmem : h.base x' ∈ (h ''ᵁ U : X.Opens)) (r : Γ(X, h ''ᵁ U)) :
    h.stalkMap x' (X.presheaf.germ (h ''ᵁ U) (h.base x') hmem r) =
      X'.presheaf.germ U x' hxU ((h.appIso U).hom r) := by
  rw [Scheme.Hom.germ_stalkMap_apply h (h ''ᵁ U) x' hmem r, Scheme.Hom.appIso_hom' h U,
    Scheme.Hom.appLE, CommRingCat.comp_apply,
    X'.presheaf.germ_res_apply (homOfLE (Scheme.Hom.preimage_image_eq h U).ge) x' hxU]

/-- **The stalk comparison for a restriction is semilinear** over the stalk map of the open
immersion. -/
private lemma restrictStalkInv_smul (rho : X.presheaf.stalk (h.base x'))
    (n : TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (h.base x')) :
    restrictStalkInv h M x' (rho • n) =
      h.stalkMap x' rho • restrictStalkInv h M x' n := by
  obtain ⟨V, hV, xi, hxi⟩ := X.presheaf.exists_germ_eq rho
  obtain ⟨W, hWV, hW, zeta, hzeta⟩ := TopCat.Presheaf.exists_le_germ_eq M.val.presheaf n hV
  subst hxi
  subst hzeta
  set U : X'.Opens := h ⁻¹ᵁ W with hU
  have hxU : x' ∈ U := hW
  have himg : (h ''ᵁ U : X.Opens) ≤ W := h.image_preimage_le W
  have hmem : h.base x' ∈ (h ''ᵁ U : X.Opens) := ⟨x', hxU, rfl⟩
  have key : ∀ (r : Γ(X, h ''ᵁ U)) (m : Γ(M, h ''ᵁ U)),
      restrictStalkInv h M x'
          (X.presheaf.germ (h ''ᵁ U) (h.base x') hmem r •
            TopCat.Presheaf.germ M.val.presheaf (h ''ᵁ U) (h.base x') hmem m) =
        h.stalkMap x' (X.presheaf.germ (h ''ᵁ U) (h.base x') hmem r) •
          restrictStalkInv h M x'
            (TopCat.Presheaf.germ M.val.presheaf (h ''ᵁ U) (h.base x') hmem m) := by
    intro r m
    rw [← germM_smul' M (h.base x') (h ''ᵁ U) hmem r m,
      restrictStalkInv_germ h M x' hxU hmem, restrictStalkInv_germ h M x' hxU hmem,
      stalkMap_germ_appIso h x' hxU hmem r,
      ← germM_smul' ((Scheme.Modules.restrictFunctor h).obj M) x' U hxU
        ((h.appIso U).hom r) m]
    congr 1
    rw [restrict_smul h M ((h.appIso U).hom r) m]
    exact congrArg (fun z => z • m) ((h.appIso U).hom_inv_id_apply r).symm
  rw [← X.presheaf.germ_res_apply (homOfLE (himg.trans hWV)) (h.base x') hmem xi,
    ← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE himg) (h.base x') hmem zeta]
  exact key _ _

end RestrictStalk

private noncomputable def openStalkRingEquiv {Z Y : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (z : Z) : Y.presheaf.stalk (j z) ≃+* Z.presheaf.stalk z :=
  haveI : IsIso (j.stalkMap z) := IsOpenImmersion.instIsIsoCommRingCatStalkMap j z
  (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv

private noncomputable def openResidueRingEquiv {Z Y : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (z : Z) : Y.residueField (j z) ≃+* Z.residueField z :=
  haveI : IsIso (j.residueFieldMap z) :=
      Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion j z
  (asIso (j.residueFieldMap z)).commRingCatIsoToRingEquiv

private noncomputable def openStalkAddEquiv {Z Y : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (G : Y.Modules) (z : Z) :
    TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (j z) ≃+
      TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.restrictFunctor j).obj G).val.presheaf z :=
  haveI := isIso_restrictStalkInv j G z
  (asIso (restrictStalkInv j G z)).addCommGroupIsoToAddEquiv

/-- The fibre rank is unchanged by restriction to an open subscheme. -/
private theorem fiberRank_restrict {Z Y : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j]
    (G : Y.Modules) (z : Z) :
    Scheme.Modules.fiberRank ((Scheme.Modules.restrictFunctor j).obj G) z =
      Scheme.Modules.fiberRank G (j z) := by
  unfold Scheme.Modules.fiberRank
  have hσρ : ∀ s, openResidueRingEquiv j z
      (algebraMap (Y.presheaf.stalk (j z)) (Y.residueField (j z)) s) =
      algebraMap (Z.presheaf.stalk z) (Z.residueField z) (openStalkRingEquiv j z s) := fun s =>
    congrArg (fun φ => CommRingCat.Hom.hom φ s) (Scheme.residue_residueFieldMap j z)
  have hν : ∀ (s : Y.presheaf.stalk (j z))
      (n : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (j z)),
      openStalkAddEquiv j G z (s • n) = openStalkRingEquiv j z s • openStalkAddEquiv j G z n :=
    fun s n => restrictStalkInv_smul j G z s n
  exact (finrank_tensor_semilinear (openStalkRingEquiv j z) (openResidueRingEquiv j z) hσρ
    (openStalkAddEquiv j G z) hν).symm

private theorem image_fst_top {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] :
    (pullback.fst f j) ''ᵁ ⊤ = f ⁻¹ᵁ (j ''ᵁ ⊤) := by
  ext x
  simp only [Scheme.Hom.coe_image, Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_top,
    Set.image_univ, Set.mem_preimage]
  rw [Scheme.Pullback.range_fst]
  rfl

private theorem appLE_congr_hom {A B : Scheme.{u}} {u v : A ⟶ B} (h : u = v) (U : B.Opens)
    (V : A.Opens) (e : V ≤ u ⁻¹ᵁ U) (e' : V ≤ v ⁻¹ᵁ U) : u.appLE U V e = v.appLE U V e' := by
  subst h; rfl

/-- The ring-level compatibility of the pullback square along an open immersion. -/
private theorem scalar_compat {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ (j ''ᵁ ⊤))
    (hW' : (⊤ : (pullback f j).Opens) ≤ (pullback.fst f j) ⁻¹ᵁ W) :
    (j.appIso ⊤).inv ≫ f.appLE (j ''ᵁ ⊤) W hW ≫ (pullback.fst f j).appLE W ⊤ hW' =
      (pullback.snd f j).appTop := by
  rw [Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom (pullback.condition (f := f) (g := j)) _ _ _
      (e' := fun x hx => by simp), Scheme.Hom.comp_appLE, Scheme.Hom.appIso_inv_app_assoc]
  rw [Scheme.Hom.map_appLE' _ _ (Scheme.Hom.preimage_image_eq j ⊤)]
  all_goals first | exact appLE_top_eq _ _ | exact le_top | simp

/-- The `R`-linear identification of the sections of the restriction of `f_* F` to `Spec R` with
the sections of the restriction of `F` to the base change `X ×_Y Spec R`. -/
private noncomputable def sectionsEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (F : X.Modules) :
    letI : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
    ((modulesSpecToSheaf.obj ((Scheme.Modules.restrictFunctor j).obj
      ((Scheme.Modules.pushforward f).obj F))).presheaf.obj (op ⊤)) ≃ₗ[R]
      Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
  letI : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
  { toFun := fun x => (F.presheaf.map (homOfLE (image_fst_top f j).le).op).hom x
    map_add' := fun x y => map_add _ _ _
    map_smul' := fun r x => by
      have h1 : r • x = (f.app (j ''ᵁ ⊤) ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))) •
          (show F.presheaf.obj (op (f ⁻¹ᵁ (j ''ᵁ ⊤))) from x) := rfl
      have h2 : ∀ y : F.presheaf.obj (op ((pullback.fst f j) ''ᵁ ⊤)),
          (RingHom.id R) r • (show Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤)
            from y) =
          (((pullback.fst f j).appIso ⊤).inv ((pullback.snd f j).appTop
            ((Scheme.ΓSpecIso R).inv r))) • y := fun y => rfl
      have h3 := Scheme.Modules.map_smul F (homOfLE (image_fst_top f j).le)
        (f.app (j ''ᵁ ⊤) ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))) x
      have hsc : X.presheaf.map (homOfLE (image_fst_top f j).le).op
          (f.app (j ''ᵁ ⊤) ((j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r))) =
          ((pullback.fst f j).appIso ⊤).inv ((pullback.snd f j).appTop
            ((Scheme.ΓSpecIso R).inv r)) := by
        have h := congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso R).inv r))
          (scalar_compat f j ((pullback.fst f j) ''ᵁ ⊤) (image_fst_top f j).le
            (Scheme.Hom.preimage_image_eq _ _).ge)
        apply ((pullback.fst f j).appIso ⊤).commRingCatIsoToRingEquiv.injective
        show ((pullback.fst f j).appIso ⊤).hom _ =
          ((pullback.fst f j).appIso ⊤).hom (((pullback.fst f j).appIso ⊤).inv _)
        rw [Iso.inv_hom_id_apply, Scheme.Hom.appIso_hom']
        exact h
      show (F.presheaf.map (homOfLE (image_fst_top f j).le).op).hom (r • x) = _
      rw [h1, h3, h2, hsc]
    invFun := fun y => (F.presheaf.map (homOfLE (image_fst_top f j).ge).op).hom y
    left_inv := fun x =>
      ConcreteCategory.congr_hom (show F.presheaf.map (homOfLE (image_fst_top f j).le).op ≫
        F.presheaf.map (homOfLE (image_fst_top f j).ge).op = 𝟙 _ by
          rw [← F.presheaf.map_comp,
            show (homOfLE (image_fst_top f j).le).op ≫ (homOfLE (image_fst_top f j).ge).op = 𝟙 _
              from Subsingleton.elim _ _, F.presheaf.map_id]) x
    right_inv := fun y =>
      ConcreteCategory.congr_hom (show F.presheaf.map (homOfLE (image_fst_top f j).ge).op ≫
        F.presheaf.map (homOfLE (image_fst_top f j).le).op = 𝟙 _ by
          rw [← F.presheaf.map_comp,
            show (homOfLE (image_fst_top f j).ge).op ≫ (homOfLE (image_fst_top f j).le).op = 𝟙 _
              from Subsingleton.elim _ _, F.presheaf.map_id]) y }

/-- Remaining comparison for step (1): over the base change `X' = X ×_Y Spec R` along an affine
open immersion `j`, the sections `Γ(X', F|_{X'})` have the same `κ`-dimension after `κ ⊗_R -` as
the fibre rank of `f_* F` at `j z`. This is the identification of `j^* f_* F` with `g_* (p^* F)`
(open base change of the pushforward). -/
private theorem fiberRank_pushforward_via_open {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] [IsIntegral (bcScheme f j)] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    letI z := (pullback.snd f j) (genericPoint (bcScheme f j))
    letI : Algebra R (Y.residueField (j z)) :=
      (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal) ≫ psiK j z).hom.toAlgebra
    letI : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
    Scheme.Modules.fiberRank ((Scheme.Modules.pushforward f).obj F) (j z) =
      Module.finrank (Y.residueField (j z))
        (Y.residueField (j z) ⊗[R] Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤))
            := by
  haveI : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward f F inferInstance
  rw [← fiberRank_restrict j ((Scheme.Modules.pushforward f).obj F)
    ((pullback.snd f j) (genericPoint (bcScheme f j)))]
  rw [fiberRank_of_isQuasicoherent R ((Scheme.Modules.restrictFunctor j).obj
    ((Scheme.Modules.pushforward f).obj F)) ((pullback.snd f j) (genericPoint (bcScheme f j)))]
  generalize hz : (pullback.snd f j) (genericPoint (bcScheme f j)) = z
  letI algR : Algebra R ((Spec R).residueField z) := (resMap R z).hom.toAlgebra
  letI alg2 : Algebra R (Y.residueField (j z)) :=
    (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal) ≫ psiK j z).hom.toAlgebra
  letI modM2 : Module R Γ((Scheme.Modules.restrictFunctor (pullback.fst f j)).obj F, ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (pullback.snd f j).appTop).hom
  have hcomm : ∀ r : R, (openResidueRingEquiv j z).symm (algebraMap R ((Spec R).residueField z) r) =
      algebraMap R (Y.residueField (j z)) r := fun r => by
    haveI : IsIso (j.residueFieldMap z) :=
        Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion j z
    show (inv (j.residueFieldMap z)).hom ((resMap R z).hom r) =
      (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal) ≫ psiK j z).hom r
    rw [psiK, ← Category.assoc, mk_comp_resMapQuot]
    rfl
  let τ : ((Spec R).residueField z) ≃ₐ[R] (Y.residueField (j z)) :=
    AlgEquiv.ofRingEquiv hcomm
  refine (finrank_tensor_inst_congr (N := ((modulesSpecToSheaf.obj
      ((Scheme.Modules.restrictFunctor j).obj ((Scheme.Modules.pushforward f).obj F))).presheaf.obj
        (op ⊤))) _ algR inferInstance inferInstance ?_ rfl).trans ?_
  · exact Algebra.algebra_ext _ _ fun r => congrArg (fun φ => φ r) (alg_eq R z)
  · exact ((TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl ((Spec R).residueField z) _) (sectionsEquiv f j F)).finrank_eq).trans
      (finrank_tensor_congr τ)

private theorem genericPoint_open {X' X : Scheme.{u}} (p : X' ⟶ X) [IsOpenImmersion p]
    [IrreducibleSpace X] [IrreducibleSpace X'] : p (genericPoint X') = genericPoint X := by
  haveI : Nonempty X' := ⟨genericPoint X'⟩
  have hrange : genericPoint X ∈ Set.range p :=
    ((genericPoint_spec X).mem_open_set_iff p.isOpenEmbedding.isOpen_range).mpr
      (by simpa using Set.range_nonempty p)
  obtain ⟨x', hx'⟩ := hrange
  have h : IsGenericPoint x' Set.univ := by
    rw [isGenericPoint_def, p.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hx', (genericPoint_spec X).def]
    simp
  rw [(genericPoint_spec X').eq h]
  exact hx'

/-- An affine chart `j : Spec R ⟶ Y` around the image of the generic point of an integral `X`,
over which the base change `X ×_Y Spec R` is integral with generic point over `f (genericPoint X)`.
-/
private theorem exists_affine_chart_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ Y) (_ : IsOpenImmersion j)
      (_ : IsIntegral (bcScheme f j)),
      f (genericPoint X) = j ((pullback.snd f j) (genericPoint (bcScheme f j))) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := f (genericPoint X)) (U := ⊤) trivial
  haveI : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  obtain ⟨x', -⟩ : genericPoint X ∈ Set.range (pullback.fst f hV.fromSpec) := by
    rw [Scheme.Pullback.range_fst, hV.range_fromSpec]; exact hxV
  haveI : Nonempty (bcScheme f hV.fromSpec) := ⟨x'⟩
  haveI : IsIntegral (bcScheme f hV.fromSpec) :=
    isIntegral_of_isOpenImmersion (pullback.fst f hV.fromSpec)
  refine ⟨_, hV.fromSpec, inferInstance, inferInstance, ?_⟩
  rw [← genericPoint_open (pullback.fst f hV.fromSpec), ← Scheme.Hom.comp_apply,
    pullback.condition, Scheme.Hom.comp_apply]

/-- **Generic rank as sections on the generic fibre.** For an integral `X` and a quasi-compact
quasi-separated `f`, the generic rank of `f_* F`, `F` quasi-coherent, is the `κ(η)`-dimension of
the global sections of the restriction of `F` to the generic fibre `X_η`. -/
private theorem relativeGenericRank_eq_finrank_fibre {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    relativeGenericRank f F = Module.finrank (Y.residueField (f (genericPoint X)))
      (cohomologyOverField (Y.residueField (f (genericPoint X)))
        (f.fiberToSpecResidueField (f (genericPoint X)))
        ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj F) 0) := by
  obtain ⟨R, j, _, _, hy⟩ := exists_affine_chart_genericPoint f
  haveI : CompactSpace (bcScheme f j) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f j)
  haveI : QuasiSeparatedSpace (bcScheme f j) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f j)
  have key : ∀ y : Y, y = j ((pullback.snd f j) (genericPoint (bcScheme f j))) →
      Scheme.Modules.fiberRank ((Scheme.Modules.pushforward f).obj F) y =
        Module.finrank (Y.residueField y)
          (cohomologyOverField (Y.residueField y) (f.fiberToSpecResidueField y)
            ((Scheme.Modules.pullback (f.fiberι y)).obj F) 0) := by
    rintro y rfl
    exact (fiberRank_pushforward_via_open f j F).trans (finrank_fibre_via_open f j F).symm
  exact key _ hy

/-- Projective varieties over `k` with `f ≫ sY = sX`: `X` is integral and `f` is quasi-compact and
quasi-separated. -/
private theorem projective_facts {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    IsIntegral X ∧ QuasiCompact f ∧ QuasiSeparated f := by
  have : IsIntegral X := (inferInstance : AlgebraicGeometry.IsVariety k sX).toIsIntegral
  have : QuasiCompact (f ≫ sY) := hf ▸ (inferInstance : QuasiCompact sX)
  have : QuasiSeparated (f ≫ sY) := hf ▸ (inferInstance : QuasiSeparated sX)
  exact ⟨inferInstance, QuasiCompact.of_comp f sY, QuasiSeparated.of_comp f sY⟩

/-- `f` is proper and `X` is locally Noetherian in the projective setting. -/
private theorem projective_facts' {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [MMP.Mori.IsProjectiveVariety k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    IsProper f ∧ IsLocallyNoetherian X ∧ IsLocallyNoetherian Y := by
  haveI : IsProper (f ≫ sY) := hf ▸ (inferInstance : IsProper sX)
  exact ⟨IsProper.of_comp f sY, LocallyOfFiniteType.isLocallyNoetherian sX,
    LocallyOfFiniteType.isLocallyNoetherian sY⟩

private theorem stalkMap_bijective_of_flat_preimmersion {Z W : Scheme.{u}} (L : Z ⟶ W) [Flat L]
    [IsPreimmersion L] (z : Z) : Function.Bijective (L.stalkMap z) := by
  refine ⟨?_, L.stalkMap_surjective z⟩
  algebraize [(L.stalkMap z).hom]
  have : Module.FaithfullyFlat (W.presheaf.stalk (L z)) (Z.presheaf.stalk z) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap L z) (L.toLRSHom.prop z)
  exact ‹RingHom.FaithfullyFlat _›.injective

private theorem isReduced_of_flat_preimmersion {Z W : Scheme.{u}} (L : Z ⟶ W) [Flat L]
    [IsPreimmersion L] [IsReduced W] : IsReduced Z := by
  have : ∀ z : Z, _root_.IsReduced (Z.presheaf.stalk z) := fun z => by
    let e := RingEquiv.ofBijective (L.stalkMap z).hom (stalkMap_bijective_of_flat_preimmersion L z)
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  exact isReduced_of_isReduced_stalk Z

private theorem isReduced_of_isPullback_flat_preimmersion {P X' T S : Scheme.{u}} (p : P ⟶ X')
    (k : P ⟶ T) (g : X' ⟶ S) (q : T ⟶ S) (H : IsPullback p k g q) [Flat q] [IsPreimmersion q]
    [IsReduced X'] : IsReduced P := by
  haveI : Flat p := MorphismProperty.of_isPullback H.flip ‹_›
  haveI : IsPreimmersion p := MorphismProperty.of_isPullback H.flip ‹_›
  exact isReduced_of_flat_preimmersion p

private theorem isPreimmersion_spec_resMapQuot (R : CommRingCat.{u}) (x : Spec R) :
    IsPreimmersion (Spec.map (resMapQuot R x)) := by
  have h : resMapQuot R x = CommRingCat.ofHom (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R x).inv := by
    ext a
    rfl
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (R ⧸ x.asIdeal))
  rw [h, Spec.map_comp]
  infer_instance

private theorem isPreimmersion_spec_psiK {Y : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ Y)
    [IsOpenImmersion j] (z : Spec R) : IsPreimmersion (Spec.map (psiK j z)) := by
  have := isPreimmersion_spec_resMapQuot R z
  rw [psiK, Spec.map_comp]
  infer_instance

private theorem irreducibleSpace_fiber_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] : IrreducibleSpace (f.fiber (f (genericPoint X))) := by
  have hirr : IsIrreducible (f ⁻¹' {f (genericPoint X)} : Set X) := by
    rw [← isIrreducible_iff_closure]
    have : closure (f ⁻¹' {f (genericPoint X)} : Set X) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (genericPoint_spec X).def]
      exact closure_mono (by simp)
    rw [this]
    exact IrreducibleSpace.isIrreducible_univ X
  refine (irreducibleSpace_def _).2 ?_
  haveI : IrreducibleSpace ↥(f ⁻¹' {f (genericPoint X)} : Set X) := Subtype.irreducibleSpace hirr
  let φ := f.fiberHomeo (f (genericPoint X))
  have h := (IrreducibleSpace.isIrreducible_univ
    ↥(f ⁻¹' {f (genericPoint X)} : Set X)).image φ.symm φ.symm.continuous.continuousOn
  rwa [Set.image_univ, φ.symm.surjective.range_eq] at h

/-- The generic fibre of an integral scheme under a morphism with integral source is integral. -/
private theorem isIntegral_generic_fibre {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]
    [QuasiCompact f] :
    IsIntegral (f.fiber (f (genericPoint X))) := by
  haveI := irreducibleSpace_fiber_genericPoint f
  obtain ⟨R, j, _, _, hy⟩ := exists_affine_chart_genericPoint f
  have key : ∀ y : Y, y = j ((pullback.snd f j) (genericPoint (bcScheme f j))) →
      IsReduced (f.fiber y) := by
    rintro y rfl
    haveI : Flat (Spec.map (psiK j ((pullback.snd f j) (genericPoint (bcScheme f j))))) :=
      (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (flat_psiK _ _)
    haveI := isPreimmersion_spec_psiK j ((pullback.snd f j) (genericPoint (bcScheme f j)))
    exact isReduced_of_isPullback_flat_preimmersion _ _ _ _ (isPullback_fiber_toSpecQuot f j)
  haveI := key _ hy
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- On an integral proper scheme of dimension zero an invertible sheaf has a non-zero section. -/
private theorem finrank_ne_zero_of_dim_zero {κ : Type u} [Field κ] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of κ)) [IsProper g] [IsIntegral Z] [IsLocallyNoetherian Z]
    (hd : topologicalKrullDim Z = 0) (P : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 P] :
    Module.finrank κ (cohomologyOverField κ g P 0) ≠ 0 := by
  have hall : ∀ x : Z, x = genericPoint Z := by
    intro x
    have hmin := Order.krullDim_nonpos_iff_forall_isMin.1 (le_of_eq hd)
    let W : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    let T : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
    have hx : IsGenericPoint x ⊤ := by
      change closure {x} = Set.univ
      exact Set.eq_univ_of_univ_subset (hmin T (fun _ _ => Set.mem_univ _ : W ≤ T))
    exact hx.eq (genericPoint_spec Z)
  obtain ⟨U, -, e, hxU, he⟩ := MMP.Intersection.exists_isTrivializingGenerator P
    (show genericPoint Z ∈ (⊤ : Z.Opens) from trivial)
  have hU : U = ⊤ := eq_top_iff.2 fun y _ => by rw [hall y]; exact hxU
  subst hU
  have he0 : e ≠ 0 := fun h0 => one_ne_zero ((he ⊤ le_rfl).1 (a₁ := (1 : Γ(Z, ⊤))) (a₂ := 0)
    (by simp only [MMP.Intersection.modules_map_id, h0, smul_zero]))
  haveI : SheafOfModules.IsCoherent P :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z P
  haveI := finiteDimensional_cohomologyOverField_of_isProper κ g P 0
  haveI : Nontrivial (cohomologyOverField κ g P 0) := @Equiv.nontrivial _ _
    (cohomologyOverFieldZeroIsoSections κ g P).toLinearEquiv.toEquiv ⟨⟨e, 0, he0⟩⟩
  exact (Module.finrank_pos (R := κ) (M := cohomologyOverField κ g P 0)).ne'

section TwistIso

variable {X : Scheme.{u}}

/-- `𝒪_X(nA + B) ≅ 𝒪_X(B) ⊗ 𝒪_X(A)^{⊗ n}` for Cartier divisors `A` and `B`. -/
public theorem _root_.MMP.Fourfold.sheaf_nsmul_add_iso (A B : X.CartierDivisor) (n : ℕ) :
    Nonempty (MMP.CartierDivisor.sheaf (n • A + B) ≅
      MMP.CartierDivisor.sheaf B ⊗
        Stacks.Ample.tensorPowModule X (MMP.CartierDivisor.sheaf A) n) := by
  induction n with
  | zero =>
    have h : ((0 : ℕ) • A + B) = B := by simp
    refine ⟨eqToIso (by rw [h]) ≪≫ (ρ_ _).symm ≪≫ ?_⟩
    exact (whiskerLeftIso _ (Stacks.Ample.tensorPowModuleZeroIso X
      (MMP.CartierDivisor.sheaf A)).symm)
  | succ n ih =>
    obtain ⟨e⟩ := ih
    have h : ((n + 1 : ℕ) • A + B) = (n • A + B) + A := by
      rw [succ_nsmul]; abel
    refine ⟨eqToIso (by rw [h]) ≪≫ (MMP.CartierDivisorSheaf.sheafMulIso _ A).symm ≪≫ ?_⟩
    refine (whiskerRightIso e _) ≪≫ (α_ _ _ _) ≪≫ ?_
    refine whiskerLeftIso _ ?_
    exact (whiskerLeftIso _ (Stacks.Ample.tensorPowModuleOneIso X
      (MMP.CartierDivisor.sheaf A)).symm) ≪≫
      Stacks.Ample.tensorPowModuleAddIso X (MMP.CartierDivisor.sheaf A) (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X (MMP.CartierDivisor.sheaf A)
        (by push_cast; ring)

end TwistIso

/-- A projective variety carries an effective Cartier divisor whose sheaf is ample. -/
public theorem _root_.MMP.Fourfold.exists_effective_ample_divisor {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] :
    ∃ H : X.CartierDivisor, MMP.Intersection.IsEffective H ∧
      Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf H) := by
  have hX : AlgebraicGeometry.IsProjectiveVariety k sX := inferInstance
  haveI : IsIntegral X := hX.toIsIntegral
  obtain ⟨-, L, hLinv, hLamp⟩ := Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sX
    hX.isProjective.isHQuasiProjective
  have hL : Stacks.Ample.IsAmple X L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hLamp
  obtain ⟨I, hI, -, -, n, hn, ⟨eI⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨A, hA, hAI⟩ :=
    (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq _).1 hI
  have e : MMP.CartierDivisor.sheaf A ≅ Stacks.Ample.tensorPowModule X L (n : ℤ) :=
    MMP.CartierDivisor.sheafIsoInvertibleSheaf A hA ≪≫ eqToIso (by rw [hAI]) ≪≫ eI.symm
  refine ⟨A, hA, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)

end GenericFibre

/-- If `±[L]` lies in a pointed cone `K` for every Cartier divisor `L`, then the class of every
`ℝ`-Cartier divisor lies in `K`. -/
private theorem mem_of_forall_ofCartier {X : Scheme.{0}} {M : Type*} [AddCommGroup M]
    [Module ℝ M] (φ : KCartierDivisor ℝ X →ₗ[ℝ] M) (K : PointedCone ℝ M)
    (hK : ∀ L : X.CartierDivisor, φ (KCartierDivisor.ofCartier ℝ L) ∈ K ∧
      -φ (KCartierDivisor.ofCartier ℝ L) ∈ K)
    (D : KCartierDivisor ℝ X) : φ D ∈ K := by
  classical
  have hD : D = D.sum fun L a => a • KCartierDivisor.ofCartier ℝ L := by
    conv_lhs => rw [← Finsupp.sum_single D]
    refine Finsupp.sum_congr fun L _ => ?_
    simp [KCartierDivisor.ofCartier]
  rw [hD, map_finsuppSum]
  refine Submodule.sum_mem _ fun L _ => ?_
  simp only [map_smul]
  rcases le_or_gt 0 (D L) with ha | ha
  · exact K.smul_mem ha (hK L).1
  · have : D L • φ (KCartierDivisor.ofCartier ℝ L) =
        (-D L) • -φ (KCartierDivisor.ofCartier ℝ L) := by
      rw [smul_neg, neg_smul, neg_neg]
    rw [this]
    exact K.smul_mem (by linarith) (hK L).2

private theorem residueFieldMap_surjective_of_stalkMap {X Y : Scheme.{0}} (g : X ⟶ Y) (x : X)
    (h : Function.Surjective (g.stalkMap x).hom) : Function.Surjective (g.residueFieldMap x).hom :=
        by
  have := congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap g x)
  have h2 : Function.Surjective ((g.residueFieldMap x).hom.comp (Y.residue (g x)).hom) := by
    rw [show (g.residueFieldMap x).hom.comp (Y.residue (g x)).hom = _ from this]
    exact (X.residue_surjective x).comp h
  exact Function.Surjective.of_comp (g := (Y.residue (g x)).hom) (by simpa [RingHom.coe_comp] using
      h2)

private theorem residueFieldTranscendenceDegree_genericPoint_eq_zero {Y S : Scheme.{0}}
    [IsIntegral Y] (f : Y ⟶ S) [QuasiCompact f]
    (hbir : IsBirationalMorphism f.toImage) :
    residueFieldTranscendenceDegree f (genericPoint Y) = 0 := by
  haveI : IsReduced f.image := inferInstance
  haveI : IrreducibleSpace f.image := (irreducibleSpace_def _).2 (by
      have h := ((IrreducibleSpace.isIrreducible_univ Y).image _
        f.toImage.continuous.continuousOn).closure
      rwa [Set.image_univ, (IsDominant.denseRange (f := f.toImage)).closure_eq] at h)
  haveI : IsIntegral f.image := isIntegral_of_irreducibleSpace_of_isReduced _
  have hb := hbir.functionFieldMap_bijective
  have hn := AlgebraicGeometry.residueFieldMap_comp_genericResidueEquivOfDominant f.toImage
  have hι : Function.Surjective (f.toImage.residueFieldMap (genericPoint Y)).hom := by
    intro x
    obtain ⟨y, hy⟩ := hb.surjective ((AlgebraicGeometry.genericResidueEquiv Y).symm x)
    refine ⟨AlgebraicGeometry.genericResidueEquivOfDominant f.toImage y, ?_⟩
    have := congrArg (fun φ => φ y) hn
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, hy]; simp
  have hu : Function.Surjective (f.imageι.residueFieldMap (f.toImage (genericPoint Y))).hom :=
    residueFieldMap_surjective_of_stalkMap _ _ (f.imageι.stalkMap_surjective _)
  have hsurj : Function.Surjective (f.residueFieldMap (genericPoint Y)).hom := by
    rw [Scheme.Hom.residueFieldMap_congr (Scheme.Hom.toImage_imageι f).symm (genericPoint Y)]
    rw [Scheme.residueFieldMap_comp]
    have hc := ConcreteCategory.bijective_of_isIso
      (S.residueFieldCongr (show (f.toImage ≫ f.imageι) (genericPoint Y) = f (genericPoint Y) by
        rw [Scheme.Hom.toImage_imageι])).hom
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact hι.comp (hu.comp hc.2)
  letI := (f.residueFieldMap (genericPoint Y)).hom.toAlgebra
  have : Algebra.IsAlgebraic (S.residueField (f (genericPoint Y))) (Y.residueField (genericPoint
      Y)) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj x
    exact isAlgebraic_algebraMap a
  unfold residueFieldTranscendenceDegree
  rw [_root_.trdeg_eq_zero]
  simp

section Numerics

variable {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}

/-- The degree `deg_C 𝒪_Y(B)` of a Cartier divisor on a proper curve `C ⊆ Y`. -/
public noncomputable def _root_.MMP.Fourfold.cdeg (B : Y.CartierDivisor) (C : ProperCurve sY) :
    ℤ :=
  C.degree ℂ (MMP.CartierDivisor.sheaf B)

/-- The degree on a curve only depends on the isomorphism class of the sheaf. -/
public theorem _root_.MMP.Fourfold.cdeg_congr {B B' : Y.CartierDivisor}
    (e : MMP.CartierDivisor.sheaf B ≅ MMP.CartierDivisor.sheaf B')
    (C : ProperCurve sY) : cdeg B C = cdeg B' C :=
  degreeOn_eq_of_iso ℂ sY C.ι C.dim_le e

/-- The degree on a curve is additive in the Cartier divisor. -/
public theorem _root_.MMP.Fourfold.cdeg_add (B B' : Y.CartierDivisor) (C : ProperCurve sY) :
    cdeg (B + B') C = cdeg B C + cdeg B' C := by
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
        Y.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf B)).obj
          (MMP.CartierDivisor.sheaf B')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible Y.presheaf Y.ringCatSheaf.2 _ _
  haveI h2 : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((MMP.CartierDivisor.sheaf B).tensorObj
        (MMP.CartierDivisor.sheaf B')) := this
  unfold cdeg ProperCurve.degree
  rw [← degreeOn_tensorSheaf ℂ sY C.ι C.dim_le (hLM := this)]
  exact (degreeOn_eq_of_iso ℂ sY C.ι C.dim_le
    (MMP.CartierDivisorSheaf.sheafMulIso B B')).symm

/-- The zero Cartier divisor has degree zero on every curve. -/
public theorem _root_.MMP.Fourfold.cdeg_zero (C : ProperCurve sY) :
    cdeg (0 : Y.CartierDivisor) C = 0 := by
  have h := cdeg_add (0 : Y.CartierDivisor) 0 C
  rw [add_zero] at h
  omega

/-- The degree of `-B` on a curve is minus that of `B`. -/
public theorem _root_.MMP.Fourfold.cdeg_neg (B : Y.CartierDivisor) (C : ProperCurve sY) :
    cdeg (-B) C = -cdeg B C := by
  have h := cdeg_add B (-B) C
  rw [add_neg_cancel, cdeg_zero] at h
  omega

/-- The degree of `n • B` on a curve is `n` times that of `B`. -/
public theorem _root_.MMP.Fourfold.cdeg_nsmul (B : Y.CartierDivisor) (n : ℕ)
    (C : ProperCurve sY) : cdeg (n • B) C = n * cdeg B C := by
  induction n with
  | zero => simp [cdeg_zero]
  | succ n ih => rw [succ_nsmul, cdeg_add, ih]; push_cast; ring

/-- Linearly equivalent Cartier divisors have the same degree on every curve. -/
public theorem _root_.MMP.Fourfold.cdeg_linearlyEquivalent {B B' : Y.CartierDivisor}
    (h : MMP.Intersection.LinearlyEquivalent B B') (C : ProperCurve sY) : cdeg B C = cdeg B' C :=
  cdeg_congr (nonempty_sheaf_iso_of_linearlyEquivalent h).some C

/-- A Cartier divisor whose sheaf is a pull-back from the base has degree zero on every curve
contracted by `f`. -/
public theorem _root_.MMP.Fourfold.cdeg_eq_zero_of_pullback {S : Scheme.{0}}
    {sS : S ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY] [IsSeparated sS]
    (f : Y ⟶ S) (hf : f ≫ sS = sY)
    {B : Y.CartierDivisor} (M : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M]
    (e : MMP.CartierDivisor.sheaf B ≅ (Scheme.Modules.pullback f).obj M)
    (C : ProperCurve sY) (hC : C.IsContractedBy f) : cdeg B C = 0 := by
  have hcomp : (C.ι ≫ f) ≫ sS = C.ι ≫ sY := by rw [Category.assoc, hf]
  haveI : IsProper (C.ι ≫ sY) := inferInstance
  haveI : IsProper ((C.ι ≫ f) ≫ sS) := hcomp ▸ inferInstance
  haveI : AlgebraicGeometry.IsCurve ℂ ((C.ι ≫ f) ≫ sS) := hcomp ▸ C.isCurve
  have hpt : ∃ y : S, Set.range (C.ι ≫ f) = {y} := by
    refine ⟨f C.point, ?_⟩
    have : Set.range (C.ι ≫ f) = f '' Set.range C.ι := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨C.ι x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    rw [this, C.range_ι]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hC x hx
    · rintro rfl
      exact ⟨C.point, subset_closure rfl, rfl⟩
  unfold cdeg ProperCurve.degree
  rw [degreeOn_eq_of_iso ℂ sY C.ι C.dim_le e,
    degreeOn_pullback_eq_degreeOn_comp sY sS f C.ι hf C.dim_le M]
  exact degreeOn_eq_zero_of_range_eq_singleton sS (C.ι ≫ f) M hpt

end Numerics

/-- If `f` is birational onto its image, `Y` and the closure of `f(Y)` have the same finite
dimension: both are the transcendence degree of the common function field. -/
private theorem topologicalKrullDim_eq_closure_range {Y S : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ))
    (f : Y ⟶ S) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hf : f ≫ sS = sY)
    (hbir : IsBirationalMorphism f.toImage) :
    ∃ a : ℕ, topologicalKrullDim Y = a ∧ topologicalKrullDim (closure (Set.range f.base)) = a := by
  haveI := hY
  haveI := hS
  obtain ⟨-, hQC, -⟩ := projective_facts sY sS f hf
  haveI := hQC
  haveI : LocallyOfFiniteType sY := inferInstance
  haveI : LocallyOfFiniteType sS := inferInstance
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have h := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range f ℂ sY sS hf
  haveI : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sS) := hf ▸ (inferInstance : LocallyOfFiniteType sY)
    exact locallyOfFiniteType_of_comp f sS
  rw [MMP.Flips.topologicalKrullDim_fiber_genericPoint,
    residueFieldTranscendenceDegree_genericPoint_eq_zero f hbir] at h
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType ℂ sY
  have hbot : topologicalKrullDim Y ≠ ⊥ := fun hb =>
    ((Order.krullDim_eq_bot_iff.mp hb).false
      (TopologicalSpace.IrreducibleCloseds.closureSingleton (genericPoint Y))).elim
  rw [show (((0 : ℕ∞) : WithBot ℕ∞)) = 0 from rfl, zero_add] at h
  induction hX : topologicalKrullDim Y using WithBot.recBotCoe with
  | bot => exact absurd hX hbot
  | coe a' =>
    have ha : a' ≠ ⊤ := by rintro rfl; exact h1 hX
    lift a' to ℕ using ha
    exact ⟨a', rfl, h.symm.trans hX⟩

/-- If a morphism `f : Y ⟶ S` of projective complex varieties is birational onto its image, an
invertible sheaf on `Y` has non-zero generic rank over `S`: the generic fibre is an integral proper
scheme of dimension zero, on which it has a non-zero section. -/
public theorem _root_.MMP.Mori.relativeGenericRank_ne_zero_of_isBirationalMorphism_toImage
    {Y S : Scheme.{0}} [IsIntegral Y]
    (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ))
    (f : Y ⟶ S) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hf : f ≫ sS = sY)
    (hbir : IsBirationalMorphism f.toImage) (F : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 F] :
    relativeGenericRank f F ≠ 0 := by
  haveI := hY
  haveI := hS
  obtain ⟨hI, hQC, hQS⟩ := projective_facts sY sS f hf
  obtain ⟨hP, -, -⟩ := projective_facts' sY sS f hf
  haveI := hQC
  haveI := hQS
  haveI := hP
  haveI hLFT : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sS) := hf ▸ (inferInstance : LocallyOfFiniteType sY)
    exact locallyOfFiniteType_of_comp f sS
  haveI hPZ : IsProper (f.fiberToSpecResidueField (f (genericPoint Y))) :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField (f
        (genericPoint Y)))))
  haveI hZI : IsIntegral (f.fiber (f (genericPoint Y))) := isIntegral_generic_fibre f
  haveI hZN : IsLocallyNoetherian (f.fiber (f (genericPoint Y))) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f _
  haveI : F.IsQuasicoherent := inferInstance
  rw [relativeGenericRank_eq_finrank_fibre f F]
  haveI hinv : SheafOfModules.IsInvertible (f.fiber (f (genericPoint Y))).presheaf
      (f.fiber (f (genericPoint Y))).ringCatSheaf.2
      ((Scheme.Modules.pullback (f.fiberι (f (genericPoint Y)))).obj F) := inferInstance
  have hd0 : topologicalKrullDim (f.fiber (f (genericPoint Y))) = 0 := by
    rw [MMP.Flips.topologicalKrullDim_fiber_genericPoint,
      residueFieldTranscendenceDegree_genericPoint_eq_zero f hbir]
    rfl
  exact @finrank_ne_zero_of_dim_zero _ _ _ (f.fiberToSpecResidueField (f (genericPoint Y)))
    hPZ hZI hZN hd0 _ hinv

section Cone

/-- On a projective variety an ample invertible sheaf has a power isomorphic to the sheaf of an
effective Cartier divisor. -/
public theorem _root_.MMP.Fourfold.exists_effective_cartier_sheaf_iso {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) :
    ∃ H : X.CartierDivisor, IsEffective H ∧ ∃ n : ℕ, 0 < n ∧
      Nonempty (MMP.CartierDivisor.sheaf H ≅
        Stacks.Ample.tensorPowModule X L (n : ℤ)) := by
  have hX : AlgebraicGeometry.IsProjectiveVariety k sX := inferInstance
  haveI : IsIntegral X := hX.toIsIntegral
  obtain ⟨I, hI, -, -, n, hn, ⟨eI⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨A, hA, hAI⟩ :=
    (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq _).1 hI
  have e : MMP.CartierDivisor.sheaf A ≅ Stacks.Ample.tensorPowModule X L (n : ℤ) :=
    MMP.CartierDivisor.sheafIsoInvertibleSheaf A hA ≪≫ eqToIso (by rw [hAI]) ≪≫ eI.symm
  exact ⟨A, hA, n, hn, ⟨e⟩⟩

variable {Y S : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} (f : Y ⟶ S)

/-- The relative degree map evaluated on the class of a Cartier divisor `B` at a contracted curve
`C` is the degree `cdeg B C`. -/
public theorem _root_.MMP.Fourfold.relativeDegreeMap_ofCartier (B : Y.CartierDivisor)
    (C : {C : ProperCurve sY // C.IsContractedBy f}) :
    relativeDegreeMap sY f (KCartierDivisor.ofCartier ℝ B) C = (cdeg B C.1 : ℝ) := by
  change OneCycle.intersectionNumber (C.1.cycle ℝ) (KCartierDivisor.ofCartier ℝ B) = _
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  rfl

private theorem relativeNumericalDivisorClass_eq_of_degrees {x y : KCartierDivisor ℝ Y}
    (h : ∀ C, relativeDegreeMap sY f x C = relativeDegreeMap sY f y C) :
    relativeNumericalDivisorClass sY f x = relativeNumericalDivisorClass sY f y := by
  refine (Submodule.Quotient.eq _).2 ?_
  rw [LinearMap.mem_ker]
  funext C
  simpa [map_sub, sub_eq_zero] using h C

private theorem class_mem_cone_of_degrees (B E₁ E₂ : Y.CartierDivisor)
    (h₁ : IsEffective E₁) (h₂ : IsEffective E₂) (a₁ a₂ : ℝ) (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂)
    (h : ∀ C : ProperCurve sY, C.IsContractedBy f →
      (cdeg B C : ℝ) = a₁ * cdeg E₁ C + a₂ * cdeg E₂ C) :
    relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ B) ∈
      relativeEffectiveCone sY f := by
  have hgen : ∀ E : Y.CartierDivisor, IsEffective E →
      relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ E) ∈
        relativeEffectiveCone sY f := fun E hE => PointedCone.subset_hull ⟨E, hE, rfl⟩
  have : relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ B) =
      a₁ • relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ E₁) +
        a₂ • relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ E₂) := by
    rw [← map_smul, ← map_smul, ← map_add]
    refine relativeNumericalDivisorClass_eq_of_degrees f fun C => ?_
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, relativeDegreeMap_ofCartier]
    exact h C.1 C.2
  rw [this]
  exact Submodule.add_mem _ ((relativeEffectiveCone sY f).smul_mem ha₁ (hgen E₁ h₁))
    ((relativeEffectiveCone sY f).smul_mem ha₂ (hgen E₂ h₂))

private theorem class_ofCartier_neg (L : Y.CartierDivisor) :
    relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ (-L)) =
      -relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ L) := by
  rw [← map_neg]
  refine relativeNumericalDivisorClass_eq_of_degrees f fun C => ?_
  simp only [map_neg, Pi.neg_apply, relativeDegreeMap_ofCartier, cdeg_neg]
  push_cast; rfl

end Cone

/-- Let `f : Y ⟶ S` be a morphism of complex projective varieties and `A` a Cartier divisor on
`Y` with `𝒪_Y(A)` `f`-ample. Some positive multiple `nA` has, on every curve contracted by `f`,
the degree of an effective Cartier divisor `H`: for `ν ≫ 0`, `A + ν f^*H_S` is ample, `H_S` an
ample divisor of `S`, so a multiple `n(A + ν f^*H_S)` is linearly equivalent to an effective `H`,
and `f^*H_S` has degree zero on the curves contracted by `f`. -/
public theorem _root_.MMP.Fourfold.exists_isEffective_degree_eq_nsmul_of_isRelativelyAmple
    {Y S : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (f : Y ⟶ S)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hf : f ≫ sS = sY) (A : Y.CartierDivisor)
    (hA : IsRelativelyAmple f (MMP.CartierDivisor.sheaf A)) :
    ∃ (H : Y.CartierDivisor) (n : ℕ), 0 < n ∧ IsEffective H ∧
      ∀ C : ProperCurve sY, C.IsContractedBy f →
        C.degree ℂ (MMP.CartierDivisor.sheaf H) =
          n * C.degree ℂ (MMP.CartierDivisor.sheaf A) := by
  haveI := hY
  haveI := hS
  obtain ⟨HS, -, hHS⟩ := exists_effective_ample_divisor sS
  have hM : Stacks.Ample.IsAmple S (MMP.CartierDivisor.sheaf HS) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ (Iso.refl (MMP.CartierDivisor.sheaf HS))).mpr hHS
  obtain ⟨B, ⟨eB⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf HS))
  have hB : Nonempty (MMP.CartierDivisor.sheaf B ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf HS)) :=
    ⟨eB.symm ≪≫
      (Scheme.Modules.pullback f).mapIso (Iso.refl (MMP.CartierDivisor.sheaf HS)).symm⟩
  have hAr : IsRelativelyAmple f (MMP.CartierDivisor.sheaf A) :=
    isRelativelyAmple_of_iso f (Iso.refl (MMP.CartierDivisor.sheaf A)).symm hA
  obtain ⟨ν, hν, hνge⟩ := ((MMP.Foundations.isAmple_add_zsmul_pullback ℂ hY hS hf hM hAr hB).and
    (Filter.eventually_ge_atTop 1)).exists
  lift ν to ℕ using (by omega)
  obtain ⟨H, hH, n, hn, ⟨eH⟩⟩ := exists_effective_cartier_sheaf_iso sY _
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _
      (Iso.refl (MMP.CartierDivisor.sheaf (A + (ν : ℤ) • B)))).mp hν)
  obtain ⟨e2⟩ := sheaf_nsmul_add_iso (A + (ν : ℤ) • B) 0 n
  obtain ⟨e0⟩ := MMP.Mori.TwistGrowth.nonempty_sheaf_zero_iso (X := Y)
  have eHn : MMP.CartierDivisor.sheaf H ≅
      MMP.CartierDivisor.sheaf (n • (A + (ν : ℤ) • B) + 0) :=
    eH ≪≫ (MonoidalCategory.leftUnitor _).symm ≪≫ MonoidalCategory.whiskerRightIso e0.symm _ ≪≫
      e2.symm
  refine ⟨H, n, hn, hH, fun C hC => ?_⟩
  change cdeg H C = n * cdeg A C
  rw [cdeg_congr eHn C, cdeg_add, cdeg_zero, cdeg_nsmul, cdeg_add, natCast_zsmul, cdeg_nsmul,
    cdeg_eq_zero_of_pullback f hf _ eB.symm C hC]
  ring

/-- If `f` is birational onto its image, the class in `N¹(Y/S)_ℝ` of every Cartier divisor lies in
the effective cone: `D` is `f`-big, so `mD ∼ A + E` with `A` `f`-ample and `E` effective, and by
`MMP.Fourfold.exists_isEffective_degree_eq_nsmul_of_isRelativelyAmple` a multiple `nA` is
numerically equivalent over `S` to an effective divisor. -/
private theorem class_ofCartier_mem {Y S : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ))
    (f : Y ⟶ S) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hf : f ≫ sS = sY)
    (hbir : IsBirationalMorphism f.toImage) (D : Y.CartierDivisor) :
    relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ D) ∈
      relativeEffectiveCone sY f := by
  haveI := hY
  haveI := hS
  obtain ⟨a, ha, hb⟩ := topologicalKrullDim_eq_closure_range sY sS f hY hS hf hbir
  have hbig : IsRelativelyBigCartier f D := by
    refine ⟨a, a, ha, hb, 1 / 2, by norm_num, 1, fun m _ => ?_⟩
    rw [Nat.sub_self, pow_zero, mul_one]
    have h1 : 1 ≤ relativeGenericRank f (MMP.CartierDivisor.sheaf (m • D)) :=
      Nat.one_le_iff_ne_zero.mpr
        (relativeGenericRank_ne_zero_of_isBirationalMorphism_toImage sY sS f hY hS hf hbir _)
    have h2 : (1 : ℝ) ≤ relativeGenericRank f (MMP.CartierDivisor.sheaf (m • D)) :=
      by exact_mod_cast h1
    linarith
  obtain ⟨m, hm, A, E, hA, hE, hlin⟩ :=
    (isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sY sS f hf D).mp hbig
  obtain ⟨H, n, hn, hH, hdeg⟩ :=
    exists_isEffective_degree_eq_nsmul_of_isRelativelyAmple sY sS f hY hS hf A hA
  have hmn : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine class_mem_cone_of_degrees f D H E hH hE
    (1 / ((m : ℝ) * n)) (1 / (m : ℝ)) (by positivity) (by positivity) fun C hC => ?_
  have h1 : (cdeg H C : ℝ) = n * cdeg A C := by exact_mod_cast hdeg C hC
  have h2 : (m : ℝ) * cdeg D C = cdeg A C + cdeg E C := by
    exact_mod_cast (show (m : ℤ) * cdeg D C = cdeg A C + cdeg E C by
      rw [← cdeg_add, ← cdeg_linearlyEquivalent hlin C, cdeg_nsmul])
  field_simp
  linear_combination (n : ℝ) * h2 - h1

/-- If `f` is birational onto its image, then for every Cartier divisor `L` on `Y` both `±[L]` lie
in the relative effective cone: apply `class_ofCartier_mem` to `L` and to `-L`. -/
private theorem pm_relativeNumericalDivisorClass_ofCartier_mem {Y S : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ))
    (f : Y ⟶ S) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hf : f ≫ sS = sY)
    (hbir : IsBirationalMorphism f.toImage) (L : Y.CartierDivisor) :
    relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ L) ∈
        relativeEffectiveCone sY f ∧
      -relativeNumericalDivisorClass sY f (KCartierDivisor.ofCartier ℝ L) ∈
        relativeEffectiveCone sY f := by
  refine ⟨class_ofCartier_mem sY sS f hY hS hf hbir L, ?_⟩
  rw [← class_ofCartier_neg f L]
  exact class_ofCartier_mem sY sS f hY hS hf hbir (-L)

end MMP.Proof_lem_fourfold_birational_relative_pseudoeffective

namespace MMP.Mori

open MMP.Proof_lem_fourfold_birational_relative_pseudoeffective

/-- If `f : Y ⟶ S` is a morphism of projective complex varieties, `Y` normal, which is birational
onto its image, then every Cartier divisor `D` on `Y` is `f`-big: `dim Y = dim f(Y)`, so the
exponent in the definition is zero, and `f_* 𝒪_Y(mD)` has non-zero rank at the generic point of
`f(Y)` because the generic fibre is a point. -/
public theorem Divisor.isRelativelyBig_of_isBirationalMorphism_toImage {Y S : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} {f : Y ⟶ S} (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hf : f ≫ sS = sY)
    (hbir : IsBirationalMorphism f.toImage) {D : Divisor Y} (hD : D.IsCartier) :
    D.IsRelativelyBig f := by
  haveI : CompactSpace Y := by
    haveI := hY
    exact QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨a, ha, hb⟩ := topologicalKrullDim_eq_closure_range sY sS f hY hS hf hbir
  refine ⟨a, a, ha, hb, 1 / 2, by norm_num, 0, fun m _ => ?_⟩
  haveI := (hD.zsmul m).isInvertibleModule_divisorialSheaf
  have hrank : 1 ≤ relativeGenericRank f (m • D).divisorialSheaf :=
    Nat.one_le_iff_ne_zero.mpr
      (relativeGenericRank_ne_zero_of_isBirationalMorphism_toImage sY sS f hY hS hf hbir _)
  rw [Nat.sub_self, pow_zero, mul_one]
  have : (1 : ℝ) ≤ relativeGenericRank f (m • D).divisorialSheaf := by exact_mod_cast hrank
  linarith

/-- If `f` is birational onto its image, every `ℚ`-Cartier `ℚ`-divisor on `Y` is `f`-big: a
positive multiple is Cartier, hence `f`-big by
`MMP.Mori.Divisor.isRelativelyBig_of_isBirationalMorphism_toImage`. -/
public theorem QDivisor.isRelativelyBig_of_isBirationalMorphism_toImage {Y S : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} {f : Y ⟶ S} (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hf : f ≫ sS = sY)
    (hbir : IsBirationalMorphism f.toImage) {G : QDivisor Y} (hG : G.IsQCartier) :
    G.IsRelativelyBig f := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hG.exists_pos
  refine ⟨m, hm, D, ?_, hDc,
    Divisor.isRelativelyBig_of_isBirationalMorphism_toImage hY hS hf hbir hDc⟩
  rw [hD, natCast_zsmul, Nat.cast_smul_eq_nsmul]

end MMP.Mori

namespace MMP.Fourfold

open MMP.Proof_lem_fourfold_birational_relative_pseudoeffective

/-- Let `f : Y ⟶ S` be a morphism of normal projective complex varieties with `Y` `ℚ`-factorial
and `f` birational onto its image. Every `ℝ`-Cartier divisor on `Y` is pseudo-effective over `S`,
and the zero `ℚ`-divisor on `Y` is `f`-big. -/
@[mmp "lem_fourfold_birational_relative_pseudoeffective"]
public theorem isRelativelyPseudoEffective_and_isRelativelyBig_zero_of_isBirationalMorphism_toImage
    {Y S : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (f : Y ⟶ S)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYQ : IsQFactorial sY)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hSn : MMP.Mori.IsNormalVariety ℂ sS)
    (hf : f ≫ sS = sY) (hbir : IsBirationalMorphism f.toImage) :
    (∀ D : KCartierDivisor ℝ Y, KCartierDivisor.IsRelativelyPseudoEffective sY f D) ∧
      (0 : QDivisor Y).IsRelativelyBig f := by
  have pm_mem := pm_relativeNumericalDivisorClass_ofCartier_mem sY sS f hY hS hf hbir
  exact ⟨fun D => subset_closure (mem_of_forall_ofCartier _ _ pm_mem D),
    QDivisor.isRelativelyBig_of_isBirationalMorphism_toImage hY hS hf hbir
      ⟨1, one_ne_zero, 0, by simp, Divisor.isCartier_zero⟩⟩

end MMP.Fourfold

end BirationalImage

end
