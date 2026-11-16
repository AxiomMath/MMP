module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreCycle
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFibreGeneric
public import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafInvertible
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackSheaf

/-!
# The restriction of divisors to the general fibre components of a curve-image component

Let `r : Z ⟶ Y` be a curve-and-point exceptional model and `E` a component of its exceptional
divisor whose image `T = r(E)` is a curve. Over a general closed point `y ∈ T`, every irreducible
component `G` of the fibre `E_y` is a smooth projective surface, and for each prime divisor `P` of
`E` the Cartier divisor `π P` with Weil divisor `P` restricts to `G` as a Cartier divisor whose
Weil divisor is `∑_{C' ⊆ G ∩ P} C'`, the curves `C'` of `G ∩ P` counted with multiplicity one.

## Main results

* `MMP.Fourfold.isOrderAlong_pullback_of_isReduced`: the pull-back of an effective Cartier
  divisor to an integral scheme meeting it in a reduced subscheme has order one along the prime
  divisors of the intersection and zero along all others.
* `MMP.Fourfold.rationalCycleClass_sum_single_eq_finsum_maximal`: on a complex surface, the class
  of the reduced divisor of a proper closed set is the sum of the classes of its curves.
* `MMP.Fourfold.exists_isOpenImmersion_fiber_of_maximal`,
  `MMP.Fourfold.smooth_of_maximal_preimage_singleton`: a component of a smooth fibre over a
  closed point is open in the fibre, and smooth over `ℂ`.
* `MMP.Fourfold.exists_restrict_of_isReduced`: the restriction of a prime divisor to a surface
  meeting it in a reduced curve.
* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_opens_isSmoothScheme_maximal_fibre`: the
  general fibre components of `E` are smooth (generic smoothness).
* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_opens_restrict_maximal_fibre`: the general
  fibre components are smooth projective surfaces, and the restriction of `π P` to them has Weil
  divisor class `∑_{C'} [C']`.

## Implementation notes

Multiplicity one is read off the local rings: at the generic point `ξ` of a curve `C' ⊆ G ∩ P`
the pulled-back local equation `a` of `π P` generates the stalk of the ideal of `G ∩ P`, and
`𝒪_{G,ξ}/(a)` is reduced, since `G ∩ P` is an open subscheme of the fibre `P ×_Y y`, reduced for
general `y`. In the one-dimensional local domain `𝒪_{G,ξ}` this makes `(a)` the maximal ideal.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
* [W. Fulton, *Intersection Theory*][fulton1998], §2.3
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MMP
open MMP.Intersection.Scheme (Subvariety)
open MMP.Intersection (hasDim_natCast_iff)
open MMP.Mori MMP.Analytic TopologicalSpace Stacks.Chow

namespace MMP.Fourfold

section PullbackEquation

open Opposite

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat

/-- The germ at `y` of the pull-back `g^♯ c` of a section `c` is the image of the germ of `c` at
`g y` under the stalk map. -/
private theorem germ_appLE {Y Z : Scheme.{0}} (g : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    (e : V ≤ g ⁻¹ᵁ U) {y : Y} (hy : y ∈ V) (c : Γ(Z, U)) :
    Y.presheaf.germ V y hy (g.appLE U V e c) =
      g.stalkMap y (Z.presheaf.germ U (g y) (show g y ∈ U from e hy) c) := by
  rw [Scheme.Hom.germ_stalkMap_apply, ← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE e) y hy]
  rfl

/-- **The pulled-back local equation.** If `a ∈ 𝒪_X(U)` is a regular local equation of a Cartier
divisor `D` on `U`, and `π : X' ⟶ X` is a morphism from an integral scheme with `π(X') ⊄ |D|`
meeting `U`, then `π^* a ∈ 𝒪_{X'}(π⁻¹ U)` is a regular local equation of `π^* D` on `π⁻¹ U`. -/
theorem isRegularLocalEquation_pullback_appLE {X X' : Scheme.{0}} [IsIntegral X'] (π : X' ⟶ X)
    {D : X.CartierDivisor} (hπ : ¬ Set.range π ⊆ MMP.Intersection.cartierSupport D)
    {U : X.Opens} {a : Γ(X, U)} (ha : MMP.CartierDivisor.IsRegularLocalEquation D a) {x : X'}
    (hxU : π x ∈ U) :
    MMP.CartierDivisor.IsRegularLocalEquation (MMP.CartierDivisor.pullback π D hπ)
      (π.appLE U (π ⁻¹ᵁ U) le_rfl a) := by
  obtain ⟨hu, hg⟩ := ha
  have hη : π (genericPoint X') ∈ U :=
    MMP.CartierDivisorPullback.genericPoint_mem (V := π ⁻¹ᵁ U) hxU
  have hξ : genericPoint X' ∈ π ⁻¹ᵁ U := MMP.CartierDivisorPullback.genericPoint_mem hxU
  obtain ⟨a₀, ha₀⟩ := MMP.CartierDivisor.exists_isGermUnit_of_not_range_subset π D hπ hg hη
  have hpb := MMP.CartierDivisor.isLocalEquationOn_pullback π D hπ hg hη ha₀
  have hstalk : a₀.val = X.presheaf.germ U _ hη a := by
    apply MMP.CartierDivisorPullback.stalkToTotalQuotient_injective X
    rw [ha₀, IsUnit.unit_spec]
    exact (MMP.CartierDivisorPullback.stalkToTotalQuotient_germ hη a).symm
  have hval : MMP.Intersection.toTotalQuotient (π ⁻¹ᵁ U) (π.appLE U (π ⁻¹ᵁ U) le_rfl a) =
      (MMP.CartierDivisorPullback.ofFunctionField (π ⁻¹ᵁ U)
        (MMP.CartierDivisorPullback.pullbackGerm π a₀) : _) := by
    refine MMP.CartierDivisorPullback.toTotalQuotient_eq_functionFieldToK _ hξ ?_
    change _ = (π.stalkMap (genericPoint X')).hom a₀.val
    rw [hstalk, germ_appLE π le_rfl hξ a]
  have hu' : IsUnit (MMP.Intersection.toTotalQuotient (π ⁻¹ᵁ U)
      (π.appLE U (π ⁻¹ᵁ U) le_rfl a)) := by
    rw [hval]
    exact Units.isUnit _
  refine ⟨hu', ?_⟩
  have : hu'.unit = MMP.CartierDivisorPullback.ofFunctionField (π ⁻¹ᵁ U)
      (MMP.CartierDivisorPullback.pullbackGerm π a₀) :=
    Units.ext ((IsUnit.unit_spec _).trans hval)
  rwa [this]

end PullbackEquation

/-- **Order one from a reduced quotient.** In a local domain of dimension at most one, a nonzero
non-unit `x` with `R ⧸ (x)` reduced has order one: `(x)` is the maximal ideal. -/
theorem ord_eq_one_of_isReduced_quotient {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Ring.KrullDimLE 1 R] {x : R} (hx0 : x ≠ 0) (hxu : ¬ IsUnit x)
    (hred : IsReduced (R ⧸ Ideal.span {x})) : Ring.ord R x = 1 := by
  have hrad : (Ideal.span {x}).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 hred
  have hmax : Ideal.span {x} = IsLocalRing.maximalIdeal R := by
    refine le_antisymm ((Ideal.span_singleton_le_iff_mem _).2
      ((IsLocalRing.mem_maximalIdeal x).2 hxu)) ?_
    rw [← hrad.radical, Ideal.radical_eq_sInf]
    refine le_sInf fun p ⟨hIp, hp⟩ ↦ ?_
    have hpb : p ≠ ⊥ := fun h ↦ hx0 (by simpa [h] using hIp (Ideal.mem_span_singleton_self x))
    exact (IsLocalRing.eq_maximalIdeal (hp.isMaximal_of_ne_bot hpb)).ge
  change Module.length R (R ⧸ Ideal.span {x}) = 1
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, hmax]
  exact IsLocalRing.maximalIdeal.isMaximal R

/-- The quotient `𝒪_{X,x} ⧸ I_x` of a local ring by the stalk of an ideal sheaf with reduced
closed subscheme is reduced, at every point of the support. -/
theorem isReduced_stalk_quotient_of_isReduced {X : Scheme.{0}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] {x : X} (hx : x ∈ I.support) :
    IsReduced (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x) := by
  obtain ⟨z, rfl⟩ : x ∈ Set.range I.subschemeι.base := by rwa [I.range_subschemeι]
  have h := IdealSheafData.stalk_ker_of_isClosedImmersion I.subschemeι z
  rw [Scheme.IdealSheafData.ker_subschemeι] at h
  rw [h]
  exact isReduced_of_injective
    (RingHom.quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective z)).toRingHom
    (RingEquiv.injective _)

open MMP.CartierDivisorSheaf MMP.Intersection in
open Classical in
/-- **Orders of a pulled-back divisor with reduced intersection.** Let `D` be an effective
Cartier divisor on `X` and `π : X' ⟶ X` a morphism from an integral locally Noetherian scheme with
`π(X') ⊄ |D|`, such that the scheme-theoretic inverse image `π⁻¹ D` is reduced. Then `π^* D` has
order one along every prime divisor of `X'` contained in `π⁻¹ D`, and order zero along every
other one. -/
theorem isOrderAlong_pullback_of_isReduced {X X' : Scheme.{0}} [IsIntegral X']
    [IsLocallyNoetherian X'] (π : X' ⟶ X) {D : X.CartierDivisor}
    (hD : MMP.Intersection.IsEffective D) (hπ : ¬ Set.range π ⊆ MMP.Intersection.cartierSupport D)
    [IsReduced ((MMP.CartierDivisor.subscheme D hD).comap π).subscheme]
    (Q : MMP.Mori.PrimeDivisor X') :
    IsOrderAlong (MMP.CartierDivisor.pullback π D hπ) (primeDivisorSubvariety Q)
      (if Q.genericPoint ∈ ((MMP.CartierDivisor.subscheme D hD).comap π).support then 1
        else 0) := by
  set J := (MMP.CartierDivisor.subscheme D hD).comap π with hJ
  set ξ := (primeDivisorSubvariety Q).genericPoint
  have hξQ : Q.genericPoint = ξ := rfl
  rw [hξQ]
  have : Ring.KrullDimLE 1 (X'.presheaf.stalk ξ) :=
    krullDimLE_of_coheight_le (by
      rw [← hξQ, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
      simp)
  obtain ⟨U, ⟨a, ha⟩, hxU⟩ := MMP.CartierDivisor.exists_affineOpens_isEffectiveOn hD (π ξ)
  have hξU : ξ ∈ π ⁻¹ᵁ (U : X.Opens) := hxU
  have ha' := isRegularLocalEquation_pullback_appLE π hπ ha hxU
  have hne := germ_ne_zero_of_isRegularLocalEquation ha' hξU
  obtain ⟨hu, hgA⟩ := ha'
  have hf : IsLocalEquationAt (MMP.CartierDivisor.pullback π D hπ) ξ
      (X'.totalQuotientSheaf.presheaf.germ _ ξ hξU (hu.unit : _)) :=
    ⟨_, hξU, hu.unit, hgA, rfl⟩
  have hab : IsFraction (X'.totalQuotientSheaf.presheaf.germ _ ξ hξU (hu.unit : _))
      (X'.presheaf.germ _ ξ hξU (π.appLE U (π ⁻¹ᵁ U) le_rfl a)) 1 := by
    refine ⟨by simp, ?_⟩
    simp only [map_one, one_mul, IsUnit.unit_spec]
    exact germ_toTotalQuotient hξU _
  have h := isOrderAlong_of_isFraction hf (mem_nonZeroDivisors_of_ne_zero hne) (one_mem _) hab
  rw [Ring.ord_one, ENat.toNat_zero, Nat.cast_zero, sub_zero] at h
  convert h using 1
  have hstalk : IdealSheafData.stalk J ξ =
      Ideal.span {X'.presheaf.germ _ ξ hξU (π.appLE U (π ⁻¹ᵁ U) le_rfl a)} := by
    rw [hJ, IdealSheafData.stalk_comap, IdealSheafData.stalk_eq_map_germ _ (π ξ) U hxU,
      MMP.CartierDivisor.ideal_subscheme_affine hD ha, Ideal.map_span, Set.image_singleton,
      Ideal.map_span, Set.image_singleton, germ_appLE π le_rfl hξU a]
  split_ifs with hmem
  · have hred := isReduced_stalk_quotient_of_isReduced J hmem
    rw [hstalk] at hred
    have hnu : ¬ IsUnit (X'.presheaf.germ _ ξ hξU (π.appLE U (π ⁻¹ᵁ U) le_rfl a)) := fun hu' ↦
      (IdealSheafData.stalk_eq_top_iff_notMem_support J ξ).1
        (by rwa [hstalk, Ideal.span_singleton_eq_top]) hmem
    rw [ord_eq_one_of_isReduced_quotient hne hnu hred]
    rfl
  · have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support J ξ).2 hmem
    rw [hstalk, Ideal.span_singleton_eq_top] at htop
    rw [Ring.ord_of_isUnit htop]
    rfl

/-- In an irreducible scheme, a maximal point for the specialization order is the generic
point. -/
theorem eq_genericPoint_of_isMax {X : Scheme} [IrreducibleSpace X] {x : X} (hx : IsMax x) :
    x = genericPoint X := by
  have h : x ≤ genericPoint X := by
    change genericPoint X ⤳ x
    exact (genericPoint_spec X).specializes (Set.mem_univ _)
  exact (Specializes.antisymm h (hx h)).eq.symm

section Surface

variable {G : Scheme.{0}} [G.Over (Spec (.of ℂ))] [IsIntegral G]
  [LocallyOfFiniteType (G ↘ Spec (.of ℂ))]

/-- On an integral `n`-dimensional scheme locally of finite type over `ℂ`, a point has height
plus coheight `n`. -/
theorem height_add_coheight_eq_of_topologicalKrullDim_eq {n : ℕ}
    (hdim : topologicalKrullDim G = n) (x : G) :
    Order.height x + Order.coheight x = n := by
  have hform := MMP.height_add_coheight_eq_krullDim ℂ x
  have hk : topologicalKrullDim G = Order.krullDim G :=
    Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints
  rw [← hk, hdim] at hform
  exact WithBot.coe_injective (hform.trans rfl)

/-- On an integral surface over `ℂ`, the height and coheight of a point are natural numbers
summing to `2`. -/
theorem exists_height_coheight_eq_natCast (hdim : topologicalKrullDim G = 2) (x : G) :
    ∃ a b : ℕ, Order.height x = a ∧ Order.coheight x = b ∧ a + b = 2 := by
  have hsum : Order.height x + Order.coheight x = 2 := by
    exact_mod_cast height_add_coheight_eq_of_topologicalKrullDim_eq (n := 2)
      (by exact_mod_cast hdim) x
  have hh : Order.height x ≠ ⊤ := fun h ↦ by
    rw [h, top_add] at hsum
    simp at hsum
  have hc : Order.coheight x ≠ ⊤ := fun h ↦ by
    rw [h, add_top] at hsum
    simp at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hh
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 hc
  rw [← ha, ← hb] at hsum
  exact ⟨a, b, ha.symm, hb.symm, by exact_mod_cast hsum⟩

/-- On an integral surface over `ℂ`, the closure of a point is a curve exactly when the point has
coheight one. -/
theorem hasDim_ofPoint_one_iff_coheight_eq_one (hdim : topologicalKrullDim G = 2) (x : G) :
    (Subvariety.ofPoint x).HasDim ((1 : ℕ) : ℤ) ↔ Order.coheight x = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq_natCast hdim x
  have hd := Subvariety.dim_eq_height_genericPoint (Subvariety.ofPoint x)
  rw [Subvariety.genericPoint_ofPoint] at hd
  rw [Subvariety.HasDim, hasDim_natCast_iff]
  change Subvariety.dim _ = _ ↔ _
  rw [hd, ha, hb]
  exact_mod_cast (show a = 1 ↔ b = 1 by omega)

/-- On an integral surface over `ℂ`, a point has delta-dimension one exactly when it has
coheight one. -/
theorem relativeDimension_eq_one_iff_coheight_eq_one (hdim : topologicalKrullDim G = 2) (x : G) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (G ↘ Spec (.of ℂ)) x =
        ((1 : ℕ) : ℤ) ↔ Order.coheight x = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq_natCast hdim x
  have htop := Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ (G ↘ Spec (.of ℂ)) x
  rw [MMP.topologicalKrullDim_closure_singleton_eq_height, ha] at htop
  have hnn := relativeDimension_nonneg (fieldChowSituation ℂ) (fun _ _ ↦ rfl) (G ↘ Spec (.of ℂ)) x
  have hrel : (relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (G ↘ Spec (.of ℂ)) x).toNat = a := by exact_mod_cast htop.symm
  rw [hb, Nat.cast_eq_one]
  omega

/-- On an integral surface over `ℂ`, the closure of a prime divisor contained in a proper closed
subset `S` is a maximal irreducible subset of `S`. -/
theorem maximal_closure_genericPoint (hdim : topologicalKrullDim G = 2) {S : Set G}
    (hS : IsClosed S) (hSu : S ≠ Set.univ) (Q : MMP.Mori.PrimeDivisor G)
    (hQS : Q.genericPoint ∈ S) :
    Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ S) (closure {Q.genericPoint}) := by
  have hcl : closure {Q.genericPoint} ⊆ S :=
    closure_minimal (Set.singleton_subset_iff.2 hQS) hS
  refine ⟨⟨isIrreducible_singleton.closure, hcl⟩, fun A ⟨hA, hAS⟩ hQA ↦ ?_⟩
  set η := hA.closure.genericPoint
  have hηA : closure {η} = closure A := by
    have := hA.closure.isGenericPoint_genericPoint_closure
    rwa [closure_closure] at this
  have hle : Q.genericPoint ≤ η := by
    change η ⤳ Q.genericPoint
    rw [specializes_iff_mem_closure, hηA]
    exact subset_closure (hQA (subset_closure rfl))
  by_cases hge : η ≤ Q.genericPoint
  · have heq : Q.genericPoint = η := (Specializes.antisymm hle hge).eq.symm
    rw [heq, hηA]
    exact subset_closure
  · have hlt : Q.genericPoint < η := lt_of_le_not_ge hle hge
    exfalso
    have hh := Order.height_strictMono hlt
    have hQh : Order.height Q.genericPoint = 1 := by
      obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq_natCast hdim Q.genericPoint
      rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hb
      have : b = 1 := by exact_mod_cast hb.symm
      rw [ha, show a = 1 by omega]
      rfl
    have hc0 : Order.coheight η = 0 := by
      obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq_natCast hdim η
      rw [hQh, ha] at hh
      have : 1 < a := by simpa using hh
      rw [hb, show b = 0 by omega]
      rfl
    have hgen : η = genericPoint G := eq_genericPoint_of_isMax (Order.coheight_eq_zero.1 hc0)
    apply hSu
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec G : closure {genericPoint G} = Set.univ), ← hgen, hηA]
    exact closure_minimal hAS hS

open Classical in
/-- **The class of the reduced divisor of a closed set of a surface.** Let `G` be an integral
complex surface, `S ⊊ G` closed and `s` the prime divisors of `G` contained in `S`. The class of
`∑_{Q ∈ s} Q` in `H_2(G, ℚ)` is the sum of the classes `cl_G(x)` of the curves `closure {x}`
which are maximal irreducible subsets of `S`. -/
theorem rationalCycleClass_sum_single_eq_finsum_maximal [IsComplexScheme G]
    (hdim : topologicalKrullDim G = 2) {S : Set G} (hS : IsClosed S) (hSu : S ≠ Set.univ)
    (s : Finset (MMP.Mori.PrimeDivisor G)) (hs : ∀ Q, Q ∈ s ↔ Q.genericPoint ∈ S) :
    Chow.rationalCycleClass G 1 (Finsupp.linearCombination ℚ (fun Q : MMP.Mori.PrimeDivisor G =>
        if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction (G ↘ Spec (.of ℂ))
            Q.genericPoint = ((1 : ℕ) : ℤ) then
          Chow.rationalPointCycle (fieldChowSituation ℂ) (G ↘ Spec (.of ℂ)) ((1 : ℕ) : ℤ)
            Q.genericPoint h else 0)
        (MMP.Mori.Divisor.toQDivisor (∑ Q ∈ s, Finsupp.single Q 1))) =
      ∑ᶠ (x : {x : G // relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (G ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
        (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ S) (closure {x.1})),
        Chow.pointCycleClass ℚ x.1 x.2 := by
  have hQdim : ∀ Q : MMP.Mori.PrimeDivisor G,
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (G ↘ Spec (.of ℂ))
        Q.genericPoint = ((1 : ℕ) : ℤ) := fun Q ↦
    (relativeDimension_eq_one_iff_coheight_eq_one hdim _).2
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)
  let T := {x : G // relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (G ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)}
  let i : MMP.Mori.PrimeDivisor G → T := fun Q ↦ ⟨Q.genericPoint, hQdim Q⟩
  have hmax : ∀ C : T,
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ S) (closure {C.1}) ↔ ∃ Q ∈ s, i Q = C := by
    refine fun C ↦ ⟨fun hC ↦ ?_, ?_⟩
    · have hc := (relativeDimension_eq_one_iff_coheight_eq_one hdim C.1).1 C.2
      refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc, (hs _).2 ?_, ?_⟩
      · simp only [MMP.Mori.PrimeDivisor.genericPoint,
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
        exact hC.1.2 (subset_closure rfl)
      · apply Subtype.ext
        simp only [i, MMP.Mori.PrimeDivisor.genericPoint,
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    · rintro ⟨Q, hQ, rfl⟩
      exact maximal_closure_genericPoint hdim hS hSu Q ((hs Q).1 hQ)
  have hfin : {C : T | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ S) (closure {C.1})}.Finite :=
    (s.finite_toSet.image i).subset fun C hC ↦ (hmax C).1 hC
  change _ = ∑ᶠ (C : T) (_ : C ∈ {C : T |
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ S) (closure {C.1})}),
    Chow.pointCycleClass ℚ C.1 C.2
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, map_sum, map_sum, map_sum]
  refine Finset.sum_bij (fun Q _ ↦ i Q) (fun Q hQ ↦ ?_) (fun Q _ Q' _ h ↦ ?_)
    (fun C hC ↦ ?_) (fun Q _ ↦ ?_)
  · rw [Set.Finite.mem_toFinset]
    exact (hmax _).2 ⟨Q, hQ, rfl⟩
  · exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (congrArg Subtype.val h)
  · rw [Set.Finite.mem_toFinset] at hC
    obtain ⟨Q, hQ, rfl⟩ := (hmax C).1 hC
    exact ⟨Q, hQ, rfl⟩
  · have hm : MMP.Mori.Divisor.toQDivisor (Finsupp.single Q (1 : ℤ)) =
        Finsupp.single Q (1 : ℚ) := by
      simp [MMP.Mori.Divisor.toQDivisor, MMP.Mori.DivisorWithCoeffs.mapCoeffsAddMonoidHom]
    rw [hm, Finsupp.linearCombination_single, one_smul, dite_eq_left (hQdim Q)]
    exact Chow.rationalCycleClass_rationalPointCycle (k := 1) Q.genericPoint (hQdim Q)

end Surface

section Fibre

open scoped MMP.SubschemeOver

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat
  MMP.CartierDivisor.isInvertible_sheaf

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- Every subvariety of a component of `F` is a projective variety. -/
theorem IsCurvePointExceptionalModel.isProjectiveVariety_subvariety
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support)
    (G : Subvariety E.1.idealSheaf.subscheme) :
    MMP.Mori.IsProjectiveVariety ℂ (G.toScheme ↘ Spec (.of ℂ)) := by
  have hZ : IsProjectiveMorphism (Z ↘ Spec (.of ℂ)) := by
    rw [← hr.comp_eq]
    exact IsProjectiveMorphism.comp hr.isResolution.2.2.2.1 hr.isProjectiveVariety.isProjective
  have hp : IsProjectiveMorphism (G.ι ≫ E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) :=
    IsProjectiveMorphism.comp (MMP.isProjectiveMorphism_of_isClosedImmersion _)
      (IsProjectiveMorphism.comp (MMP.isProjectiveMorphism_of_isClosedImmersion _) hZ)
  have : IsProper (G.ι ≫ E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) :=
    hp.isProjective.isProper
  refine (MMP.Mori.isProjectiveVariety_iff _ _).2 ⟨(MMP.Mori.isVariety_iff _ _).2
    ⟨inferInstance, (inferInstance : IsSeparated (G.ι ≫ E.1.idealSheaf.subschemeι ≫ _)),
      (inferInstance : LocallyOfFiniteType (G.ι ≫ E.1.idealSheaf.subschemeι ≫ _)),
      (inferInstance : QuasiCompact (G.ι ≫ E.1.idealSheaf.subschemeι ≫ _))⟩, hp⟩

/-- **A component of a smooth fibre over a closed point is open in the fibre.** Let
`p : X ⟶ B` be a morphism and `b ∈ B` a closed point whose fibre `X_b` is smooth over `κ(b)`.
Every subvariety `G ⊆ X` which is a maximal irreducible subset of `p⁻¹(b)` is an open subscheme
of `X_b`, compatibly with the inclusions into `X`. -/
theorem exists_isOpenImmersion_fiber_of_maximal {X B : Scheme.{0}} (p : X ⟶ B) {b : B}
    (hb : IsClosed {b}) [Smooth (p.fiberToSpecResidueField b)] (G : Subvariety X)
    (hG : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ p.base ⁻¹' {b}) (G.support : Set X)) :
    ∃ e : G.toScheme ⟶ p.fiber b, IsOpenImmersion e ∧ e ≫ p.fiberι b = G.ι := by
  have : IsClosedImmersion (B.fromSpecResidueField b) :=
    isClosed_singleton_iff_isClosedImmersion.1 hb
  have : IsClosedImmersion (p.fiberι b) := by
    change IsClosedImmersion (Limits.pullback.fst _ _)
    infer_instance
  have hφ : Topology.IsEmbedding (p.fiberι b).base := (p.fiberι b).isEmbedding
  rw [← p.range_fiberι b, maximal_isIrreducible_subset_range_iff hφ] at hG
  obtain ⟨C, hC, hGC⟩ := hG
  have hCo : IsOpen C :=
    @MMP.Flips.ResolutionInputs.isOpen_of_mem_irreducibleComponents_of_smooth _ _ _
      (p.fiberToSpecResidueField b) ‹_› _ hC
  let O : (p.fiber b).Opens := ⟨C, hCo⟩
  have hrange : Set.range (O.ι ≫ p.fiberι b).base = (G.support : Set X) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, hGC]
    rfl
  have : IsClosedImmersion (O.ι ≫ p.fiberι b) := by
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    rw [hrange]
    exact G.ideal.support.isClosed
  have : IsReduced (p.fiber b) := isReduced_of_smooth (p.fiberToSpecResidueField b)
  have hker : (O.ι ≫ p.fiberι b).ker = G.ι.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hrange,
      Scheme.IdealSheafData.range_subschemeι]
    rfl
  have := IsClosedImmersion.isIso_lift _ _ hker
  refine ⟨IsClosedImmersion.lift (O.ι ≫ p.fiberι b) G.ι hker.le ≫ O.ι, inferInstance, ?_⟩
  rw [Category.assoc]
  exact IsClosedImmersion.lift_fac (O.ι ≫ p.fiberι b) G.ι hker.le

/-- **A component of a smooth fibre over a closed point is smooth.** Let `X` be a scheme over `ℂ`,
`p : X ⟶ B` a morphism over `ℂ` to a scheme `B` locally of finite type over `ℂ`, and `b ∈ B` a
closed point whose fibre `X_b` is smooth over `κ(b) = ℂ`. Every subvariety `G ⊆ X` which is a
maximal irreducible subset of `p⁻¹(b)` is smooth over `ℂ`. -/
theorem smooth_of_maximal_preimage_singleton {X B : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (sB : B ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sB] (p : X ⟶ B)
    (hp : p ≫ sB = X ↘ Spec (.of ℂ)) {b : B} (hb : IsClosed {b})
    [Smooth (p.fiberToSpecResidueField b)] (G : Subvariety X)
    (hG : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ p.base ⁻¹' {b}) (G.support : Set X)) :
    Smooth (G.toScheme ↘ Spec (.of ℂ)) := by
  obtain ⟨e, he, hfac⟩ := exists_isOpenImmersion_fiber_of_maximal p hb G hG
  have : IsIso (B.fromSpecResidueField b ≫ sB) := by
    rw [← SpecMap_residueFieldIsoBase_inv sB b hb]
    infer_instance
  have hG' : G.toScheme ↘ Spec (.of ℂ) =
      e ≫ p.fiberToSpecResidueField b ≫ B.fromSpecResidueField b ≫ sB := by
    change G.ι ≫ X ↘ Spec (.of ℂ) = _
    rw [← hp, ← Scheme.Hom.fiber_fac_assoc, ← reassoc_of% hfac]
  rw [hG']
  infer_instance

/-- The image of the support of a prime divisor is irreducible. -/
theorem isIrreducible_image_primeDivisor_support {X W : Scheme.{0}} (f : X ⟶ W)
    (E : MMP.Mori.PrimeDivisor X) : IsIrreducible (f.base '' (E.support : Set X)) := by
  have hEirr : IsIrreducible (E.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  exact hEirr.image _ f.continuous.continuousOn

/-- A factorisation `p ≫ j = f` through an injective `j` whose range lies in that of `f` is
surjective. -/
theorem surjective_base_of_comp_eq {X B W : Scheme.{0}} {p : X ⟶ B} {j : B ⟶ W} {f : X ⟶ W}
    (hj : Function.Injective j.base) (hp : p ≫ j = f)
    (h : Set.range j.base ⊆ Set.range f.base) : Function.Surjective p.base := by
  intro t
  obtain ⟨x, hx⟩ := h ⟨t, rfl⟩
  refine ⟨x, hj ?_⟩
  change (p ≫ j).base x = j.base t
  rwa [hp]

/-- For a factorisation `p ≫ j = f` through an injective `j`, the point `t` is closed when `j t`
is, and the fibre of `f` over `j t` is the fibre of `p` over `t`. -/
theorem isClosed_singleton_and_preimage_eq_of_comp_eq {X B W : Scheme.{0}} {p : X ⟶ B}
    {j : B ⟶ W} {f : X ⟶ W} (hj : Function.Injective j.base) (hp : p ≫ j = f) {t : B}
    (ht : IsClosed {j.base t}) : IsClosed {t} ∧ f.base ⁻¹' {j.base t} = p.base ⁻¹' {t} := by
  have he : j.base ⁻¹' {j.base t} = {t} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact hj.eq_iff
  refine ⟨by rw [← he]; exact ht.preimage j.base.hom.continuous, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [← hp]
  exact hj.eq_iff

/-- An open `U` of the reduced curve `T ⊆ Y` is cut out by an open `W` of `Y`: `W` meets `T` if
`U` is nonempty, and every point of `W ∩ T` comes from `U`. -/
theorem exists_opens_forall_mem_inter_curve (T : IrreducibleCloseds Y)
    (U : (curveScheme T).Opens) (hU : (U : Set (curveScheme T)).Nonempty) :
    ∃ W : Y.Opens, ((W : Set Y) ∩ T).Nonempty ∧
      ∀ y ∈ (W : Set Y) ∩ T, ∃ t ∈ U, (curveι T).base t = y := by
  obtain ⟨W, hW, hWU⟩ := (curveι T).isClosedEmbedding.isInducing.isOpen_iff.1 U.2
  have hrange := range_curveι_base T
  refine ⟨⟨W, hW⟩, ?_, fun y hy ↦ ?_⟩
  · obtain ⟨t, ht⟩ := hU
    refine ⟨(curveι T).base t, ?_, hrange ▸ ⟨t, rfl⟩⟩
    change (curveι T).base t ∈ W
    rw [← Set.mem_preimage, hWU]
    exact ht
  · obtain ⟨t, rfl⟩ : y ∈ Set.range (curveι T).base := hrange ▸ hy.2
    have h1 : t ∈ (curveι T).base ⁻¹' W := hy.1
    rw [hWU] at h1
    exact ⟨t, h1, rfl⟩

omit [IsComplexScheme Z] in
/-- A component `E` of the exceptional divisor of a curve-and-point exceptional model is smooth
over `ℂ`. -/
theorem IsCurvePointExceptionalModel.isSmoothScheme_component
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support) :
    MMP.Mori.IsSmoothScheme (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
  change MMP.Mori.IsSmoothScheme (E.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ)))
  rw [← hr.comp_eq]
  exact hr.isSNC.1 E.1 E.2

/-- A component `E` of the exceptional divisor of a curve-and-point exceptional model is a variety
over `ℂ`. -/
theorem IsCurvePointExceptionalModel.isVariety_component
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support) :
    AlgebraicGeometry.IsVariety ℂ (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
  have : MMP.Mori.IsVariety ℂ (r ≫ sY) := hr.isResolution.2.1
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hr.comp_eq]
    exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : IsSeparated (Z ↘ Spec (.of ℂ)) := by
    rw [← hr.comp_eq]
    exact AlgebraicGeometry.IsVariety.toIsSeparated
  set ι := E.1.idealSheaf.subschemeι
  have : IsIntegral E.1.idealSheaf.subscheme := E.1.integral
  have : LocallyOfFiniteType (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (ι ≫ (Z ↘ Spec (.of ℂ))))
  have : QuasiCompact (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (QuasiCompact (ι ≫ (Z ↘ Spec (.of ℂ))))
  have : IsSeparated (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsSeparated (ι ≫ (Z ↘ Spec (.of ℂ))))
  exact (MMP.Mori.isVariety_iff _ _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- A component `E` of the exceptional divisor of a curve-and-point exceptional model is a
threefold. -/
theorem IsCurvePointExceptionalModel.topologicalKrullDim_component_eq_three
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support) :
    topologicalKrullDim E.1.idealSheaf.subscheme = ((3 : ℕ) : WithBot ℕ∞) := by
  have hres := hr.isResolution
  have : MMP.Mori.IsVariety ℂ sY := hres.1
  have : IsProper r := (IsProjectiveMorphism.isProjective hres.2.2.2.1).isProper
  have : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  have : IsIntegral Z := (inferInstance : MMP.Mori.IsVariety ℂ (r ≫ sY)).toIsIntegral
  have : IsIntegral E.1.idealSheaf.subscheme := E.1.integral
  have := hr.isVariety_component E
  have hdimZ : topologicalKrullDim Z = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY)
      hres.2.2.2.2]
    exact hr.topologicalKrullDim_eq
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
  exact MMP.Fourfold.ConductorBlowup.topologicalKrullDim_support_eq_three hdimZ E.1

/-- **Generic smoothness of `E` over its image curve.** The morphism `r|_E` factors through the
reduced curve `T = r(E)` by a morphism `p`, whose fibres over a dense open of `T` are smooth. -/
theorem IsCurvePointExceptionalModel.exists_dense_smooth_fiber_curveScheme
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support) (T : IrreducibleCloseds Y)
    (hT : (T : Set Y) = r.base '' (E.1.support : Set Z)) :
    ∃ (p : E.1.idealSheaf.subscheme ⟶ curveScheme T) (U' : (curveScheme T).Opens),
      p ≫ curveι T = E.1.idealSheaf.subschemeι ≫ r ∧ Dense (U' : Set (curveScheme T)) ∧
      (U' : Set (curveScheme T)).Nonempty ∧ ∀ t ∈ U', Smooth (p.fiberToSpecResidueField t) := by
  classical
  obtain ⟨K, hKirr, hKcl⟩ := T
  change K = _ at hT
  subst hT
  have hres := hr.isResolution
  have : MMP.Mori.IsVariety ℂ sY := hres.1
  have : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  have : IsIntegral Z := (inferInstance : MMP.Mori.IsVariety ℂ (r ≫ sY)).toIsIntegral
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hr.comp_eq]
    exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  set ι := E.1.idealSheaf.subschemeι
  set j := curveι ⟨_, hKirr, hKcl⟩ with hj
  have hrangej : Set.range j.base = r.base '' (E.1.support : Set Z) := range_curveι_base _
  have : IsIntegral E.1.idealSheaf.subscheme := E.1.integral
  have hrangeι : Set.range ι.base = (E.1.support : Set Z) := E.1.idealSheaf.range_subschemeι
  have hrangef : Set.range (ι ≫ r).base = r.base '' (E.1.support : Set Z) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrangeι]
  have hker : j.ker ≤ (ι ≫ r).ker := by
    rw [hj, Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine le_of_eq (congrArg _ (TopologicalSpace.Closeds.ext ?_))
    rw [TopologicalSpace.Closeds.coe_closure, hrangef, hKcl.closure_eq]
    rfl
  let p := IsClosedImmersion.lift j (ι ≫ r) hker
  have hp : p ≫ j = ι ≫ r := IsClosedImmersion.lift_fac _ _ _
  let : (curveScheme ⟨_, hKirr, hKcl⟩).Over (Spec (.of ℂ)) := ⟨j ≫ sY⟩
  have : IsIntegral (curveScheme ⟨_, hKirr, hKcl⟩) :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal ⟨_, hKcl⟩ hKirr
  have hpo : p ≫ j ≫ sY = E.1.idealSheaf.subscheme ↘ Spec (.of ℂ) := by
    change p ≫ j ≫ sY = ι ≫ (Z ↘ Spec (.of ℂ))
    rw [← Category.assoc, hp, Category.assoc, hr.comp_eq]
  have : p.IsOver (Spec (.of ℂ)) := ⟨hpo⟩
  have : Smooth (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    (MMP.Mori.isSmoothScheme_iff _).1 (hr.isSmoothScheme_component E)
  have : LocallyOfFiniteType ((curveScheme ⟨_, hKirr, hKcl⟩) ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (j ≫ sY)
    infer_instance
  have : QuasiCompact ((curveScheme ⟨_, hKirr, hKcl⟩) ↘ Spec (.of ℂ)) := by
    change QuasiCompact (j ≫ sY)
    infer_instance
  have : LocallyOfFiniteType (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (ι ≫ (Z ↘ Spec (.of ℂ)))
    infer_instance
  have : QuasiCompact (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change QuasiCompact (ι ≫ (Z ↘ Spec (.of ℂ)))
    infer_instance
  obtain ⟨U', hU'd, -, -, hfib⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := ℂ) p
  have : IsDominant p := ⟨(surjective_base_of_comp_eq j.isClosedEmbedding.injective hp
    (hrangej.trans hrangef.symm).le).denseRange⟩
  exact ⟨p, U', hp, hU'd, hU'd.nonempty, fun t ht ↦ (hfib inferInstance t ht).1⟩

/-- **Smooth general fibre components.** Over the closed points of an open `U` meeting the curve
`r(E)`, every surface component of the fibre of `E` is smooth over `ℂ`. -/
theorem IsCurvePointExceptionalModel.exists_opens_isSmoothScheme_maximal_fibre
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty ∧
      ∀ y ∈ (U : Set Y) ∩ r.base '' (E.1.support : Set Z), IsClosed {y} →
        ∀ G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          MMP.Mori.IsSmoothScheme (G.1.toScheme ↘ Spec (.of ℂ)) := by
  have : MMP.Mori.IsVariety ℂ sY := hr.isResolution.1
  have : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  let T : IrreducibleCloseds Y := ⟨_, isIrreducible_image_primeDivisor_support r E.1,
    r.isClosedMap _ E.1.idealSheaf.support.isClosed⟩
  obtain ⟨p, U', hp, -, hU', hfib⟩ := hr.exists_dense_smooth_fiber_curveScheme E T rfl
  obtain ⟨W, hW, hWT⟩ := exists_opens_forall_mem_inter_curve T U' hU'
  refine ⟨W, hW, fun y hy hyc G hG ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := hWT y hy
  obtain ⟨htc, hfibset⟩ :=
    isClosed_singleton_and_preimage_eq_of_comp_eq (curveι T).isClosedEmbedding.injective hp hyc
  have := hfib t ht
  rw [hfibset] at hG
  have hpo : p ≫ curveι T ≫ sY = E.1.idealSheaf.subscheme ↘ Spec (.of ℂ) := by
    change p ≫ curveι T ≫ sY = E.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ))
    rw [← Category.assoc, hp, Category.assoc, hr.comp_eq]
  exact (MMP.Mori.isSmoothScheme_iff _).2
    (smooth_of_maximal_preimage_singleton (curveι T ≫ sY) p hpo htc G.1 hG)

/-- If `P ×_Y Spec κ(t)` is reduced, where `P ⟶ E ⟶ B` and `j : B ⟶ Y` is a monomorphism, then
`G ×_E P` is reduced for every open subscheme `G` of the fibre `E_t`. -/
theorem isReduced_pullback_comp_fiberι {E B Y P G : Scheme.{0}} (p : E ⟶ B) (j : B ⟶ Y) [Mono j]
    (i : P ⟶ E) {t : B} (e : G ⟶ p.fiber t) [IsOpenImmersion e]
    (h : IsReduced (Limits.pullback (i ≫ p ≫ j) (B.fromSpecResidueField t ≫ j))) :
    IsReduced (Limits.pullback (e ≫ p.fiberι t) i) := by
  have h2 : IsReduced (Limits.pullback (i ≫ p) (B.fromSpecResidueField t)) := by
    rw [← Category.assoc] at h
    have φ := (IsPullback.of_isLimit (Limits.pullbackIsPullbackOfCompMono
        (i ≫ p) (B.fromSpecResidueField t) j)).isoPullback
    exact @isReduced_of_isOpenImmersion _ _ φ.hom (IsOpenImmersion.of_isIso (g := φ.hom)) h
  have h3 : IsReduced (Limits.pullback (p.fiberι t) i) := by
    have φ := (Limits.pullbackSymmetry _ _) ≪≫
      (Limits.pullbackRightPullbackFstIso p (B.fromSpecResidueField t) i)
    exact @isReduced_of_isOpenImmersion _ _ φ.hom (IsOpenImmersion.of_isIso (g := φ.hom)) h2
  exact isReduced_of_isOpenImmersion
    ((Limits.pullbackRightPullbackFstIso (p.fiberι t) i e).inv ≫
      Limits.pullback.snd e (Limits.pullback.fst (p.fiberι t) i))

/-- If `P ×_Y κ(t)` is reduced, where `P ⊆ E`, `p : E ⟶ B` has smooth fibre over the closed point
`t` and `j : B ⟶ Y` is a monomorphism, then `P ∩ G` is reduced for every subvariety `G` which is a
maximal irreducible subset of `p⁻¹(t)`. -/
theorem isReduced_comap_of_maximal_preimage_singleton {E B Y : Scheme.{0}} (p : E ⟶ B)
    (j : B ⟶ Y) [Mono j] (P : E.IdealSheafData) {t : B} (ht : IsClosed {t})
    [Smooth (p.fiberToSpecResidueField t)] (G : Subvariety E)
    (hG : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ p.base ⁻¹' {t}) (G.support : Set E))
    (h : IsReduced (Limits.pullback (P.subschemeι ≫ p ≫ j) (B.fromSpecResidueField t ≫ j))) :
    IsReduced (P.comap G.ι).subscheme := by
  obtain ⟨e, he, hfac⟩ := exists_isOpenImmersion_fiber_of_maximal p ht G hG
  have h4 := isReduced_pullback_comp_fiberι p j P.subschemeι e h
  rw [hfac] at h4
  exact isReduced_of_isOpenImmersion (P.comapIso G.ι).hom

/-- For a nonempty `K` and a closed `R`, some open `U` meets `K`, and `K ⊆ R` or `y ∉ R` for
every `y ∈ U`. -/
theorem exists_opens_inter_nonempty_and_subset_or_notMem {X : Type*} [TopologicalSpace X]
    {K R : Set X} (hK : K.Nonempty) (hR : IsClosed R) :
    ∃ U : TopologicalSpace.Opens X, ((U : Set X) ∩ K).Nonempty ∧ ∀ y ∈ (U : Set X), K ⊆ R ∨ y ∉ R := by
  by_cases hKR : K ⊆ R
  · obtain ⟨y, hy⟩ := hK
    exact ⟨⊤, ⟨y, trivial, hy⟩, fun _ _ ↦ Or.inl hKR⟩
  · obtain ⟨y, hyK, hyR⟩ := Set.not_subset.1 hKR
    exact ⟨⟨Rᶜ, hR.isOpen_compl⟩, ⟨y, hyR, hyK⟩, fun y hy ↦ Or.inr hy⟩

/-- On an integral threefold over `ℂ`, the generic point of a prime divisor has height two. -/
theorem height_genericPoint_primeDivisor_eq_two {E : Scheme.{0}} [E.Over (Spec (.of ℂ))]
    [IsIntegral E] [LocallyOfFiniteType (E ↘ Spec (.of ℂ))]
    (hE3 : topologicalKrullDim E = ((3 : ℕ) : WithBot ℕ∞)) (P : MMP.Mori.PrimeDivisor E) :
    Order.height P.genericPoint = 2 := by
  have h := height_add_coheight_eq_of_topologicalKrullDim_eq hE3 P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h
  have : Order.height P.genericPoint ≠ ⊤ := fun h' ↦ by
    rw [h', top_add] at h
    simp at h
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 this
  rw [← ha] at h ⊢
  have : a + 1 = 3 := by exact_mod_cast h
  rw [show a = 2 by omega]
  rfl

/-- **A general fibre component is not contained in a prime divisor.** Let `E` be an integral
threefold over `ℂ`, `f : E ⟶ Y`, `K ⊆ Y` a curve and `P` a prime divisor of `E` with image `R`
in `Y`. If `K ⊆ R` or `y ∉ R`, no surface `G` which is a maximal irreducible subset of `f⁻¹(y)`
lies in `P`. -/
theorem not_support_subset_primeDivisor_of_maximal {E Y : Scheme.{0}} [E.Over (Spec (.of ℂ))]
    [IsIntegral E] [LocallyOfFiniteType (E ↘ Spec (.of ℂ))]
    (hE3 : topologicalKrullDim E = ((3 : ℕ) : WithBot ℕ∞)) (f : E ⟶ Y) {K : Set Y}
    (hK : topologicalKrullDim K = 1) (P : MMP.Mori.PrimeDivisor E) {y : Y}
    (hy : K ⊆ Set.range (P.idealSheaf.subschemeι ≫ f).base ∨
      y ∉ Set.range (P.idealSheaf.subschemeι ≫ f).base)
    (G : {V : Subvariety E // V.HasDim 2})
    (hG : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ f.base ⁻¹' {y}) (G.1.support : Set E)) :
    ¬ (G.1.support : Set E) ⊆ (P.support : Set E) := by
  intro hGP
  have hPr : (P.support : Set E) = Set.range P.idealSheaf.subschemeι.base :=
    (P.idealSheaf.range_subschemeι).symm
  rcases hy with hKR | hyR
  · by_cases heq : (G.1.support : Set E) = P.support
    · have hRy : Set.range (P.idealSheaf.subschemeι ≫ f).base ⊆ {y} := by
        rintro _ ⟨q, rfl⟩
        have hq : P.idealSheaf.subschemeι.base q ∈ (G.1.support : Set E) := by
          rw [heq, hPr]
          exact ⟨q, rfl⟩
        exact hG.1.2 hq
      have : Subsingleton K := (Set.subsingleton_singleton.anti (hKR.trans hRy)).coe_sort
      have h0 := @topologicalKrullDim_zero_of_discreteTopology K _ Subsingleton.discreteTopology
      rw [hK] at h0
      exact absurd h0 (by decide)
    · have hle : G.1.genericPoint ≤ P.genericPoint := by
        change P.genericPoint ⤳ G.1.genericPoint
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        refine hGP ?_
        rw [← Subvariety.closure_genericPoint]
        exact subset_closure rfl
      have hnge : ¬ P.genericPoint ≤ G.1.genericPoint := by
        intro hge
        apply heq
        refine le_antisymm hGP ?_
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        have hm := specializes_iff_mem_closure.1 hge
        rw [Subvariety.closure_genericPoint] at hm
        exact closure_minimal (Set.singleton_subset_iff.2 hm) G.1.ideal.support.isClosed
      have hG2 : Order.height G.1.genericPoint = 2 := by
        have hd := Subvariety.dim_eq_height_genericPoint G.1
        have h2 : G.1.dim = ((2 : ℕ) : WithBot ℕ∞) := (hasDim_natCast_iff 2).1 G.2
        rw [h2] at hd
        exact (WithBot.coe_injective hd).symm
      have hlt := Order.height_strictMono (lt_of_le_not_ge hle hnge) (by rw [hG2]; decide)
      rw [hG2, height_genericPoint_primeDivisor_eq_two hE3 P] at hlt
      exact lt_irrefl _ hlt
  · obtain ⟨g⟩ := (inferInstance : Nonempty G.1.toScheme)
    have hgG : G.1.ι.base g ∈ (G.1.support : Set E) := by
      rw [Subvariety.support_eq, ← G.1.ideal.range_subschemeι]
      exact ⟨g, rfl⟩
    obtain ⟨q, hq⟩ : G.1.ι.base g ∈ Set.range P.idealSheaf.subschemeι.base := by
      rw [← hPr]
      exact hGP hgG
    apply hyR
    refine ⟨q, ?_⟩
    have := hG.1.2 hgG
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hq]
    exact this

open Classical in
/-- **The restriction of a prime divisor to a surface meeting it in a reduced curve.** Let `G` be
an integral complex surface in `X`, `A` an effective Cartier divisor on `X` with closed subscheme
a prime divisor `P ⊉ G`, and suppose `P ∩ G` is reduced. Then `𝒪_X(A)|_G` is the sheaf of the
Cartier divisor `A|_G`, whose Weil divisor `W` is the sum of the curves of `P ∩ G`, with
multiplicity one; its class is the sum of their classes. -/
theorem exists_restrict_of_isReduced {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (G : Subvariety X) [LocallyOfFiniteType (G.toScheme ↘ Spec (.of ℂ))]
    [QuasiCompact (G.toScheme ↘ Spec (.of ℂ))] (hdimG : topologicalKrullDim G.toScheme = 2)
    {A : X.CartierDivisor} (hAe : MMP.Intersection.IsEffective A) (P : MMP.Mori.PrimeDivisor X)
    (hsub : MMP.CartierDivisor.subscheme A hAe = P.idealSheaf)
    (hGP : ¬ (G.support : Set X) ⊆ (P.support : Set X))
    (hred : IsReduced (P.idealSheaf.comap G.ι).subscheme) :
    ∃ (D' : G.toScheme.CartierDivisor) (W : Divisor G.toScheme),
      Nonempty ((Scheme.Modules.pullback G.ι).obj (MMP.CartierDivisor.sheaf A) ≅
        MMP.CartierDivisor.sheaf D') ∧
      MMP.Intersection.IsWeilDivisorOfCartier D' W ∧
      Chow.rationalCycleClass G.toScheme 1
          (Finsupp.linearCombination ℚ (fun Q : MMP.Mori.PrimeDivisor G.toScheme =>
            if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction
                (G.toScheme ↘ Spec (.of ℂ)) Q.genericPoint = ((1 : ℕ) : ℤ) then
              Chow.rationalPointCycle (fieldChowSituation ℂ) (G.toScheme ↘ Spec (.of ℂ))
                ((1 : ℕ) : ℤ) Q.genericPoint h else 0) (MMP.Mori.Divisor.toQDivisor W)) =
        ∑ᶠ (x : {x : G.toScheme // relativeDimension (fieldChowSituation ℂ).dimensionFunction
            (G.toScheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
          (_ : Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ G.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2 := by
  have hD : ¬ Set.range G.ι.base ⊆ MMP.Intersection.cartierSupport A := by
    intro h
    apply hGP
    rw [Subvariety.support_eq, ← G.ideal.range_subschemeι]
    refine h.trans
      ((MMP.CartierDivisor.support_subset_support_subscheme hAe).trans ?_)
    rw [hsub]
  set J := (MMP.CartierDivisor.subscheme A hAe).comap G.ι with hJ
  have : IsReduced J.subscheme := by rwa [hJ, hsub]
  have : IsLocallyNoetherian G.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (G.toScheme ↘ Spec (.of ℂ))
  have : CompactSpace G.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (G.toScheme ↘ Spec (.of ℂ))
  have : IsNoetherian G.toScheme := ⟨⟩
  have hSdef : (J.support : Set G.toScheme) = G.ι.base ⁻¹' (P.support : Set _) := by
    rw [hJ, hsub, Scheme.IdealSheafData.support_comap]
    rfl
  have hSu : (J.support : Set G.toScheme) ≠ Set.univ := by
    intro h
    apply hGP
    rw [Subvariety.support_eq, ← G.ideal.range_subschemeι]
    rintro _ ⟨g, rfl⟩
    have : g ∈ (J.support : Set G.toScheme) := h ▸ Set.mem_univ g
    rwa [hSdef] at this
  have hfinQ : {Q : MMP.Mori.PrimeDivisor G.toScheme |
      Q.genericPoint ∈ (J.support : Set G.toScheme)}.Finite := by
    refine MMP.Mori.finite_setOf_genericPoint_mem J.support.isClosed fun x hx h0 ↦ hSu ?_
    have hgen : x = genericPoint G.toScheme :=
      eq_genericPoint_of_isMax (Order.coheight_eq_zero.1 h0)
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec G.toScheme : closure {genericPoint G.toScheme} = Set.univ), ← hgen]
    exact closure_minimal (Set.singleton_subset_iff.2 hx) J.support.isClosed
  refine ⟨MMP.CartierDivisor.pullback G.ι A hD,
    ∑ Q ∈ hfinQ.toFinset, Finsupp.single Q 1,
    ⟨(MMP.CartierDivisor.pullbackSheafIso G.ι A hD).symm⟩, fun Q ↦ ?_, ?_⟩
  · convert isOrderAlong_pullback_of_isReduced G.ι hAe hD Q using 1
    rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq', Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq]
    rfl
  · rw [← hSdef]
    exact rationalCycleClass_sum_single_eq_finsum_maximal hdimG J.support.isClosed hSu _
      fun Q ↦ hfinQ.mem_toFinset

open Classical in
/-- **The restriction of one prime divisor to the general fibre components.** Over the closed
points `y` of an open `U` meeting `r(E)`, for every surface `G` which is a maximal irreducible
subset of the fibre `E_y`, the pull-back of `𝒪_E(π P)` to `G` is the sheaf of a Cartier divisor
whose Weil divisor `W` has class `∑_{C' ⊆ G ∩ P} [C']` in `H_2(G, ℚ)`. -/
theorem IsCurvePointExceptionalModel.exists_opens_restrict_primeDivisor
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support)
    (hE : topologicalKrullDim (r.base '' (E.1.support : Set Z)) = 1)
    (π : MMP.Mori.PrimeDivisor E.1.idealSheaf.subscheme → E.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π P) (Finsupp.single P 1))
    (P : MMP.Mori.PrimeDivisor E.1.idealSheaf.subscheme) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty ∧
      ∀ y ∈ (U : Set Y) ∩ r.base '' (E.1.support : Set Z), IsClosed {y} →
        ∀ G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          ∃ (D' : G.1.toScheme.CartierDivisor) (W : Divisor G.1.toScheme),
            Nonempty ((Scheme.Modules.pullback G.1.ι).obj (MMP.CartierDivisor.sheaf (π P)) ≅
              MMP.CartierDivisor.sheaf D') ∧
            MMP.Intersection.IsWeilDivisorOfCartier D' W ∧
            Chow.rationalCycleClass G.1.toScheme 1
                (Finsupp.linearCombination ℚ (fun Q : MMP.Mori.PrimeDivisor G.1.toScheme =>
                  if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction
                      (G.1.toScheme ↘ Spec (.of ℂ)) Q.genericPoint = ((1 : ℕ) : ℤ) then
                    Chow.rationalPointCycle (fieldChowSituation ℂ) (G.1.toScheme ↘ Spec (.of ℂ))
                      ((1 : ℕ) : ℤ) Q.genericPoint h else 0) (MMP.Mori.Divisor.toQDivisor W)) =
              ∑ᶠ (x : {x : G.1.toScheme //
                  relativeDimension (fieldChowSituation ℂ).dimensionFunction
                    (G.1.toScheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
                (_ : Maximal (fun A ↦ IsIrreducible A ∧
                    A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
                Chow.pointCycleClass ℚ x.1 x.2 := by
  have : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  have : MMP.Mori.IsVariety ℂ (r ≫ sY) := hr.isResolution.2.1
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hr.comp_eq]
    exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : IsIntegral E.1.idealSheaf.subscheme := E.1.integral
  have : LocallyOfFiniteType (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (E.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
  have hKirr := isIrreducible_image_primeDivisor_support r E.1
  let T : IrreducibleCloseds Y := ⟨_, hKirr, r.isClosedMap _ E.1.idealSheaf.support.isClosed⟩
  obtain ⟨p, U', hp, hU'd, -, hfib⟩ := hr.exists_dense_smooth_fiber_curveScheme E T rfl
  obtain ⟨V, hVne, hred⟩ := hr.exists_nonempty_open_isReduced_pullback T hE E P
  obtain ⟨t₀, htV, htU⟩ := hU'd.inter_open_nonempty V V.isOpen hVne
  obtain ⟨W, hW, hWT⟩ := exists_opens_forall_mem_inter_curve T (U' ⊓ V) ⟨t₀, htU, htV⟩
  obtain ⟨U₂, hU₂ne, hU₂⟩ := exists_opens_inter_nonempty_and_subset_or_notMem hKirr.nonempty
    (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r).isClosedMap.isClosed_range
  refine ⟨W ⊓ U₂, inter_inter_nonempty_of_irreducibleCloseds T hW hU₂ne,
    fun y hy hyc G hG ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := hWT y ⟨hy.1.1, hy.2⟩
  obtain ⟨htc, hfibset⟩ :=
    isClosed_singleton_and_preimage_eq_of_comp_eq (curveι T).isClosedEmbedding.injective hp hyc
  have := hfib t ht.1
  have hG' := hG
  rw [hfibset] at hG'
  have h1 : IsReduced (Limits.pullback (P.idealSheaf.subschemeι ≫ p ≫ curveι T)
      ((curveScheme T).fromSpecResidueField t ≫ curveι T)) := by
    have := hred _ ((curveScheme T).fromSpecResidueField t) fun z hz ↦ by
      rw [Set.mem_singleton_iff.1 (((curveScheme T).range_fromSpecResidueField t).le hz)]
      exact ht.2
    rwa [← hp] at this
  have h5 := isReduced_comap_of_maximal_preimage_singleton p (curveι T) P.idealSheaf htc G.1 hG' h1
  have := hr.isVariety_component E
  obtain ⟨hAe, hsub⟩ := (hπ P).isEffective_and_subscheme_eq_of_isSmoothScheme _
    (hr.isSmoothScheme_component E)
  have hGP := not_support_subset_primeDivisor_of_maximal
    (hr.topologicalKrullDim_component_eq_three E) (E.1.idealSheaf.subschemeι ≫ r) hE P
    (hU₂ _ hy.1.2) G hG
  have : LocallyOfFiniteType (G.1.toScheme ↘ Spec (.of ℂ)) := inferInstanceAs
    (LocallyOfFiniteType (G.1.ι ≫ E.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
  have : QuasiCompact (G.1.toScheme ↘ Spec (.of ℂ)) := inferInstanceAs
    (QuasiCompact (G.1.ι ≫ E.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
  exact exists_restrict_of_isReduced G.1 ((hasDim_natCast_iff 2).1 G.2) hAe P hsub hGP h5

open Classical in
/-- **The restriction of divisors to the general fibre components.** Let `r : Z ⟶ Y` be a
curve-and-point exceptional model, `E` a component of `F` mapping onto a curve, `π P` a Cartier
divisor on `E` with Weil divisor `P` for each prime divisor `P` of `E`, and `S` a finite set of
prime divisors of `E`. Over the closed points `y` of an open `U` meeting `r(E)`, every component
`G` of the fibre `E_y` is a smooth projective surface, and for `P ∈ S` the restriction of
`𝒪_E(π P)` to `G` is the sheaf of a Cartier divisor whose Weil divisor `W` has class
`∑_{C' ⊆ G ∩ P} [C']` in `H_2(G, ℚ)`, `C'` running over the maximal irreducible subsets of
`G ∩ P`. -/
theorem IsCurvePointExceptionalModel.exists_opens_restrict_maximal_fibre
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support)
    (hE : topologicalKrullDim (r.base '' (E.1.support : Set Z)) = 1)
    (π : MMP.Mori.PrimeDivisor E.1.idealSheaf.subscheme → E.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π P) (Finsupp.single P 1))
    (S : Finset (MMP.Mori.PrimeDivisor E.1.idealSheaf.subscheme)) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty ∧
      ∀ y ∈ (U : Set Y) ∩ r.base '' (E.1.support : Set Z), IsClosed {y} →
        ∀ G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          MMP.Mori.IsProjectiveVariety ℂ (G.1.toScheme ↘ Spec (.of ℂ)) ∧
          MMP.Mori.IsSmoothScheme (G.1.toScheme ↘ Spec (.of ℂ)) ∧
          ∀ P ∈ S, ∃ (D' : G.1.toScheme.CartierDivisor) (W : Divisor G.1.toScheme),
            Nonempty ((Scheme.Modules.pullback G.1.ι).obj (MMP.CartierDivisor.sheaf (π P)) ≅
              MMP.CartierDivisor.sheaf D') ∧
            MMP.Intersection.IsWeilDivisorOfCartier D' W ∧
            Chow.rationalCycleClass G.1.toScheme 1
                (Finsupp.linearCombination ℚ (fun Q : MMP.Mori.PrimeDivisor G.1.toScheme =>
                  if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction
                      (G.1.toScheme ↘ Spec (.of ℂ)) Q.genericPoint = ((1 : ℕ) : ℤ) then
                    Chow.rationalPointCycle (fieldChowSituation ℂ) (G.1.toScheme ↘ Spec (.of ℂ))
                      ((1 : ℕ) : ℤ) Q.genericPoint h else 0) (MMP.Mori.Divisor.toQDivisor W)) =
              ∑ᶠ (x : {x : G.1.toScheme //
                  relativeDimension (fieldChowSituation ℂ).dimensionFunction
                    (G.1.toScheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
                (_ : Maximal (fun A ↦ IsIrreducible A ∧
                    A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
                Chow.pointCycleClass ℚ x.1 x.2 := by
  have : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  let T : IrreducibleCloseds Y := ⟨_, isIrreducible_image_primeDivisor_support r E.1,
    r.isClosedMap _ E.1.idealSheaf.support.isClosed⟩
  obtain ⟨U₀, hU₀, hsm⟩ := hr.exists_opens_isSmoothScheme_maximal_fibre E
  obtain ⟨U₁, hU₁, hres⟩ := exists_forall_of_finite T _
    (fun P : S ↦ hr.exists_opens_restrict_primeDivisor E hE π hπ P.1)
  refine ⟨U₀ ⊓ U₁, inter_inter_nonempty_of_irreducibleCloseds T hU₀ hU₁,
    fun y hy hyc G hG ↦ ?_⟩
  have hGs := hsm y ⟨hy.1.1, hy.2⟩ hyc G hG
  exact ⟨hr.isProjectiveVariety_subvariety E G.1, hGs,
    fun P hP ↦ hres y ⟨hy.1.2, hy.2⟩ ⟨P, hP⟩ hyc G hG⟩

end Fibre

end MMP.Fourfold
