module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.SurfaceBirationalSimplicial
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
import MMP.AlgebraicGeometry.MMP.Contraction.CurveFactorization
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart
import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeRhoOne
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Contraction.ExceptionalDivisorNegativeOnRay
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.ProjectiveBundle.UniversalProperty
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Contraction.Existence
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialQFactorial
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialContractionKlt
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# thm mmp surface real birational model

Chain fold of: `thm_mmp_surface_real_birational_model`.
-/

/-! ### `thm_mmp_surface_real_birational_model` -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fold06.ThmMmpSurfaceRealBirationalModel

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori

section Infrastructure

open Order

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- On an integral surface over `ℂ`, the dimension of the closure of a point plus its coheight
is two. -/
private theorem dim_closure_add_coheight [IsIntegral X] (hX : IsNormalVariety ℂ sX)
    (hd : topologicalKrullDim X = 2) (x : X) :
    topologicalKrullDim (closure {x} : Set X) + (Order.coheight x : WithBot ℕ∞) = 2 := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  rw [MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x, hd]

/-- On an integral surface every point has coheight at most two. -/
private theorem coheight_le_two [IsIntegral X] (hX : IsNormalVariety ℂ sX)
    (hd : topologicalKrullDim X = 2) (x : X) : Order.coheight x ≤ 2 := by
  have h := dim_closure_add_coheight hX hd x
  have h0 : 0 ≤ topologicalKrullDim (closure {x} : Set X) :=
    Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨x, subset_closure rfl⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h2 : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_ofNat]; exact h ▸ le_add_of_nonneg_left h0
  exact WithBot.coe_le_coe.mp h2

/-- On an integral surface a point of coheight at least two is closed. -/
private theorem isClosed_singleton_of_two_le_coheight [IsIntegral X] (hX : IsNormalVariety ℂ sX)
    (hd : topologicalKrullDim X = 2) {x : X} (hx : 2 ≤ Order.coheight x) :
    IsClosed ({x} : Set X) := by
  refine closure_subset_iff_isClosed.mp fun y hy => ?_
  by_contra hne
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hlt : y < x := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hxy) fun h =>
    hne (hxy.antisymm (Scheme.le_iff_specializes.1 h)).eq.symm
  have h1 := Order.coheight_add_one_le hlt
  have h2 := coheight_le_two hX hd y
  have h3 : (2 : ℕ∞) + 1 ≤ 2 := (add_le_add hx le_rfl).trans (h1.trans h2)
  exact absurd h3 (by decide)

/-- On an integral surface a closed point has coheight two. -/
private theorem coheight_eq_two_of_isClosed [IsIntegral X] (hX : IsNormalVariety ℂ sX)
    (hd : topologicalKrullDim X = 2) {x : X} (hx : IsClosed ({x} : Set X)) :
    Order.coheight x = 2 := by
  have h := dim_closure_add_coheight hX hd x
  rw [hx.closure_eq] at h
  have h0 : topologicalKrullDim ({x} : Set X) ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
  have h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight x : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_ofNat, ← h]
    exact (add_le_add h0 le_rfl).trans_eq (zero_add _)
  exact le_antisymm (coheight_le_two hX hd x) (WithBot.coe_le_coe.mp h2)

/-- A proper morphism of integral surfaces maps points of coheight two to points of coheight
two. -/
private theorem two_le_coheight_map {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral X]
    [IsIntegral Y] (hX : IsNormalVariety ℂ sX) (hXd : topologicalKrullDim X = 2)
    (hY : IsNormalVariety ℂ sY) (hYd : topologicalKrullDim Y = 2) (f : X ⟶ Y) [IsProper f]
    {x : X} (hx : 2 ≤ Order.coheight x) : 2 ≤ Order.coheight (f x) := by
  have hc := isClosed_singleton_of_two_le_coheight hX hXd hx
  have : IsClosed ({f x} : Set Y) := by
    rw [← Set.image_singleton]; exact f.isClosedMap _ hc
  exact (coheight_eq_two_of_isClosed hY hYd this).ge

end Infrastructure

section Divisors

variable {X Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}

/-- On a surface, a prime divisor is exceptional for a proper birational morphism `φ` exactly when
its image is a point of coheight two. -/
private theorem isExceptionalPrimeDivisor_iff [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] (hY : IsNormalVariety ℂ sY) (hYd : topologicalKrullDim Y = 2) (φ : X ⟶ Y)
    (hX : IsNormalVariety ℂ (φ ≫ sY)) (hφ : IsBirationalMorphism φ) [IsProper φ]
    (P : MMP.Mori.PrimeDivisor X) :
    MMP.Flips.IsExceptionalPrimeDivisor sY φ P ↔ 2 ≤ Order.coheight (φ P.genericPoint) := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (φ P.genericPoint)
  rw [hYd, show (2 : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) from rfl] at hd
  constructor
  · rintro ⟨hY', hf, hp, hexc⟩
    unfold MMP.Flips.ProperDivisorOver.IsExceptional at hexc
    rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
      MMP.Mori.DivisorOver.center_eq_closure_genericPoint, hYd,
      show (2 : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) from rfl] at hexc
    exact (Oai4C1.Negativity.withBot_add_two_le_iff hd).mp hexc
  · intro h
    refine ⟨hX, hφ, inferInstance, ?_⟩
    unfold MMP.Flips.ProperDivisorOver.IsExceptional
    rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
      MMP.Mori.DivisorOver.center_eq_closure_genericPoint, hYd,
      show (2 : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) from rfl]
    exact (Oai4C1.Negativity.withBot_add_two_le_iff hd).mpr h

/-- For a proper birational morphism `f` of normal varieties with `f(η_P) = η_Q`, the coefficient
of `Q` in `f_* D` is the coefficient of `P` in `D`. -/
private theorem transformDivisor_apply_of_map_genericPoint [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : IsNormalVariety ℂ sY) {f : X ⟶ Y}
    (hX : IsNormalVariety ℂ (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (h : f P.genericPoint = Q.genericPoint) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor f.toRationalMap D Q = D P := by
  have : IsSeparated sY := hY.1.toIsSeparated
  have := isSeparated_toTerminal_of_isNormalVariety hY
  obtain ⟨E, -, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hf Q
  have key := htr (Finsupp.single P (1 : ℤ))
  rw [MMP.Mori.RationalMap.transformDivisor_single_of_eq_some
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr h)] at key
  have hEP : E = P := by
    by_contra hne
    simp [Finsupp.single_apply, Ne.symm hne] at key
  rw [htr, hEP]

/-- Transforms of divisors along composites of proper birational morphisms of normal
varieties. -/
private theorem transformDivisor_comp {X₁ : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety ℂ sY) {g : X ⟶ X₁} {φ : X₁ ⟶ Y}
    (hX₁ : IsNormalVariety ℂ (φ ≫ sY)) (hX : IsNormalVariety ℂ (g ≫ φ ≫ sY)) [IsProper g]
    [IsProper φ] (hg : IsBirationalMorphism g) (hφ : IsBirationalMorphism φ)
    (hgφ : IsBirationalMorphism (g ≫ φ)) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor (g ≫ φ).toRationalMap D =
      MMP.Mori.RationalMap.transformDivisor φ.toRationalMap
        (MMP.Mori.RationalMap.transformDivisor g.toRationalMap D) := by
  refine Finsupp.ext fun Q => ?_
  obtain ⟨Q₁, hQ₁, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hY hX₁ hφ Q
  obtain ⟨P, hP, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ (f := g) hX hg Q₁
  have hX' : IsNormalVariety ℂ ((g ≫ φ) ≫ sY) := by rwa [Category.assoc]
  rw [transformDivisor_apply_of_map_genericPoint hY hX' hgφ (P := P)
      (by rw [Scheme.Hom.comp_apply, hP, hQ₁]) D,
    transformDivisor_apply_of_map_genericPoint hY hX₁ hφ hQ₁,
    transformDivisor_apply_of_map_genericPoint hX₁ hX hg hP]

/-- The transform along the identity is the identity. -/
private theorem transformDivisor_id [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor (Scheme.Hom.toRationalMap (𝟙 X)) D = D :=
  Finsupp.ext fun P => transformDivisor_apply_of_map_genericPoint hX (f := 𝟙 X)
    (by rwa [Category.id_comp]) (isBirationalMorphism_of_isIso _) rfl D

/-- An `ℝ`-divisor that is a combination of Cartier divisors is `ℝ`-Cartier in the coefficient
sense. -/
private theorem isRCartier_of_isCartierCombination [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} (hD : MMP.Flips.IsCartierCombination D) : RDivisor.IsRCartier D := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  refine ⟨m, r, L, hL, fun Γ => ?_⟩
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, DivisorWithCoeffs.mapCoeffs]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isQFactorial [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : IsQFactorial sY) (D : RDivisor Y) : MMP.Flips.IsCartierCombination D := by
  classical
  choose m hm hc using fun P : MMP.Mori.PrimeDivisor Y => hY.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨_, fun j => D (e.symm j) / m (e.symm j),
    fun j => ((m (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor Y) 1,
    fun j => hc _, ?_⟩
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  have hterm : ∀ P : MMP.Mori.PrimeDivisor Y, (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)) =
        Finsupp.single P (D P) := by
    intro P
    ext Q
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : P = Q
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply, div_mul_cancel₀ _ hm0]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  rw [Equiv.sum_comp e.symm (fun P : D.support => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single (P : MMP.Mori.PrimeDivisor Y) 1 :
        Divisor Y)))]
  rw [Finset.sum_coe_sort D.support (fun P => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)))]
  simp_rw [hterm]
  exact (Finsupp.sum_single D).symm

/-- The pull-back along the identity. -/
private theorem isRCartierPullback_id [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {D : RDivisor X} (hD : MMP.Flips.IsCartierCombination D) :
    MMP.Flips.IsRCartierPullback (𝟙 X) D D := by
  obtain ⟨G, hG, -⟩ := MMP.Flips.existsUnique_isRCartierPullback (𝟙 X) hD
  have hGD : G = D := Finsupp.ext fun P =>
    MMP.Fourfold.coeff_eq_of_isRCartierPullback P P rfl hG
  rwa [hGD] at hG

end Divisors

section Pullbacks

/-- A point of an irreducible space lies in each of its irreducible components. -/
private theorem mem_irreducibleComponent' {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 :=
  (Set.eq_univ_of_univ_subset
    (W.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _))).symm ▸ Set.mem_univ t

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent'
    (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent' (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Pulling a pull-back back once more.** If `g^*M = D` and `f` is dominant, then `D` has a
pull-back `G` along `f` which is also the pull-back of `M` along `f ≫ g`; moreover `D` is
`ℝ`-Cartier. -/
private theorem exists_isRCartierPullback_comp {V W Z : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (f : V ⟶ W) [IsDominant f]
    (g : W ⟶ Z) [IsDominant g] {M : RDivisor Z} {D : RDivisor W}
    (hD : MMP.Flips.IsRCartierPullback g M D) :
    ∃ G : RDivisor V, MMP.Flips.IsRCartierPullback (f ≫ g) M G ∧
      MMP.Flips.IsRCartierPullback f D G ∧ MMP.Flips.IsCartierCombination D := by
  obtain ⟨m, r, L, L', hLc, hM, hpb, rfl⟩ := hD
  have hL'c : ∀ j, (L' j).IsCartier := fun j => ((hpb j).2).isCartier (hLc j)
  let L'' : Fin m → Divisor V := fun j =>
    (L' j).pullback (hL'c j) (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _)
  have hL'' : ∀ j, (L' j).IsPullback f
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _) (L'' j) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  refine ⟨∑ j, r j • Divisor.toRDivisor (L'' j), ⟨m, r, L, L'', hLc, hM, fun j =>
    ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (f ≫ g) _,
      isPullback_comp (hpb j).2 (hL'' j) _⟩, rfl⟩,
    ⟨m, r, L', L'', hL'c, rfl, fun j => ⟨_, hL'' j⟩, rfl⟩,
    ⟨m, r, L', hL'c, by simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩⟩

end Pullbacks

section Rational

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor along a dominant morphism is a `ℚ`-divisor. -/
private theorem exists_toRDivisor_eq_of_isRCartierPullback {T Y : Scheme.{0}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [IsLocallyNoetherian Y] [IsNormal Y]
    (h : T ⟶ Y) [IsDominant h] {D : QDivisor Y} (hD : D.IsQCartier) {G : RDivisor T}
    (hG : MMP.Flips.IsRCartierPullback h (QDivisor.toRDivisor D) G) :
    ∃ Gq : QDivisor T, QDivisor.toRDivisor Gq = G := by
  obtain ⟨m, hm, L, hL, hLc⟩ := hD.exists_pos
  have hB := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant h L
  have h' := MMP.Flips.isRCartierPullback_of_zsmul_eq h hm hLc hL.symm
    ⟨hB, Divisor.isPullback_pullback hLc hB⟩
  rw [MMP.Flips.IsRCartierPullback.eq h hG h']
  refine ⟨(1 / (m : ℚ)) • Divisor.toQDivisor (L.pullback hLc hB), ?_⟩
  ext E
  simp [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor]

end Rational

section Dimension

open Order

/-- The dimension of the reduced closed subscheme on `{x}⁻` is the height of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt {S : Scheme.{0}} (x : S) :
    topologicalKrullDim (curveSubschemeAt x) = (height x : WithBot ℕ∞) := by
  have h := MMP.Intersection.subvarietyDim_eq_height (MMP.Intersection.associatedSubvariety x)
  rw [MMP.Intersection.genericPoint_associatedSubvariety] at h
  exact h

/-- On an integral surface locally of finite type over `ℂ`, `height x + coheight x = 2`. -/
private theorem height_add_coheight_eq_two {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ))
    [IsIntegral S] [LocallyOfFiniteType f] (hdim : topologicalKrullDim S = 2) (x : S) :
    height x + coheight x = 2 := by
  letI : S.Over (Spec (.of ℂ)) := ⟨f⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType f›
  have hpure : MMP.Intersection.IsPureDimensional S 2 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ S).isHomeomorph.topologicalKrullDim_eq, hdim]
    rfl
  exact MMP.Intersection.height_add_coheight_eq_of_isPureDimensional ℂ hpure x

private theorem eq_one_of_add_eq_two {a b : ℕ∞} (h : a + b = 2) (hb : b = 1) : a = 1 := by
  subst hb
  exact WithTop.add_right_cancel ENat.one_ne_top (h.trans one_add_one_eq_two.symm)

/-- The generic point of a proper curve on a surface has coheight one. -/
private theorem coheight_point_eq_one {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) [IsIntegral S]
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim S = 2) (C : ProperCurve f) :
    coheight C.point = 1 := by
  have h := height_add_coheight_eq_two f hdim C.point
  have h1 : height C.point = 1 := by
    have := C.dim_eq
    rw [topologicalKrullDim_curveSubschemeAt] at this
    exact_mod_cast this
  rw [add_comm] at h
  exact eq_one_of_add_eq_two h h1

/-- The generic point of a prime divisor on a proper surface is the generic point of a proper
curve. -/
private theorem isProperCurve_genericPoint {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) [IsProper f]
    [IsIntegral S] [LocallyOfFiniteType f] (hdim : topologicalKrullDim S = 2)
    (P : MMP.Mori.PrimeDivisor S) : IsProperCurve f P.genericPoint := by
  refine isProperCurve_of_isProper f ?_
  rw [topologicalKrullDim_curveSubschemeAt]
  have h := height_add_coheight_eq_two f hdim P.genericPoint
  rw [eq_one_of_add_eq_two h (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)]
  rfl

end Dimension

section OffExceptional

/-- Away from a prime divisor `C` with `Ex(g) = C`, the morphism `g` is a local isomorphism at the
generic point of every prime divisor, which it maps to the generic point of a prime divisor. -/
private theorem exists_genericPoint_eq_of_ne {X X₁ : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {g : X ⟶ X₁} {C : MMP.Mori.PrimeDivisor X}
    (hC : (MMP.Mori.exceptionalSet g : Set X) = C.support) {P : MMP.Mori.PrimeDivisor X}
    (hP : P ≠ C) :
    ∃ P₁ : MMP.Mori.PrimeDivisor X₁, g P.genericPoint = P₁.genericPoint ∧
      IsIso (g.stalkMap P.genericPoint) := by
  have hmem : g P.genericPoint ∈ MMP.Mori.biregularLocus g := by
    by_contra h
    have h' : P.genericPoint ∈ (MMP.Mori.exceptionalSet g : Set X) :=
      MMP.Mori.mem_exceptionalSet.mpr h
    rw [hC] at h'
    exact hP (MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support h').symm
  have hcoh : Order.coheight (g P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus g hmem,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm,
    MMP.isIso_stalkMap_of_mem_biregularLocus g hmem⟩

/-- Off the exceptional curve `C` of `g`, the coefficients of `(K + Δ) - G`, for `G` a pull-back
of `M` along `g`, are those of `(g_* K + g_* Δ) - M`. -/
private theorem exists_coeff_sub_eq_of_ne {X X₁ : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian X₁] [IsNormal X₁]
    {sX₁ : X₁ ⟶ Spec (.of ℂ)} (hX₁ : IsNormalVariety ℂ sX₁) {g : X ⟶ X₁}
    (hX : IsNormalVariety ℂ (g ≫ sX₁)) [IsProper g] (hg : IsBirationalMorphism g)
    {C : MMP.Mori.PrimeDivisor X} (hC : (MMP.Mori.exceptionalSet g : Set X) = C.support)
    (K : Divisor X) (Δ : RDivisor X) {M : RDivisor X₁} {G : RDivisor X}
    (hG : MMP.Flips.IsRCartierPullback g M G) {P : MMP.Mori.PrimeDivisor X} (hP : P ≠ C) :
    ∃ P₁ : MMP.Mori.PrimeDivisor X₁, g P.genericPoint = P₁.genericPoint ∧
      (MMP.Flips.logCanonicalDivisor K Δ - G).coeff P =
        (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor g.toRationalMap K)
          (MMP.Mori.RationalMap.transformDivisor g.toRationalMap Δ) - M).coeff P₁ := by
  obtain ⟨P₁, hP₁, _⟩ := exists_genericPoint_eq_of_ne hC hP
  refine ⟨P₁, hP₁, ?_⟩
  rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub,
    MMP.Fourfold.coeff_eq_of_isRCartierPullback P P₁ hP₁ hG]
  simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
  simp only [DivisorWithCoeffs.coeff_apply,
    transformDivisor_apply_of_map_genericPoint hX₁ hX hg hP₁]

end OffExceptional

section Degrees

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{0}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [Oai4C1.Negativity.degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = x`, for some presentation of `D` by Cartier divisors. -/
private def HasDeg (D : RDivisor X) (C : ProperCurve sX) (x : ℝ) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), IsRIntersectionNumber k sX D r L C x

variable {k sX}

private theorem HasDeg.unique {D : RDivisor X} {C : ProperCurve sX} {x y : ℝ}
    (hx : HasDeg k sX D C x) (hy : HasDeg k sX D C y) : x = y := by
  obtain ⟨m, r, L, hx⟩ := hx
  obtain ⟨m', r', L', hy⟩ := hy
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 D r L r' L' x y hx hy

private theorem HasDeg.add_smul {D₁ D₂ : RDivisor X} {C : ProperCurve sX} {x₁ x₂ : ℝ}
    (h₁ : HasDeg k sX D₁ C x₁) (h₂ : HasDeg k sX D₂ C x₂) (a b : ℝ) :
    HasDeg k sX (a • D₁ + b • D₂) C (a * x₁ + b * x₂) := by
  obtain ⟨m₁, r₁, L₁, h₁⟩ := h₁
  obtain ⟨m₂, r₂, L₂, h₂⟩ := h₂
  exact ⟨_, _, _, (IsRIntersectionNumber.eq_and_linear k sX C).2 D₁ D₂ r₁ L₁ r₂ L₂ x₁ x₂ a b h₁ h₂⟩

private theorem HasDeg.congr {D D' : RDivisor X} {C : ProperCurve sX} {x x' : ℝ}
    (h : HasDeg k sX D C x) (hD : D = D') (hx : x = x') : HasDeg k sX D' C x' := hD ▸ hx ▸ h

/-- If `D - G = a P` with `D · C < 0`, `P · C < 0` and `G · C = 0`, then `0 < a`. -/
private theorem pos_of_hasDeg_sub_eq_single {D G : RDivisor X} {C : ProperCurve sX} {P : _}
    {a x e : ℝ} (hD : HasDeg k sX D C x) (hx : x < 0)
    (hP : HasDeg k sX (Finsupp.single P 1) C e) (he : e < 0) (hG : HasDeg k sX G C 0)
    (hDG : D - G = Finsupp.single P a) : 0 < a := by
  have := hD.unique <| (hP.add_smul hG a 1).congr
    (by rw [one_smul, Finsupp.smul_single, smul_eq_mul, mul_one, ← hDG, sub_add_cancel]) rfl
  by_contra hna
  push Not at hna
  nlinarith

/-- `∑ r_j L_j · C = ∑ r_j deg_C 𝒪(L_j)`. -/
private theorem hasDeg_sum (C : ProperCurve sX) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) :
    HasDeg k sX (∑ j, r j • Divisor.toRDivisor (L j)) C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨m, r, L, hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

/-- An `ℝ`-Cartier divisor has an intersection number with every proper curve. -/
private theorem exists_hasDeg {D : RDivisor X} (hD : IsCartierCombination D) (C : ProperCurve sX) :
    ∃ x, HasDeg k sX D C x := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  refine ⟨_, (hasDeg_sum C r L hL).congr ?_ rfl⟩
  simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]

/-- The intersection number of a `ℚ`-Cartier `ℚ`-divisor in the sense of Kollár–Mori is its
intersection number as an `ℝ`-Cartier divisor. -/
private theorem hasDeg_toRDivisor {D : QDivisor X} (hD : D.IsQCartier) (C : ProperCurve sX) :
    HasDeg k sX (QDivisor.toRDivisor D) C (D.intersectionNumber k sX C.ι C.dim_le hD : ℝ) := by
  obtain ⟨E, hE, hEc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hD
  have hm := QDivisor.cartierIndex_pos hD
  set m := D.cartierIndex hD
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD E hEc hE]
  refine (hasDeg_sum C ![1 / (m : ℝ)] ![E] (fun j => by fin_cases j; exact hEc)).congr ?_ ?_
  · ext P
    have h := congrArg (fun G : QDivisor X => G.coeff P) hE
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toRDivisor, smul_eq_mul, QDivisor.coeff_toRDivisor]
    have h' : ((E.coeff P : ℚ) : ℝ) = (m : ℝ) * ((D.coeff P : ℚ) : ℝ) := by
      rw [h]; push_cast; ring
    rw [show ((E.coeff P : ℤ) : ℝ) = ((E.coeff P : ℚ) : ℝ) by push_cast; rfl, h']
    field_simp
  · simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    push_cast
    ring

end Degrees

section Vertices

open MMP.Flips Filter _root_.Topology

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- A non-nef `ℝ`-Cartier divisor is negative on some contracted proper curve. -/
private theorem exists_properCurve_hasDeg_neg {Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [QuasiCompact sX] {f : X ⟶ Y} {D : RDivisor X} (hD : IsCartierCombination D)
    (hnef : ¬ IsRelativelyNef ℂ sX f D) :
    ∃ C : ProperCurve sX, C.IsContractedBy f ∧ ∃ x < 0, HasDeg ℂ sX D C x := by
  obtain ⟨m, r, L, hL, hDeq⟩ := hD
  by_contra h
  push Not at h
  refine hnef ⟨m, r, L, hL, by simpa only [← MMP.Flips.toRDivisor_eq_mapCoeffs] using hDeq,
    fun C hC x hx => ?_⟩
  by_contra hx0
  exact h C hC x (lt_of_not_ge hx0) ⟨m, r, L, hx⟩

/-- Intersection numbers of finite combinations. -/
private theorem hasDeg_finset_sum [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (D : ι → RDivisor X) (C : ProperCurve sX)
    (x : ι → ℝ) (h : ∀ i ∈ s, HasDeg ℂ sX (D i) C (x i)) :
    HasDeg ℂ sX (∑ i ∈ s, c i • D i) C (∑ i ∈ s, c i * x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (hasDeg_sum (k := ℂ) C (Fin.elim0 : Fin 0 → ℝ) Fin.elim0 fun j => j.elim0)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have := (h i (Finset.mem_insert_self _ _)).add_smul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) (c i) 1
    simpa using this

open scoped Classical in
/-- The coefficient of `∑ᵢ yᵢ pᵢ` along `P`. -/
private theorem coeff_sum_single {ι : Type*} [Fintype ι] {R : Type*} [AddCommMonoid R]
    (p : ι → MMP.Mori.PrimeDivisor X) (y : ι → R) (P : MMP.Mori.PrimeDivisor X) :
    (∑ i, Finsupp.single (p i) (y i) : DivisorWithCoeffs R X).coeff P =
      ∑ i, if p i = P then y i else 0 := by
  classical
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- A divisor supported on the injective family `p` is the sum of its coefficients along `p`. -/
private theorem eq_sum_single_coeff {R : Type*} [AddCommMonoid R] {r : ℕ}
    {p : Fin r → MMP.Mori.PrimeDivisor X} (hp : Function.Injective p)
    {D : DivisorWithCoeffs R X}
    (hD : ∀ P, D.coeff P ≠ 0 → P ∈ Set.range p) :
    D = ∑ i, Finsupp.single (p i) (D.coeff (p i)) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum_of_support_subset D (s := Finset.univ.image p) (g := Finsupp.single)
    (fun P hP => by simpa using hD P (by simpa [DivisorWithCoeffs.coeff_apply] using hP))
    (fun _ _ => Finsupp.single_zero _), Finset.sum_image fun i _ j _ h => hp h]
  rfl

/-- Casting the coefficients of `∑ᵢ vᵢ pᵢ` from `ℚ` to `ℝ`. -/
private theorem toRDivisor_sum_single {r : ℕ} (p : Fin r → MMP.Mori.PrimeDivisor X)
    (v : Fin r → ℚ) :
    QDivisor.toRDivisor (∑ i, Finsupp.single (p i) (v i)) =
      ∑ i, Finsupp.single (p i) (v i : ℝ) := by
  classical
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => DivisorWithCoeffs.ext' fun P => ?_
  rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- Every neighbourhood `U` of `x ∈ ℝ^ι` contains a set `V` of rational vectors whose convex hull
is a neighbourhood of `x`: the vertices of a small rational box around `x`. -/
private theorem exists_rat_convexHull_mem_nhds {ι : Type*} [Fintype ι] {x : ι → ℝ}
    {U : Set (ι → ℝ)} (hU : U ∈ 𝓝 x) :
    ∃ V : Set (ι → ℝ), (∀ v ∈ V, v ∈ U ∧ ∃ q : ι → ℚ, v = fun i => (q i : ℝ)) ∧
      convexHull ℝ V ∈ 𝓝 x := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  choose a ha using fun i => exists_rat_btwn (show x i - ε < x i by linarith)
  choose b hb using fun i => exists_rat_btwn (show x i < x i + ε by linarith)
  refine ⟨Set.univ.pi fun i => {(a i : ℝ), (b i : ℝ)}, fun v hv => ⟨hball ?_, ?_⟩, ?_⟩
  · rw [ball_pi _ hε]
    intro i _
    show v i ∈ Metric.ball (x i) ε
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rcases hv i trivial with h | h
    · rw [h]; constructor <;> linarith [ha i, hb i]
    · rw [Set.mem_singleton_iff.mp h]; constructor <;> linarith [ha i, hb i]
  · refine ⟨fun i => if v i = (a i : ℝ) then a i else b i, funext fun i => ?_⟩
    rcases hv i trivial with h | h
    · simp [h]
    · rw [Set.mem_singleton_iff.mp h]
      dsimp only
      split_ifs with h'
      · rw [← h', Set.mem_singleton_iff.mp h]
      · rfl
  · rw [convexHull_pi]
    refine set_pi_mem_nhds Set.finite_univ fun i _ => ?_
    rw [convexHull_pair, segment_eq_Icc (by linarith [ha i, hb i])]
    exact Icc_mem_nhds (ha i).2 (hb i).1

/-- **Rational vertices.** A real klt boundary `Δ` on a `ℚ`-factorial projective variety with
`(K + Δ) · C < 0` is a convex combination of effective rational klt boundaries `Δᵢ` with
`(K + Δᵢ) · C < 0`: klt is open on the support of `Δ`, and so is the negativity on `C`. -/
private theorem exists_rational_vertices [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (K : Divisor X) {Δ : RDivisor X} (hΔ0 : ∀ P, 0 ≤ Δ.coeff P) (hklt : IsRealKltPair sX Δ)
    (C : ProperCurve sX) {x₀ : ℝ} (hx₀ : x₀ < 0)
    (hdeg : HasDeg ℂ sX (logCanonicalDivisor K Δ) C x₀) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (Δv : ι → QDivisor X), (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ Δ = ∑ i, w i • QDivisor.toRDivisor (Δv i) ∧
      ∀ i, (∀ P, 0 ≤ (Δv i).coeff P) ∧ IsRealKltPair sX (QDivisor.toRDivisor (Δv i)) ∧
        ∃ y < 0, HasDeg ℂ sX (logCanonicalDivisor K (QDivisor.toRDivisor (Δv i))) C y := by
  classical
  set S := Δ.support
  let e := S.equivFin
  let p : Fin S.card → MMP.Mori.PrimeDivisor X := fun j => (e.symm j : MMP.Mori.PrimeDivisor X)
  have hp : Function.Injective p := fun i j h => e.symm.injective (Subtype.ext h)
  have hpS : ∀ P, Δ.coeff P ≠ 0 → P ∈ Set.range p := fun P hP =>
    ⟨e ⟨P, Finsupp.mem_support_iff.mpr (by rwa [DivisorWithCoeffs.coeff_apply] at hP)⟩,
      by simp [p]⟩
  set x : Fin S.card → ℝ := fun j => Δ.coeff (p j) with hxdef
  have hxpos : ∀ j, 0 < x j := fun j => lt_of_le_of_ne (hΔ0 _) (Ne.symm (by
    show DivisorWithCoeffs.coeff Δ (p j) ≠ 0
    rw [DivisorWithCoeffs.coeff_apply]; exact Finsupp.mem_support_iff.mp (e.symm j).2))
  have hΔeq : Δ = ∑ j, Finsupp.single (p j) (x j) := eq_sum_single_coeff hp hpS
  haveI := hXp
  have hqp : IsQuasiProjectiveVariety ℂ sX := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sX
  have hev := (eventually_isRealKltPair_and_isRealTerminalPair sX hqp hQ p x).1 (hΔeq ▸ hklt)
  have hIci : Set.Ici (0 : Fin S.card → ℝ) ∈ 𝓝 x := by
    have : {y : Fin S.card → ℝ | ∀ j, 0 < y j} ∈ 𝓝 x := by
      refine IsOpen.mem_nhds ?_ hxpos
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_apply j)
    exact Filter.mem_of_superset this fun y hy j => (hy j).le
  rw [nhdsWithin_eq_nhds.mpr hIci] at hev
  choose d hd using fun j => exists_hasDeg (k := ℂ)
    (isCartierCombination_of_isQFactorial hQ (Finsupp.single (p j) (1 : ℝ))) C
  let F : (Fin S.card → ℝ) → ℝ := fun y => x₀ + ∑ j, (y j - x j) * d j
  have hFdeg : ∀ y, HasDeg ℂ sX (logCanonicalDivisor K (∑ j, Finsupp.single (p j) (y j))) C
      (F y) := by
    intro y
    have h1 := hdeg.add_smul (hasDeg_finset_sum Finset.univ (fun j => y j - x j)
      (fun j => Finsupp.single (p j) (1 : ℝ)) C d (fun j _ => hd j)) 1 1
    refine h1.congr ?_ (by simp [F])
    simp only [one_smul, logCanonicalDivisor]
    rw [hΔeq, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.smul_single, smul_eq_mul, mul_one, ← Finsupp.single_add, add_sub_cancel]
  have hFx : F x = x₀ := by simp [F]
  have hFcont : Continuous F := by
    refine continuous_const.add (continuous_finset_sum _ fun j _ => ?_)
    exact ((continuous_apply j).sub continuous_const).mul continuous_const
  have hFev : ∀ᶠ y in 𝓝 x, F y < 0 :=
    (hFcont.tendsto x).eventually (gt_mem_nhds (by rwa [hFx]))
  have hU : {y : Fin S.card → ℝ | IsRealKltPair sX (∑ j, Finsupp.single (p j) (y j)) ∧
      F y < 0 ∧ ∀ j, 0 ≤ y j} ∈ 𝓝 x := by
    filter_upwards [hev, hFev, hIci] with y h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨V, hV, hVx⟩ := exists_rat_convexHull_mem_nhds hU
  obtain ⟨ι, hι, w, z, hw0, hw1, hzV, hsum⟩ :=
    mem_convexHull_iff_exists_fintype.mp (mem_of_mem_nhds hVx)
  choose hzU q hq using fun i => hV (z i) (hzV i)
  have hcast : ∀ i, QDivisor.toRDivisor (∑ j, Finsupp.single (p j) (q i j)) =
      ∑ j, Finsupp.single (p j) (z i j) := fun i => by
    rw [toRDivisor_sum_single, hq i]
  refine ⟨ι, hι, w, fun i => ∑ j, Finsupp.single (p j) (q i j), hw0, hw1, ?_, fun i => ?_⟩
  · have hxj : ∀ j, x j = ∑ i, w i * z i j := fun j => by
      rw [← hsum]; simp [Finset.sum_apply]
    simp_rw [hcast]
    rw [hΔeq]
    calc ∑ j, Finsupp.single (p j) (x j)
        = ∑ j, ∑ i, Finsupp.single (p j) (w i * z i j) := by
          simp_rw [hxj, Finsupp.single_finset_sum]
      _ = ∑ i, ∑ j, Finsupp.single (p j) (w i * z i j) := Finset.sum_comm
      _ = ∑ i, w i • ∑ j, Finsupp.single (p j) (z i j) := by
          simp_rw [Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]
  · obtain ⟨hk, hF, h0⟩ := hzU i
    refine ⟨fun P => ?_, by rwa [hcast], F (z i), hF, ?_⟩
    · rw [coeff_sum_single]
      refine Finset.sum_nonneg fun j _ => ?_
      split_ifs
      · have h := h0 j
        rw [hq i] at h
        have h' : (0 : ℝ) ≤ (q i j : ℝ) := h
        exact_mod_cast h'
      · exact le_rfl
    · rw [hcast]; exact hFdeg (z i)

end Vertices

section ContractionHelpers

open MMP.Flips

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- The natural map `N₁(X/Z) ⟶ N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective {Z : Scheme.{0}} (f : X ⟶ Z) :
    Function.Injective (relativeToAbsolute sX f) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := relativeNumericalClass_surjective sX f a
  obtain ⟨b, rfl⟩ := relativeNumericalClass_surjective sX f b
  rw [isNaturalRelativeMap_relativeToAbsolute, isNaturalRelativeMap_relativeToAbsolute] at hab
  rw [relativeNumericalClass, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    mem_relativeNumericallyTrivial]
  rw [OneCycle.numericalClass, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq] at hab
  simpa using hab

/-- The class of a contracted curve in `N₁(X/Z)` maps to its class in `N₁(X)`. -/
private theorem relativeToAbsolute_relativeClass {Z : Scheme.{0}} (f : X ⟶ Z)
    {C : ProperCurve sX} (hC : C.IsContractedBy f) :
    relativeToAbsolute sX f (C.relativeClass f hC) = OneCycle.numericalClass sX (C.cycle ℝ) :=
  isNaturalRelativeMap_relativeToAbsolute sX f _

/-- **Verticality.** A curve whose class is a multiple of the class of a curve contracted by a
morphism to a projective variety is contracted. -/
private theorem isContractedBy_of_smul_numericalClass_eq {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) {C C' : ProperCurve sX} (hC : C.IsContractedBy f) {c : ℝ}
    (h : c • OneCycle.numericalClass sX (C.cycle ℝ) = OneCycle.numericalClass sX (C'.cycle ℝ)) :
    C'.IsContractedBy f := by
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZ
  have : IsSeparated sZ := hZ.toIsSeparated
  have : LocallyOfFiniteType sZ := hZ.toLocallyOfFiniteType
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hf H hHa C' ?_
  have h0 := MMP.Mori.ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hf C hC H
  have key := congrArg (NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj H)) h
  rw [map_smul, NumericalCurveClasses.degree_numericalClass,
    NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, OneCycle.degree_cycle,
    h0] at key
  simp only [Int.cast_zero, smul_zero] at key
  exact_mod_cast key.symm

/-- **Simplicial relative cones separate curves.** If the classes of the curves contracted by
`f` are linearly independent in `N₁(X/Z)`, a curve whose class is a multiple of the class of a
contracted curve `C` is `C`. -/
private theorem eq_of_smul_numericalClass_eq {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hli : LinearIndependent ℝ
      (fun C : {C : ProperCurve sX // C.IsContractedBy f} => C.1.relativeClass f C.2))
    {C C' : ProperCurve sX} (hC : C.IsContractedBy f) {c : ℝ}
    (h : c • OneCycle.numericalClass sX (C.cycle ℝ) = OneCycle.numericalClass sX (C'.cycle ℝ)) :
    C' = C := by
  classical
  have hC' := isContractedBy_of_smul_numericalClass_eq hZ f hf hC h
  by_contra hne
  have hrel : c • C.relativeClass f hC = C'.relativeClass f hC' :=
    relativeToAbsolute_injective f (by
      rw [map_smul, relativeToAbsolute_relativeClass, relativeToAbsolute_relativeClass, h])
  have hne' : (⟨C, hC⟩ : {C : ProperCurve sX // C.IsContractedBy f}) ≠ ⟨C', hC'⟩ :=
    fun h => hne (congrArg Subtype.val h).symm
  have h0 := (linearIndependent_iff'.mp hli) {⟨C, hC⟩, ⟨C', hC'⟩}
    (fun i => if i = ⟨C', hC'⟩ then -1 else c) (by
      rw [Finset.sum_pair hne', if_neg hne', if_pos rfl, hrel]
      simp) ⟨C', hC'⟩ (by simp)
  simp at h0

/-- The contraction of the ray spanned by the class of a curve `C₀` has relative Picard number
one: `N ↦ N · C₀` identifies `N¹(X/W)` with `ℝ`. -/
private theorem relativePicardNumber_eq_one_of_ray [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {W : Scheme.{0}} {ψ : X ⟶ W} (C₀ : ProperCurve sX)
    (hne : OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0)
    (hcontr : ∀ C : ProperCurve sX, C.IsContractedBy ψ ↔ OneCycle.numericalClass sX (C.cycle ℝ) ∈
      {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C₀.cycle ℝ) = u}) :
    MMP.Flips.relativePicardNumber sX ψ = 1 := by
  have hC₀ : C₀.IsContractedBy ψ := (hcontr C₀).mpr ⟨1, zero_le_one, one_smul _ _⟩
  let φ : KCartierDivisor ℝ X →ₗ[ℝ] ℝ :=
    (OneCycle.intersectionPairing (sX := sX)).flip (C₀.cycle ℝ)
  have hφ : ∀ D, φ D = (C₀.cycle ℝ).intersectionNumber D := fun _ => rfl
  have hker : LinearMap.ker φ = MMP.Flips.relativeNumericallyTrivialDivisors sX ψ := by
    ext D
    rw [LinearMap.mem_ker, MMP.Flips.mem_relativeNumericallyTrivialDivisors, hφ]
    refine ⟨fun hD C hC => ?_, fun h => h C₀ hC₀⟩
    obtain ⟨c, -, hc⟩ := (hcontr C).mp hC
    rw [← NumericalCurveClasses.intersectionNumber_numericalClass, ← hc, map_smul,
      NumericalCurveClasses.intersectionNumber_numericalClass, hD, smul_zero]
  have hsurj : Function.Surjective φ := by
    obtain ⟨L, _, hL⟩ : ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf
        X.ringCatSheaf.2 L), OneCycle.degree ℝ sX L (C₀.cycle ℝ) ≠ 0 := by
      by_contra h
      push Not at h
      exact hne ((Submodule.Quotient.mk_eq_zero _).mpr
        (OneCycle.mem_numericallyTrivial.mpr fun L _ => h L inferInstance))
    obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
    have hE : φ (KCartierDivisor.ofCartier ℝ E) ≠ 0 := by
      rw [hφ, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
        OneCycle.degree_cycle]
      rw [OneCycle.degree_cycle] at hL
      unfold ProperCurve.degree at hL ⊢
      rwa [← degreeOn_eq_of_iso ℂ sX C₀.ι C₀.dim_le e]
    intro r
    exact ⟨(r / φ (KCartierDivisor.ofCartier ℝ E)) • KCartierDivisor.ofCartier ℝ E, by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hE]⟩
  rw [MMP.Flips.relativePicardNumber,
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivOfSurjective hsurj)).rank_eq, Module.rank_self]
  simp

/-- **Curves in the fibres of a morphism of fibre type.** Let `f : Y ⟶ V` be a dominant proper
morphism of varieties with `dim V < dim Y`, `Y` proper over `ℂ`. For every closed set `B ∌ η_Y`
there is a proper curve contracted by `f` whose generic point is outside `B`. -/
private theorem exists_properCurve_isContractedBy_of_lt {Y V : Scheme.{0}} [IsIntegral Y]
    {sY : Y ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hY : AlgebraicGeometry.IsVariety ℂ sY)
    [IsProper sY] (hV : AlgebraicGeometry.IsVariety ℂ sV) (f : Y ⟶ V) (hf : f ≫ sV = sY)
    [IsDominant f] [IsProper f] (hdim : topologicalKrullDim V < topologicalKrullDim Y)
    {B : Set Y} (hB : IsClosed B) (hηB : genericPoint Y ∉ B) :
    ∃ Γ : ProperCurve sY, Γ.IsContractedBy f ∧ Γ.point ∉ B := by
  have : IsIntegral V := hV.toIsIntegral
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨U, hUo, hUd, -, hfib⟩ :=
    MMP.Foundations.exists_dense_isOpen_forall_irreducibleComponents_fiber_dim sY sV hY hV f hf
  have hηU : f (genericPoint Y) ∈ U := by
    rw [map_genericPoint_of_isDominant]
    obtain ⟨v, hv⟩ := hUd.nonempty
    exact ((genericPoint_spec V).mem_open_set_iff hUo).mpr ⟨v, trivial, hv⟩
  obtain ⟨y, ⟨hyU, hyB⟩, hyc⟩ := nonempty_inter_closedPoints (Z := f ⁻¹' U ∩ Bᶜ)
    ⟨genericPoint Y, hηU, hηB⟩
    ((hUo.preimage f.continuous).inter hB.isOpen_compl).isLocallyClosed
  have hyc' : IsClosed ({y} : Set Y) := mem_closedPoints_iff.mp hyc
  have hfyc : IsClosed ({f y} : Set V) := by
    rw [← Set.image_singleton]; exact f.isClosedMap _ hyc'
  set F : Set Y := f ⁻¹' {f y} with hF
  have hFc : IsClosed F := hfyc.preimage f.continuous
  let yF : F := ⟨y, rfl⟩
  set C := irreducibleComponent yF with hCdef
  have hCmem : C ∈ irreducibleComponents F := irreducibleComponent_mem_irreducibleComponents yF
  have hdC := hfib (f y) hyU C hCmem
  set C' : Set Y := Subtype.val '' C with hC'def
  have hC'irr : IsIrreducible C' :=
    isIrreducible_irreducibleComponent.image _ continuous_subtype_val.continuousOn
  have hC'cl : IsClosed C' :=
    hFc.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents C hCmem)
  have hgen := hC'irr.isGenericPoint_genericPoint_closure
  rw [hC'cl.closure_eq] at hgen
  set η := hC'irr.genericPoint
  have hyC' : y ∈ C' := ⟨yF, mem_irreducibleComponent, rfl⟩
  have hηy : η ⤳ y := hgen.specializes hyC'
  have hηne : η ≠ y := by
    intro hη
    have hC'y : C' = {y} := by rw [← hgen.def, hη, hyc'.closure_eq]
    have : Subsingleton C := ⟨fun a b => by
      have ha : a.1.1 ∈ C' := ⟨a.1, a.2, rfl⟩
      have hb : b.1.1 ∈ C' := ⟨b.1, b.2, rfl⟩
      rw [hC'y] at ha hb
      exact Subtype.ext (Subtype.ext (ha.trans hb.symm))⟩
    have : Nonempty C := ⟨⟨yF, mem_irreducibleComponent⟩⟩
    rw [topologicalKrullDim_eq_zero_of_subsingleton, zero_add] at hdC
    exact hdim.ne hdC
  have hηB' : η ∉ B := fun h => hyB (hηy.mem_closed hB h)
  obtain ⟨y', hηy', -, hy'Z, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sY hηy hyc'
    (hB.union hyc') (Or.inr rfl) (by
      rintro (h | h)
      · exact hηB' h
      · exact hηne h)
  refine ⟨⟨y', hy'⟩, ?_, fun h => hy'Z (Or.inl h)⟩
  have hsubF : closure {y'} ⊆ F := by
    have h1 : closure ({y'} : Set Y) ⊆ C' := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hηy'))
        isClosed_closure
    exact h1.trans (Set.image_subset_iff.mpr fun c _ => c.2)
  intro x hx
  have h1 : f x = f y := hsubF hx
  have h2 : f y' = f y := hsubF (subset_closure rfl)
  exact h1.trans h2.symm

/-- A morphism with closed range and `f.c` an isomorphism is surjective. -/
private theorem surjective_of_isIso_c {X Z : Scheme.{0}} (f : X ⟶ Z)
    (hf : IsClosed (Set.range f)) [IsIso f.c] : Function.Surjective f := by
  intro z
  by_contra hz
  let U : Z.Opens := ⟨(Set.range f)ᶜ, hf.isOpen_compl⟩
  have hU : f ⁻¹ᵁ U = ⊥ := le_bot_iff.mp fun x hx => (hx ⟨x, rfl⟩).elim
  have : Subsingleton Γ(X, f ⁻¹ᵁ U) := by rw [hU]; infer_instance
  have : IsIso (f.app U) := inferInstanceAs (IsIso (f.c.app _))
  have hinj : Function.Injective (f.app U) :=
    (ConcreteCategory.bijective_of_isIso (f.app U)).1
  have h10 : (1 : Γ(Z, U)) = 0 := hinj (Subsingleton.elim _ _)
  have hzU : z ∈ U := fun ⟨x, hx⟩ => hz ⟨x, hx⟩
  have := congrArg (Z.presheaf.germ U z hzU) h10
  simp at this

/-- A contracted proper curve is mapped to a closed point by a proper morphism. -/
private theorem isClosed_singleton_map_of_isContractedBy {W : Scheme.{0}} [IsProper sX]
    [IsLocallyNoetherian X] (ψ : X ⟶ W) [IsProper ψ] {C : ProperCurve sX}
    (hC : C.IsContractedBy ψ) : IsClosed ({ψ C.point} : Set W) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨c, hc, hcC⟩ : ∃ c ∈ closure ({C.point} : Set X), IsClosed ({c} : Set X) := by
    obtain ⟨c, hc, hcl⟩ := (isClosed_closure (s := ({C.point} : Set X))).exists_closed_singleton
      ⟨C.point, subset_closure rfl⟩
    exact ⟨c, hc, hcl⟩
  rw [← hC c hc, ← Set.image_singleton]
  exact ψ.isClosedMap _ hcC

/-- **Adding Cartier divisors to the boundary.** For Cartier divisors `Cᵢ` and a divisor `D` over
`X`, there are numbers `μᵢ` such that a log discrepancy `a` of `D` for `(X, B)` gives the log
discrepancy `a - ∑ sᵢ μᵢ` for `(X, B + ∑ sᵢ Cᵢ)`, for all real `sᵢ`. -/
private theorem exists_isLogDiscrepancy_add_sum [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {ι : Type*} [Fintype ι] (C : ι → Divisor X)
    (hC : ∀ i, (C i).IsCartier) (D : DivisorOver ℂ sX) :
    ∃ μ : ι → ℝ, ∀ (n : ℕ) (B B' : RDivisor X) (s : ι → ℝ) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n B D a →
      (∀ Γ, B'.coeff Γ = B.coeff Γ + ∑ i, s i * ((C i).coeff Γ : ℝ)) →
      MMP.Intersection.IsLogDiscrepancy sX n B' D (a - ∑ i, s i * μ i) := by
  classical
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isIntegral
  have := D.isBirationalMorphism.isDominant
  have : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hB := fun i => MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f (C i)
  choose C' hC' using fun i => (hC i).exists_isPullback (hB i)
  refine ⟨fun i => ((C' i).coeff D.E : ℝ), fun n B B' s a h hB' => ?_⟩
  obtain ⟨hnv, hprop, ω, hω0, hK, m, r, C₀, C₀', hC₀, hrel, hpb, ha⟩ := h
  let e := Fintype.equivFin ι
  refine ⟨hnv, hprop, ω, hω0, hK, m + Fintype.card ι, Fin.append r (s ∘ e.symm),
    Fin.append C₀ (C ∘ e.symm), Fin.append C₀' (C' ∘ e.symm), ?_, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hC₀ j
    · simpa using hC (e.symm j)
  · intro Γ
    rw [Fin.sum_univ_add, hB' Γ, ← add_assoc, hrel Γ]
    simp only [Fin.append_left, Fin.append_right, Function.comp_apply]
    congr 1
    exact (e.symm.sum_comp (fun i => s i * ((C i).coeff Γ : ℝ))).symm
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hpb j
    · rw [Fin.append_right, Fin.append_right]
      exact ⟨hB _, hC' _⟩
  · rw [ha, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Function.comp_apply]
    rw [e.symm.sum_comp (fun i => s i * ((C' i).coeff D.E : ℝ))]
    ring

/-- **Log discrepancies are affine in the coefficients.** On a fixed family `pᵢ` of prime divisors
with Cartier multiples `mᵢ pᵢ`, the coefficient vectors `y` for which every log discrepancy of
`(X, ∑ yᵢ pᵢ)` exceeds `c` form a convex set. -/
private theorem convex_setOf_lt_isLogDiscrepancy [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {ι : Type*} [Fintype ι]
    (p : ι → MMP.Mori.PrimeDivisor X) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hC : ∀ i, Divisor.IsCartier ((m i : ℤ) • Finsupp.single (p i) (1 : ℤ) : Divisor X))
    (c : ℝ) :
    Convex ℝ {y : ι → ℝ | ∀ (n : ℕ) (D : DivisorOver ℂ sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (∑ i, Finsupp.single (p i) (y i)) D a → c < a} := by
  classical
  intro y₁ hy₁ y₂ hy₂ α β hα hβ hαβ n D a ha
  set y := α • y₁ + β • y₂ with hy
  obtain ⟨μ, hμ⟩ := exists_isLogDiscrepancy_add_sum
    (fun i => ((m i : ℤ) • Finsupp.single (p i) (1 : ℤ) : Divisor X)) hC D
  have key : ∀ v : ι → ℝ, MMP.Intersection.IsLogDiscrepancy sX n
      (∑ i, Finsupp.single (p i) (v i)) D (a - ∑ i, ((v i - y i) / m i) * μ i) := fun v =>
    hμ n _ _ _ a ha fun Γ => by
      rw [coeff_sum_single, coeff_sum_single, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hm0 : (m i : ℝ) ≠ 0 := by exact_mod_cast (hm i).ne'
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
      split_ifs <;> field_simp <;> push_cast <;> ring
  have h1 := hy₁ n D _ (key y₁)
  have h2 := hy₂ n D _ (key y₂)
  have hT : α * ∑ i, ((y₁ i - y i) / m i) * μ i + β * ∑ i, ((y₂ i - y i) / m i) * μ i = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : y i = α * y₁ i + β * y₂ i := by simp [hy]
    rw [this]
    linear_combination (-(μ i / (m i : ℝ)) * (α * y₁ i + β * y₂ i)) * hαβ
  rcases hα.eq_or_lt with h | h
  · subst h
    have hβ1 : β = 1 := by linarith
    subst hβ1
    linarith
  · nlinarith [mul_lt_mul_of_pos_left h1 h, mul_le_mul_of_nonneg_left h2.le hβ]

/-- On a `ℚ`-factorial variety, an effective `ℚ`-divisor that is klt as a real boundary is
klt. -/
private theorem isKltPair_of_isRealKltPair [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hQ : IsQFactorial sX) {B : QDivisor X} (hB : ∀ P, 0 ≤ B.coeff P)
    (h : IsRealKltPair sX (QDivisor.toRDivisor B)) : MMP.Fourfold.IsKltPair sX B := by
  obtain ⟨hn, -, ⟨n, K, hK, -⟩, hd⟩ := h
  exact ⟨⟨inferInstance, inferInstance, ⟨hn, n, K, hK, isQCartier_of_isQFactorial sX hQ _⟩, hB⟩,
    hd⟩

/-- On a `ℚ`-factorial variety, a convex combination of rational boundaries with positive log
discrepancies has positive log discrepancies: log discrepancies are affine in the boundary. -/
private theorem pos_of_isLogDiscrepancy_of_convexCombination [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hQ : IsQFactorial sX) {ι : Type} [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (B : ι → QDivisor X)
    (hB : ∀ i (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor (B i)) E a → 0 < a)
    {D : RDivisor X} (hD : ∀ P, D P = ∑ i, w i * (B i P : ℝ)) :
    ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n D E a → 0 < a := by
  classical
  set T : Finset (MMP.Mori.PrimeDivisor X) := Finset.univ.biUnion fun i => (B i).support
  let e := T.equivFin
  let p : Fin T.card → MMP.Mori.PrimeDivisor X := fun j => (e.symm j : MMP.Mori.PrimeDivisor X)
  have hp : Function.Injective p := fun i j h => e.symm.injective (Subtype.ext h)
  have hpT : ∀ P ∈ T, P ∈ Set.range p := fun P hP => ⟨e ⟨P, hP⟩, by simp [p]⟩
  choose m hm hmc using fun j => hQ.2 (Finsupp.single (p j) (1 : ℤ))
  have hconv := convex_setOf_lt_isLogDiscrepancy (sX := sX) p m hm hmc 0
  let yv : ι → Fin T.card → ℝ := fun i j => (B i (p j) : ℝ)
  have hBeq : ∀ i, QDivisor.toRDivisor (B i) = ∑ j, Finsupp.single (p j) (yv i j) := fun i => by
    have h := eq_sum_single_coeff hp (D := QDivisor.toRDivisor (B i)) (fun P hP => hpT P (by
      rw [QDivisor.coeff_toRDivisor] at hP
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ?_⟩
      intro h0
      apply hP
      rw [DivisorWithCoeffs.coeff_apply, h0, Rat.cast_zero]))
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply]
  have hmem : ∀ i, yv i ∈ {y : Fin T.card → ℝ | ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (∑ j, Finsupp.single (p j) (y j)) E a → 0 < a} :=
    fun i n E a h => hB i n E a (by rwa [hBeq])
  have hsum := hconv.sum_mem (t := Finset.univ) (fun i _ => hw0 i) hw1 (fun i _ => hmem i)
  have hDsupp : ∀ P, D.coeff P ≠ 0 → P ∈ Set.range p := by
    intro P hP
    rw [DivisorWithCoeffs.coeff_apply, hD] at hP
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
    refine hpT P (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ?_⟩)
    intro h0
    apply hi
    rw [h0, Rat.cast_zero, mul_zero]
  have hDeq : D = ∑ j, Finsupp.single (p j) ((∑ i, w i • yv i) j) := by
    rw [eq_sum_single_coeff hp hDsupp]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [DivisorWithCoeffs.coeff_apply, hD]
    simp [yv, Finset.sum_apply]
  intro n E a ha
  rw [hDeq] at ha
  exact hsum n E a ha

/-- Intersection numbers of multiples. -/
private theorem HasDeg.smul {D : RDivisor X} {C : ProperCurve sX} {x : ℝ} [IsLocallyNoetherian X]
    [IsNormal X] [QuasiCompact sX] (h : HasDeg ℂ sX D C x) (a : ℝ) :
    HasDeg ℂ sX (a • D) C (a * x) :=
  (h.add_smul h a 0).congr (by simp) (by simp)

end ContractionHelpers

section Main

variable {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))

/-- The standing hypotheses on a model `(X, Δ)` over `Z`. -/
private structure IsSurfaceModel {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (K : Divisor X)
    (Δ : RDivisor X) : Prop where
  proj : MMP.Mori.IsProjectiveVariety ℂ sX
  normal : IsNormalVariety ℂ sX
  dim : topologicalKrullDim X = 2
  qfact : IsQFactorial sX
  comp : f ≫ sZ = sX
  projMor : IsProjectiveMorphism f
  birat : IsBirationalMorphism f
  canon : K.IsCanonicalDivisor sX 2
  eff : ∀ P, 0 ≤ Δ.coeff P
  klt : IsRealKltPair sX Δ

/-- The conclusion of the theorem for a model `(X, Δ)` over `Z`. -/
private def HasRealKltModel {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (K : Divisor X)
    (Δ : RDivisor X) : Prop :=
    ∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
      (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
      (sY : ∀ i, Y i ⟶ Spec (.of ℂ)) (πY : ∀ i, Y i ⟶ Z) (g : ∀ i, modelSeq X Y i ⟶ Y i)
      (KY : ∀ i, Divisor (Y i)) (ΔY : ∀ i, RDivisor (Y i)),
      -- the chain of divisorial contractions over `Z`
      (∀ i < n,
        πY i ≫ sZ = sY i ∧ g i ≫ πY i = modelMap f πY i ∧
        IsBirationalMorphism (g i) ∧
        (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
          (MMP.Mori.exceptionalSet (g i) : Set (modelSeq X Y i)) = E.support) ∧
        MMP.Flips.IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sY i)
          (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i) (divisorSeq Δ ΔY i)) (g i) ∧
        KY i = MMP.Mori.RationalMap.transformDivisor (g i).toRationalMap (divisorSeq K KY i) ∧
        ΔY i = MMP.Mori.RationalMap.transformDivisor (g i).toRationalMap (divisorSeq Δ ΔY i)) ∧
      -- the final model
      MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY n) ∧
      IsQFactorial (modelStr sX sY n) ∧
      IsRealKltPair (modelStr sX sY n) (divisorSeq Δ ΔY n) ∧
      MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY n) (modelMap f πY n)
        (MMP.Flips.logCanonicalDivisor (divisorSeq K KY n) (divisorSeq Δ ΔY n)) ∧
      -- the composite morphism and the comparison
      ∃ φ : X ⟶ modelSeq X Y n,
        φ ≫ modelMap f πY n = f ∧ IsBirationalMorphism φ ∧
        divisorSeq K KY n = MMP.Mori.RationalMap.transformDivisor φ.toRationalMap K ∧
        divisorSeq Δ ΔY n = MMP.Mori.RationalMap.transformDivisor φ.toRationalMap Δ ∧
        (∀ Q : MMP.Mori.PrimeDivisor (modelSeq X Y n),
          ∃ D : MMP.Mori.PrimeDivisor X,
            MMP.Mori.RationalMap.transformPrimeDivisor φ.toRationalMap D = some Q) ∧
        ∃ G : RDivisor X,
          MMP.Flips.IsRCartierPullback φ
            (MMP.Flips.logCanonicalDivisor (divisorSeq K KY n) (divisorSeq Δ ΔY n)) G ∧
          (∀ P, 0 ≤ (MMP.Flips.logCanonicalDivisor K Δ - G).coeff P) ∧
          (∀ P, (MMP.Flips.logCanonicalDivisor K Δ - G).coeff P ≠ 0 →
            MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX sY n) φ P) ∧
          (∀ P, MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX sY n) φ P →
            0 < (MMP.Flips.logCanonicalDivisor K Δ - G).coeff P) ∧
          ((∃ Δq : QDivisor X, QDivisor.toRDivisor Δq = Δ) →
            (∃ Bq : QDivisor (modelSeq X Y n), QDivisor.toRDivisor Bq = divisorSeq Δ ΔY n) ∧
            ∃ Eq : QDivisor X,
              QDivisor.toRDivisor Eq = MMP.Flips.logCanonicalDivisor K Δ - G)

/-- The prime divisors of `X` whose image in `Z` is a closed point. -/
private def excPrimes {X : Scheme.{0}} (f : X ⟶ Z) : Set (MMP.Mori.PrimeDivisor X) :=
  {P | 2 ≤ Order.coheight (f P.genericPoint)}

variable (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
  (hZd : topologicalKrullDim Z = 2)

include hZ hZn hZd in
private theorem excPrimes_finite {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X}
    {Δ : RDivisor X} (hM : IsSurfaceModel sZ sX f K Δ) : (excPrimes f).Finite := by
  classical
  have hXv : MMP.Mori.IsVariety ℂ sX := hM.normal.1
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hM.proj.isProjective
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  have : IsIntegral Z := hZn.1.toIsIntegral
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsProper f := isProper_of_isProjectiveMorphism f hM.projMor
  have hgf :=
    MMP.Threefold.Resolution.exists_isFinite_morphismRestrict_of_isBirationalMorphism hM.birat
  have hfin := MMP.Resolution.finite_setOf_isContractedBy hXv hM.dim.le hgf
  have hcon : ∀ P ∈ excPrimes f,
      (⟨P.genericPoint, isProperCurve_genericPoint sX hM.dim P⟩ : ProperCurve sX).IsContractedBy
        f := by
    intro P hP x hx
    have hc := isClosed_singleton_of_two_le_coheight hZn hZd hP
    have hsp : f P.genericPoint ⤳ f x := (specializes_iff_mem_closure.mpr hx).map f.continuous
    have := specializes_iff_mem_closure.mp hsp
    rw [hc.closure_eq] at this
    exact this
  let F : excPrimes f → {C : ProperCurve sX | C.IsContractedBy f} := fun P =>
    ⟨⟨P.1.genericPoint, isProperCurve_genericPoint sX hM.dim P.1⟩, hcon P.1 P.2⟩
  have hinj : Function.Injective F := fun P Q h => Subtype.ext
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (congrArg (fun C => C.1.point) h))
  haveI := hfin.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective F hinj)

include hZ hZn hZd in
/-- The case of a nef adjoint: the empty program. -/
private theorem concl_of_isRelativelyNef {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X}
    {Δ : RDivisor X} (hM : IsSurfaceModel sZ sX f K Δ)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K Δ)) :
    HasRealKltModel sZ sX f K Δ := by
  have hD : MMP.Flips.IsCartierCombination (MMP.Flips.logCanonicalDivisor K Δ) :=
    isCartierCombination_of_isQFactorial hM.qfact _
  have : IsSeparated sX := hM.normal.1.toIsSeparated
  have := isSeparated_toTerminal_of_isNormalVariety hM.normal
  refine ⟨0, fun _ => X, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => sX, fun _ => f,
    fun i => match i with | 0 => 𝟙 X | _ + 1 => 𝟙 X, fun _ => K, fun _ => Δ,
    fun i hi => absurd hi (Nat.not_lt_zero i), hM.proj, hM.qfact, hM.klt, hnef, 𝟙 X,
    Category.id_comp f, isBirationalMorphism_of_isIso (𝟙 X),
    (transformDivisor_id hM.normal K).symm,
    (transformDivisor_id hM.normal Δ).symm,
    fun Q => ⟨Q, (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 X) Q Q).mpr
      rfl⟩, MMP.Flips.logCanonicalDivisor K Δ, isRCartierPullback_id hD, ?_, ?_, ?_, ?_⟩
  · intro P
    simp
  · intro P h
    simp at h
  · intro P h
    have h2 := (isExceptionalPrimeDivisor_iff hM.normal hM.dim (𝟙 X)
      (by rw [Category.id_comp]; exact hM.normal) (isBirationalMorphism_of_isIso _) P).mp h
    change 2 ≤ Order.coheight P.genericPoint at h2
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  · rintro ⟨Δq, hΔq⟩
    exact ⟨⟨Δq, hΔq⟩, 0, by simp⟩

/-- A contraction of an extremal ray of a surface which contracts a single curve, through
whose generic point it is not biregular once the target is a surface, is divisorial. -/
private theorem isDivisorialContraction_of_dim_two {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    [IsProper sX] {ψ : X ⟶ W} [IsDominant ψ] [IsProper ψ] (hXv : MMP.Mori.IsVariety ℂ sX)
    (hWv : MMP.Mori.IsVariety ℂ sW) (hXd : topologicalKrullDim X = 2) (hXq : IsQFactorial sX)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hψ : IsContractionOfFace ℂ sX sW R ψ) (C : ProperCurve sX)
    (hC1 : Order.coheight C.point = 1)
    (honly : ∀ C' : ProperCurve sX, C'.IsContractedBy ψ → C' = C)
    (hmemEx : topologicalKrullDim W = 2 → C.point ∈ MMP.Mori.exceptionalSet ψ) :
    IsDivisorialContraction ℂ sX sW R ψ := by
  rcases (IsContractionOfFace.trichotomy_of_isExtremalRay hXq hR hψ).1 with hft | hd | hsm
  · exfalso
    have hηB : genericPoint X ∉ closure ({C.point} : Set X) := by
      intro hη
      have hle : genericPoint X ≤ C.point :=
        Scheme.le_iff_specializes.2 (specializes_iff_mem_closure.mpr hη)
      have h0 := Order.coheight_anti hle
      rw [hC1, Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at h0
      exact absurd h0 (by decide)
    obtain ⟨Γ, hΓ, hΓB⟩ := exists_properCurve_isContractedBy_of_lt hXv hWv ψ hψ.comp_eq
      hft.dim_lt isClosed_closure hηB
    exact hΓB (honly Γ hΓ ▸ subset_closure rfl)
  · exact hd
  · exfalso
    have hWd : topologicalKrullDim W = 2 := by
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW sX
        hsm.isBirationalMorphism, hXd]
    have h2 := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hsm.two_le_codimension
      (hmemEx hWd)
    rw [hC1] at h2
    exact absurd h2 (by decide)

include hZ hZn hZd in
/-- If `K + Δ` is not nef over `Z`, there is a divisorial `(K + Δ)`-negative extremal contraction
over `Z` whose target is again a surface model. -/
private theorem exists_divisorialContraction_of_not_isRelativelyNef {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X}
    {Δ : RDivisor X} (hM : IsSurfaceModel sZ sX f K Δ)
    (hnef : ¬ MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K Δ)) :
    ∃ (X₁ : Scheme.{0}) (_ : IsIntegral X₁) (_ : CompactSpace X₁) (_ : IsLocallyNoetherian X₁)
      (_ : IsNormal X₁) (sX₁ : X₁ ⟶ Spec (.of ℂ)) (π₁ : X₁ ⟶ Z) (g : X ⟶ X₁)
      (C : MMP.Mori.PrimeDivisor X) (a : ℝ) (G : RDivisor X),
      g ≫ π₁ = f ∧ IsBirationalMorphism g ∧
      (MMP.Mori.exceptionalSet g : Set X) = C.support ∧
      MMP.Flips.IsNegativeExtremalContraction ℂ sX sX₁
        (MMP.Flips.logCanonicalDivisor K Δ) g ∧
      IsSurfaceModel sZ sX₁ π₁ (MMP.Mori.RationalMap.transformDivisor g.toRationalMap K)
        (MMP.Mori.RationalMap.transformDivisor g.toRationalMap Δ) ∧
      MMP.Flips.IsRCartierPullback g
        (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor g.toRationalMap K)
          (MMP.Mori.RationalMap.transformDivisor g.toRationalMap Δ)) G ∧
      MMP.Flips.logCanonicalDivisor K Δ - G = Finsupp.single C a ∧ 0 < a ∧
      2 ≤ Order.coheight (g C.genericPoint) := by
  classical
  -- instances
  have hXv : MMP.Mori.IsVariety ℂ sX := hM.normal.1
  haveI := hM.proj
  have : QuasiCompact sX := hXv.toQuasiCompact
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hM.proj.isProjective
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : IsSeparated sX := hXv.toIsSeparated
  have hZv : MMP.Mori.IsVariety ℂ sZ := hZn.1
  have : IsIntegral Z := hZv.toIsIntegral
  have : LocallyOfFiniteType sZ := hZv.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsNormal Z := hZn.2
  have : IsSeparated sZ := hZv.toIsSeparated
  have : IsProper f := isProper_of_isProjectiveMorphism f hM.projMor
  haveI := hZ
  -- a curve on which the adjoint is negative
  have hDc : MMP.Flips.IsCartierCombination (MMP.Flips.logCanonicalDivisor K Δ) :=
    isCartierCombination_of_isQFactorial hM.qfact _
  obtain ⟨C, hCf, x₀, hx₀, hdeg₀⟩ := exists_properCurve_hasDeg_neg hDc hnef
  -- rational vertices
  obtain ⟨ι, hι, w, Δv, hw0, hw1, hΔsum, hv⟩ :=
    exists_rational_vertices hM.proj hM.qfact K hM.eff hM.klt C hx₀ hdeg₀
  choose hv0 hvklt y hy hydeg using hv
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  -- the relative cone is simplicial, so the ray of `C` is extremal
  have hXq : IsQuasiProjectiveVariety ℂ sX := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sX
  have hZq : IsQuasiProjectiveVariety ℂ sZ := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sZ
  obtain ⟨-, -, hext, hli⟩ := relativeClosedConeOfCurves_eq_hull_of_isBirationalMorphism
    hM.qfact hZn hXq hZq hM.dim hZd f hM.comp hM.projMor.isProjective hM.birat
  set R : Set (NumericalCurveClasses sX) :=
    {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = u} with hRdef
  have hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R := by
    have h := isExtremalRay_image_relativeToAbsolute sX sZ f hM.comp (hext ⟨C, hCf⟩)
    convert h using 1
    ext u
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • C.relativeClass f hCf, ⟨c, hc, rfl⟩, by
        rw [map_smul, relativeToAbsolute_relativeClass]⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, by rw [map_smul, relativeToAbsolute_relativeClass]⟩
  have hCne : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
    obtain ⟨-, v, hv, hRv⟩ := hR
    intro h0
    have hvR : v ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := ⟨1, zero_le_one, one_smul _ _⟩
    rw [← hRv] at hvR
    obtain ⟨c, -, hc⟩ := hvR
    rw [h0, smul_zero] at hc
    exact hv hc.symm
  -- the vertices are klt and negative on the ray
  have hvQ : ∀ i, (Divisor.toQDivisor K + Δv i).IsQCartier := fun i =>
    isQCartier_of_isQFactorial sX hM.qfact _
  have hlc : ∀ i, QDivisor.toRDivisor (Divisor.toQDivisor K + Δv i) =
      MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor (Δv i)) := fun i => by
    rw [map_add, QDivisor.toRDivisor_toQDivisor]; rfl
  have hvdeg : ∀ i, ((Divisor.toQDivisor K + Δv i).intersectionNumber ℂ sX C.ι C.dim_le
      (hvQ i) : ℝ) = y i := fun i =>
    (hasDeg_toRDivisor (hvQ i) C).unique ((hydeg i).congr (hlc i).symm rfl)
  have hvneg : ∀ i, IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δv i) R := fun i =>
    ⟨hvQ i, hR, fun u hu hu0 => by
      obtain ⟨c, hc, rfl⟩ := hu
      have hc0 : c ≠ 0 := by rintro rfl; simp at hu0
      rw [map_smul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle, hvdeg i, smul_eq_mul]
      exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hc (Ne.symm hc0)) (hy i)⟩
  have hvkltM : ∀ i, MMP.Mori.IsKltPair sX 2 K (Δv i) := fun i => by
    have hF := isKltPair_of_isRealKltPair hM.qfact (hv0 i) (hvklt i)
    exact (isKltPair_iff_mori_isKltPair sX hM.canon hF.1).mp hF
  -- the contraction theorem
  have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (QDivisor.curveForm sX (Divisor.toQDivisor K + Δv i₀) (hvkltM i₀).1.2.2) R :=
    ⟨hR.1, fun u hu v hv => by
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      exact ⟨a + b, add_nonneg ha hb, add_smul a b _⟩, fun z hz hz0 => (hvneg i₀).2.2 z hz hz0⟩
  obtain ⟨W, sW, ψ, hψ, hWn⟩ :=
    MMP.Mori.exists_isContractionOfFace_of_isNegativeExtremalFace (hvkltM i₀) (hv0 i₀) hF
  have hWv : MMP.Mori.IsVariety ℂ sW := hWn.1
  have : IsIntegral W := hWv.toIsIntegral
  have : QuasiCompact sW := hWv.toQuasiCompact
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : LocallyOfFiniteType sW := hWv.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : IsNormal W := hWn.2
  have : IsSeparated sW := hWv.toIsSeparated
  have hWp := hψ.isProjectiveVariety_target
  have : IsProper (ψ ≫ sW) := by rw [hψ.comp_eq]; infer_instance
  have : IsProper ψ := IsProper.of_comp ψ sW
  have : ∀ U : W.Opensᵒᵖ, IsIso (ψ.c.app U) := fun U => hψ.isIso_app U.unop
  have : IsIso ψ.c := NatIso.isIso_of_isIso_app _
  have hψs : Function.Surjective ψ := surjective_of_isIso_c ψ ψ.isClosedMap.isClosed_range
  have : Surjective ψ := ⟨hψs⟩
  have : IsDominant ψ := ⟨hψs.denseRange⟩
  have hCψ : C.IsContractedBy ψ := (hψ.isContractedBy_iff C).mpr ⟨1, zero_le_one, one_smul _ _⟩
  -- the contraction contracts `C` only
  have honly : ∀ C' : ProperCurve sX, C'.IsContractedBy ψ → C' = C := fun C' hC' => by
    obtain ⟨_, -, hcC⟩ := (hψ.isContractedBy_iff C').mp hC'
    exact eq_of_smul_numericalClass_eq hZ f hM.comp hli hCf hcC
  -- the contraction lies over `Z`
  have hψP : IsProjectiveMorphism ψ :=
    IsProjectiveMorphism.of_comp ψ sW (hψ.comp_eq ▸ hM.proj.isProjective)
  obtain ⟨h, hh, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hM.proj hWp hZ hψP
    hψ.comp_eq hM.comp (fun C' hC' => (honly C' hC') ▸ hCf)
  have hhs : h ≫ sZ = sW := by
    obtain ⟨_, -, huniq⟩ := MMP.existsUnique_comp_eq_of_isIso_c ψ sX (fun x x' hxx => by
      rw [← hψ.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hxx])
    exact (huniq _ (show ψ ≫ h ≫ sZ = sX by rw [← Category.assoc, hh, hM.comp])).trans
      (huniq _ hψ.comp_eq).symm
  -- the contraction is divisorial
  have hC1 : Order.coheight C.point = 1 := coheight_point_eq_one sX hM.dim C
  have hCW := isClosed_singleton_map_of_isContractedBy ψ hCψ
  have hmemEx : ∀ hWd : topologicalKrullDim W = 2, C.point ∈ MMP.Mori.exceptionalSet ψ := by
    intro hWd
    by_contra hnm
    rw [MMP.Mori.mem_exceptionalSet, not_not] at hnm
    have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus ψ hnm
    rw [coheight_eq_two_of_isClosed hWn hWd hCW, hC1] at h1
    exact absurd h1 (by decide)
  have hdiv := isDivisorialContraction_of_dim_two hXv hWv hM.dim hM.qfact hR hψ C hC1 honly
    hmemEx
  have hψb := hdiv.isBirationalMorphism
  have hWd : topologicalKrullDim W = 2 := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW sX hψb, hM.dim]
  set Cp := AlgebraicGeometry.PrimeDivisor.ofCoheightOne C.point hC1 with hCp
  have hCpη : Cp.genericPoint = C.point :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hEx : (MMP.Mori.exceptionalSet ψ : Set X) = Cp.support := by
    obtain ⟨E, hE⟩ := hdiv.exists_primeDivisor
    have hCE : C.point ∈ E.support := hE ▸ hmemEx hWd
    rw [← hCpη] at hCE
    rw [hE, MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hCE]
  have hC2 : 2 ≤ Order.coheight (ψ Cp.genericPoint) := by
    rw [hCpη, coheight_eq_two_of_isClosed hWn hWd hCW]
  have hXψ : IsNormalVariety ℂ (ψ ≫ sW) := by rw [hψ.comp_eq]; exact hM.normal
  -- the target is `ℚ`-factorial and klt for every pushed-forward vertex
  have hWq : IsQFactorial sW := MMP.Mori.isQFactorial_of_isDivisorialContraction hM.qfact
    (hvkltM i₀) (hv0 i₀) (fun z hz hz0 => (hvneg i₀).2.2 z hz hz0) hdiv
  have hkW : ∀ i, MMP.Mori.IsKltPair sW 2
      (MMP.Mori.RationalMap.transformDivisor ψ.toRationalMap K)
      (MMP.Mori.RationalMap.transformDivisor ψ.toRationalMap (Δv i)) := fun i =>
    MMP.Mori.IsDivisorialContraction.isKltPair_transformDivisor hM.qfact (hvneg i) hdiv
      (Or.inl fun P => hv0 i P) (hvkltM i)
  have hcoefW : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X)
      (Q : MMP.Mori.PrimeDivisor W), ∃ P : MMP.Mori.PrimeDivisor X,
        MMP.Mori.RationalMap.transformDivisor ψ.toRationalMap D Q = D P := by
    intro R _ D Q
    obtain ⟨P, hP, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hWn hXψ hψb Q
    exact ⟨P, transformDivisor_apply_of_map_genericPoint hWn hXψ hψb hP D⟩
  set KW := MMP.Mori.RationalMap.transformDivisor ψ.toRationalMap K with hKW
  set ΔW := MMP.Mori.RationalMap.transformDivisor ψ.toRationalMap Δ with hΔW
  have hΔWv : ∀ Q, ΔW Q = ∑ i, w i *
      ((MMP.Mori.RationalMap.transformDivisor ψ.toRationalMap (Δv i)) Q : ℝ) := by
    intro Q
    obtain ⟨P, hP, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hWn hXψ hψb Q
    rw [hΔW, transformDivisor_apply_of_map_genericPoint hWn hXψ hψb hP]
    simp_rw [transformDivisor_apply_of_map_genericPoint hWn hXψ hψb hP]
    rw [hΔsum]
    simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← DivisorWithCoeffs.coeff_apply, QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply]
  have hSM : IsSurfaceModel sZ sW h KW ΔW := by
    refine ⟨hWp, hWn, hWd, hWq, hhs, IsProjectiveMorphism.of_comp h sZ (hhs ▸ hWp.isProjective),
      ?_, (hkW i₀).1.2.1, ?_, ?_⟩
    · have : LocallyOfFiniteType (h ≫ sZ) := by rw [hhs]; infer_instance
      have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h sZ
      exact MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left ψ h hψb (hh ▸ hM.birat)
    · intro Q
      obtain ⟨P, hP⟩ := hcoefW Δ Q
      rw [DivisorWithCoeffs.coeff_apply, hP, ← DivisorWithCoeffs.coeff_apply]
      exact hM.eff P
    · refine ⟨hWn, fun Q => ?_, ⟨2, KW, (hkW i₀).1.2.1,
        isRCartier_of_isCartierCombination (isCartierCombination_of_isQFactorial hWq _)⟩, ?_⟩
      · obtain ⟨P, hP⟩ := hcoefW Δ Q
        rw [DivisorWithCoeffs.coeff_apply, hP, ← DivisorWithCoeffs.coeff_apply]
        exact hM.klt.2.1 P
      · refine pos_of_isLogDiscrepancy_of_convexCombination hWq w hw0 hw1 _ (fun i => ?_) hΔWv
        have hFk := (isKltPair_iff_mori_isKltPair sW (hkW i).1.2.1
          (B := MMP.Mori.RationalMap.transformDivisor ψ.toRationalMap (Δv i))
          ⟨inferInstance, inferInstance, (hkW i).1.isPair, fun Q => ?_⟩).mpr (hkW i)
        · exact hFk.2
        · obtain ⟨P, hP⟩ := hcoefW (Δv i) Q
          rw [DivisorWithCoeffs.coeff_apply, hP, ← DivisorWithCoeffs.coeff_apply]
          exact hv0 i P
  -- the negative extremal contraction
  have hρ : MMP.Flips.relativePicardNumber sX ψ = 1 :=
    relativePicardNumber_eq_one_of_ray C hCne hψ.isContractedBy_iff
  have hnegD : MMP.Flips.IsCartierCombination (-MMP.Flips.logCanonicalDivisor K Δ) :=
    isCartierCombination_of_isQFactorial hM.qfact _
  have hdegneg : HasDeg ℂ sX (-MMP.Flips.logCanonicalDivisor K Δ) C (-x₀) :=
    (hdeg₀.smul (-1)).congr (by simp) (by ring)
  have hNEC : MMP.Flips.IsNegativeExtremalContraction ℂ sX sW
      (MMP.Flips.logCanonicalDivisor K Δ) ψ := by
    refine ⟨hM.normal, hWn, hDc, ⟨hWv, hXv, hψ.comp_eq, inferInstance, hψ.isIso_app⟩, ?_, hρ⟩
    refine MMP.Flips.isRelativelyAmple_of_isRelativelyNef_of_relativePicardNumber_eq_one sX sW
      hM.normal hWn ψ hψP.isProjective hψ.comp_eq hρ _ hnegD ?_ ?_
    · obtain ⟨m, r, L, hL, hLeq⟩ := hnegD
      refine ⟨m, r, L, hL, by simpa only [← MMP.Flips.toRDivisor_eq_mapCoeffs] using hLeq,
        fun C' hC' x hx => ?_⟩
      obtain rfl := honly C' hC'
      have := hdegneg.unique ⟨m, r, L, hx⟩
      linarith
    · intro htriv
      obtain ⟨m, r, L, hx⟩ := hdegneg
      obtain ⟨m₀, r₀, L₀, h0⟩ : HasDeg ℂ sX (0 : RDivisor X) C 0 :=
        (hasDeg_sum (k := ℂ) C (Fin.elim0 : Fin 0 → ℝ) Fin.elim0 fun j => j.elim0).congr
          (by simp) (by simp)
      have := htriv.2.2 C hCψ m r L (-x₀) m₀ r₀ L₀ 0 hx h0
      linarith
  -- the comparison along the contracted curve
  have hDW : MMP.Flips.IsCartierCombination (MMP.Flips.logCanonicalDivisor KW ΔW) :=
    isCartierCombination_of_isQFactorial hWq _
  obtain ⟨mW, rW, LW, hLW, hDWeq⟩ := hDW
  have hBW := fun j => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant ψ (LW j)
  set G : RDivisor X := ∑ j, rW j • Divisor.toRDivisor ((LW j).pullback (hLW j) (hBW j)) with hGdef
  have hG : MMP.Flips.IsRCartierPullback ψ (MMP.Flips.logCanonicalDivisor KW ΔW) G :=
    ⟨mW, rW, LW, _, hLW, by simpa only [← MMP.Flips.toRDivisor_eq_mapCoeffs] using hDWeq,
      fun j => ⟨_, Divisor.isPullback_pullback (hLW j) _⟩, rfl⟩
  have hGdeg : HasDeg ℂ sX G C 0 := by
    refine (hasDeg_sum C rW _ fun j => (hLW j).isCartier_pullback ψ (hBW j)).congr rfl ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Divisor.degreeOn_pullback_eq_zero_of_isContractedBy ψ hψ.comp_eq (hLW j) (hBW j) C hCψ]
    simp
  set a := (MMP.Flips.logCanonicalDivisor K Δ - G).coeff Cp with ha_def
  have hDG : MMP.Flips.logCanonicalDivisor K Δ - G = Finsupp.single Cp a := by
    refine Finsupp.ext fun P => ?_
    by_cases hPC : P = Cp
    · subst hPC
      rw [Finsupp.single_eq_same, ha_def, DivisorWithCoeffs.coeff_apply]
    · obtain ⟨_, -, hco⟩ := exists_coeff_sub_eq_of_ne hWn hXψ hψb hEx K Δ hG hPC
      simpa [← hKW, ← hΔW, Finsupp.single_eq_of_ne hPC, DivisorWithCoeffs.coeff_apply] using hco
  have hE1 := isQCartier_of_isQFactorial sX hM.qfact (Finsupp.single Cp (1 : ℚ))
  have hEneg := MMP.Mori.intersectionNumber_single_neg_of_isContractionOfFace hM.qfact hR hψ hψb
    Cp hEx.symm.subset C hCψ
  have hEdeg := hasDeg_toRDivisor hE1 C
  have hs1 : QDivisor.toRDivisor (Finsupp.single Cp (1 : ℚ)) = Finsupp.single Cp (1 : ℝ) :=
    DivisorWithCoeffs.ext' fun P => by
      rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
        Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp
  have ha : 0 < a := pos_of_hasDeg_sub_eq_single hdeg₀ hx₀ (hEdeg.congr hs1 rfl)
    (by exact_mod_cast hEneg) hGdeg hDG
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, sW, h, ψ, Cp, a, G, hh,
    hψb, hEx, hNEC, hSM, hG, hDG, ha, hC2⟩

include hZ hZn hZd in
/-- The step decreases the number of exceptional primes over `Z`. -/
private theorem excPrimes_ncard_lt {X X₁ : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X₁] [CompactSpace X₁]
    [IsLocallyNoetherian X₁] [IsNormal X₁] {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X}
    {Δ : RDivisor X} (hM : IsSurfaceModel sZ sX f K Δ) {sX₁ : X₁ ⟶ Spec (.of ℂ)} {π₁ : X₁ ⟶ Z}
    {K₁ : Divisor X₁} {Δ₁ : RDivisor X₁} (hM₁ : IsSurfaceModel sZ sX₁ π₁ K₁ Δ₁) {g : X ⟶ X₁}
    (hg : g ≫ π₁ = f) (hgb : IsBirationalMorphism g) (hgs : g ≫ sX₁ = sX) [IsProper g]
    (C : MMP.Mori.PrimeDivisor X) (hC2 : 2 ≤ Order.coheight (g C.genericPoint)) :
    (excPrimes π₁).ncard < (excPrimes f).ncard := by
  classical
  have hfin := excPrimes_finite sZ hZ hZn hZd hM
  have : IsProper π₁ := isProper_of_isProjectiveMorphism π₁ hM₁.projMor
  have hXg : IsNormalVariety ℂ (g ≫ sX₁) := by rw [hgs]; exact hM.normal
  have key : ∀ Q : MMP.Mori.PrimeDivisor X₁, ∃ P : MMP.Mori.PrimeDivisor X,
      g P.genericPoint = Q.genericPoint := fun Q =>
    (MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hM₁.normal hXg
      hgb Q).imp fun P h => h.1
  choose ι hι using key
  have hsub : ι '' excPrimes π₁ ⊆ excPrimes f \ {C} := by
    rintro _ ⟨Q, hQ, rfl⟩
    refine ⟨?_, fun h => ?_⟩
    · show 2 ≤ Order.coheight (f (ι Q).genericPoint)
      rw [← hg, Scheme.Hom.comp_apply, hι]
      exact hQ
    · have h' : ι Q = C := h
      have h2 := hC2
      rw [← h', hι, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
      exact absurd h2 (by decide)
  have hinj : Set.InjOn ι (excPrimes π₁) := fun Q _ Q' _ h =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective (by
      have h1 := hι Q
      have h2 := hι Q'
      rw [h] at h1
      exact h1.symm.trans h2)
  have : IsIntegral Z := hZn.1.toIsIntegral
  have hCm : C ∈ excPrimes f := by
    show 2 ≤ Order.coheight (f C.genericPoint)
    rw [← hg, Scheme.Hom.comp_apply]
    exact two_le_coheight_map hM₁.normal hM₁.dim hZn hZd π₁ hC2
  calc (excPrimes π₁).ncard = (ι '' excPrimes π₁).ncard := hinj.ncard_image.symm
    _ ≤ (excPrimes f \ {C}).ncard := Set.ncard_le_ncard hsub (hfin.diff)
    _ < (excPrimes f).ncard := Set.ncard_sdiff_singleton_lt_of_mem hCm hfin

include hZ hZn hZd in
/-- Prepending a step to a program. -/
private theorem concl_of_step {X X₁ : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X₁] [CompactSpace X₁]
    [IsLocallyNoetherian X₁] [IsNormal X₁] {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X}
    {Δ : RDivisor X} (hM : IsSurfaceModel sZ sX f K Δ) {sX₁ : X₁ ⟶ Spec (.of ℂ)} {π₁ : X₁ ⟶ Z}
    {g : X ⟶ X₁} {C : MMP.Mori.PrimeDivisor X} {a : ℝ} {G : RDivisor X}
    (hg : g ≫ π₁ = f) (hgb : IsBirationalMorphism g)
    (hC : (MMP.Mori.exceptionalSet g : Set X) = C.support)
    (hneg : MMP.Flips.IsNegativeExtremalContraction ℂ sX sX₁
        (MMP.Flips.logCanonicalDivisor K Δ) g)
    (hM₁ : IsSurfaceModel sZ sX₁ π₁ (MMP.Mori.RationalMap.transformDivisor g.toRationalMap K)
        (MMP.Mori.RationalMap.transformDivisor g.toRationalMap Δ))
    (hG : MMP.Flips.IsRCartierPullback g
        (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor g.toRationalMap K)
          (MMP.Mori.RationalMap.transformDivisor g.toRationalMap Δ)) G)
    (hGE : MMP.Flips.logCanonicalDivisor K Δ - G = Finsupp.single C a) (ha : 0 < a)
    (hC2 : 2 ≤ Order.coheight (g C.genericPoint))
    (h₁ : HasRealKltModel sZ sX₁ π₁ (MMP.Mori.RationalMap.transformDivisor g.toRationalMap K)
        (MMP.Mori.RationalMap.transformDivisor g.toRationalMap Δ)) :
    HasRealKltModel sZ sX f K Δ := by
  classical
  obtain ⟨n, Y', hYi, hYc, hYl, hYn, sY', πY', g', KY', ΔY', hsteps, hproj, hqf, hklt', hnef',
    φ', hφ'f, hφ'b, hφ'K, hφ'Δ, hφ'ext, G', hG', hE'eff, hE'exc, hE'pos, hE'rat⟩ := h₁
  have := hYi; have := hYc; have := hYl; have := hYn
  set K₁ := MMP.Mori.RationalMap.transformDivisor g.toRationalMap K with hK₁
  set Δ₁ := MMP.Mori.RationalMap.transformDivisor g.toRationalMap Δ with hΔ₁
  have hgs : g ≫ sX₁ = sX := hneg.isContraction.comp_eq
  have : IsProper g := hneg.isContraction.isProper
  have hYnn : IsNormalVariety ℂ (modelStr sX₁ sY' n) := hqf.1
  have hmapc : modelMap π₁ πY' n ≫ sZ = modelStr sX₁ sY' n := by
    rcases n with _ | m
    · exact hM₁.comp
    · exact (hsteps m (Nat.lt_succ_self m)).1
  have hφ's : φ' ≫ modelStr sX₁ sY' n = sX₁ := by
    rw [← hmapc, ← Category.assoc, hφ'f, hM₁.comp]
  have : IsSeparated (modelStr sX₁ sY' n) := hYnn.1.toIsSeparated
  have := isSeparated_toTerminal_of_isNormalVariety hYnn
  have : IsProper sX₁ := isProper_of_isProjectiveMorphism sX₁ hM₁.proj.isProjective
  have : IsProper (φ' ≫ modelStr sX₁ sY' n) := by rw [hφ's]; infer_instance
  have : IsProper φ' := IsProper.of_comp φ' (modelStr sX₁ sY' n)
  have : IsDominant g := hgb.isDominant
  have : IsDominant φ' := hφ'b.isDominant
  have hX₁n : IsNormalVariety ℂ (φ' ≫ modelStr sX₁ sY' n) := by rw [hφ's]; exact hM₁.normal
  have hXn : IsNormalVariety ℂ (g ≫ φ' ≫ modelStr sX₁ sY' n) := by
    rw [hφ's, hgs]; exact hM.normal
  have hXn' : IsNormalVariety ℂ ((g ≫ φ') ≫ modelStr sX₁ sY' n) := by
    rwa [Category.assoc]
  have hXg : IsNormalVariety ℂ (g ≫ sX₁) := by rw [hgs]; exact hM.normal
  have hgφ := Oai4C1.CommonModel.isBirationalMorphism_comp hgb hφ'b
  have : (g ≫ φ') ≫ modelStr sX₁ sY' n = sX := by rw [Category.assoc, hφ's, hgs]
  have : IsProper (g ≫ φ') := inferInstance
  -- the dimension of the final model
  have hYd : topologicalKrullDim (modelSeq X₁ Y' n) = 2 := by
    have := hYnn.1
    have := hM₁.normal.1
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (modelStr sX₁ sY' n) sX₁
      hφ'b, hM₁.dim]
  -- the pull-back along the composite
  obtain ⟨G₂, hG₂c, hG₂g, -⟩ := exists_isRCartierPullback_comp g φ' hG'
  set E' := MMP.Flips.logCanonicalDivisor K₁ Δ₁ - G' with hE'
  have hpull : MMP.Flips.IsRCartierPullback g E' (G - G₂) := by
    have h := MMP.Fourfold.isRCartierPullback_add hG
      (MMP.Fourfold.isRCartierPullback_smul (-1) hG₂g)
    simpa [hE', sub_eq_add_neg] using h
  have heff : 0 ≤ G - G₂ :=
    (MMP.Fourfold.isEffective_of_isRCartierPullback g
      (isRCartier_of_isCartierCombination (isCartierCombination_of_isQFactorial hM₁.qfact E'))
      hE'eff).2 _ hpull
  have hEeq : MMP.Flips.logCanonicalDivisor K Δ - G₂ = Finsupp.single C a + (G - G₂) := by
    rw [← hGE]; abel
  -- coefficients away from `C`
  have hcoef : ∀ P : MMP.Mori.PrimeDivisor X, P ≠ C → ∃ P₁ : MMP.Mori.PrimeDivisor X₁,
      g P.genericPoint = P₁.genericPoint ∧
      (MMP.Flips.logCanonicalDivisor K Δ - G₂).coeff P = E'.coeff P₁ :=
    fun P hP => exists_coeff_sub_eq_of_ne hM₁.normal hXg hgb hC K Δ hG₂g hP
  have hexc_iff : ∀ P : MMP.Mori.PrimeDivisor X,
      MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX₁ sY' n) (g ≫ φ') P ↔
        2 ≤ Order.coheight (φ' (g P.genericPoint)) :=
    fun P => isExceptionalPrimeDivisor_iff hYnn hYd (g ≫ φ') hXn' hgφ P
  have hexc'_iff : ∀ P₁ : MMP.Mori.PrimeDivisor X₁,
      MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX₁ sY' n) φ' P₁ ↔
        2 ≤ Order.coheight (φ' P₁.genericPoint) :=
    fun P₁ => isExceptionalPrimeDivisor_iff hYnn hYd φ' hX₁n hφ'b P₁
  have hCexc : 2 ≤ Order.coheight (φ' (g C.genericPoint)) :=
    two_le_coheight_map hM₁.normal hM₁.dim hYnn hYd φ' hC2
  have hK_fin : divisorSeq K₁ KY' n =
      MMP.Mori.RationalMap.transformDivisor (g ≫ φ').toRationalMap K := by
    rw [transformDivisor_comp hYnn hX₁n hXn hgb hφ'b hgφ]
    exact hφ'K
  have hΔ_fin : divisorSeq Δ₁ ΔY' n =
      MMP.Mori.RationalMap.transformDivisor (g ≫ φ').toRationalMap Δ := by
    rw [transformDivisor_comp hYnn hX₁n hXn hgb hφ'b hgφ]
    exact hφ'Δ
  have hext_fin : ∀ Q : MMP.Mori.PrimeDivisor (modelSeq X₁ Y' n), ∃ D : MMP.Mori.PrimeDivisor X,
      MMP.Mori.RationalMap.transformPrimeDivisor (g ≫ φ').toRationalMap D = some Q := by
    intro Q
    obtain ⟨D₁, hD₁⟩ := hφ'ext Q
    rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff] at hD₁
    obtain ⟨P, hP, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hM₁.normal hXg
        hgb D₁
    refine ⟨P, ?_⟩
    rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff, Scheme.Hom.comp_apply,
      hP, hD₁]
  have heff_fin : ∀ P, 0 ≤ (MMP.Flips.logCanonicalDivisor K Δ - G₂).coeff P := by
    intro P
    rw [hEeq, DivisorWithCoeffs.coeff_add]
    have h1 : 0 ≤ DivisorWithCoeffs.coeff (Finsupp.single C a : RDivisor X) P := by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs <;> linarith
    exact add_nonneg h1 (heff P)
  have hsupp_fin : ∀ P, (MMP.Flips.logCanonicalDivisor K Δ - G₂).coeff P ≠ 0 →
      MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX₁ sY' n) (g ≫ φ') P := by
    intro P hP
    rw [hexc_iff]
    by_cases hPC : P = C
    · subst hPC; exact hCexc
    · obtain ⟨P₁, hP₁, hco⟩ := hcoef P hPC
      rw [hco] at hP
      rw [hP₁]
      exact (hexc'_iff P₁).mp (hE'exc P₁ hP)
  have hpos_fin : ∀ P, MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX₁ sY' n) (g ≫ φ') P →
      0 < (MMP.Flips.logCanonicalDivisor K Δ - G₂).coeff P := by
    intro P hP
    rw [hexc_iff] at hP
    by_cases hPC : P = C
    · subst hPC
      rw [hEeq, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_apply,
        Finsupp.single_eq_same]
      exact add_pos_of_pos_of_nonneg ha (heff P)
    · obtain ⟨P₁, hP₁, hco⟩ := hcoef P hPC
      rw [hco]
      rw [hP₁] at hP
      exact hE'pos P₁ ((hexc'_iff P₁).mpr hP)
  refine ⟨n + 1, fun i => modelSeq X₁ Y' i, fun i => inferInstance, fun i => inferInstance,
    fun i => inferInstance, fun i => inferInstance, fun i => modelStr sX₁ sY' i,
    fun i => modelMap π₁ πY' i, fun i => match i with | 0 => g | i + 1 => g' i,
    fun i => divisorSeq K₁ KY' i, fun i => divisorSeq Δ₁ ΔY' i, ?_, hproj, hqf, hklt', hnef',
    g ≫ φ', ?_, hgφ, hK_fin, hΔ_fin, hext_fin, G₂, hG₂c, heff_fin, hsupp_fin, hpos_fin, ?_⟩
  · intro i hi
    rcases i with _ | i
    · exact ⟨hM₁.comp, hg, hgb, ⟨C, hC⟩, hneg, rfl, rfl⟩
    · exact hsteps i (by omega)
  · show (g ≫ φ') ≫ modelMap π₁ πY' n = f
    rw [Category.assoc, hφ'f, hg]
  · rintro ⟨Δq, hΔq⟩
    have hΔ₁q : ∃ Δ₁q : QDivisor X₁, QDivisor.toRDivisor Δ₁q = Δ₁ :=
      ⟨MMP.Mori.RationalMap.transformDivisor g.toRationalMap Δq, by
        rw [hΔ₁, ← hΔq]
        refine Finsupp.ext fun Q => ?_
        obtain ⟨P, hP, -, -⟩ :=
          MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hM₁.normal
            hXg hgb Q
        rw [transformDivisor_apply_of_map_genericPoint hM₁.normal hXg hgb hP]
        change ((MMP.Mori.RationalMap.transformDivisor g.toRationalMap Δq).coeff Q : ℝ) = _
        rw [DivisorWithCoeffs.coeff_apply,
          transformDivisor_apply_of_map_genericPoint hM₁.normal hXg hgb hP]
        rfl⟩
    obtain ⟨⟨Bq, hBq⟩, -⟩ := hE'rat hΔ₁q
    refine ⟨⟨Bq, hBq⟩, ?_⟩
    have hlc : MMP.Flips.logCanonicalDivisor (divisorSeq K₁ KY' n) (divisorSeq Δ₁ ΔY' n) =
        QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K₁ KY' n) + Bq) := by
      rw [map_add, QDivisor.toRDivisor_toQDivisor, hBq]; rfl
    have hG₂q : MMP.Flips.IsRCartierPullback (g ≫ φ')
        (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K₁ KY' n) + Bq)) G₂ := by
      rwa [← hlc]
    obtain ⟨Gq, hGq⟩ := exists_toRDivisor_eq_of_isRCartierPullback (g ≫ φ')
      (MMP.Fourfold.isQCartier_of_isQFactorial _ hqf _) hG₂q
    refine ⟨Divisor.toQDivisor K + Δq - Gq, ?_⟩
    rw [map_sub, map_add, QDivisor.toRDivisor_toQDivisor, hΔq, hGq]
    rfl

include hZ hZn hZd in
/-- Every surface model with `N` prime divisors over closed points of `Z` has a real klt model. -/
private theorem hasRealKltModel_of_ncard_excPrimes_eq (N : ℕ) : ∀ {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X}
    {Δ : RDivisor X}, IsSurfaceModel sZ sX f K Δ → (excPrimes f).ncard = N →
      HasRealKltModel sZ sX f K Δ := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro X _ _ _ _ sX f K Δ hM hN
    by_cases hnef : MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K Δ)
    · exact concl_of_isRelativelyNef sZ hZ hZn hZd hM hnef
    · obtain ⟨X₁, _, _, _, _, sX₁, π₁, g, C, a, G, hg, hgb, hC, hneg, hM₁, hG, hGE, ha, hC2⟩ :=
        exists_divisorialContraction_of_not_isRelativelyNef sZ hZ hZn hZd hM hnef
      have := hneg.isContraction.isProper
      exact concl_of_step sZ hZ hZn hZd hM hg hgb hC hneg hM₁ hG hGE ha hC2 (ih _
        (hN ▸ excPrimes_ncard_lt sZ hZ hZn hZd hM hM₁ hg hgb hneg.isContraction.comp_eq C hC2)
        hM₁ rfl)

end Main

end MMP.Fold06.ThmMmpSurfaceRealBirationalModel

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **Real klt surface models over a projective birational base.** Let `f : X ⟶ Z` be a
projective birational morphism of normal projective complex surfaces, `X` `ℚ`-factorial, `K` a
canonical divisor of `X` and `Δ` an effective real divisor with `(X, Δ)` klt. Then there are
`n : ℕ` and models `X_i = modelSeq X Y i` over `Z`, with divisorial contractions
`g_i : X_i ⟶ X_{i+1}` over `Z` of `(K_i + Δ_i)`-negative extremal rays (`i < n`), where
`K_{i+1} = (g_i)_* K_i` and `Δ_{i+1} = (g_i)_* Δ_i`, such that the last model `Y = X_n` is
projective and `ℚ`-factorial, `(Y, Δ_n)` is klt and `K_n + Δ_n` is nef over `Z`; and the morphism
`φ : X ⟶ Y` over `Z` is birational, extracts no prime divisor, pushes `K` and `Δ` forward to
`K_n` and `Δ_n`, and satisfies `K + Δ = φ^*(K_n + Δ_n) + E` with `E` effective,
`φ`-exceptional and positive along every `φ`-exceptional prime divisor. If `Δ` is a
`ℚ`-divisor, then so are `Δ_n` and `E`. -/
@[mmp "thm_mmp_surface_real_birational_model"]
public theorem exists_surface_divisorial_chain_isRealKltPair
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXn : IsNormalVariety ℂ sX)
    (hXd : topologicalKrullDim X = 2) (hXq : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hZd : topologicalKrullDim Z = 2)
    (hf : f ≫ sZ = sX) (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f)
    (K : Divisor X) (hK : K.IsCanonicalDivisor sX 2)
    (Δ : RDivisor X) (hΔ : ∀ P, 0 ≤ Δ.coeff P) (hklt : IsRealKltPair sX Δ) :
    ∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
      (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
      (sY : ∀ i, Y i ⟶ Spec (.of ℂ)) (πY : ∀ i, Y i ⟶ Z) (g : ∀ i, modelSeq X Y i ⟶ Y i)
      (KY : ∀ i, Divisor (Y i)) (ΔY : ∀ i, RDivisor (Y i)),
      -- the chain of divisorial contractions over `Z`
      (∀ i < n,
        πY i ≫ sZ = sY i ∧ g i ≫ πY i = modelMap f πY i ∧
        IsBirationalMorphism (g i) ∧
        (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
          (MMP.Mori.exceptionalSet (g i) : Set (modelSeq X Y i)) = E.support) ∧
        MMP.Flips.IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sY i)
          (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i) (divisorSeq Δ ΔY i)) (g i) ∧
        KY i = MMP.Mori.RationalMap.transformDivisor (g i).toRationalMap (divisorSeq K KY i) ∧
        ΔY i = MMP.Mori.RationalMap.transformDivisor (g i).toRationalMap (divisorSeq Δ ΔY i)) ∧
      -- the final model
      MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY n) ∧
      IsQFactorial (modelStr sX sY n) ∧
      IsRealKltPair (modelStr sX sY n) (divisorSeq Δ ΔY n) ∧
      MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY n) (modelMap f πY n)
        (MMP.Flips.logCanonicalDivisor (divisorSeq K KY n) (divisorSeq Δ ΔY n)) ∧
      -- the composite morphism and the comparison
      ∃ φ : X ⟶ modelSeq X Y n,
        φ ≫ modelMap f πY n = f ∧ IsBirationalMorphism φ ∧
        divisorSeq K KY n = MMP.Mori.RationalMap.transformDivisor φ.toRationalMap K ∧
        divisorSeq Δ ΔY n = MMP.Mori.RationalMap.transformDivisor φ.toRationalMap Δ ∧
        (∀ Q : MMP.Mori.PrimeDivisor (modelSeq X Y n),
          ∃ D : MMP.Mori.PrimeDivisor X,
            MMP.Mori.RationalMap.transformPrimeDivisor φ.toRationalMap D = some Q) ∧
        ∃ G : RDivisor X,
          MMP.Flips.IsRCartierPullback φ
            (MMP.Flips.logCanonicalDivisor (divisorSeq K KY n) (divisorSeq Δ ΔY n)) G ∧
          (∀ P, 0 ≤ (MMP.Flips.logCanonicalDivisor K Δ - G).coeff P) ∧
          (∀ P, (MMP.Flips.logCanonicalDivisor K Δ - G).coeff P ≠ 0 →
            MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX sY n) φ P) ∧
          (∀ P, MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX sY n) φ P →
            0 < (MMP.Flips.logCanonicalDivisor K Δ - G).coeff P) ∧
          ((∃ Δq : QDivisor X, QDivisor.toRDivisor Δq = Δ) →
            (∃ Bq : QDivisor (modelSeq X Y n), QDivisor.toRDivisor Bq = divisorSeq Δ ΔY n) ∧
            ∃ Eq : QDivisor X,
              QDivisor.toRDivisor Eq = MMP.Flips.logCanonicalDivisor K Δ - G) :=
  MMP.Fold06.ThmMmpSurfaceRealBirationalModel.hasRealKltModel_of_ncard_excPrimes_eq sZ hZ hZn hZd _
    ⟨hX, hXn, hXd, hXq, hf, hfp, hfb, hK, hΔ, hklt⟩ rfl

end MMP.Fourfold
