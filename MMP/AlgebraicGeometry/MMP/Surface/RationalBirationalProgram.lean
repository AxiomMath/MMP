module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.RationalProgram
import MMP.AlgebraicGeometry.MMP.Contraction.RelativeNegativeRay
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialQFactorial
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialContractionKlt
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization

/-!
# thm mmp surface rational birational program q2

Chain fold of: `thm_mmp_surface_rational_birational_program_q2`.
-/

/-! ### `thm_mmp_surface_rational_birational_program_q2` -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fold06.ThmMmpSurfaceRationalBirationalProgramQ2

open MMP MMP.Mori MMP.Fourfold

/-! ### Generic points under morphisms -/

section GenericPoints

variable {A B : Scheme.{0}}

/-- `X ⟶ ⊤_ Scheme` is separated for a variety `X`. -/
private theorem isSeparated_terminal_of_isVariety {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) : IsSeparated (X ↘ ⊤_ Scheme) := by
  have : IsSeparated sX := hX.toIsSeparated
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- Over an open `V` on which `g` restricts to an isomorphism, a point `b ∈ V` has exactly one
preimage, of the same coheight. -/
private theorem exists_unique_of_isIso_morphismRestrict (g : A ⟶ B) (V : B.Opens)
    [IsIso (g ∣_ V)] {b : B} (hb : b ∈ V) :
    ∃ a : A, g a = b ∧ (∀ a', g a' = b → a' = a) ∧ Order.coheight a = Order.coheight b := by
  have hopen : IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g) := by
    rw [← morphismRestrict_ι]; infer_instance
  set y : (g ⁻¹ᵁ V).toScheme := (inv (g ∣_ V)) ⟨b, hb⟩
  have h1 : (g ∣_ V) y = ⟨b, hb⟩ := by
    change ((inv (g ∣_ V)) ≫ (g ∣_ V)) _ = _
    rw [IsIso.inv_hom_id]; rfl
  have h2 := congrArg (fun k : (g ⁻¹ᵁ V).toScheme ⟶ B => k y) (morphismRestrict_ι g V)
  have hgy : g ((g ⁻¹ᵁ V).ι y) = b := by
    change V.ι ((g ∣_ V) y) = g ((g ⁻¹ᵁ V).ι y) at h2
    rw [← h2, h1]; rfl
  refine ⟨(g ⁻¹ᵁ V).ι y, hgy, fun a' ha' => ?_, ?_⟩
  · have ha'V : a' ∈ g ⁻¹ᵁ V := by
      change g a' ∈ V; rwa [ha']
    have := ((g ⁻¹ᵁ V).ι ≫ g).isOpenEmbedding.injective (a₁ := ⟨a', ha'V⟩) (a₂ := y) (by
      change g a' = g ((g ⁻¹ᵁ V).ι y); rw [ha', hgy])
    rw [← this]; rfl
  · have e1 := coheight_eq_of_isOpenImmersion (x := y) ((g ⁻¹ᵁ V).ι ≫ g)
    have e2 := coheight_eq_of_isOpenImmersion (x := y) (g ⁻¹ᵁ V).ι
    change Order.coheight (g ((g ⁻¹ᵁ V).ι y)) = _ at e1
    rw [e2, ← e1, hgy]

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over a
neighbourhood of the generic point of the target. -/
private theorem genericPoint_mem_biregularLocus [IsIntegral A] [IsIntegral B]
    [IsLocallyNoetherian B] [IsNormal B] (g : A ⟶ B) [IsProper g] (hg : IsBirationalMorphism g) :
    genericPoint B ∈ biregularLocus g :=
  MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg <| by
    rw [Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y]; exact zero_le_one

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over a
neighbourhood of the generic point of every prime divisor `Q` of the target: `Q` is the image of
exactly one point, the generic point of a prime divisor of the source. -/
private theorem exists_primeDivisor_of_isBirationalMorphism [IsIntegral A] [IsIntegral B]
    [IsLocallyNoetherian B] [IsNormal B] (g : A ⟶ B) [IsProper g] (hg : IsBirationalMorphism g)
    (Q : Mori.PrimeDivisor B) :
    ∃ P : Mori.PrimeDivisor A, g P.genericPoint = Q.genericPoint ∧
      ∀ a : A, g a = Q.genericPoint → a = P.genericPoint := by
  have hQ := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg
    (y := Q.genericPoint) (by rw [Q.coheight_genericPoint])
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  obtain ⟨a, ha, huniq, hcoh⟩ := exists_unique_of_isIso_morphismRestrict g _ hQ
  rw [Q.coheight_genericPoint] at hcoh
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne a hcoh, ?_, fun a' ha' => ?_⟩
  · change g (AlgebraicGeometry.PrimeDivisor.genericPoint _) = _
    rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  · change _ = AlgebraicGeometry.PrimeDivisor.genericPoint _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]; exact huniq a' ha'

/-- The strict transform of a prime divisor under a morphism is computed on generic points. -/
private theorem transformPrimeDivisor_toRationalMap_eq_some_iff [IsReduced A]
    [IsSeparated (B ↘ ⊤_ Scheme)] (g : A ⟶ B) (P : Mori.PrimeDivisor A) (E : Mori.PrimeDivisor B) :
    RationalMap.transformPrimeDivisor g.toRationalMap P = some E ↔
      g P.genericPoint = E.genericPoint := by
  have hg' : g.toPartialMap.toRationalMap = g.toRationalMap := rfl
  have hP : P.genericPoint ∈ g.toPartialMap.domain := trivial
  have happ : g.toPartialMap.hom ⟨P.genericPoint, hP⟩ = g P.genericPoint := rfl
  constructor
  · intro h
    rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g.toPartialMap hg' hP, happ]
  · intro hE
    refine RationalMap.transformPrimeDivisor_eq_some_iff.mpr
      ⟨RationalMap.definedAt_iff.mpr ⟨g.toPartialMap, hP, hg'⟩, ?_⟩
    have h1 : RationalMap.transform g.toRationalMap P.idealSheaf.support =
        E.idealSheaf.support := by
      apply SetLike.coe_injective
      rw [MMP.Flips.coe_transform_eq_closure_singleton g.toPartialMap hg' P hP, happ, hE]
      exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
    have := E.integral
    rw [RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- Mapping prime divisors along `φ₁` and then `φ₂` is mapping them along the Kleisli
composite of `φ₁` and `φ₂`. -/
private theorem mapPrimeDivisors_mapPrimeDivisors {R : Type*} [AddCommMonoid R] {V : Scheme.{0}}
    (φ₁ : Mori.PrimeDivisor A → Option (Mori.PrimeDivisor B))
    (φ₂ : Mori.PrimeDivisor B → Option (Mori.PrimeDivisor V)) (D : DivisorWithCoeffs R A) :
    DivisorWithCoeffs.mapPrimeDivisors φ₂ (DivisorWithCoeffs.mapPrimeDivisors φ₁ D) =
      DivisorWithCoeffs.mapPrimeDivisors (fun P => (φ₁ P).bind φ₂) D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, map_add, h, h']
  | single P r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases φ₁ P with _ | E
    · simp
    · simp [DivisorWithCoeffs.mapPrimeDivisors_single]

/-- **The strict transform is functorial along a proper birational morphism onto a normal
target.** -/
private theorem transformDivisor_comp {V : Scheme.{0}} [IsReduced A] [IsIntegral B]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [IsSeparated (B ↘ ⊤_ Scheme)]
    [IsSeparated (V ↘ ⊤_ Scheme)] (g : A ⟶ B) (q : B ⟶ V) [IsProper q]
    (hq : IsBirationalMorphism q) (D : QDivisor A) :
    RationalMap.transformDivisor (g ≫ q).toRationalMap D =
      RationalMap.transformDivisor q.toRationalMap
        (RationalMap.transformDivisor g.toRationalMap D) := by
  have key : ∀ P : Mori.PrimeDivisor A,
      RationalMap.transformPrimeDivisor (g ≫ q).toRationalMap P =
        (RationalMap.transformPrimeDivisor g.toRationalMap P).bind
          (RationalMap.transformPrimeDivisor q.toRationalMap) := by
    intro P
    rcases hP : RationalMap.transformPrimeDivisor g.toRationalMap P with _ | E
    · rcases h : RationalMap.transformPrimeDivisor (g ≫ q).toRationalMap P with _ | F
      · rfl
      · exfalso
        rw [transformPrimeDivisor_toRationalMap_eq_some_iff] at h
        obtain ⟨P', -, huniq⟩ := exists_primeDivisor_of_isBirationalMorphism q hq F
        have h' : g P.genericPoint = P'.genericPoint :=
          huniq _ (by rw [← Scheme.Hom.comp_apply]; exact h)
        have := (transformPrimeDivisor_toRationalMap_eq_some_iff g P P').mpr h'
        rw [hP] at this
        cases this
    · rw [transformPrimeDivisor_toRationalMap_eq_some_iff] at hP
      refine Option.ext fun F => ?_
      rw [Option.bind_some, transformPrimeDivisor_toRationalMap_eq_some_iff,
        transformPrimeDivisor_toRationalMap_eq_some_iff, Scheme.Hom.comp_apply, hP]
  change DivisorWithCoeffs.mapPrimeDivisors _ D =
    DivisorWithCoeffs.mapPrimeDivisors _ (DivisorWithCoeffs.mapPrimeDivisors _ D)
  rw [mapPrimeDivisors_mapPrimeDivisors, funext key]

/-- The strict transform under the identity is the identity. -/
private theorem transformDivisor_id {A : Scheme.{0}} [IsReduced A] [IsSeparated (A ↘ ⊤_ Scheme)]
    (D : QDivisor A) : RationalMap.transformDivisor (Scheme.Hom.toRationalMap (𝟙 A)) D = D := by
  have key : ∀ P : Mori.PrimeDivisor A,
      RationalMap.transformPrimeDivisor (Scheme.Hom.toRationalMap (𝟙 A)) P = some P :=
    fun P => (transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 A) P P).mpr rfl
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, h, h']
  | single P r => exact RationalMap.transformDivisor_single_of_eq_some (key P) r

/-- The strict transform of an effective divisor is effective. -/
private theorem coeff_transformDivisor_nonneg (φ : A.RationalMap B) {D : QDivisor A}
    (hD : ∀ P, 0 ≤ D.coeff P) (Q : Mori.PrimeDivisor B) :
    0 ≤ (RationalMap.transformDivisor φ D).coeff Q := by
  rw [← D.sum_single, map_finsuppSum, DivisorWithCoeffs.coeff_apply, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun P _ => ?_
  dsimp only
  rw [RationalMap.transformDivisor_single]
  rcases RationalMap.transformPrimeDivisor φ P with _ | E
  · simp
  · exact Finsupp.single_nonneg.2 (hD P) Q

end GenericPoints

/-! ### Birational morphisms and dimension -/

section Birational

variable {X V S : Scheme.{0}}

/-- For integral schemes, birationality at the generic point is the condition that the generic
point maps to the generic point with an isomorphism of stalks there. -/
private theorem isBirational_iff_of_isIntegral [IsIntegral X] [IsIntegral V] (f : X ⟶ V) :
    IsBirational f ↔
      f (genericPoint X) = genericPoint V ∧ IsIso (f.stalkMap (genericPoint X)) := by
  unfold IsBirational
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
  simp

/-- If `f` and `f ≫ g` are birational at the generic point, so is `g`. -/
private theorem isBirational_of_comp [IsIntegral X] [IsIntegral V] [IsIntegral S] {f : X ⟶ V}
    {g : V ⟶ S} (hf : IsBirational f) (hfg : IsBirational (f ≫ g)) : IsBirational g := by
  rw [isBirational_iff_of_isIntegral] at *
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hfg1, hfg2⟩ := hfg
  refine ⟨by rw [← hf1, ← Scheme.Hom.comp_apply, hfg1], ?_⟩
  rw [Scheme.Hom.stalkMap_comp] at hfg2
  have : IsIso (g.stalkMap (f (genericPoint X))) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hf2 hfg2
  exact hf1 ▸ this

/-- If `q` and `q ≫ h` are birational morphisms and `h` is proper between normal integral
schemes, then `h` is a birational morphism. -/
private theorem isBirationalMorphism_of_comp [IsIntegral X] [IsIntegral V] [IsIntegral S]
    [IsNormal V] [IsNormal S] [IsLocallyNoetherian V] [IsLocallyNoetherian S] (q : X ⟶ V)
    (h : V ⟶ S) [IsProper h] (hq : IsBirationalMorphism q)
    (hqh : IsBirationalMorphism (q ≫ h)) : IsBirationalMorphism h := by
  have hBh : IsBirational h :=
    isBirational_of_comp (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hq)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hqh)
  simpa using isBirationalMorphism_comp_of_isBirational h (𝟙 V) hBh
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      (isBirationalMorphism_of_isIso _))

/-- A proper birational morphism `π : U ⟶ S` from a variety onto a normal integral scheme does not
factor through a scheme of smaller dimension: over the biregular locus of `π`, the morphism
`U ⟶ T` is a topological embedding. -/
private theorem topologicalKrullDim_le_of_comp_eq {U T : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sU : U ⟶ Spec (.of ℂ)} (hU : MMP.Mori.IsVariety ℂ sU)
    {πU : U ⟶ S} [IsProper πU] (hb : IsBirationalMorphism πU) (g : U ⟶ T) (gT : T ⟶ S)
    (h : g ≫ gT = πU) : topologicalKrullDim U ≤ topologicalKrullDim T := by
  haveI : AlgebraicGeometry.IsVariety ℂ sU := hU
  haveI : IsIntegral U := hU.toIsIntegral
  haveI : IsDominant πU := hb.isDominant
  haveI : IsIso (πU ∣_ biregularLocus πU) := isBiregular_biregularLocus πU
  set W : U.Opens := πU ⁻¹ᵁ biregularLocus πU
  have hWne : (W : Set U).Nonempty := ⟨genericPoint U, by
    change πU (genericPoint U) ∈ biregularLocus πU
    rw [map_genericPoint_of_isDominant]; exact genericPoint_mem_biregularLocus πU hb⟩
  have hopen : IsOpenImmersion (W.ι ≫ πU) := by rw [← morphismRestrict_ι]; infer_instance
  have hind : Topology.IsInducing (W.ι ≫ g).base := by
    refine Topology.IsInducing.of_comp (W.ι ≫ g).base.hom.continuous gT.base.hom.continuous ?_
    have : (W.ι ≫ πU).base = (W.ι ≫ g).base ≫ gT.base := by
      rw [← h, ← Category.assoc, Scheme.Hom.comp_base]
    have h2 := (W.ι ≫ πU).isOpenEmbedding.isInducing
    rwa [this] at h2
  rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ U sU _ W.isOpen hWne]
  exact hind.topologicalKrullDim_le

end Birational

/-! ### The relative ray of an absolute ray -/

section RelativeRay

variable {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {π : X ⟶ S}

private theorem degree_relativeToAbsolute (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (z : RelativeNumericalCurveClasses sX π) :
    NumericalCurveClasses.degree sX L (relativeToAbsolute sX π z) =
      RelativeNumericalCurveClasses.degree sX π L z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX π z
  rfl

private theorem continuous_relativeToAbsolute : Continuous (relativeToAbsolute sX π) :=
  continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => continuous_induced_rng.2 <| by
    have := h
    have he : ⇑(NumericalCurveClasses.degree sX L) ∘ ⇑(relativeToAbsolute sX π) =
        RelativeNumericalCurveClasses.degree sX π L :=
      funext (degree_relativeToAbsolute L)
    rw [he]
    exact RelativeNumericalCurveClasses.continuous_degree sX π L

private theorem relativeToAbsolute_mem_coneOfCurves {z : RelativeNumericalCurveClasses sX π}
    (hz : z ∈ relativeConeOfCurves sX π) : relativeToAbsolute sX π z ∈ coneOfCurves sX := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    exact numericalClass_cycle_mem_coneOfCurves sX C
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [show a • x = (a : ℝ) • x from rfl, map_smul]
    exact (coneOfCurves sX).smul_mem a.2 hx

private theorem relativeToAbsolute_mem_closedConeOfCurves
    {z : RelativeNumericalCurveClasses sX π} (hz : z ∈ relativeClosedConeOfCurves sX π) :
    relativeToAbsolute sX π z ∈ closedConeOfCurves sX :=
  closure_mono (Set.image_subset_iff.2 fun _ hw => relativeToAbsolute_mem_coneOfCurves hw)
    (image_closure_subset_closure_image continuous_relativeToAbsolute ⟨z, hz, rfl⟩)

/-- The natural map `N₁(X/S) → N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective :
    Function.Injective (relativeToAbsolute sX π) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX π z
  change (OneCycle.numericallyTrivial sX).mkQ (Z : OneCycle ℝ sX) = 0 at hz
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_relativeNumericallyTrivial.mpr hz)

variable [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

private theorem relativeCurveForm_apply (D : QDivisor X) (h : D.IsQCartier)
    (z : RelativeNumericalCurveClasses sX π) :
    QDivisor.relativeCurveForm sX π D h z =
      QDivisor.curveForm sX D h (relativeToAbsolute sX π z) := by
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, degree_relativeToAbsolute]

/-- **The relative ray of an absolute ray.** A `D`-negative extremal ray `R` of `NE̅(X)` spanned by
the class of a curve `C₀` contracted by `π` is the image of a `D`-negative extremal ray of
`NE̅(X/S)`: the ray spanned by the relative class of `C₀`. A curve contracted by `π` has its
relative class in this ray exactly when its class lies in `R`. -/
private theorem exists_isNegativeRelativeExtremalRayOf {D : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} (hR : IsNegativeExtremalRayOf sX D R)
    (C₀ : ProperCurve sX) (hC₀ : C₀.IsContractedBy π)
    (hRC : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C₀.cycle ℝ) = w}) :
    ∃ Rrel : Set (RelativeNumericalCurveClasses sX π),
      IsNegativeRelativeExtremalRayOf sX π D Rrel ∧
      ∀ (C : ProperCurve sX) (hC : C.IsContractedBy π),
        C.relativeClass π hC ∈ Rrel ↔ OneCycle.numericalClass sX (C.cycle ℝ) ∈ R := by
  obtain ⟨hQ, hRext, hneg⟩ := hR
  set ι := relativeToAbsolute sX π
  set g := C₀.relativeClass π hC₀
  have hιg : ι g = OneCycle.numericalClass sX (C₀.cycle ℝ) := rfl
  set Rrel : Set (RelativeNumericalCurveClasses sX π) := {w | ∃ c : ℝ, 0 ≤ c ∧ c • g = w}
  have key : ∀ z, z ∈ Rrel ↔ ι z ∈ R := by
    intro z
    rw [hRC]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, by rw [map_smul, hιg]⟩
    · rintro ⟨c, hc, hz⟩
      refine ⟨c, hc, relativeToAbsolute_injective ?_⟩
      rw [map_smul, hιg, hz]
  have hg0 : g ≠ 0 := by
    intro hg
    obtain ⟨v, hv, hRv⟩ := hRext.2
    have hvR : v ∈ R := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
    rw [hRC] at hvR
    obtain ⟨c, -, hcv⟩ := hvR
    rw [← hιg, hg, map_zero, smul_zero] at hcv
    exact hv hcv.symm
  refine ⟨Rrel, ⟨hQ, ⟨⟨?_, ?_, ?_, ?_⟩, g, hg0, rfl⟩, fun u hu hu0 => ?_⟩, fun C hC => key _⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact subset_closure ((relativeConeOfCurves sX π).smul_mem hc
      (relativeClass_mem_relativeConeOfCurves hC₀))
  · refine ⟨⟨0, le_rfl, zero_smul _ _⟩, ?_⟩
    rintro _ ⟨c, hc, rfl⟩ c' hc'
    exact ⟨c' * c, mul_nonneg hc'.le hc, by rw [mul_smul]⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    exact ⟨c + c', add_nonneg hc hc', by rw [add_smul]⟩
  · intro u hu v hv huv
    have hu' := relativeToAbsolute_mem_closedConeOfCurves hu
    have hv' := relativeToAbsolute_mem_closedConeOfCurves hv
    have huv' : ι u + ι v ∈ R := by rw [← map_add]; exact (key _).mp huv
    obtain ⟨h1, h2⟩ := hRext.1.2.2.2 _ hu' _ hv' huv'
    exact ⟨(key _).mpr h1, (key _).mpr h2⟩
  · rw [relativeCurveForm_apply]
    refine hneg _ ((key u).mp hu) fun h0 => hu0 (relativeToAbsolute_injective ?_)
    rw [h0, map_zero]

end RelativeRay

/-! ### Negative extremal contractions -/

section NegativeContraction

variable {X V : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- If `L = m D` with `m ≠ 0`, then `D = m⁻¹ L` as `ℝ`-divisors. -/
private theorem toRDivisor_eq_inv_smul {D : QDivisor X} {m : ℤ} (hm : m ≠ 0) {L : Divisor X}
    (hL : Divisor.toQDivisor L = m • D) :
    QDivisor.toRDivisor D = ((m : ℝ)⁻¹) • Divisor.toRDivisor L := by
  ext E
  have h := congrArg (fun D : QDivisor X => D.coeff E) hL
  simp only [Divisor.coeff_toQDivisor] at h
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  rw [mul_comm]
  exact_mod_cast h.symm

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor {D : QDivisor X} (h : D.IsQCartier) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := h
  exact ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, by
    rw [Fin.sum_univ_one]; exact toRDivisor_eq_inv_smul hm hL⟩

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-ample as an `ℝ`-divisor. -/
private theorem isRelativelyAmple_toRDivisor {f : X ⟶ V} [QuasiCompact f] {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) :
    MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have := hL.isInvertibleModule_divisorialSheaf
  refine ⟨1, fun _ => ((m : ℤ) : ℝ)⁻¹, fun _ => L, le_rfl, fun _ => by positivity,
    fun _ => ⟨hL, fun U hU =>
      (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
        inferInstance hamp).2 U hU⟩, ?_⟩
  rw [Fin.sum_univ_one]
  exact toRDivisor_eq_inv_smul (by exact_mod_cast hm.ne') hLD

/-- The contraction of an extremal ray with `-D` relatively ample and relative Picard number one
is a `D`-negative extremal contraction. -/
private theorem isNegativeExtremalContraction_of_isContractionOfRay {sX : X ⟶ Spec (.of ℂ)}
    {sV : V ⟶ Spec (.of ℂ)} {R : Set (NumericalCurveClasses sX)} {q : X ⟶ V} {D : QDivisor X}
    (hqR : IsContractionOfRay sX sV R q) (hD : D.IsQCartier)
    (hamp : (-D).HasRelativelyAmpleMultiple q) (hρ : MMP.Flips.relativePicardNumber sX q = 1) :
    MMP.Flips.IsNegativeExtremalContraction ℂ sX sV (QDivisor.toRDivisor D) q := by
  have hXn := hqR.isNormalVariety_source
  have hVn := hqR.isNormalVariety_target
  have : IsProper q := isProper_of_isProjectiveMorphism _ hqR.isProjectiveMorphism
  refine
    { isNormalVariety_source := hXn
      isNormalVariety_target := hVn
      isCartierCombination := isCartierCombination_toRDivisor hD
      isContraction :=
        { isVariety_target := hVn.1
          isVariety_source := hXn.1
          comp_eq := hqR.comp_eq
          isProper := inferInstance
          isIso_app := hqR.isIso_app }
      isRelativelyAntiAmple := ?_
      relativePicardNumber_eq_one := hρ }
  have h := isRelativelyAmple_toRDivisor hamp
  rwa [map_neg] at h

end NegativeContraction

/-! ### Divisorial contractions of surfaces -/

section Surface

variable {X V : Scheme.{0}}

/-- **A small contraction of a surface contracts no curve.** If a curve `C₀` on a variety of
dimension at most two is contracted by `q`, then `q` is not an isomorphism near the generic point
of `C₀`, so `C₀` lies in the exceptional set of `q`, which then has codimension at most one. -/
private theorem not_isSmallContraction [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} {R : Set (NumericalCurveClasses sX)}
    {q : X ⟶ V} (hX : MMP.Mori.IsVariety ℂ sX)
    (hdim : topologicalKrullDim X ≤ ((2 : ℕ) : WithBot ℕ∞)) (C₀ : ProperCurve sX)
    (hC₀ : C₀.IsContractedBy q) (hsmall : IsSmallContraction ℂ sX sV R q) : False := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  set x := C₀.point
  have hdimC : topologicalKrullDim (closure ({x} : Set X)) = 1 :=
    (MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq x).symm.trans C₀.dim_eq
  have hx : x ∈ (exceptionalSet q : Set X) := by
    intro hmem
    change q x ∈ biregularLocus q at hmem
    haveI : IsIso (q ∣_ biregularLocus q) := isBiregular_biregularLocus q
    obtain ⟨a, -, huniq, -⟩ := exists_unique_of_isIso_morphismRestrict q _ hmem
    have hcl : closure ({x} : Set X) = {x} := by
      refine le_antisymm (fun y hy => ?_) subset_closure
      exact (huniq y (hC₀ y hy)).trans (huniq x rfl).symm
    rw [hcl] at hdimC
    haveI : Subsingleton ({x} : Set X) := Set.subsingleton_singleton.coe_sort
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({x} : Set X)
    rw [hdimC] at h0
    exact absurd h0 (by decide)
  have hcoh : 2 ≤ Order.coheight x :=
    (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hsmall.two_le_codimension) x hx
  have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  rw [hdimC] at hsum
  have h3 : ((3 : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    rw [← hsum]
    exact_mod_cast (add_le_add le_rfl hcoh : (1 + 2 : ℕ∞) ≤ _)
  exact absurd (h3.trans hdim) (by decide)

/-- **The number of prime divisors contracted over the base drops.** Let `q : X ⟶ V` and
`h : V ⟶ S` be proper birational morphisms of integral schemes onto normal ones, with
`Ex(q)` a prime divisor `E`. Every prime divisor of `V` contracted by `h` is the strict
transform of a prime divisor of `X` contracted by `q ≫ h` other than `E`, and `E` itself is
contracted by `q ≫ h`. -/
private theorem ncard_exc_lt [IsIntegral X] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] (q : X ⟶ V)
    (h : V ⟶ S) [IsProper q] [IsProper h] (hq : IsBirationalMorphism q)
    (hh : IsBirationalMorphism h) {π : X ⟶ S} (hqh : q ≫ h = π) (E : Mori.PrimeDivisor X)
    (hE : (exceptionalSet q : Set X) = E.support)
    (hfin : {P : Mori.PrimeDivisor X | ∀ Q : Mori.PrimeDivisor S,
      π P.genericPoint ≠ Q.genericPoint}.Finite) :
    {P : Mori.PrimeDivisor V | ∀ Q : Mori.PrimeDivisor S,
        h P.genericPoint ≠ Q.genericPoint}.ncard <
      {P : Mori.PrimeDivisor X | ∀ Q : Mori.PrimeDivisor S,
        π P.genericPoint ≠ Q.genericPoint}.ncard := by
  subst hqh
  -- a point mapping to the generic point of a prime divisor of `V` is not in `Ex(q)`
  have hnot : ∀ (Q' : Mori.PrimeDivisor V), q E.genericPoint ≠ Q'.genericPoint := by
    intro Q' hQ'
    have hmem : E.genericPoint ∈ (exceptionalSet q : Set X) := by
      rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    apply hmem
    change q E.genericPoint ∈ biregularLocus q
    rw [hQ']
    exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal q hq
      (by rw [Q'.coheight_genericPoint])
  have hEmem : E ∈ {P : Mori.PrimeDivisor X | ∀ Q : Mori.PrimeDivisor S,
      (q ≫ h) P.genericPoint ≠ Q.genericPoint} := by
    intro Q hQ
    obtain ⟨P', -, huniq⟩ := exists_primeDivisor_of_isBirationalMorphism h hh Q
    exact hnot P' (huniq _ (by rw [← Scheme.Hom.comp_apply]; exact hQ))
  choose g hg _ using fun Q' : Mori.PrimeDivisor V =>
    exists_primeDivisor_of_isBirationalMorphism q hq Q'
  set Sx := {P : Mori.PrimeDivisor X | ∀ Q : Mori.PrimeDivisor S,
    (q ≫ h) P.genericPoint ≠ Q.genericPoint}
  set Sv := {P : Mori.PrimeDivisor V | ∀ Q : Mori.PrimeDivisor S,
    h P.genericPoint ≠ Q.genericPoint}
  have hmaps : ∀ Q' ∈ Sv, g Q' ∈ Sx \ {E} := by
    intro Q' hQ'
    refine ⟨fun Q hQ => ?_, fun hgE => ?_⟩
    · rw [Scheme.Hom.comp_apply, hg] at hQ
      exact hQ' Q hQ
    · exact hnot Q' (by rw [← Set.mem_singleton_iff.mp hgE, hg])
  have hinj : Set.InjOn g Sv := fun Q₁ _ Q₂ _ h12 =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hg Q₁).symm.trans ((congrArg (fun P => q (Mori.PrimeDivisor.genericPoint P)) h12).trans
        (hg Q₂)))
  exact lt_of_le_of_lt (Set.ncard_le_ncard_of_injOn g hmaps hinj hfin.diff)
    (Set.ncard_diff_singleton_lt_of_mem hEmem hfin)

end Surface

/-! ### Models over the base -/

variable {W Z : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]

/-- A model over `Z` of the program from `W`: a normal integral scheme `X` over `ℂ` with a
morphism to `Z`, a canonical divisor `K`, a boundary `B` and a morphism `ψ : W ⟶ X`. -/
private structure Model (W Z : Scheme.{0}) where
  X : Scheme.{0}
  [isIntegral : IsIntegral X]
  [compactSpace : CompactSpace X]
  [isLocallyNoetherian : IsLocallyNoetherian X]
  [isNormal : IsNormal X]
  sX : X ⟶ Spec (.of ℂ)
  π : X ⟶ Z
  K : Divisor X
  B : QDivisor X
  ψ : W ⟶ X

attribute [local instance] Model.isIntegral Model.compactSpace Model.isLocallyNoetherian
  Model.isNormal

/-- The invariants of a model of the program from `(W, C)` over `p : W ⟶ Z`. -/
private structure Model.Good (sZ : Z ⟶ Spec (.of ℂ)) (p : W ⟶ Z) (C : QDivisor W)
    (s : Model W Z) : Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ s.sX
  comp_eq : s.π ≫ sZ = s.sX
  isProjectiveMorphism : IsProjectiveMorphism s.π
  isQFactorial : IsQFactorial s.sX
  isKltPair : MMP.Mori.IsKltPair s.sX 2 s.K s.B
  nonneg : ∀ P, 0 ≤ s.B.coeff P
  isBirationalMorphism : IsBirationalMorphism s.π
  dim_le : topologicalKrullDim s.X ≤ ((2 : ℕ) : WithBot ℕ∞)
  ψ_comp : s.ψ ≫ s.π = p
  isProper_ψ : IsProper s.ψ
  isBirationalMorphism_ψ : IsBirationalMorphism s.ψ
  B_eq : s.B = RationalMap.transformDivisor s.ψ.toRationalMap C

/-- The adjoint `K + B` of the model is nef over `Z`. -/
private def Model.IsNef (s : Model W Z) : Prop :=
  QDivisor.IsRelativelyNef s.sX s.π (Divisor.toQDivisor s.K + s.B)

/-- The prime divisors of the model contracted over `Z`: those whose generic point is not mapped
to the generic point of a prime divisor of `Z`. -/
private def Model.exc (s : Model W Z) : Set (Mori.PrimeDivisor s.X) :=
  {P | ∀ Q : Mori.PrimeDivisor Z, s.π P.genericPoint ≠ Q.genericPoint}

/-- The data of a step of the program from the model `s` to the model `t`. -/
private structure StepData (s t : Model W Z) where
  R : Set (RelativeNumericalCurveClasses s.sX s.π)
  Zs : Scheme.{0}
  sZs : Zs ⟶ Spec (.of ℂ)
  f : s.X ⟶ Zs
  gZ : Zs ⟶ Z
  fp : t.X ⟶ Zs
  φ : s.X.RationalMap t.X

/-- The data of the trivial step, used where no step is taken. -/
private noncomputable def StepData.refl (s : Model W Z) : StepData s s :=
  ⟨∅, s.X, s.sX, 𝟙 _, s.π, 𝟙 _, Scheme.Hom.toRationalMap (𝟙 s.X)⟩

/-- The properties of a step of the program. -/
private def StepData.IsStep {s t : Model W Z} (d : StepData s t) : Prop :=
  IsElementaryDltStep s.sX s.π d.sZs t.sX t.π s.K s.B d.R d.f d.gZ d.fp d.φ ∧
    t.B = RationalMap.transformDivisor d.φ s.B

variable {sZ : Z ⟶ Spec (.of ℂ)} {p : W ⟶ Z} {C : QDivisor W}

/-- The prime divisors contracted over `Z` by a good model are finitely many. -/
private theorem Model.Good.finite_exc (hZn : IsNormalVariety ℂ sZ) {s : Model W Z}
    (hs : s.Good sZ p C) : s.exc.Finite := by
  have := hZn.1.toIsIntegral
  have : IsNormal Z := hZn.2
  have : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsProper s.π := isProper_of_isProjectiveMorphism _ hs.isProjectiveMorphism
  have : IsNoetherian s.X := ⟨⟩
  haveI : IsIso (s.π ∣_ biregularLocus s.π) := isBiregular_biregularLocus s.π
  haveI : IsDominant s.π := hs.isBirationalMorphism.isDominant
  refine (MMP.Mori.finite_setOf_genericPoint_mem (exceptionalSet s.π).isClosed ?_).subset ?_
  · intro x hx h0
    have hmax : IsMax x := Order.coheight_eq_zero.mp h0
    have hgx : x = genericPoint s.X :=
      (Specializes.antisymm (hmax (genericPoint_specializes x)) (genericPoint_specializes x)).eq
    apply hx
    change s.π x ∈ biregularLocus s.π
    rw [hgx, map_genericPoint_of_isDominant]
    exact genericPoint_mem_biregularLocus s.π hs.isBirationalMorphism
  · intro P hP
    change s.π P.genericPoint ∉ biregularLocus s.π
    intro hmem
    obtain ⟨a, -, huniq, hcoh⟩ := exists_unique_of_isIso_morphismRestrict s.π _ hmem
    rw [← huniq P.genericPoint rfl, P.coheight_genericPoint] at hcoh
    refine hP (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh.symm) ?_
    change _ = AlgebraicGeometry.PrimeDivisor.genericPoint _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]

/-- A good model is klt in the sense of the fourfold program. -/
private theorem Model.Good.isKltPair_fourfold {s : Model W Z} (hs : s.Good sZ p C) :
    MMP.Fourfold.IsKltPair s.sX s.B :=
  (isKltPair_iff_mori_isKltPair s.sX hs.isKltPair.1.2.1
    ⟨inferInstance, inferInstance, hs.isKltPair.1.isPair, hs.nonneg⟩).mpr hs.isKltPair

/-- The contraction of a negative extremal ray of a good model, spanned by a curve, onto a
projective variety of dimension at least that of the model is divisorial. -/
private theorem Model.Good.isDivisorialContraction {s : Model W Z} (hs : s.Good sZ p C)
    {R : Set (NumericalCurveClasses s.sX)}
    (hRneg : IsNegativeExtremalRayOf s.sX (Divisor.toQDivisor s.K + s.B) R) {C₀ : ProperCurve s.sX}
    (hRC : R = {w | ∃ c : ℝ, 0 ≤ c ∧
      c • (OneCycle.numericalClass s.sX) (ProperCurve.cycle ℝ C₀) = w})
    {V : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {q : s.X ⟶ V} (hqR : IsContractionOfRay s.sX sV R q)
    (hVp : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hdim : topologicalKrullDim s.X ≤ topologicalKrullDim V) :
    IsDivisorialContraction ℂ s.sX sV R q := by
  have hRext := hRneg.choose_spec.1
  have hface : IsContractionOfFace ℂ s.sX sV R q :=
    { isProjectiveVariety_source := hs.isProjectiveVariety
      isProjectiveVariety_target := hVp
      comp_eq := hqR.comp_eq
      isExtremalFace := hRext.1
      isContractedBy_iff := hqR.isContractedBy_iff
      isIso_app := hqR.isIso_app }
  have hC₀q : C₀.IsContractedBy q :=
    (hqR.isContractedBy_iff C₀).mpr (by rw [hRC]; exact ⟨1, zero_le_one, one_smul _ _⟩)
  rcases (hface.trichotomy_of_isExtremalRay hs.isQFactorial hRext).1 with hfib | hdiv | hsm
  · exact absurd hfib.dim_lt (not_lt.mpr hdim)
  · exact hdiv
  · exact (not_isSmallContraction hs.isProjectiveVariety.toIsVariety hs.dim_le C₀ hC₀q hsm).elim

/-- The transform of a good model along a proper birational morphism `q` onto a Q-factorial klt
projective variety, projective and birational over `Z`, is good. -/
private theorem Model.Good.transform [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (hZd : topologicalKrullDim Z = 2) {s : Model W Z} (hs : s.Good sZ p C) {V : Scheme.{0}}
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)}
    (q : s.X ⟶ V) (h : V ⟶ Z) [IsProper q]
    (hqb : IsBirationalMorphism q) (hqh : q ≫ h = s.π) (hVp : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hsV : h ≫ sZ = sV) (hhproj : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hVQ : IsQFactorial sV)
    (hVklt : MMP.Mori.IsKltPair sV 2 (RationalMap.transformDivisor q.toRationalMap s.K)
      (RationalMap.transformDivisor q.toRationalMap s.B)) :
    (⟨V, sV, h, RationalMap.transformDivisor q.toRationalMap s.K,
      RationalMap.transformDivisor q.toRationalMap s.B, s.ψ ≫ q⟩ : Model W Z).Good sZ p C := by
  have : IsProper h := isProper_of_isProjectiveMorphism _ hhproj
  have := hs.isProper_ψ
  have := isSeparated_terminal_of_isVariety hs.isProjectiveVariety.toIsVariety
  have := isSeparated_terminal_of_isVariety hVp.toIsVariety
  exact
    { isProjectiveVariety := hVp
      comp_eq := hsV
      isProjectiveMorphism := hhproj
      isQFactorial := hVQ
      isKltPair := hVklt
      nonneg := coeff_transformDivisor_nonneg _ hs.nonneg
      isBirationalMorphism := hhb
      dim_le := (topologicalKrullDim_le_of_comp_eq hVp.toIsVariety hhb h (𝟙 Z)
        (Category.comp_id h)).trans (by rw [hZd]; rfl)
      ψ_comp := by
        change (s.ψ ≫ q) ≫ h = p
        rw [Category.assoc, hqh, hs.ψ_comp]
      isProper_ψ := inferInstance
      isBirationalMorphism_ψ := isBirationalMorphism_comp hs.isBirationalMorphism_ψ hqb
      B_eq := by
        change RationalMap.transformDivisor q.toRationalMap s.B = _
        rw [hs.B_eq]
        exact (transformDivisor_comp s.ψ q hqb C).symm }

/-- **The step.** If the adjoint of a good model is not nef over `Z`, the divisorial contraction
of a negative extremal ray spanned by a curve contracted over `Z` is a step of the program to a
good model with fewer prime divisors contracted over `Z`. -/
private theorem exists_step (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hZd : topologicalKrullDim Z = 2) {s : Model W Z}
    (hs : s.Good sZ p C) (hnef : ¬ s.IsNef) :
    ∃ (t : Model W Z) (d : StepData s t), t.Good sZ p C ∧ d.IsStep ∧
      t.exc.ncard < s.exc.ncard := by
  have : IsIntegral Z := hZn.1.toIsIntegral
  have : IsNormal Z := hZn.2
  have : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsSeparated sZ := hZn.1.toIsSeparated
  have hXp := hs.isProjectiveVariety
  have : IsProper s.π := isProper_of_isProjectiveMorphism _ hs.isProjectiveMorphism
  have hK2 : s.K.IsCanonicalDivisor s.sX 2 := hs.isKltPair.1.2.1
  obtain ⟨R, hRneg, ⟨C₀, hC₀π, hRC⟩, V, sV, q, hqR, hVp, -, hρ, hamp, ⟨h, hqh, hsV⟩, -⟩ :=
    exists_isContractionOfRay_comp_eq_of_not_isRelativelyNef s.sX hXp hs.isKltPair_fourfold hK2 hZ
      hs.comp_eq hnef
  have hVn : IsNormalVariety ℂ sV := hqR.isNormalVariety_target
  have : IsIntegral V := hVn.1.toIsIntegral
  have : IsNormal V := hVn.2
  have : LocallyOfFiniteType sV := hVn.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : QuasiCompact sV := hVn.1.toQuasiCompact
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : IsProper q := isProper_of_isProjectiveMorphism _ hqR.isProjectiveMorphism
  have hhproj : IsProjectiveMorphism h :=
    IsProjectiveMorphism.of_comp h sZ (by rw [hsV]; exact hVp.isProjective)
  have : IsProper h := isProper_of_isProjectiveMorphism _ hhproj
  have hdiv := hs.isDivisorialContraction hRneg hRC hqR hVp
    (topologicalKrullDim_le_of_comp_eq hXp.toIsVariety hs.isBirationalMorphism q h hqh)
  obtain ⟨E, hE⟩ := hdiv.exists_primeDivisor
  have hqb := hdiv.isBirationalMorphism
  have hhb : IsBirationalMorphism h :=
    isBirationalMorphism_of_comp q h hqb (hqh ▸ hs.isBirationalMorphism)
  have hVQ : IsQFactorial sV := isQFactorial_of_isDivisorialContraction hs.isQFactorial
    hs.isKltPair hs.nonneg hRneg.choose_spec.2 hdiv
  have hVklt := hdiv.isKltPair_transformDivisor hs.isQFactorial hRneg
    (Or.inl (Finsupp.le_def.mpr hs.nonneg)) hs.isKltPair
  let t : Model W Z := ⟨V, sV, h, RationalMap.transformDivisor q.toRationalMap s.K,
    RationalMap.transformDivisor q.toRationalMap s.B, s.ψ ≫ q⟩
  have ht : t.Good sZ p C := hs.transform hZd q h hqb hqh hVp hsV hhproj hhb hVQ hVklt
  obtain ⟨Rrel, hRrel, hkey⟩ := exists_isNegativeRelativeExtremalRayOf hRneg C₀ hC₀π hRC
  let d : StepData s t := ⟨Rrel, V, sV, q, h, 𝟙 V, q.toRationalMap⟩
  have hd : d.IsStep := by
    refine ⟨{ isNegativeRelativeRayContraction := ⟨hRrel, ?_, ?_⟩
              comp_eq := Category.id_comp h
              divisorial_or_flip := Or.inl ⟨hqb, ⟨E, hE⟩, inferInstance, hqb, ?_⟩ }, rfl⟩
    · exact
        { isExtremalFace := hRrel.choose_spec.1.1
          isProjectiveMorphism := hhproj
          comp_eq := hqh
          isIso_app := hqR.isIso_app
          isContractedBy_iff := fun C hC => (hqR.isContractedBy_iff C).trans (hkey C hC).symm }
    · exact isNegativeExtremalContraction_of_isContractionOfRay hqR hRneg.choose hamp hρ
    · change (q ≫ 𝟙 V).toRationalMap = q.toRationalMap
      rw [Category.comp_id]
  exact ⟨t, d, ht, hd, ncard_exc_lt q h hqb hhb hqh E hE (hs.finite_exc hZn)⟩

/-- A good model is a model of a relative elementary dlt program. -/
private theorem Model.Good.isRelativeDltModel (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {s : Model W Z} (hs : s.Good sZ p C) :
    IsRelativeDltModel s.sX sZ s.π s.K s.B := by
  have := hs.isProjectiveVariety
  have := hZ
  exact
    { isQuasiProjectiveVariety_base := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sZ
      isQuasiProjectiveVariety := IsProjectiveVariety.isQuasiProjectiveVariety ℂ s.sX
      comp_eq := hs.comp_eq
      isProjectiveMorphism := hs.isProjectiveMorphism
      isQFactorial := hs.isQFactorial
      isCanonicalDivisor := ⟨2, hs.isKltPair.1.2.1⟩
      isDltPair := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair s.sX hs.isKltPair.1.2.1 s.B).mpr
        (MMP.Threefold.Mori.IsKltPair.isDltPair hs.isKltPair hs.nonneg).1 }

/-- The output of the program at a good model with nef adjoint. -/
private theorem Model.Good.final {s : Model W Z} (hs : s.Good sZ p C) (hnef : s.IsNef) :
    IsQFactorial s.sX ∧ MMP.Mori.IsProjectiveVariety ℂ s.sX ∧ IsProjectiveMorphism s.π ∧
      IsKltPair s.sX s.B ∧
      QDivisor.IsRelativelyNef s.sX s.π (Divisor.toQDivisor s.K + s.B) ∧
      ∃ φ : W.RationalMap s.X, MMP.Mori.RationalMap.IsBirational φ ∧
        MMP.Flips.RationalMap.IsOver p s.π φ ∧ s.B = RationalMap.transformDivisor φ C ∧
        ∀ Q : Mori.PrimeDivisor s.X, ∃ D : Mori.PrimeDivisor W,
          RationalMap.transformPrimeDivisor φ D = some Q := by
  have := hs.isProper_ψ
  have := isSeparated_terminal_of_isVariety hs.isProjectiveVariety.toIsVariety
  refine ⟨hs.isQFactorial, hs.isProjectiveVariety, hs.isProjectiveMorphism, hs.isKltPair_fourfold,
    hnef, s.ψ.toRationalMap, hs.isBirationalMorphism_ψ, ?_, hs.B_eq, fun Q => ?_⟩
  · change (s.ψ ≫ s.π).toRationalMap = p.toRationalMap
    rw [hs.ψ_comp]
  · obtain ⟨D, hD, -⟩ := exists_primeDivisor_of_isBirationalMorphism s.ψ
      hs.isBirationalMorphism_ψ Q
    exact ⟨D, (transformPrimeDivisor_toRationalMap_eq_some_iff s.ψ D Q).mpr hD⟩

/-! ### Iterating the step -/

/-- A step from every model, which is a step of the program with the decrease of `exc` whenever
the model is good and its adjoint is not nef. -/
private theorem exists_next (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hZd : topologicalKrullDim Z = 2) (s : Model W Z) :
    ∃ x : Σ t : Model W Z, StepData s t, s.Good sZ p C → ¬ s.IsNef →
      x.1.Good sZ p C ∧ x.2.IsStep ∧ x.1.exc.ncard < s.exc.ncard := by
  by_cases h : s.Good sZ p C ∧ ¬ s.IsNef
  · obtain ⟨t, d, ht, hd, hlt⟩ := exists_step hZ hZn hZd h.1 h.2
    exact ⟨⟨t, d⟩, fun _ _ => ⟨ht, hd, hlt⟩⟩
  · exact ⟨⟨s, StepData.refl s⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

/-- The orbit of a model under a choice of steps. -/
private noncomputable def orbit (nx : ∀ s : Model W Z, Σ t : Model W Z, StepData s t)
    (s₀ : Model W Z) : ℕ → Model W Z
  | 0 => s₀
  | i + 1 => (nx (orbit nx s₀ i)).1

/-- Along the orbit of a good model under steps that keep models good and decrease `exc` while
the adjoint is not nef, some stage has a nef adjoint, and the stages up to the first such are
good. -/
private theorem exists_isNef_orbit {nx : ∀ s : Model W Z, Σ t : Model W Z, StepData s t}
    (hnx : ∀ s : Model W Z, s.Good sZ p C → ¬ s.IsNef →
      (nx s).1.Good sZ p C ∧ (nx s).2.IsStep ∧ (nx s).1.exc.ncard < s.exc.ncard)
    {s₀ : Model W Z} (h₀ : s₀.Good sZ p C) :
    ∃ N, (orbit nx s₀ N).IsNef ∧ (∀ i < N, ¬ (orbit nx s₀ i).IsNef) ∧
      ∀ i ≤ N, (orbit nx s₀ i).Good sZ p C := by
  have hex : ∃ N, (orbit nx s₀ N).IsNef := by
    by_contra hne
    push Not at hne
    have hg : ∀ i, (orbit nx s₀ i).Good sZ p C ∧ (orbit nx s₀ i).exc.ncard + i ≤ s₀.exc.ncard := by
      intro i
      induction i with
      | zero => exact ⟨h₀, le_rfl⟩
      | succ i ih =>
        obtain ⟨hg', -, hlt⟩ := hnx _ ih.1 (hne i)
        rw [show orbit nx s₀ (i + 1) = (nx (orbit nx s₀ i)).1 from rfl]
        exact ⟨hg', by omega⟩
    have := (hg (s₀.exc.ncard + 1)).2
    omega
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi, fun i => ?_⟩
  induction i with
  | zero => exact fun _ => h₀
  | succ i ih => exact fun hi => (hnx _ (ih (by omega)) (Nat.find_min hex (by omega))).1

/-! ### The program -/

/-- The initial model `(W, C)` over `Z` is good. -/
private theorem good_initial {sW : W ⟶ Spec (.of ℂ)} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWn : IsNormalVariety ℂ sW) (hWsm : IsSmoothScheme sW)
    (hWd : topologicalKrullDim W = ((2 : ℕ) : WithBot ℕ∞)) (hpZ : p ≫ sZ = sW)
    (hpproj : IsProjectiveMorphism p) (hpbir : IsBirationalMorphism p) {K : Divisor W}
    (hK : K.IsCanonicalDivisor sW 2) (hC : ∀ P, 0 ≤ C.coeff P ∧ C.coeff P < 1)
    (hCsnc : DivisorWithCoeffs.IsSNC sW C) :
    (⟨W, sW, p, K, C, 𝟙 W⟩ : Model W Z).Good sZ p C where
  isProjectiveVariety := hW
  comp_eq := hpZ
  isProjectiveMorphism := hpproj
  isQFactorial := ⟨hWn, fun D => ⟨1, one_pos, by simpa using isCartier_of_isSmoothScheme hWsm D⟩⟩
  isKltPair := isKltPair_of_isSNC sW hWn hWsm hK hCsnc fun E => (hC E).2
  nonneg := fun P => (hC P).1
  isBirationalMorphism := hpbir
  dim_le := hWd.le
  ψ_comp := Category.id_comp p
  isProper_ψ := inferInstance
  isBirationalMorphism_ψ := isBirationalMorphism_of_isIso _
  B_eq := by
    have := isSeparated_terminal_of_isVariety hW.toIsVariety
    exact (transformDivisor_id C).symm

/-- **The rational birational program property `Q(2)`.** -/
private theorem solution : MMP.Fourfold.RationalBirationalProgramProperty 2 := by
  refine ⟨by norm_num, ?_⟩
  intro W _ _ _ _ sW Z sZ p hW hWn hWsm hWd hZ hZn hZd hpZ hpproj hpbir K hK C hC hCsnc
  let s₀ : Model W Z := ⟨W, sW, p, K, C, 𝟙 W⟩
  have h₀ : s₀.Good sZ p C :=
    good_initial hW hWn hWsm hWd hpZ hpproj hpbir hK hC hCsnc
  have hZd' : topologicalKrullDim Z = 2 := by exact_mod_cast hZd
  choose nx hnx using exists_next (p := p) (C := C) hZ hZn hZd'
  let S := orbit nx s₀
  obtain ⟨N, hNnef, hlt, hgood⟩ := exists_isNef_orbit hnx h₀
  have hstep : ∀ i < N, (nx (S i)).2.IsStep := fun i hi =>
    (hnx (S i) (hgood i hi.le) (hlt i hi)).2.1
  let dat : ∀ i, StepData (S i) (S (i + 1)) := fun i => (nx (S i)).2
  let P : RelativeDltProgram sW sZ p K C :=
  { n := N
    Y := fun i => (S (i + 1)).X
    sY := fun i => (S (i + 1)).sX
    isIntegral := fun i => inferInstance
    compactSpace := fun i => inferInstance
    isLocallyNoetherian := fun i => inferInstance
    isNormal := fun i => inferInstance
    πY := fun i => (S (i + 1)).π
    KY := fun i => (S (i + 1)).K
    BY := fun i => (S (i + 1)).B
    R := fun i => match i with
      | 0 => (dat 0).R
      | i + 1 => (dat (i + 1)).R
    Z := fun i => (dat i).Zs
    sZ := fun i => (dat i).sZs
    f := fun i => match i with
      | 0 => (dat 0).f
      | i + 1 => (dat (i + 1)).f
    gZ := fun i => (dat i).gZ
    fp := fun i => (dat i).fp
    φ := fun i => match i with
      | 0 => (dat 0).φ
      | i + 1 => (dat (i + 1)).φ
    isRelativeDltModel := fun i hi => match i, hi with
      | 0, _ => h₀.isRelativeDltModel hZ
      | i + 1, hi => (hgood (i + 1) (by exact_mod_cast hi)).isRelativeDltModel hZ
    isElementaryDltStep := fun i hi => match i, hi with
      | 0, hi => (hstep 0 (by exact_mod_cast hi)).1
      | i + 1, hi => (hstep (i + 1) (by exact_mod_cast hi)).1
    BY_eq := fun i hi => match i, hi with
      | 0, hi => (hstep 0 (by exact_mod_cast hi)).2
      | i + 1, hi => (hstep (i + 1) (by exact_mod_cast hi)).2
    hasFinal := False
    finalRay := ∅
    T := Z
    sT := sZ
    gT := 𝟙 Z
    g := modelMap p (fun i => (S (i + 1)).π) _
    final_spec := fun h => h.elim }
  refine ⟨P, ENat.coe_ne_top N, ⟨hZ, fun i hi => ?_⟩, not_false, ?_⟩
  · rcases i with _ | i
    · exact h₀.isProjectiveVariety
    · exact (hgood (i + 1) (ENat.coe_le_coe.mp hi)).isProjectiveVariety
  · -- the final model is `modelStr … N`, which unfolds to `S N` only case by case
    rcases N with _ | N <;> exact (hgood _ le_rfl).final hNnef

end MMP.Fold06.ThmMmpSurfaceRationalBirationalProgramQ2

namespace MMP.Fourfold

/-- **The rational birational program property holds for surfaces.** Every projective birational
morphism of normal projective complex surfaces with smooth source, together with an effective
snc `ℚ`-boundary of coefficients less than one, admits a finite projective negative program over
the base. The program ends with a `ℚ`-factorial klt model with nef adjoint, the boundary is the
push-forward, and no prime divisor is extracted. See `RationalBirationalProgramProperty`. -/
@[mmp "thm_mmp_surface_rational_birational_program_q2"]
public theorem rationalBirationalProgramProperty_two : RationalBirationalProgramProperty 2 :=
  MMP.Fold06.ThmMmpSurfaceRationalBirationalProgramQ2.solution

end MMP.Fourfold
