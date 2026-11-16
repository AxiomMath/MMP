module

public import MMP.AlgebraicGeometry.ChowForm.FibreRestriction
import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureAssociatedPoints
import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TowerProjective
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceHyperplaneSection

/-!
# The Chow form of a closed fibre

Auxiliary declarations for the Chow form of a proper flat family of curves
(`MMP.Chow.DeterminantCurveForm`), split out of the proof of the determinant curve form.

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3
-/

@[expose] public section

universe u

namespace MMP.Chow.DeterminantCurveForm

open CategoryTheory AlgebraicGeometry

open MMP CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Defs

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} {N : ℕ}

section Skeleton

section CoreLemmas

attribute [local instance] LocalFreeData.isOpenImmersion LocalFreeData.isAffine
  LocalFreeData.isDomain LocalFreeData.isNoetherian LocalFreeData.isIntegrallyClosed
  LocalFreeData.locFT

attribute [local instance] KoszulFamily.invertible

variable {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)} {S 𝒞 : Scheme.{u}}
  {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}

section FibreChow

attribute [local instance] isInvertibleModule_fibreH
attribute [local instance] isNoetherian_proj

/-- The degree of `𝒪(1)` on a curve of `ℙᴺ` is positive. -/
theorem curveDeg_pos (C : Mori.ProperCurve (projToSpecCoeff k N)) : 0 < curveDeg C := by
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  haveI : IsIntegral C.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k N
  haveI : AlgebraicGeometry.IsCurve k (C.ι ≫ projToSpecCoeff k N) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance,
      topologicalKrullDim_eq_one := C.dim_eq }
  haveI : SheafOfModules.IsInvertible C.scheme.presheaf C.scheme.ringCatSheaf.2
      ((Scheme.Modules.pullback C.ι).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback C.ι _
  exact invertibleCurveDegree_pos_of_isAmple_of_isCurve k (C.ι ≫ projToSpecCoeff k N) C.dim_le _
    (isAmple_pullback_of_isFinite C.ι _
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr
        (Stacks.ProjectiveSpace.isAmple_twistingSheaf_one k N)))

/-- The closure of a point of a quasi-sober `T₀` space is an irreducible component exactly when the
point has no proper generization. -/
theorem closure_singleton_mem_irreducibleComponents_iff {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] (η : X) :
    closure ({η} : Set X) ∈ irreducibleComponents X ↔ ∀ η', η' ⤳ η → η' = η := by
  constructor
  · intro h η' hη'
    have h1 : closure ({η} : Set X) ⊆ closure {η'} :=
      closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.mp hη'))
        isClosed_closure
    have h2 := h.2 isIrreducible_singleton.closure h1
    have h3 : η ⤳ η' := specializes_iff_mem_closure.mpr (h2 (subset_closure rfl))
    exact (hη'.antisymm h3).eq
  · intro h
    have hgen := isIrreducible_irreducibleComponent.isGenericPoint_genericPoint
      (isClosed_irreducibleComponent (x := η))
    have hsp := hgen.specializes (mem_irreducibleComponent (x := η))
    have he := h _ hsp
    have hc : closure ({η} : Set X) = irreducibleComponent η := by
      have := hgen.def
      rwa [he] at this
    rw [hc]
    exact irreducibleComponent_mem_irreducibleComponents η

open Classical in
/-- The coefficient of a proper curve `C` in the push-forward of a point, times the degree of `L`
on `C`, is the degree of `L` on the push-forward if the point maps to the generic point of `C`,
and `0` otherwise. -/
theorem cyclePushforwardOfPoint_apply_mul_degree {K : Type u} [Field K] {X' Y' : Scheme.{u}}
    (sY : Y' ⟶ Spec (.of K)) (φ : X' ⟶ Y') (x : X') (C : Mori.ProperCurve sY) (L : Y'.Modules)
    [SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2 L] :
    Mori.cyclePushforwardOfPoint ℤ sY φ x C * C.degree K L =
      if φ x = C.point then
        Mori.OneCycle.degree ℤ sY L (Mori.cyclePushforwardOfPoint ℤ sY φ x) else 0 := by
  unfold Mori.cyclePushforwardOfPoint
  by_cases h1 : Mori.IsProperCurve sY (φ x)
  · rw [dif_pos h1, Mori.OneCycle.degree_apply, Finsupp.sum_single_index (by simp)]
    by_cases h2 : φ x = C.point
    · rw [if_pos h2]
      have : (⟨φ x, h1⟩ : Mori.ProperCurve sY) = C := Mori.ProperCurve.ext h2
      rw [this, Finsupp.single_eq_same]
      rfl
    · rw [if_neg h2, Finsupp.single_apply, if_neg (fun h => h2 (by rw [← h])), zero_mul]
  · rw [dif_neg h1, Finsupp.coe_zero, Pi.zero_apply, zero_mul, map_zero, ite_self]

open Classical in
/-- **The local lengths over a curve add up to its multiplicity times its degree.** -/
theorem sum_fibreLen_eq {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (t : S) (ht : IsClosed ({t} : Set S)) (a : Fin (N + 1) → k)
    (hreg : FibreRegular g π q t a) (C : Mori.ProperCurve (projToSpecCoeff k N))
    (hsep : FibreSeparates g π q t a C) :
    0 ≤ cyc g sS π q t C ∧
      ((∑ᶠ y : π.fiber t, if fibrePsi g π q t y ∈ closure ({C.point} : Set _) then
        fibreLen g π q t a y else 0 : ℕ) : ℤ) =
      ((cyc g sS π q t) C).toNat * curveDeg C := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  obtain ⟨hψp, hFprop, hdimF, hcompfin, -, -⟩ := fibre_facts sS sY hS hY g hg hgY π q hπq hdim t ht
  haveI := hFprop
  haveI : LocallyOfFiniteType (π.fiberι t ≫ π ≫ sS) := hFprop.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (π.fiber t) :=
    LocallyOfFiniteType.isLocallyNoetherian (π.fiberι t ≫ π ≫ sS)
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k N
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  haveI : SheafOfModules.IsInvertible (π.fiber t).sheaf.obj (π.fiber t).ringCatSheaf.property
      (fibreH g π q t) := isInvertibleModule_fibreH g π q t
  obtain ⟨hZfin, -, hlen⟩ := fibreZero_facts sS sY hS hY g hg hgY π q hπq hdim t ht a hreg
  have hφs : fibrePsi g π q t ≫ projToSpecCoeff k N = π.fiberι t ≫ π ≫ sS := by
    rw [Category.assoc, Category.assoc, hgY, ← hπq]
  haveI : Finite {C' : Mori.ProperCurve (π.fiberι t ≫ π ≫ sS) //
      closure ({C'.point} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)} := by
    haveI := hcompfin.to_subtype
    exact Finite.of_injective (fun C' => (⟨C'.1.point, C'.2⟩ : fibreComponents π t))
      (fun C₁ C₂ h => Subtype.ext (Mori.ProperCurve.ext (congrArg Subtype.val h)))
  letI : Fintype {C' : Mori.ProperCurve (π.fiberι t ≫ π ≫ sS) //
      closure ({C'.point} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)} :=
    Fintype.ofFinite _
  have hmemZ : ∀ y, y ∈ hZfin.toFinset ↔ linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal :=
    fun y => hZfin.mem_toFinset
  -- the zero scheme of `ℓ_a` at a point is cut out by the local equation
  have hZs : ∀ y, IdealSheafData.stalk (Stacks.Divisors.zeroScheme (π.fiber t) (fibreH g π q t)
      (fibreLin g π q t a)) y = Ideal.span {fibreEq g π q t a y} := fun y =>
    stalk_zeroScheme_eq_span_coord (fibreH g π q t) (fibreLin g π q t a) _ (fibreIdx_mem g π q t y)
  -- the local length on a component through a point
  let T : {C' : Mori.ProperCurve (π.fiberι t ≫ π ≫ sS) //
      closure ({C'.point} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)} →
      π.fiber t → ℕ := fun C' y =>
    (Module.length ((π.fiber t).presheaf.stalk y) ((π.fiber t).presheaf.stalk y ⧸
      (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({C'.1.point} : Set (π.fiber t)))) y ⊔
        IdealSheafData.stalk (Stacks.Divisors.zeroScheme (π.fiber t) (fibreH g π q t)
          (fibreLin g π q t a)) y))).toNat
  have hT0 : ∀ C' y, y ∉ hZfin.toFinset → T C' y = 0 := by
    intro C' y hy
    have hu : IsUnit (fibreEq g π q t a y) :=
      (isUnit_fibreEq_iff g π q t a y).2 (fun h => hy ((hmemZ y).2 h))
    have h0 : Module.length ((π.fiber t).presheaf.stalk y) ((π.fiber t).presheaf.stalk y ⧸
        (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure ({C'.1.point} : Set (π.fiber t)))) y ⊔
          IdealSheafData.stalk (Stacks.Divisors.zeroScheme (π.fiber t) (fibreH g π q t)
            (fibreLin g π q t a)) y)) = 0 := by
      rw [hZs, Ideal.span_singleton_eq_top.2 hu, sup_top_eq, Module.length_eq_zero_iff,
        Submodule.Quotient.subsingleton_iff]
    show (Module.length _ _).toNat = 0
    rw [h0]
    rfl
  -- the degree on a component is the sum of the local lengths on it
  have hB : ∀ C' : {C' : Mori.ProperCurve (π.fiberι t ≫ π ≫ sS) //
      closure ({C'.point} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)},
      C'.1.degree k ((Scheme.Modules.pullback (fibrePsi g π q t)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)) =
      ∑ y ∈ hZfin.toFinset, if C'.1.point ⤳ y then (T C' y : ℤ) else 0 := by
    intro C'
    have hassoc : C'.1.point ∈ Stacks.Divisors.schemeAssociatedPoints (π.fiber t) :=
      mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent _ C'.2
        isGenericPoint_closure
    have e1 : C'.1.degree k ((Scheme.Modules.pullback (fibrePsi g π q t)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)) =
        C'.1.degree k (fibreH g π q t) :=
      MMP.Mori.degreeOn_eq_of_iso k _ _ _
        ((Scheme.Modules.pullbackComp (π.fiberι t) (q ≫ g)).app _).symm
    refine e1.trans ((degree_eq_finsum_length C'.1 (fibreH g π q t) (fibreLin g π q t a)
      (hreg.mem_nonvanishingLocus _ hassoc)).trans ?_)
    rw [finsum_mem_def]
    refine (finsum_eq_sum_of_support_subset _ (s := hZfin.toFinset) fun y hy => ?_).trans
      (Finset.sum_congr rfl fun y _ => ?_)
    · by_contra hn
      apply hy
      rw [Set.indicator_apply]
      split_ifs
      · exact congrArg (Nat.cast : ℕ → ℤ) (hT0 C' y hn)
      · rfl
    · rw [Set.indicator_apply]
      simp only [specializes_iff_mem_closure]
      rfl
  -- the cycle coefficient
  have hcycC : cyc g sS π q t C * curveDeg C =
      ∑ C' : {C' : Mori.ProperCurve (π.fiberι t ≫ π ≫ sS) //
        closure ({C'.point} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)},
        if fibrePsi g π q t C'.1.point = C.point then
          ((Module.length ((π.fiber t).presheaf.stalk C'.1.point)
            ((π.fiber t).presheaf.stalk C'.1.point)).toNat : ℤ) *
            C'.1.degree k ((Scheme.Modules.pullback (fibrePsi g π q t)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)) else 0 := by
    unfold cyc curveDeg
    rw [finsum_eq_sum_of_fintype, Finsupp.finset_sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun C' _ => ?_
    have h1 := cyclePushforwardOfPoint_apply_mul_degree (K := k) (projToSpecCoeff k N)
      (fibrePsi g π q t) C'.1.point C (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
    have h2 := MMP.Chow.degree_cyclePushforwardOfPoint_eq (fibrePsi g π q t) hφs C'.1
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
    rw [Finsupp.smul_apply, smul_eq_mul, mul_assoc]
    refine (congrArg (fun z => _ * z) h1).trans ?_
    simp only [mul_ite, mul_zero]
    split_ifs
    · exact congrArg _ h2
    · rfl
  -- the local identity at a point of the hyperplane
  have hA : ∀ y ∈ hZfin.toFinset,
      ((if fibrePsi g π q t y ∈ closure ({C.point} : Set _) then fibreLen g π q t a y else 0 : ℕ) :
        ℤ) =
      ∑ C' : {C' : Mori.ProperCurve (π.fiberι t ≫ π ≫ sS) //
        closure ({C'.point} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)},
        if fibrePsi g π q t C'.1.point = C.point then
          ((Module.length ((π.fiber t).presheaf.stalk C'.1.point)
            ((π.fiber t).presheaf.stalk C'.1.point)).toNat : ℤ) *
            (if C'.1.point ⤳ y then (T C' y : ℤ) else 0) else 0 := by
    intro y hyZ
    have hya := (hmemZ y).1 hyZ
    by_cases hyC : fibrePsi g π q t y ∈ closure ({C.point} : Set _)
    · rw [if_pos hyC]
      have hc : fibreEq g π q t a y ∈ nonZeroDivisors ((π.fiber t).presheaf.stalk y) :=
        coord_mem_nonZeroDivisors (fibreH g π q t) (fibreLin g π q t a)
          (fibreCoord g π q t (fibreIdx g π q t y)) hreg.mem_nonvanishingLocus
          (fibreIdx_mem g π q t y)
      have hcu : ¬ IsUnit (fibreEq g π q t a y) := fun h =>
        (isUnit_fibreEq_iff g π q t a y).1 h hya
      have hLM := length_quotient_eq_finsum_components hdimF y hc hcu
      have hset : Stacks.Chow.componentGenericPointsThrough (⊥ : (π.fiber t).IdealSheafData) y =
          (fun C' : {C' : Mori.ProperCurve (π.fiberι t ≫ π ≫ sS) //
            closure ({C'.point} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)} =>
            C'.1.point) '' {C' | fibrePsi g π q t C'.1.point = C.point ∧ C'.1.point ⤳ y} := by
        ext η
        simp only [Stacks.Chow.componentGenericPointsThrough, Set.mem_setOf_eq, Set.mem_image]
        constructor
        · rintro ⟨-, hηy, hmax⟩
          have hcomp : closure ({η} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t) :=
            (closure_singleton_mem_irreducibleComponents_iff η).2 fun η' h =>
              hmax η' (by rw [Scheme.IdealSheafData.support_bot]; trivial) h
          have hψη : fibrePsi g π q t η = C.point := hsep y η hyC hya hηy hcomp
          have hcurve : Mori.IsProperCurve (π.fiberι t ≫ π ≫ sS) η := by
            rcases isClosed_or_isProperCurve (π.fiberι t ≫ π ≫ sS) η
              (fun w₁ w₂ h1 h2 h1' h2' =>
                not_chain_of_topologicalKrullDim_le_one hdimF h1 h2 h1' h2') with h | h
            · exfalso
              obtain ⟨w, hw, hne⟩ :=
                exists_specializes_ne_of_isProperCurve _ C.point C.isProperCurve
              have hcl := isClosed_image_of_isClosed (projToSpecCoeff k N)
                (π.fiberι t ≫ π ≫ sS) (fibrePsi g π q t) hφs η h
              rw [hψη] at hcl
              exact hne (hw.mem_closed hcl rfl)
            · exact h
          exact ⟨⟨⟨η, hcurve⟩, hcomp⟩, ⟨hψη, hηy⟩, rfl⟩
        · rintro ⟨C', ⟨-, hy'⟩, rfl⟩
          exact ⟨by rw [Scheme.IdealSheafData.support_bot]; trivial, hy',
            fun η' _ h => (closure_singleton_mem_irreducibleComponents_iff _).1 C'.2 η' h⟩
      rw [hset, finsum_mem_image (fun C₁ _ C₂ _ h => Subtype.ext (Mori.ProperCurve.ext h)),
        finsum_mem_def, finsum_eq_sum_of_fintype] at hLM
      have hne : Module.length ((π.fiber t).presheaf.stalk y)
          ((π.fiber t).presheaf.stalk y ⧸ Ideal.span {fibreEq g π q t a y}) ≠ ⊤ :=
        length_quotient_span_ne_top hdimF y hc
      rw [hLM] at hne
      show ((Module.length ((π.fiber t).presheaf.stalk y)
          ((π.fiber t).presheaf.stalk y ⧸ Ideal.span {fibreEq g π q t a y})).toNat : ℤ) = _
      rw [hLM, ENat.toNat_sum (fun C' _ => ne_top_of_le_ne_top hne
        (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ C'))), Nat.cast_sum]
      refine Finset.sum_congr rfl fun C' _ => ?_
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      by_cases h1 : fibrePsi g π q t C'.1.point = C.point
      · by_cases h2 : C'.1.point ⤳ y
        · have hT : T C' y = (Module.length ((π.fiber t).presheaf.stalk y)
              ((π.fiber t).presheaf.stalk y ⧸ (Ideal.span {fibreEq g π q t a y} ⊔
                IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
                  (TopologicalSpace.Closeds.closure ({C'.1.point} : Set (π.fiber t)))) y))).toNat :=
              by
            show (Module.length _ _).toNat = _
            rw [hZs, sup_comm]
          rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, hT, ENat.toNat_mul, Nat.cast_mul, mul_comm]
        · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2]
          simp
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
        simp
    · rw [if_neg hyC, Nat.cast_zero]
      refine (Finset.sum_eq_zero fun C' _ => ?_).symm
      split_ifs with h1 h2
      · exfalso
        apply hyC
        have := specializes_iff_mem_closure.mp (h2.map (fibrePsi g π q t).continuous)
        rwa [h1] at this
      · simp
      · rfl
  have hL : (∑ᶠ y : π.fiber t, if fibrePsi g π q t y ∈ closure ({C.point} : Set _) then
      fibreLen g π q t a y else 0 : ℕ) = ∑ y ∈ hZfin.toFinset,
        (if fibrePsi g π q t y ∈ closure ({C.point} : Set _) then fibreLen g π q t a y else 0 :
          ℕ) :=
    finsum_eq_sum_of_support_subset _ fun y hy =>
      (hmemZ y).2 ((hlen y).1 fun h0 => hy (by simp [h0]))
  have hR : ∑ C' : {C' : Mori.ProperCurve (π.fiberι t ≫ π ≫ sS) //
        closure ({C'.point} : Set (π.fiber t)) ∈ irreducibleComponents (π.fiber t)},
      ∑ y ∈ hZfin.toFinset, (if fibrePsi g π q t C'.1.point = C.point then
          ((Module.length ((π.fiber t).presheaf.stalk C'.1.point)
            ((π.fiber t).presheaf.stalk C'.1.point)).toNat : ℤ) *
            (if C'.1.point ⤳ y then (T C' y : ℤ) else 0) else 0) =
      cyc g sS π q t C * curveDeg C := by
    rw [hcycC]
    refine Finset.sum_congr rfl fun C' _ => ?_
    split_ifs with h
    · rw [← Finset.mul_sum, hB C']
    · simp
  have hnn : 0 ≤ cyc g sS π q t C * curveDeg C := by
    rw [← hR]
    refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
    split_ifs <;> positivity
  have hcnn : 0 ≤ cyc g sS π q t C := nonneg_of_mul_nonneg_left hnn (curveDeg_pos C)
  refine ⟨hcnn, ?_⟩
  rw [hL, Nat.cast_sum, Finset.sum_congr rfl hA, Finset.sum_comm, hR, Int.toNat_of_nonneg hcnn]

/-- The linear form of a closed point of `ℙᴺ` is irreducible of degree one, and determines the
point. -/
theorem ptForm_facts :
    (∀ p : AlgebraicGeometry.Proj (polyGrading k N), IsClosed ({p} : Set _) →
      Irreducible (ptForm p) ∧ (ptForm p).totalDegree = 1) ∧
    ∀ p p' : AlgebraicGeometry.Proj (polyGrading k N), IsClosed ({p} : Set _) →
      IsClosed ({p'} : Set _) → Associated (ptForm p) (ptForm p') → p = p' := by
  classical
  refine ⟨fun p _ => ⟨irreducible_of_totalDegree_eq_one (totalDegree_ptForm p),
    totalDegree_ptForm p⟩, fun p p' hp hp' hass => ?_⟩
  obtain ⟨u, hu⟩ := hass
  obtain ⟨c, hc, hcu⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 u.isUnit
  have hq : ∀ j, ptCoord p' j = c * ptCoord p j := by
    intro j
    rw [← coeff_ptForm, ← hu, hcu, mul_comm, coeff_C_mul, coeff_ptForm]
  have hle : p.asHomogeneousIdeal ≤ p'.asHomogeneousIdeal := by
    intro f hf
    rw [mem_closedPt_iff p' hp']
    rw [mem_closedPt_iff p hp, mem_lineIdeal_iff] at hf
    rw [mem_lineIdeal_iff]
    intro m
    have h1 := scal_homogeneous c (homogeneousComponent_isHomogeneous m f)
    have h2 := congrArg (eval (ptCoord p)) h1
    rw [map_mul, eval_C, hf m, mul_zero] at h2
    rw [← h2, scal, eval_aeval_eq]
    have : (fun i => eval (ptCoord p) (C c * X i : MvPolynomial (Fin (N + 1)) k)) = ptCoord p' :=
      funext fun i => by simp [hq i]
    rw [this]
  have hp2 : IsClosed
      ({(p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))} :
        Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))) := hp
  exact (hp2.closure_subset ((ProjectiveSpectrum.le_iff_mem_closure _ p p').mp hle)).symm

/-! #### The incidence form of a curve from the family of the curve itself

The incidence form of a proper curve `C ⊆ ℙᴺ` restricted to a hyperplane `u = a` is computed by
the determinant construction for the family `C ⟶ Spec k` itself, whose only fibre is `C`: there
the fibre polynomial is `c · G_C^e`, and on a hyperplane `a` not containing `C` it is the product
of the linear forms of the points of `C ∩ H_a` with the local lengths as exponents, which add up to
`deg C`. A general hyperplane cuts `C` in a reduced scheme (Bertini), where all the local lengths
are one, so `e = 1`. -/

/-- The identity of `Spec k` is a normal variety over `k`. -/
theorem isNormalVariety_id_spec : Mori.IsNormalVariety k (𝟙 (Spec (.of k))) :=
  ⟨{ toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance },
    AlgebraicGeometry.isNormal_spec_of_isIntegrallyClosed k⟩

/-- Every point of `Spec k` is closed. -/
theorem isClosed_singleton_spec (s : Spec (.of k)) :
    IsClosed ({s} : Set (Spec (.of k))) := by
  have : ({s} : Set (Spec (.of k))) = Set.univ := by
    ext t
    simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have h1 : (t : PrimeSpectrum k).asIdeal = ⊥ :=
      haveI := (t : PrimeSpectrum k).isPrime; Ideal.eq_bot_of_prime _
    have h2 : (s : PrimeSpectrum k).asIdeal = ⊥ :=
      haveI := (s : PrimeSpectrum k).isPrime; Ideal.eq_bot_of_prime _
    exact PrimeSpectrum.ext (h1.trans h2.symm)
  exact this ▸ isClosed_univ

/-- Over `Spec k`, the inclusion of a fibre is an isomorphism. -/
theorem isIso_fiberι_spec {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) (s : Spec (.of k)) :
    IsIso (π.fiberι s) := by
  haveI : IsIso ((Spec (.of k)).fromSpecResidueField s) := by
    have := SpecMap_residueFieldIsoBase_inv (𝟙 (Spec (.of k))) s (isClosed_singleton_spec s)
    rw [Category.comp_id] at this
    rw [← this]
    infer_instance
  exact (IsPullback.of_hasPullback π ((Spec (.of k)).fromSpecResidueField s)).isIso_fst_of_isIso

/-- The structure morphism `projToSpecCoeff k N` of `ℙᴺ` over `Spec k` is projective. -/
theorem isProjectiveMorphism_projToSpecCoeff :
    IsProjectiveMorphism (projToSpecCoeff k N) :=
  IsProjectiveMorphism.of_iso (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k N).iso
    (Iso.refl _) (by
      rw [Iso.refl_hom, Category.comp_id]
      exact (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k N).toBase)
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩

section CurveSelf

variable {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The underlying scheme of a proper curve is integral. -/
theorem isIntegral_properCurve_scheme (C : Mori.ProperCurve sX) : IsIntegral C.scheme :=
  StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
    isIrreducible_singleton.closure

/-- The image of the closed immersion of a proper curve is the closure of its point. -/
theorem range_properCurve_ι (C : Mori.ProperCurve sX) :
    Set.range C.ι = closure ({C.point} : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The closed immersion of a proper curve maps the generic point of the curve to its point. -/
theorem ι_genericPoint (C : Mori.ProperCurve sX) :
    haveI := isIntegral_properCurve_scheme C
    C.ι (genericPoint C.scheme) = C.point := by
  haveI := isIntegral_properCurve_scheme C
  obtain ⟨w, hw⟩ : C.point ∈ Set.range C.ι := by
    rw [range_properCurve_ι]; exact subset_closure rfl
  have h1 : C.ι (genericPoint C.scheme) ⤳ C.point := by
    rw [← hw]
    exact ((genericPoint_spec C.scheme).specializes (Set.mem_univ w)).map C.ι.continuous
  have h2 : C.point ⤳ C.ι (genericPoint C.scheme) := by
    rw [specializes_iff_mem_closure, ← range_properCurve_ι]
    exact ⟨_, rfl⟩
  exact (h1.antisymm h2).eq

/-- The closure of the generic point of a proper curve `C` is a proper curve over `C.ι ≫ sX`. -/
theorem isProperCurve_genericPoint (C : Mori.ProperCurve sX) :
    haveI := isIntegral_properCurve_scheme C
    Mori.IsProperCurve (C.ι ≫ sX) (genericPoint C.scheme) := by
  haveI := isIntegral_properCurve_scheme C
  have hcl : closure ({genericPoint C.scheme} : Set C.scheme) = Set.univ :=
    (genericPoint_spec C.scheme).def
  refine ⟨?_, inferInstance⟩
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hcl, ← C.dim_eq]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ C.scheme).isHomeomorph

/-- The closed immersion of a proper curve has residue field degree one at the generic point. -/
theorem residueFieldDegree_ι_genericPoint (C : Mori.ProperCurve sX) :
    haveI := isIntegral_properCurve_scheme C
    Mori.residueFieldDegree C.ι (genericPoint C.scheme) = 1 := by
  haveI := isIntegral_properCurve_scheme C
  set η := genericPoint C.scheme
  unfold Mori.residueFieldDegree
  letI := (C.ι.residueFieldMap η).hom.toAlgebra
  have hs : Function.Surjective (C.ι.residueFieldMap η).hom := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨b, rfl⟩ := C.ι.stalkMap_surjective η a
    exact ⟨IsLocalRing.residue _ b, IsLocalRing.ResidueField.map_residue _ _⟩
  have hb : Function.Bijective (algebraMap (X.residueField (C.ι η)) (C.scheme.residueField η)) :=
    ⟨RingHom.injective _, hs⟩
  rw [← (AlgEquiv.ofBijective (Algebra.ofId _ _) hb).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- The fundamental cycle of a proper curve, on the curve itself, pushes forward to the curve. -/
theorem finsum_cyclePushforwardOfPoint_self (C : Mori.ProperCurve sX) :
    (∑ᶠ C' : {C' : Mori.ProperCurve (C.ι ≫ sX) //
        closure {C'.point} ∈ irreducibleComponents C.scheme},
      ((Module.length (C.scheme.presheaf.stalk C'.1.point)
          (C.scheme.presheaf.stalk C'.1.point)).toNat : ℤ) •
        Mori.cyclePushforwardOfPoint ℤ sX C.ι C'.1.point) = Finsupp.single C 1 := by
  classical
  haveI := isIntegral_properCurve_scheme C
  set η := genericPoint C.scheme
  have hcomp : closure ({η} : Set C.scheme) ∈ irreducibleComponents C.scheme := by
    rw [(genericPoint_spec C.scheme).def, irreducibleComponents_eq_singleton]; rfl
  let C₀ : {C' : Mori.ProperCurve (C.ι ≫ sX) //
      closure {C'.point} ∈ irreducibleComponents C.scheme} :=
    ⟨⟨η, isProperCurve_genericPoint C⟩, hcomp⟩
  have huniq : ∀ C' : {C' : Mori.ProperCurve (C.ι ≫ sX) //
      closure {C'.point} ∈ irreducibleComponents C.scheme}, C' = C₀ := by
    rintro ⟨C', hC'⟩
    apply Subtype.ext
    apply Mori.ProperCurve.ext
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hC'
    exact (show IsGenericPoint C'.point ⊤ from hC').eq (genericPoint_spec C.scheme)
  rw [finsum_eq_single _ C₀ (fun C' hC' => absurd (huniq C') hC')]
  have hlen : Module.length (C.scheme.presheaf.stalk η) (C.scheme.presheaf.stalk η) = 1 := by
    letI : Field (C.scheme.presheaf.stalk η) := inferInstanceAs (Field C.scheme.functionField)
    exact Module.length_eq_one _ _
  show ((Module.length (C.scheme.presheaf.stalk η) (C.scheme.presheaf.stalk η)).toNat : ℤ) •
      Mori.cyclePushforwardOfPoint ℤ sX C.ι η = _
  rw [hlen]
  unfold Mori.cyclePushforwardOfPoint
  have hp : Mori.IsProperCurve sX (C.ι η) := by
    rw [ι_genericPoint]; exact C.isProperCurve
  rw [dif_pos hp, residueFieldDegree_ι_genericPoint]
  have : (⟨C.ι η, hp⟩ : Mori.ProperCurve sX) = C := Mori.ProperCurve.ext (ι_genericPoint C)
  rw [this]
  simp

end CurveSelf

/-- A reduced local ring of finite length is a field: its length is at most one. -/
theorem length_self_le_one {A : Type*} [CommRing A] [IsLocalRing A] [_root_.IsReduced A]
    (h : Module.length A A ≠ ⊤) : Module.length A A ≤ 1 := by
  have hfl := Module.length_ne_top_iff.mp h
  obtain ⟨-, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI : IsArtinianRing A := hart
  have hnil := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have hm : IsLocalRing.maximalIdeal A = ⊥ := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    obtain ⟨n, hn⟩ := hnil
    rw [eq_bot_iff]
    intro x hx
    have : x ^ n ∈ (⊥ : Ideal A) := by
      rw [← Ideal.zero_eq_bot, ← hn]; exact Ideal.pow_mem_pow hx n
    rw [Ideal.mem_bot] at this ⊢
    exact _root_.IsReduced.eq_zero x ⟨n, this⟩
  have hf : IsField A := (IsLocalRing.isField_iff_maximalIdeal_eq).2 hm
  letI := hf.toField
  exact (Module.length_eq_one A A).le

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
/-- **Bertini for a generating system of sections**: the zero scheme of `∑ⱼ cⱼ sⱼ` is reduced for
`c` off a hypersurface. -/
theorem exists_poly_isReduced_zeroScheme {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsReduced X] [LocallyOfFiniteType sX] [QuasiCompact sX] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ∀ y, ∃ j, y ∈ Stacks.Ample.nonvanishingLocus L (s j)) :
    haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
      (inferInstance : Stacks.Ample.IsInvertibleModule X L)
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 → IsReduced (Stacks.Divisors.zeroScheme X L
        (∑ j, ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom (c j) • s j)).subscheme := by
  haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    (inferInstance : Stacks.Ample.IsInvertibleModule X L)
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  letI := globalSectionsModule k X L
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType sX›
  haveI : QuasiCompact (X ↘ Spec (.of k)) := ‹QuasiCompact sX›
  have hsys : ∀ c, MMP.Threefold.Bridges.systemSection s c =
      ∑ j, ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom (c j) • s j := fun c => by
    rw [MMP.Threefold.Bridges.systemSection_apply]; rfl
  have hs' : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen X L
      (MMP.Threefold.Bridges.systemSection s c) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨j, hj⟩ := hs y
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨Pi.single j 1, ?_⟩
    rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen, MMP.Threefold.Bridges.systemSection_apply,
      Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
    exact hj
  obtain ⟨Q, hQ0, hQ⟩ := MMP.Threefold.Bridges.exists_polynomial_isReduced_zeroScheme s hs'
  exact ⟨Q, hQ0, fun c hc => by rw [← hsys]; exact hQ c hc⟩

/-- Where the zero scheme of a section of an invertible module is reduced, its local lengths are at
most one. -/
theorem length_le_one_of_isReduced_zeroScheme {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (σ e : Γ(M, ⊤)) {y : X}
    (he : y ∈ Stacks.Ample.nonvanishingLocus M e)
    (hred : haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
        ‹Stacks.Ample.IsInvertibleModule X M›
      IsReduced (Stacks.Divisors.zeroScheme X M σ).subscheme)
    (hfin : Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸ Ideal.span
      {(Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus M e he).coord
        ((M.presheaf.Γgerm y).hom σ)}) ≠ ⊤) :
    (Module.length (X.presheaf.stalk y) (X.presheaf.stalk y ⧸ Ideal.span
      {(Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus M e he).coord
        ((M.presheaf.Γgerm y).hom σ)})).toNat ≤ 1 := by
  haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    ‹Stacks.Ample.IsInvertibleModule X M›
  have hIy := stalk_zeroScheme_eq_span_coord M σ e he
  set c := (Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus M e he).coord
    ((M.presheaf.Γgerm y).hom σ) with hc
  set I := Stacks.Divisors.zeroScheme X M σ with hI
  by_cases hu : IsUnit c
  · rw [(length_quotient_span_eq_zero_iff c).2 hu]; simp
  have hle : IdealSheafData.stalk I y ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
    rw [hIy, Ideal.span_le, Set.singleton_subset_iff]; exact hu
  have hysupp : y ∈ (I.support : Set X) := by
    have := (Stacks.Chow.le_iff_fromSpecStalk_mem_support I y
      (IsLocalRing.closedPoint (X.presheaf.stalk y))).1 hle
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  rw [← Scheme.IdealSheafData.range_subschemeι] at hysupp
  obtain ⟨z, hz⟩ := hysupp
  have h1 := length_stalk_subscheme' I z
  rw [hz, hIy] at h1
  rw [← h1] at hfin ⊢
  have h2 := length_self_le_one hfin
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at h2 ⊢
  simp only [ENat.toNat_coe]
  exact_mod_cast h2

/-- For realizing local free data, every closed point of the base carries a fibre polynomial. -/
theorem exists_isFibrePoly (D : LocalFreeData g sS π q d s) (hD : D.Realizes)
    (h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b)
    (x : D.U) (hx : IsClosed ({x} : Set D.U)) : ∃ F', IsFibrePoly D x F' := by
  obtain ⟨P, hP⟩ := complexDet_mem_polynomial D hD h0
  let eκ := RingEquiv.ofBijective (kEval (D.ι ≫ sS) x) (kEval_bijective (D.ι ≫ sS) x hx)
  refine ⟨MvPolynomial.map eκ.symm.toRingHom (D.specHom x P), P, hP, ?_⟩
  have : (kEval (D.ι ≫ sS) x).comp eκ.symm.toRingHom = RingHom.id _ := by
    ext z
    exact eκ.apply_symm_apply z
  rw [MvPolynomial.map_map, this, MvPolynomial.map_id]

/-- **The incidence form restricted to a hyperplane not containing the curve** is a nonzero form of
degree the degree of the curve, whose irreducible factors are the linear forms of the points of the
curve on the hyperplane. -/
theorem restrictU_incForm0 (C : Mori.ProperCurve (projToSpecCoeff k N))
    (a : Fin (N + 1) → k) (ha : linForm a ∉ C.point.asHomogeneousIdeal) :
    restrictU a (incForm0 C) ≠ 0 ∧ ((restrictU a (incForm0 C)).totalDegree : ℤ) = curveDeg C ∧
      ∀ H, Irreducible H → H ∣ restrictU a (incForm0 C) →
        ∃ p : AlgebraicGeometry.Proj (polyGrading k N), IsClosed ({p} : Set _) ∧
          p ∈ closure ({C.point} : Set _) ∧ linForm a ∈ p.asHomogeneousIdeal ∧
          Associated H (ptForm p) := by
  classical
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  -- the family `C ⟶ Spec k`
  let sS : Spec (.of k) ⟶ Spec (.of k) := 𝟙 _
  let sY := projToSpecCoeff k N
  let g₀ : AlgebraicGeometry.Proj (polyGrading k N) ⟶ AlgebraicGeometry.Proj (polyGrading k N) :=
    𝟙 _
  let π : C.scheme ⟶ Spec (.of k) := C.ι ≫ sY
  let q : C.scheme ⟶ AlgebraicGeometry.Proj (polyGrading k N) := C.ι
  have hS : Mori.IsNormalVariety k sS := isNormalVariety_id_spec
  have hY : IsProjectiveMorphism sY := isProjectiveMorphism_projToSpecCoeff
  have hg : IsProjectiveMorphism g₀ := isProjectiveMorphism_id _
  have hgY : g₀ ≫ projToSpecCoeff k N = sY := Category.id_comp _
  have hπq : π ≫ sS = q ≫ sY := Category.comp_id _
  haveI : IsClosedImmersion (pullback.lift π q hπq) := by
    have : pullback.lift π q hπq = q ≫ inv (pullback.snd sS sY) := by
      rw [IsIso.eq_comp_inv, pullback.lift_snd]
    rw [this]; infer_instance
  haveI : IsProper π := C.isProper_ι_comp
  haveI : Flat π := inferInstance
  have hfib : ∀ t, IsIso (π.fiberι t) := fun t => isIso_fiberι_spec π t
  have hdim : ∀ t : Spec (.of k), IsClosed ({t} : Set _) → topologicalKrullDim (π.fiber t) = 1 := by
    intro t _
    haveI := hfib t
    rw [← C.dim_eq]
    exact IsHomeomorph.topologicalKrullDim_eq _ (π.fiberι t).homeomorph.isHomeomorph
  have hcyc : ∀ t : Spec (.of k), cyc g₀ sS π q t = Finsupp.single C 1 := by
    intro t
    haveI := hfib t
    have h1 := cycleOf_iso (asIso (π.fiberι t)) (π.fiberι t ≫ π ≫ sS) π (projToSpecCoeff k N)
      (C.ι ≫ g₀) (by rw [asIso_hom]; exact (Category.comp_id _).symm)
    have h2 : cyc g₀ sS π q t = cycleOf (π.fiberι t ≫ π ≫ sS) (projToSpecCoeff k N)
        ((asIso (π.fiberι t)).hom ≫ C.ι ≫ g₀) := rfl
    rw [h2, h1, show C.ι ≫ g₀ = C.ι from Category.comp_id _]
    exact finsum_cyclePushforwardOfPoint_self C
  set d := (curveDeg C).toNat
  have hdC : (d : ℤ) = curveDeg C := Int.toNat_of_nonneg (curveDeg_pos C).le
  have hd : 0 < d := by have := curveDeg_pos C; omega
  have hdeg : ∀ t : Spec (.of k), IsClosed ({t} : Set _) →
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (cyc g₀ sS π q t) = d := by
    intro t _
    rw [hcyc]
    refine (Mori.OneCycle.degree_apply ℤ _ _ _).trans ?_
    rw [Finsupp.sum_single_index (by simp), one_mul, hdC]
    rfl
  -- the local free data and a fibre polynomial
  let s₀ : Spec (.of k) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  obtain ⟨F⟩ := exists_koszulFamily sS sY hS hY g₀ hg hgY π q hπq hdim d hd hdeg s₀
  set D := F.toLocalFreeData hS
  obtain ⟨x, hx⟩ := D.exists_isClosed_point
  have hD : D.Realizes :=
    ⟨koszulFamily_exact_of_avoid sS sY hS hY g₀ hg hgY π q hπq hdim d hd F,
      koszulFamily_horizontal sS sY hS hY g₀ hg hgY π q hπq hdim d hd F⟩
  have h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g₀ π q D.ι x) a b :=
    fun x hx => exists_avoidsPair sS sY hS hY g₀ hg hgY π q hπq hdim D.ι x hx
  obtain ⟨F', hF'⟩ := exists_isFibrePoly D hD h0 x hx
  set t := D.ι x
  have ht : IsClosed ({t} : Set (Spec (.of k))) := isClosed_singleton_spec t
  -- the fibre over `t` is the curve
  haveI := hfib t
  haveI : IsIntegral C.scheme := isIntegral_properCurve_scheme C
  haveI : Nonempty (π.fiber t) := ⟨inv (π.fiberι t) (genericPoint C.scheme)⟩
  haveI : IsIntegral (π.fiber t) := isIntegral_of_isOpenImmersion (π.fiberι t)
  obtain ⟨-, hFprop, hdimF, -, -, -⟩ := fibre_facts sS sY hS hY g₀ hg hgY π q hπq hdim t ht
  haveI := hFprop
  haveI : LocallyOfFiniteType (π.fiberι t ≫ π ≫ sS) := hFprop.toLocallyOfFiniteType
  haveI : QuasiCompact (π.fiberι t ≫ π ≫ sS) :=
    @instQuasiCompactOfUniversallyClosed _ _ _ hFprop.toUniversallyClosed
  haveI : IsLocallyNoetherian (π.fiber t) :=
    LocallyOfFiniteType.isLocallyNoetherian (π.fiberι t ≫ π ≫ sS)
  haveI : SheafOfModules.IsInvertible (π.fiber t).sheaf.obj (π.fiber t).ringCatSheaf.property
      (fibreH g₀ π q t) := isInvertibleModule_fibreH g₀ π q t
  set ψ := fibrePsi g₀ π q t with hψdef
  have hψι : ∀ y, ψ y = C.ι (π.fiberι t y) := fun y => by
    rw [hψdef, show fibrePsi g₀ π q t = π.fiberι t ≫ C.ι by
      show π.fiberι t ≫ C.ι ≫ 𝟙 _ = _; rw [Category.comp_id], Scheme.Hom.comp_apply]
  have hrange : Set.range ψ = closure ({C.point} : Set _) := by
    rw [← range_properCurve_ι C]
    ext p
    simp only [Set.mem_range, hψι]
    constructor
    · rintro ⟨z, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨w, rfl⟩
      refine ⟨inv (π.fiberι t) w, ?_⟩
      rw [← Scheme.Hom.comp_apply (inv (π.fiberι t)) (π.fiberι t), IsIso.inv_hom_id]
      rfl
  have hψinj : Function.Injective ψ := by
    intro y y' h
    rw [hψι, hψι] at h
    exact (π.fiberι t).isOpenEmbedding.injective (C.ι.isClosedEmbedding.injective h)
  have hgen : ψ (genericPoint (π.fiber t)) = C.point := by
    obtain ⟨w, hw⟩ : C.point ∈ Set.range ψ := by rw [hrange]; exact subset_closure rfl
    have h1 : ψ (genericPoint (π.fiber t)) ⤳ C.point := by
      rw [← hw]
      exact ((genericPoint_spec (π.fiber t)).specializes (Set.mem_univ w)).map ψ.continuous
    have h2 : C.point ⤳ ψ (genericPoint (π.fiber t)) := by
      rw [specializes_iff_mem_closure, ← hrange]; exact ⟨_, rfl⟩
    exact (h1.antisymm h2).eq
  have hassoc : Stacks.Divisors.schemeAssociatedPoints (π.fiber t) =
      {genericPoint (π.fiber t)} := schemeAssociatedPoints_eq_singleton_genericPoint _
  have hreg : ∀ b : Fin (N + 1) → k, linForm b ∉ C.point.asHomogeneousIdeal →
      FibreRegular g₀ π q t b := by
    intro b hb ζ hζ
    rw [hassoc, Set.mem_singleton_iff] at hζ
    rw [hζ]
    show linForm b ∉ (ψ (genericPoint (π.fiber t))).asHomogeneousIdeal
    rw [hgen]; exact hb
  have hsep : ∀ b, FibreSeparates g₀ π q t b C := by
    intro b y ξ _ _ _ hξ
    have hξg : ξ = genericPoint (π.fiber t) := by
      rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hξ
      exact (show IsGenericPoint ξ ⊤ from hξ).eq (genericPoint_spec _)
    show ψ ξ = C.point
    rw [hξg]; exact hgen
  have hT : (({C} : Finset (Mori.ProperCurve (projToSpecCoeff k N))) : Set _) =
      fibreCurves g₀ π q t := by
    ext C'
    simp only [Finset.coe_singleton, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      show C'.point ∈ Set.range ψ
      rw [hrange]; exact subset_closure rfl
    · intro h
      have h' : C'.point ∈ Set.range ψ := h
      rw [hrange] at h'
      exact eq_of_point_mem_closure C' C h'
  obtain ⟨c₀, e, hc₀, hF'eq⟩ :=
    fibrePoly_factor sS sY hS hY g₀ hg hgY π q hπq hdim d hd F x hx hF' {C} hT
  rw [Finset.prod_singleton] at hF'eq
  -- the restriction to a hyperplane `b` not containing `C`
  have hsumb : ∀ b : Fin (N + 1) → k, linForm b ∉ C.point.asHomogeneousIdeal →
      (∑ᶠ y : π.fiber t, fibreLen g₀ π q t b y) = d := by
    intro b hb
    obtain ⟨-, h⟩ :=
      sum_fibreLen_eq sS sY hS hY g₀ hg hgY π q hπq hdim t ht b (hreg b hb) C (hsep b)
    have h2 : ∀ y : π.fiber t, (if fibrePsi g₀ π q t y ∈ closure ({C.point} : Set _) then
        fibreLen g₀ π q t b y else 0) = fibreLen g₀ π q t b y := fun y =>
      if_pos (by rw [← hrange]; exact ⟨y, rfl⟩)
    simp only [h2, hcyc t, Finsupp.single_eq_same, Int.toNat_one, Nat.cast_one, one_mul,
      ← hdC] at h
    exact_mod_cast h
  have hkey : ∀ b : Fin (N + 1) → k, linForm b ∉ C.point.asHomogeneousIdeal → ∃ c₁ : k,
      c₁ ≠ 0 ∧ MvPolynomial.C c₀ * restrictU b (incForm0 C) ^ e C = MvPolynomial.C c₁ *
        ∏ᶠ y : π.fiber t, ptForm (ψ y) ^ fibreLen g₀ π q t b y := by
    intro b hb
    obtain ⟨c₁, hc₁, hres⟩ := exists_restrictU_eq_C_mul_finprod_ptForm sS sY hS hY g₀ hg hgY π q
      hπq hdim d F x hx F' hF' b (hreg b hb) (hsumb b hb)
    refine ⟨c₁, hc₁, ?_⟩
    rw [← hres, hF'eq, map_mul, map_pow,
      show restrictU b (MvPolynomial.C c₀) = MvPolynomial.C c₀ from (restrictU b).commutes c₀]
  have hptH : ∀ p : AlgebraicGeometry.Proj (polyGrading k N), (ptForm p).IsHomogeneous 1 :=
    fun p => MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (MvPolynomial.isHomogeneous_X k j).C_mul (ptCoord p j)
  have hpt0 : ∀ p : AlgebraicGeometry.Proj (polyGrading k N), ptForm p ≠ 0 := fun p h => by
    simpa [h] using totalDegree_ptForm p
  have hfactor : ∀ b : Fin (N + 1) → k, linForm b ∉ C.point.asHomogeneousIdeal →
      ∃ Z : Finset (π.fiber t), (∀ y, fibreLen g₀ π q t b y ≠ 0 → y ∈ Z) ∧
        (∀ y ∈ Z, IsClosed ({ψ y} : Set _) ∧ linForm b ∈ (ψ y).asHomogeneousIdeal) ∧
        (∏ᶠ y : π.fiber t, ptForm (ψ y) ^ fibreLen g₀ π q t b y) =
          ∏ y ∈ Z, ptForm (ψ y) ^ fibreLen g₀ π q t b y ∧
        ∑ y ∈ Z, fibreLen g₀ π q t b y = d := by
    intro b hb
    obtain ⟨hZfin, hZcl, hlen⟩ :=
      fibreZero_facts sS sY hS hY g₀ hg hgY π q hπq hdim t ht b (hreg b hb)
    have hsub : ∀ y, fibreLen g₀ π q t b y ≠ 0 → y ∈ hZfin.toFinset := fun y hy =>
      hZfin.mem_toFinset.2 ((hlen y).1 hy)
    refine ⟨hZfin.toFinset, hsub, fun y hy => ⟨hZcl y (hZfin.mem_toFinset.1 hy),
      hZfin.mem_toFinset.1 hy⟩, ?_, ?_⟩
    · exact finprod_eq_prod_of_mulSupport_subset _ fun y hy =>
        Finset.mem_coe.2 (hsub y fun h0 => hy (by simp [h0]))
    · rw [← hsumb b hb]
      exact (finsum_eq_sum_of_support_subset _ fun y hy => Finset.mem_coe.2 (hsub y hy)).symm
  have hRhom : ∀ (Z : Finset (π.fiber t)) (n : π.fiber t → ℕ),
      (∏ y ∈ Z, ptForm (ψ y) ^ n y).IsHomogeneous (∑ y ∈ Z, n y) ∧
        (∏ y ∈ Z, ptForm (ψ y) ^ n y) ≠ 0 := by
    intro Z n
    refine ⟨?_, Finset.prod_ne_zero_iff.2 fun y _ => pow_ne_zero _ (hpt0 _)⟩
    have := MvPolynomial.IsHomogeneous.prod Z (fun y => ptForm (ψ y) ^ n y) (fun y => 1 * n y)
      fun y _ => (hptH (ψ y)).pow (n y)
    simpa using this
  -- a Bertini hyperplane: the exponent `e` is one
  have hcoord : ∀ y, ∃ j, y ∈ Stacks.Ample.nonvanishingLocus (fibreH g₀ π q t)
      (fibreCoord g₀ π q t j) := exists_mem_nonvanishingLocus_fibreCoord g₀ π q t
  obtain ⟨Q, hQ0, hQ⟩ := exists_poly_isReduced_zeroScheme (π.fiberι t ≫ π ≫ sS)
    (fibreH g₀ π q t) (fibreCoord g₀ π q t) hcoord
  have hmor : π.fiberι t ≫ q ≫ g₀ ≫ projToSpecCoeff k N = π.fiberι t ≫ π ≫ sS := by
    simp only [π, q, g₀, sS, sY, Category.id_comp, Category.comp_id]
  have hconst : ∀ r : k, (π.fiberι t).appTop.hom ((q ≫ g₀).appTop.hom
      (Stacks.ProjectiveSpace.Cohomology.coeffToGlobalSections k N r)) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (π.fiberι t ≫ π ≫ sS).appTop).hom r := by
    intro r
    have h := congrArg (fun φ => ((Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Hom.appTop φ).hom r) hmor
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h ⊢
    exact h
  have hlinsys : ∀ b : Fin (N + 1) → k, (∑ j, ((Scheme.ΓSpecIso (.of k)).inv ≫
      (π.fiberι t ≫ π ≫ sS).appTop).hom (b j) • fibreCoord g₀ π q t j) = fibreLin g₀ π q t b := by
    intro b
    show _ = (pullbackGlobalSections (π.fiberι t) (hyperplaneBundle g₀ q)).hom (linSection g₀ q b)
    rw [linSection]
    erw [pullbackGlobalSections_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [pullbackGlobalSections_smul, hconst]
    rfl
  obtain ⟨Lp, hLp0, hLp⟩ := exists_poly_of_point (k := k) (N := N) C.point
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, MvPolynomial.eval a₀ (Q * Lp) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact mul_ne_zero hQ0 hLp0 (MvPolynomial.funext fun w => by simpa using hcon w)
  rw [map_mul] at ha₀
  have ha₀C : linForm a₀ ∉ C.point.asHomogeneousIdeal := fun hm =>
    right_ne_zero_of_mul ha₀ (hLp a₀ hm)
  have hred : IsReduced (Stacks.Divisors.zeroScheme (π.fiber t) (fibreH g₀ π q t)
      (fibreLin g₀ π q t a₀)).subscheme := by
    rw [← hlinsys]; exact hQ a₀ (left_ne_zero_of_mul ha₀)
  have hle1 : ∀ y, fibreLen g₀ π q t a₀ y ≤ 1 := fun y =>
    length_le_one_of_isReduced_zeroScheme (fibreH g₀ π q t) (fibreLin g₀ π q t a₀)
      (fibreCoord g₀ π q t (fibreIdx g₀ π q t y)) (fibreIdx_mem g₀ π q t y) hred
      (length_quotient_span_ne_top hdimF y (coord_mem_nonZeroDivisors _ _ _
        (hreg a₀ ha₀C).mem_nonvanishingLocus (fibreIdx_mem g₀ π q t y)))
  obtain ⟨hptI, hptinj⟩ := ptForm_facts (k := k) (N := N)
  have he : e C = 1 := by
    obtain ⟨c₁, hc₁, h1⟩ := hkey a₀ ha₀C
    obtain ⟨Z, hZsub, hZcl, hprod, -⟩ := hfactor a₀ ha₀C
    obtain ⟨y₀, hy₀⟩ : ∃ y, fibreLen g₀ π q t a₀ y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : (∑ᶠ y : π.fiber t, fibreLen g₀ π q t a₀ y) = 0 :=
        finsum_eq_zero_of_forall_eq_zero hcon
      have := hsumb a₀ ha₀C
      omega
    have hy₀Z := hZsub y₀ hy₀
    have hl₀ : fibreLen g₀ π q t a₀ y₀ = 1 := by have := hle1 y₀; omega
    rw [hprod, ← Finset.mul_prod_erase _ _ hy₀Z, hl₀, pow_one] at h1
    have hP0 : Prime (ptForm (ψ y₀)) := (hptI _ (hZcl y₀ hy₀Z).1).1.prime
    have hP0R : ¬ ptForm (ψ y₀) ∣ ∏ y ∈ Z.erase y₀, ptForm (ψ y) ^ fibreLen g₀ π q t a₀ y := by
      intro hdvd
      obtain ⟨y, hy, hdy⟩ := (Prime.dvd_finset_prod_iff hP0 _).1 hdvd
      have hyZ := Finset.mem_of_mem_erase hy
      have hne := Finset.ne_of_mem_erase hy
      have hdy' := hP0.dvd_of_dvd_pow hdy
      have hass := (hptI _ (hZcl y₀ hy₀Z).1).1.associated_of_dvd (hptI _ (hZcl y hyZ).1).1 hdy'
      exact hne (hψinj (hptinj _ _ (hZcl y₀ hy₀Z).1 (hZcl y hyZ).1 hass)).symm
    generalize ptForm (ψ y₀) = P0 at hP0 hP0R h1
    generalize (∏ y ∈ Z.erase y₀, ptForm (ψ y) ^ fibreLen g₀ π q t a₀ y) = R at hP0R h1
    have hCunit : ∀ c : k, c ≠ 0 → ¬ P0 ∣ MvPolynomial.C c := fun c hc hd =>
      hP0.not_unit (isUnit_of_dvd_unit hd ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C))
    have hdvdR : P0 ∣ MvPolynomial.C c₁ * (P0 * R) :=
      dvd_mul_of_dvd_right (dvd_mul_right P0 R) _
    rcases Nat.lt_or_ge (e C) 1 with hlt | hge
    · exfalso
      have he0 : e C = 0 := by omega
      rw [he0, pow_zero, mul_one] at h1
      exact hCunit c₀ hc₀ (h1 ▸ hdvdR)
    · by_contra hne1
      have h2 : 2 ≤ e C := by omega
      have hdG : P0 ∣ restrictU a₀ (incForm0 C) := by
        have : P0 ∣ MvPolynomial.C c₀ * restrictU a₀ (incForm0 C) ^ e C := h1 ▸ hdvdR
        rcases hP0.dvd_or_dvd this with h | h
        · exact absurd h (hCunit c₀ hc₀)
        · exact hP0.dvd_of_dvd_pow h
      have h3 : P0 ^ 2 ∣ MvPolynomial.C c₁ * (P0 * R) := by
        rw [← h1]
        exact dvd_mul_of_dvd_right ((pow_dvd_pow_of_dvd hdG 2).trans (pow_dvd_pow _ h2)) _
      have h4 : P0 * P0 ∣ P0 * (MvPolynomial.C c₁ * R) := by
        rw [← pow_two]
        exact h3.trans (by rw [show MvPolynomial.C c₁ * (P0 * R) = P0 * (MvPolynomial.C c₁ * R)
          by ring])
      have h5 := (mul_dvd_mul_iff_left hP0.ne_zero).1 h4
      rcases hP0.dvd_or_dvd h5 with h | h
      · exact hCunit c₁ hc₁ h
      · exact hP0R h
  -- the conclusion for `a`
  obtain ⟨c₁, hc₁, h1⟩ := hkey a ha
  obtain ⟨Z, -, hZcl, hprod, hsumZ⟩ := hfactor a ha
  rw [he, pow_one, hprod] at h1
  obtain ⟨hRh, hR0⟩ := hRhom Z (fun y => fibreLen g₀ π q t a y)
  have hG : restrictU a (incForm0 C) = MvPolynomial.C (c₁ / c₀) *
      ∏ y ∈ Z, ptForm (ψ y) ^ fibreLen g₀ π q t a y := by
    have h2 := congrArg (MvPolynomial.C c₀⁻¹ * ·) h1
    simp only [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hc₀, MvPolynomial.C_1,
      one_mul] at h2
    rw [h2, div_eq_inv_mul]
  have hc10 : MvPolynomial.C (c₁ / c₀) ≠ (0 : MvPolynomial (Fin (N + 1)) k) :=
    MvPolynomial.C_ne_zero.2 (div_ne_zero hc₁ hc₀)
  refine ⟨by rw [hG]; exact mul_ne_zero hc10 hR0, ?_, fun H hH hdvd => ?_⟩
  · rw [hG, ((hRh.C_mul (c₁ / c₀))).totalDegree (mul_ne_zero hc10 hR0), hsumZ, hdC]
  · rw [hG] at hdvd
    have hHp := hH.prime
    rcases hHp.dvd_or_dvd hdvd with h | h
    · exact absurd (isUnit_of_dvd_unit h ((isUnit_iff_ne_zero.2 (div_ne_zero hc₁ hc₀)).map
        MvPolynomial.C)) hH.not_isUnit
    · obtain ⟨y, hy, hdy⟩ := (Prime.dvd_finset_prod_iff hHp _).1 h
      have hdy' := hHp.dvd_of_dvd_pow hdy
      refine ⟨ψ y, (hZcl y hy).1, by rw [← hrange]; exact ⟨y, rfl⟩, (hZcl y hy).2,
        hH.associated_of_dvd (hptI _ (hZcl y hy).1).1 hdy'⟩

/-- **The fibre polynomial is the product of the incidence forms of the curves of the fibre cycle,
with the cycle multiplicities as exponents**, up to a nonzero scalar. -/
theorem fibrePoly_eq {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d) {s : S} (F : KoszulFamily g π q d s)
    (x : (F.toLocalFreeData hS).U) (hx : IsClosed ({x} : Set (F.toLocalFreeData hS).U))
    {F' : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    (hF' : IsFibrePoly (F.toLocalFreeData hS) x F')
    (hdeg : haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
        (cyc g sS π q ((F.toLocalFreeData hS).ι x)) = d) :
    ∃ c : k, c ≠ 0 ∧ F' = MvPolynomial.C c *
      ∏ C ∈ (cyc g sS π q ((F.toLocalFreeData hS).ι x)).support,
        incForm0 C ^ (cyc g sS π q ((F.toLocalFreeData hS).ι x) C).toNat := by
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set t := (F.toLocalFreeData hS).ι x with htdef
  have ht : IsClosed ({t} : Set S) :=
    isClosed_image_of_isClosed sS ((F.toLocalFreeData hS).ι ≫ sS) (F.toLocalFreeData hS).ι rfl x hx
  set ψ := fibrePsi g π q t
  set m : Mori.ProperCurve (projToSpecCoeff k N) → ℕ := fun C => (cyc g sS π q t C).toNat
  have hfin := finite_fibreCurves sS sY hS hY g hg hgY π q hπq hdim t ht
  set T := hfin.toFinset
  have hTset : (T : Set _) = fibreCurves g π q t := hfin.coe_toFinset
  have hmemT : ∀ C, C ∈ T ↔ C ∈ fibreCurves g π q t := fun C => hfin.mem_toFinset
  obtain ⟨c₀, e, hc₀, hF'eq⟩ :=
    fibrePoly_factor sS sY hS hY g hg hgY π q hπq hdim d hd F x hx hF' T hTset
  suffices he : ∀ C ∈ T, e C = m C by
    refine ⟨c₀, hc₀, ?_⟩
    rw [hF'eq]
    congr 1
    rw [Finset.prod_congr rfl fun C hC => by rw [he C hC]]
    symm
    refine Finset.prod_subset (fun C hC => ?_) (fun C _ hC => ?_)
    · exact (hmemT C).2
        (mem_fibreCurves_of_cyc_ne_zero sS g π q t C (Finsupp.mem_support_iff.mp hC))
    · rw [Finsupp.notMem_support_iff.mp hC]; simp
  intro C₀ hC₀
  obtain ⟨a, hreg, hsep, hcurve⟩ := exists_goodHyperplane sS sY hS hY g hg hgY π q hπq hdim t ht
  obtain ⟨hZfin, hZcl, hlen⟩ := fibreZero_facts sS sY hS hY g hg hgY π q hπq hdim t ht a hreg
  obtain ⟨hψp, -, -, -, hcover, -⟩ := fibre_facts sS sY hS hY g hg hgY π q hπq hdim t ht
  set Z := hZfin.toFinset
  have hmemZ : ∀ y, y ∈ Z ↔ linForm a ∈ (ψ y).asHomogeneousIdeal := fun y => hZfin.mem_toFinset
  have hcls : ∀ y ∈ Z, ∃ C ∈ T, ψ y ∈ closure ({C.point} : Set _) := by
    intro y hy
    obtain ⟨C, hC, h⟩ := hcurve y ((hmemZ y).1 hy)
    exact ⟨C, (hmemT C).2 hC, h⟩
  have huniq : ∀ y ∈ Z, ∀ C ∈ T, ∀ C' ∈ T, ψ y ∈ closure ({C.point} : Set _) →
      ψ y ∈ closure ({C'.point} : Set _) → C = C' := by
    intro y hy C hC C' hC' h h'
    obtain ⟨ξ, hξ, hξy⟩ := hcover y
    have e1 := (hsep C ((hmemT C).1 hC)).1 y ξ h ((hmemZ y).1 hy) hξy hξ
    have e2 := (hsep C' ((hmemT C').1 hC')).1 y ξ h' ((hmemZ y).1 hy) hξy hξ
    exact Mori.ProperCurve.ext (e1.symm.trans e2)
  let cls : π.fiber t → Mori.ProperCurve (projToSpecCoeff k N) := fun y =>
    if h : ∃ C ∈ T, ψ y ∈ closure ({C.point} : Set _) then h.choose else C₀
  have hcls_spec : ∀ y ∈ Z, cls y ∈ T ∧ ψ y ∈ closure ({(cls y).point} : Set _) := by
    intro y hy
    have h := hcls y hy
    simp only [cls, dif_pos h]
    exact h.choose_spec
  have hcls_iff : ∀ y ∈ Z, ∀ C ∈ T, cls y = C ↔ ψ y ∈ closure ({C.point} : Set _) := by
    intro y hy C hC
    refine ⟨?_, huniq y hy _ (hcls_spec y hy).1 C hC (hcls_spec y hy).2⟩
    rintro rfl
    exact (hcls_spec y hy).2
  have hsumC : ∀ C ∈ T, (∑ᶠ y : π.fiber t, if ψ y ∈ closure ({C.point} : Set _) then
      fibreLen g π q t a y else 0 : ℕ) = ∑ y ∈ Z with cls y = C, fibreLen g π q t a y := by
    intro C hC
    rw [Finset.sum_filter]
    refine (finsum_eq_sum_of_support_subset _ (s := Z) (fun y hy => ?_)).trans
      (Finset.sum_congr rfl fun y hy => ?_)
    · rw [hZfin.coe_toFinset]
      exact (hlen y).1 fun h0 => hy (by simp [h0])
    · simp only [hcls_iff y hy C hC]
  have htot : (∑ᶠ y : π.fiber t, fibreLen g π q t a y) = d := by
    have e1 : (∑ᶠ y : π.fiber t, fibreLen g π q t a y) = ∑ y ∈ Z, fibreLen g π q t a y := by
      refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
      rw [hZfin.coe_toFinset]; exact (hlen y).1 hy
    have e2 : ∑ y ∈ Z, fibreLen g π q t a y =
        ∑ C ∈ T, ∑ y ∈ Z with cls y = C, fibreLen g π q t a y :=
      (Finset.sum_fiberwise_of_maps_to (fun y hy => (hcls_spec y hy).1) _).symm
    have e3 : ∀ C ∈ T, ((∑ y ∈ Z with cls y = C, fibreLen g π q t a y : ℕ) : ℤ) =
        cyc g sS π q t C * curveDeg C := by
      intro C hC
      obtain ⟨hnn, h⟩ := sum_fibreLen_eq sS sY hS hY g hg hgY π q hπq hdim t ht a hreg C
        (hsep C ((hmemT C).1 hC)).1
      rw [← hsumC C hC, h, Int.toNat_of_nonneg hnn]
    have e4 : ∑ C ∈ T, cyc g sS π q t C * curveDeg C = d := by
      refine Eq.trans ?_ hdeg
      refine Eq.trans ?_ (Mori.OneCycle.degree_apply ℤ _ _ _).symm
      exact (Finsupp.sum_of_support_subset (cyc g sS π q t) (s := T) (fun C hC => (hmemT C).2
        (mem_fibreCurves_of_cyc_ne_zero sS g π q t C (Finsupp.mem_support_iff.mp hC)))
        (fun C a => a * ((C.degree k (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) :
          ℤ) : ℤ)) (fun C _ => zero_mul _)).symm
    have : ((∑ᶠ y : π.fiber t, fibreLen g π q t a y : ℕ) : ℤ) = d := by
      rw [e1, e2, Nat.cast_sum, Finset.sum_congr rfl e3, e4]
    exact_mod_cast this
  obtain ⟨c₁, hc₁, hres⟩ :=
    exists_restrictU_eq_C_mul_finprod_ptForm sS sY hS hY g hg hgY π q hπq hdim d F x hx F' hF' a
      hreg htot
  have hR : restrictU a F' = MvPolynomial.C c₀ * ∏ C ∈ T, restrictU a (incForm0 C) ^ e C := by
    rw [hF'eq, map_mul, map_prod]
    simp only [map_pow]
    congr 1
    exact (restrictU a).commutes c₀
  have hprodZ : ∏ᶠ y : π.fiber t, ptForm (ψ y) ^ fibreLen g π q t a y =
      ∏ y ∈ Z, ptForm (ψ y) ^ fibreLen g π q t a y := by
    refine finprod_eq_prod_of_mulSupport_subset _ (fun y hy => ?_)
    rw [hZfin.coe_toFinset]
    exact (hlen y).1 fun h0 => hy (by simp [h0])
  have h1 : ∏ C ∈ T, restrictU a (incForm0 C) ^ e C =
      MvPolynomial.C (c₁ / c₀) * ∏ y ∈ Z, ptForm (ψ y) ^ fibreLen g π q t a y := by
    have h2 := hR.symm.trans hres
    rw [hprodZ] at h2
    have hc0' : (MvPolynomial.C c₀ : MvPolynomial (Fin (N + 1)) k) ≠ 0 :=
      MvPolynomial.C_ne_zero.2 hc₀
    apply mul_left_cancel₀ hc0'
    rw [h2, ← mul_assoc, ← MvPolynomial.C_mul, mul_div_cancel₀ _ hc₀]
  obtain ⟨hptI, hptinj⟩ := ptForm_facts (k := k) (N := N)
  have h2 : ∀ C ∈ T, ∀ H, Irreducible H → H ∣ restrictU a (incForm0 C) →
      ∃ y ∈ Z, cls y = C ∧ Associated H (ptForm (ψ y)) := by
    intro C hC H hH hdvd
    obtain ⟨p, -, hpC, hpa, hass⟩ :=
      (restrictU_incForm0 C a ((hsep C ((hmemT C).1 hC)).2)).2.2 H hH hdvd
    obtain ⟨y₀, hy₀⟩ := (hmemT C).1 hC
    have hsp : ψ y₀ ⤳ p := by rw [hy₀]; exact specializes_iff_mem_closure.mpr hpC
    haveI := hψp
    obtain ⟨y, -, rfl⟩ := exists_specializes_lift (fibrePsi g π q t).isClosedMap hsp
    have hyZ : y ∈ Z := (hmemZ y).2 hpa
    exact ⟨y, hyZ, (hcls_iff y hyZ C hC).2 hpC, hass⟩
  have h3 : ∀ y ∈ Z, ∀ y' ∈ Z, cls y ≠ cls y' →
      ¬ Associated (ptForm (ψ y)) (ptForm (ψ y')) := by
    intro y hy y' hy' hne hass
    apply hne
    have : ψ y = ψ y' :=
      hptinj _ _ (hZcl y ((hmemZ y).1 hy)) (hZcl y' ((hmemZ y').1 hy')) hass
    simp only [cls, this]
  have key := mul_totalDegree_eq_sum Z (fun y => ptForm (ψ y))
    (fun y hy => (hptI _ (hZcl y ((hmemZ y).1 hy))).1)
    (fun y hy => (hptI _ (hZcl y ((hmemZ y).1 hy))).2)
    (fun y => fibreLen g π q t a y) T (fun C => restrictU a (incForm0 C))
    (fun C hC => (restrictU_incForm0 C a ((hsep C ((hmemT C).1 hC)).2)).1)
    e cls (c₁ / c₀) (div_ne_zero hc₁ hc₀) h1 h2 h3 C₀ hC₀
  have hlenC := (sum_fibreLen_eq sS sY hS hY g hg hgY π q hπq hdim t ht a hreg C₀
    (hsep C₀ ((hmemT C₀).1 hC₀)).1).2
  rw [hsumC C₀ hC₀, ← key] at hlenC
  push_cast at hlenC
  rw [(restrictU_incForm0 C₀ a ((hsep C₀ ((hmemT C₀).1 hC₀)).2)).2.1] at hlenC
  exact_mod_cast mul_right_cancel₀ (curveDeg_pos C₀).ne' hlenC

end FibreChow

/-- **(S1d) The determinant of a closed fibre.**  For the local free data of a `KoszulFamily`, at
a closed point `x` of `W` and a choice `G` of incidence forms for the cycle of the fibre, the
determinant of the fibre complex over `κ(x)[u, v]` is a nonzero scalar times
`∏_C G_C ^ m_C`.  Route: for a generic hyperplane `u = a`, `ℓ_a` is a regular section on the
fibre, the determinant restricted to `u = a` is the determinant of `ℓ_v` between the quotients
`Γ(N_{-1}) / ℓ_a Γ(N_{-2})` and `Γ(N_0) / ℓ_a Γ(N_{-1})`, which are the sections of the twists on
the zero scheme of `ℓ_a` (by gluing and the degree of `H`), so it factors over the points of that
zero scheme with the local lengths as exponents; the local multiplicity formula
`len(B / tB) = ∑_𝔭 len(B_𝔭) · len(B / (𝔭 + tB))` identifies the exponent at a point of a curve `C`
with `m_C`, and the restriction of `G_C` to `u = a` is the squarefree product of the linear forms
of the points of `C` on the hyperplane. -/
theorem koszulFamily_fibre_det {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d) {s : S} (F : KoszulFamily g π q d s)
    (hdeg : haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
      ∀ s : S, IsClosed ({s} : Set S) →
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (cyc g sS π q s) = d) :
    let D := F.toLocalFreeData hS
    ∀ x : D.U, IsClosed ({x} : Set D.U) →
    ∀ G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k,
      (∀ C ∈ (D.cycAt x).support, IncForm C (G C)) →
      ∃ l : D.U.residueField x, l ≠ 0 ∧
        D.fibreDet x = algebraMap (D.PolAt x) (FractionRing (D.PolAt x))
          ((MvPolynomial.C l : D.PolAt x) * MvPolynomial.map (kEval (D.ι ≫ sS) x)
            (∏ C ∈ (D.cycAt x).support, G C ^ ((D.cycAt x) C).toNat)) := by
  intro D x hx G hG
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  have hD : D.Realizes := ⟨koszulFamily_exact_of_avoid sS sY hS hY g hg hgY π q hπq hdim d hd F,
    koszulFamily_horizontal sS sY hS hY g hg hgY π q hπq hdim d hd F⟩
  have h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b :=
    fun x hx => exists_avoidsPair sS sY hS hY g hg hgY π q hπq hdim D.ι x hx
  obtain ⟨F', hF'⟩ := exists_isFibrePoly D hD h0 x hx
  obtain ⟨P, hP, hF'map⟩ := id hF'
  obtain ⟨c, hc, hFeq⟩ := fibrePoly_eq sS sY hS hY g hg hgY π q hπq hdim d hd F x hx hF'
    (hdeg _ (isClosed_image_of_isClosed sS (D.ι ≫ sS) D.ι rfl x hx))
  have hcyc : D.cycAt x = cyc g sS π q (D.ι x) := cyc_pullback sS (D.ι ≫ sS) g π q D.ι rfl x hx
  have hGu : ∀ C ∈ (D.cycAt x).support, ∃ u : kˣ, G C = MvPolynomial.C (u : k) * incForm0 C :=
    fun C hC => incForm_unique (incForm_incForm0 C) (hG C hC)
  choose! u hu using hGu
  set w : k := ∏ C ∈ (D.cycAt x).support, ((u C : k)) ^ ((D.cycAt x) C).toNat with hwdef
  have hw : w ≠ 0 := Finset.prod_ne_zero_iff.2 fun C _ => pow_ne_zero _ (u C).ne_zero
  have hprod : ∏ C ∈ (D.cycAt x).support, G C ^ ((D.cycAt x) C).toNat =
      MvPolynomial.C w * ∏ C ∈ (D.cycAt x).support, incForm0 C ^ ((D.cycAt x) C).toNat := by
    rw [Finset.prod_congr rfl fun C hC => by rw [hu C hC, mul_pow, ← MvPolynomial.C_pow],
      Finset.prod_mul_distrib, ← map_prod]
  refine ⟨kEval (D.ι ≫ sS) x (c / w), (map_ne_zero _).2 (div_ne_zero hc hw), ?_⟩
  rw [← complexDet_specialize D hD h0 P hP x hx, ← hF'map, hFeq, hprod, ← hcyc]
  congr 1
  simp only [map_mul, MvPolynomial.map_C]
  rw [← mul_assoc, ← MvPolynomial.C_mul, ← map_mul, div_mul_cancel₀ _ hw]

/-- **(S1) Free local data exists near every point.**  Assembled from the sheaf-theoretic input
`exists_koszulFamily`, the two properties S1b, S1c of `LocalFreeData.Realizes`, and S1d. -/
theorem exists_localFreeData {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d)
    (hdeg : haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
      ∀ s : S, IsClosed ({s} : Set S) →
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (cyc g sS π q s) = d)
    (s : S) : ∃ D : LocalFreeData g sS π q d s, D.Realizes ∧ D.FibreDetSpec := by
  obtain ⟨F⟩ := exists_koszulFamily sS sY hS hY g hg hgY π q hπq hdim d hd hdeg s
  exact ⟨F.toLocalFreeData hS,
    ⟨koszulFamily_exact_of_avoid sS sY hS hY g hg hgY π q hπq hdim d hd F,
     koszulFamily_horizontal sS sY hS hY g hg hgY π q hπq hdim d hd F⟩,
     koszulFamily_fibre_det sS sY hS hY g hg hgY π q hπq hdim d hd F hdeg⟩

end CoreLemmas

end Skeleton

end Defs

end MMP.Chow.DeterminantCurveForm
