module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreCycle
public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Iterate
public import MMP.AlgebraicGeometry.ReducedSubschemeOver

/-!
# Fibre classes of a divisor on the components of a general fibre

Let `r : Z ⟶ Y` be a curve-and-point exceptional model with exceptional divisor `F = ∑ Fᵢ`, and
`L E` a `ℚ`-divisor on each component `E` of `F`. Over a closed point `y` of a curve `T ⊆ Sing Y`
there are two fibres: the scheme-theoretic fibre `F_t = Z ×_Y Spec ℂ`, and the reduced fibre
`r⁻¹(y)`, the closed subscheme of `Z` cut out by the vanishing ideal of `r⁻¹(y)`. The reduced
fibre is a closed subscheme of `F_t` with the same points, so the two have the same homology.

When the fibres `P ×_Y Spec ℂ` of the prime divisors `P` of the `L E` are reduced, the fibre
cycle `∑_E ∑_P c_P [P ×_Y t]_1` (Stacks, Tag 02QU) of `F_t` is the proper push-forward of a cycle
of the reduced fibre, whose class is `∑_E ∑_P c_P ∑_C cl(C)`, the curves `C = closure {x}` running
over the maximal irreducible subsets of `P ∩ r⁻¹(y)` and `cl(C)` their cycle classes
`MMP.Chow.pointCycleClass`. So the vanishing of the class of the fibre cycle in `H_2(F_t, ℚ)`
gives the vanishing of `∑_E ∑_P c_P ∑_C cl(C)` in `H_2(r⁻¹(y), ℚ)`. Since the fibres `P ×_Y t`
are reduced for `t` in a nonempty open of `T`, the vanishing of the fibre cycle on a dense open of
`T` gives the vanishing of the component sums on the closed points of `U ∩ T`, for an open `U` of
`Y` meeting `T`.

## Main results

* `MMP.Fourfold.sum_rationalCycleClass_fibreComponents_eq_zero_of_isReduced`: at one point with
  reduced fibres.
* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_opens_sum_rationalCycleClass_eq_zero`: from the
  fibre cycle on a dense open of a curve to the component sums on the closed points of
  an open of `Y` meeting the curve.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MMP
open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open scoped MMP.SubschemeOver TensorProduct

namespace MMP.Fourfold

/-- The points of `Z ×_Y Spec ℂ` map onto the set-theoretic fibre `r⁻¹(y)` of `r : Z ⟶ Y`,
`y` the image of the `ℂ`-point `g`. -/
theorem range_pullback_fst_base_eq_preimage {Z Y : Scheme.{0}} {r : Z ⟶ Y}
    {g : Spec (.of ℂ) ⟶ Y} {y : Y} (hgy : g.base (IsLocalRing.closedPoint ℂ) = y) :
    Set.range (pullback.fst r g).base = r.base ⁻¹' {y} := by
  rw [Scheme.Pullback.range_fst]
  congr 1
  ext z
  refine ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩
    rw [Subsingleton.elim a (IsLocalRing.closedPoint ℂ), hgy]
    rfl
  · rintro rfl
    exact ⟨_, hgy⟩

/-- Borel–Moore push-forward along a surjective closed immersion over `ℂ` is injective: on
`ℂ`-points it is a homeomorphism. -/
theorem injective_pushforward_map_of_surjective {A B : Scheme.{0}} [A.Over (Spec (.of ℂ))]
    [B.Over (Spec (.of ℂ))] [LocallyOfFiniteType (A ↘ Spec (.of ℂ))] [IsComplexScheme B]
    (j : A ⟶ B) [IsClosedImmersion j] [Surjective j] [j.IsOver (Spec (.of ℂ))] (n : ℤ) :
    Function.Injective (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) j))
      (UnderlyingSpace.isProperMap_map (K := ℂ) j) n).hom := by
  let φ := (UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) j).isEmbedding
    |>.toHomeomorphOfSurjective (UnderlyingSpace.mapFun_surjective (K := ℂ) j)
  have key : ∀ (f : C(UnderlyingSpace ℂ A, UnderlyingSpace ℂ B)) (hf : IsProperMap f),
      f = (φ : C(_, _)) → Function.Injective (borelMooreHomology.pushforward ℚ
        (ModuleCat.of ℚ ℚ) (TopCat.ofHom f) hf n).hom := by
    rintro f hf rfl
    exact (borelMooreHomology.bijective_pushforward_homeomorph ℚ
      (Y := TopCat.of (UnderlyingSpace ℂ A)) (Y' := TopCat.of (UnderlyingSpace ℂ B)) φ _).1
  exact key _ _ (ContinuousMap.ext fun p ↦ rfl)

/-- A closed immersion `m` of a reduced scheme into `X` whose range lies in the range of a closed
immersion `j` factors through `j` by a closed immersion, whose range is the preimage under `j` of
the range of `m`. -/
theorem exists_isClosedImmersion_comp_eq_of_range_subset {A B X : Scheme.{0}} (j : A ⟶ X)
    [IsClosedImmersion j] (m : B ⟶ X) [IsClosedImmersion m] [IsReduced B]
    (hmj : Set.range m.base ⊆ Set.range j.base) :
    ∃ k : B ⟶ A, IsClosedImmersion k ∧ k ≫ j = m ∧
      Set.range k.base = j.base ⁻¹' Set.range m.base := by
  have hkerm : j.ker ≤ m.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range m,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]
    exact closure_mono hmj hx
  let k := IsClosedImmersion.lift j m hkerm
  have hk : k ≫ j = m := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion (k ≫ j) := by
    rw [hk]
    infer_instance
  refine ⟨k, IsClosedImmersion.of_comp k j, hk, Set.ext fun x ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [← hk, Scheme.Hom.comp_apply]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, j.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hk, ha]

/-- The reduced fibre `r⁻¹(y)` embeds in `Z ×_Y Spec ℂ` by a surjective closed immersion over
`Z`, `y` the image of the `ℂ`-point `g`. -/
theorem exists_isClosedImmersion_vanishingIdeal_comp_pullback_fst {Z Y : Scheme.{0}}
    {r : Z ⟶ Y} {g : Spec (.of ℂ) ⟶ Y} [IsClosedImmersion g] {y : Y}
    (hgy : g.base (IsLocalRing.closedPoint ℂ) = y) (hy : IsClosed {y}) :
    ∃ j : (Scheme.IdealSheafData.vanishingIdeal
        ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme ⟶ pullback r g,
      IsClosedImmersion j ∧ Function.Surjective j.base ∧
        j ≫ pullback.fst r g = (Scheme.IdealSheafData.vanishingIdeal
          ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subschemeι := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := Z)
    ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩
  have hrange := range_pullback_fst_base_eq_preimage (r := r) hgy
  have : IsReduced I.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hI : Set.range I.subschemeι.base = r.base ⁻¹' {y} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨k, hk, hkj, hkr⟩ := exists_isClosedImmersion_comp_eq_of_range_subset
    (pullback.fst r g) I.subschemeι (by rw [hI, hrange])
  refine ⟨k, hk, Set.range_eq_univ.1 ?_, hkj⟩
  rw [hkr, hI, ← hrange, Set.preimage_range]

open Classical in
/-- The cycle of a reduced closed subscheme `m` of `X` is the push-forward along a surjective
closed immersion `j : A ⟶ X` of a cycle on `A`, whose class is the sum of the classes of the
curves which are maximal irreducible subsets of `j⁻¹(m(B))`. -/
theorem exists_rationalProperPushforward_eq_of_surjective {A B X : Scheme.{0}}
    [A.Over (Spec (.of ℂ))] [IsComplexScheme A] [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
    (j : A ⟶ X) [IsClosedImmersion j] [Surjective j] [j.IsOver (Spec (.of ℂ))] (m : B ⟶ X)
    [IsClosedImmersion m] [IsReduced B] :
    ∃ x : Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ) (A ↘ Spec (.of ℂ))
        ((1 : ℕ) : ℤ),
      (1 : ℚ) ⊗ₜ[ℤ] Stacks.Chow.cycleAssociatedToClosedSubscheme
          (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) m ((1 : ℕ) : ℤ) =
        Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ)
          (A ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ((1 : ℕ) : ℤ) j (comp_over j _) x ∧
      Chow.rationalCycleClass A 1 x =
        ∑ᶠ (x : {x : A // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (A ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ j.base ⁻¹' Set.range m.base)
            (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2 := by
  obtain ⟨k, _, hk, hk₁⟩ := exists_isClosedImmersion_comp_eq_of_range_subset j m
    (Set.range_eq_univ.2 j.surjective ▸ Set.subset_univ _)
  refine ⟨(1 : ℚ) ⊗ₜ[ℤ] Stacks.Chow.cycleAssociatedToClosedSubscheme
    (Stacks.Chow.fieldChowSituation ℂ) (A ↘ Spec (.of ℂ)) k ((1 : ℕ) : ℤ), ?_, ?_⟩
  · rw [Chow.rationalProperPushforward_tmul,
      Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
      Stacks.Chow.cycleAssociatedToClosedSubscheme_congr _ _ (k ≫ j) m hk]
  · rw [rationalCycleClass_cycleAssociatedToClosedSubscheme_of_isReduced, hk₁]

open Classical in
/-- The cycle of the fibre `W ×_Y Spec ℂ` of a closed subscheme `i : W ⟶ Z` with reduced fibre is
the push-forward along a surjective closed immersion `j : A ⟶ Z ×_Y Spec ℂ` of a cycle on `A`,
whose class is the sum of the classes of the curves which are maximal irreducible subsets of the
preimage of `W` in `A`. -/
theorem exists_rationalProperPushforward_pullback_map_eq {Z Y A W : Scheme.{0}} {r : Z ⟶ Y}
    {g : Spec (.of ℂ) ⟶ Y} [(pullback r g).Over (Spec (.of ℂ))] [IsComplexScheme (pullback r g)]
    [A.Over (Spec (.of ℂ))] [IsComplexScheme A] (j : A ⟶ pullback r g) [IsClosedImmersion j]
    [Surjective j] [j.IsOver (Spec (.of ℂ))] {k : A ⟶ Z} (hj : j ≫ pullback.fst r g = k)
    (i : W ⟶ Z) [IsClosedImmersion i] {φ : W ⟶ Y} (hφ : i ≫ r = φ) [IsReduced (pullback φ g)]
    {S : Set Z} (hS : Set.range i.base = S) :
    ∃ x : Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ) (A ↘ Spec (.of ℂ))
        ((1 : ℕ) : ℤ),
      (haveI := isClosedImmersion_pullback_map_of_comp_eq i r hφ g
      (1 : ℚ) ⊗ₜ[ℤ] Stacks.Chow.cycleAssociatedToClosedSubscheme
        (Stacks.Chow.fieldChowSituation ℂ) (pullback r g ↘ Spec (.of ℂ))
        (pullback.map φ g r g i (𝟙 _) (𝟙 _) ((Category.comp_id _).trans hφ.symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm)) ((1 : ℕ) : ℤ)) =
        Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ)
          (A ↘ Spec (.of ℂ)) (pullback r g ↘ Spec (.of ℂ)) ((1 : ℕ) : ℤ) j (comp_over j _) x ∧
      Chow.rationalCycleClass A 1 x =
        ∑ᶠ (x : {x : A // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (A ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun T ↦ IsIrreducible T ∧ T ⊆ k.base ⁻¹' S) (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2 := by
  subst hj hS
  have := isClosedImmersion_pullback_map_of_comp_eq i r hφ g
  obtain ⟨x, hx₁, hx₂⟩ := exists_rationalProperPushforward_eq_of_surjective j
    (pullback.map φ g r g i (𝟙 _) (𝟙 _) ((Category.comp_id _).trans hφ.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  refine ⟨x, hx₁, ?_⟩
  rw [hx₂, range_pullback_map_of_comp_eq i r hφ g, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.preimage_comp]

/-- For `r : Z ⟶ Y` over `Spec ℂ` and a `ℂ`-point `g` of `Y`, the projection
`Z ×_Y Spec ℂ ⟶ Z` lies over `Spec ℂ`. -/
theorem isOver_pullback_fst_of_comp_eq_id {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} (hcomp : r ≫ sY = Z ↘ Spec (.of ℂ))
    {g : Spec (.of ℂ) ⟶ Y} (hg : g ≫ sY = 𝟙 _) :
    letI : (pullback r g).Over (Spec (.of ℂ)) := ⟨pullback.snd r g⟩
    (pullback.fst r g).IsOver (Spec (.of ℂ)) := by
  let : (pullback r g).Over (Spec (.of ℂ)) := ⟨pullback.snd r g⟩
  refine ⟨?_⟩
  rw [← hcomp, pullback.condition_assoc, hg, Category.comp_id]
  rfl

/-- A point `v` of a scheme locally of finite type over `ℂ`, closed in some scheme `W` into which
it maps injectively, is the image of a `ℂ`-point. -/
theorem exists_complexPoints_hom_base_eq {X W : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType f] (e : X ⟶ W) (he : Function.Injective e.base) {v : X}
    (hv : IsClosed {e.base v}) :
    ∃ t : ComplexPoints f, t.hom.base (IsLocalRing.closedPoint ℂ) = v := by
  have h := hv.preimage e.base.hom.continuous
  rw [← Set.image_singleton, he.preimage_image] at h
  exact ⟨⟨_, ((pointEquivClosedPoint f).symm ⟨v, h⟩).2⟩,
    congrArg Subtype.val ((pointEquivClosedPoint f).apply_symm_apply ⟨v, h⟩)⟩

open Classical in
/-- **The component sums of a divisor on a fibre with reduced divisor fibres.** Let
`r : Z ⟶ Y` be a morphism with `Z` a complex scheme over `Y`, `g : Spec ℂ ⟶ Y` a `ℂ`-point with
image `y`, and `L E` a `ℚ`-divisor on each component `E` of a divisor `F` of `Z`. If the fibres
`P ×_Y Spec ℂ` of the prime divisors `P` of the `L E` are reduced and the class of the fibre cycle
`∑_E ∑_P c_P [P ×_Y Spec ℂ]_1` (Stacks, Tag 02QU) vanishes in `H_2(Z ×_Y Spec ℂ, ℚ)`, then the sum
`∑_E ∑_P c_P ∑_C cl(C)` vanishes in the homology of the reduced fibre `r⁻¹(y)`, `C = closure {x}`
running over the curves which are maximal irreducible subsets of `P ∩ r⁻¹(y)`. -/
theorem sum_rationalCycleClass_fibreComponents_eq_zero_of_isReduced
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} (hcomp : r ≫ sY = Z ↘ Spec (.of ℂ)) {F : Divisor Z}
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (g : Spec (.of ℂ) ⟶ Y) (hg : g ≫ sY = 𝟙 _) {y : Y}
    (hgy : g.base (IsLocalRing.closedPoint ℂ) = y) (hy : IsClosed {y}) :
    letI : (pullback r g).Over (Spec (.of ℂ)) := ⟨pullback.snd r g⟩
    ∀ [IsComplexScheme (pullback r g)],
    (∀ E : F.support, ∀ P ∈ (L E).support,
      IsReduced (pullback (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r) g)) →
    Chow.rationalCycleClass (pullback r g) 1
      (∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
        haveI := isClosedImmersion_pullback_map_of_comp_eq
          (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _) g
        (1 : ℚ) ⊗ₜ[ℤ] Stacks.Chow.cycleAssociatedToClosedSubscheme
          (Stacks.Chow.fieldChowSituation ℂ) (pullback r g ↘ Spec (.of ℂ))
          (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r) g r g
            (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
            ((Category.comp_id _).trans (Category.id_comp _).symm)) ((1 : ℕ) : ℤ)) = 0 →
    (∑ E : F.support, (L E).sum fun P c ↦ c •
      ∑ᶠ (x : {x : (Scheme.IdealSheafData.vanishingIdeal
            ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme //
          Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            ((Scheme.IdealSheafData.vanishingIdeal
              ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme ↘ Spec (.of ℂ)) x =
            (1 : ℕ)})
        (_ : Maximal (fun A ↦ IsIrreducible A ∧
            A ⊆ (Scheme.IdealSheafData.vanishingIdeal
              ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subschemeι.base ⁻¹'
              (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
          (closure {x.1})),
        Chow.pointCycleClass ℚ x.1 x.2) = 0 := by
  let : (pullback r g).Over (Spec (.of ℂ)) := ⟨pullback.snd r g⟩
  intro _ hred h0
  set I := Scheme.IdealSheafData.vanishingIdeal (X := Z)
    ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩
  have : IsClosedImmersion g := isClosedImmersion_of_comp_eq_id sY g hg
  have hfo := isOver_pullback_fst_of_comp_eq_id hcomp hg
  obtain ⟨j, _, hjs, hj⟩ := exists_isClosedImmersion_vanishingIdeal_comp_pullback_fst hgy hy
  have hjo : j.IsOver (Spec (.of ℂ)) := ⟨by
    change j ≫ pullback.snd r g = I.subschemeι ≫ Z ↘ Spec (.of ℂ)
    rw [← hj, Category.assoc]
    congr 1
    exact hfo.comp_over.symm⟩
  have : Surjective j := ⟨hjs⟩
  choose x hx1 hx2 using fun (E : F.support) (P : Mori.PrimeDivisor E.1.idealSheaf.subscheme)
      (hP : P ∈ (L E).support) ↦
    haveI := hred E P hP
    exists_rationalProperPushforward_pullback_map_eq j hj
      (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (Category.assoc _ _ _)
      (S := E.1.idealSheaf.subschemeι.base '' (P.support : Set _))
      (by rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.IdealSheafData.range_subschemeι])
  set X : Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ)
      (I.subscheme ↘ Spec (.of ℂ)) ((1 : ℕ) : ℤ) := ∑ E : F.support,
    ∑ P ∈ (L E).support.attach, (L E) P.1 • x E P.1 P.2 with hXdef
  have hcyc : (∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
      haveI := isClosedImmersion_pullback_map_of_comp_eq
        (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _) g
      (1 : ℚ) ⊗ₜ[ℤ] Stacks.Chow.cycleAssociatedToClosedSubscheme
        (Stacks.Chow.fieldChowSituation ℂ) (pullback r g ↘ Spec (.of ℂ))
        (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r) g r g
          (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
          ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm)) ((1 : ℕ) : ℤ)) =
      Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ)
        (I.subscheme ↘ Spec (.of ℂ)) (pullback r g ↘ Spec (.of ℂ)) ((1 : ℕ) : ℤ) j
        (comp_over j _) X := by
    rw [hXdef, map_sum]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    rw [map_sum]
    refine (Finset.sum_attach _ _).symm.trans (Finset.sum_congr rfl fun P _ ↦ ?_)
    rw [map_smul, ← hx1 E P.1 P.2]
  rw [hcyc, Chow.rationalCycleClass_rationalProperPushforward] at h0
  have hX : Chow.rationalCycleClass I.subscheme 1 X = 0 :=
    injective_pushforward_map_of_surjective j _ (h0.trans (map_zero _).symm)
  refine Eq.trans ?_ hX
  rw [hXdef, map_sum]
  refine Finset.sum_congr rfl fun E _ ↦ ?_
  rw [Finsupp.sum, map_sum]
  refine (Finset.sum_attach _ _).symm.trans (Finset.sum_congr rfl fun P _ ↦ ?_)
  rw [map_smul, hx2 E P.1 P.2]

/-- An open `U'` of the curve `T` with its reduced structure meeting it is cut out on `T` by an
open of `Y`: there is an open `V ⊆ Y` meeting `T` with `V ∩ T` contained in the image of `U'`. -/
theorem exists_opens_inter_nonempty_subset_image {Y : Scheme.{0}} {T : IrreducibleCloseds Y}
    {U' : Set (curveScheme T)} (hU'o : IsOpen U') (hU' : U'.Nonempty) :
    ∃ V : Y.Opens, ((V : Set Y) ∩ T).Nonempty ∧ (V : Set Y) ∩ T ⊆ (curveι T).base '' U' := by
  obtain ⟨u₀, hu₀⟩ := hU'
  have hTc := range_curveι_base T
  refine ⟨⟨((curveι T).base '' U'ᶜ)ᶜ,
    ((curveι T).isClosedEmbedding.isClosedMap _ hU'o.isClosed_compl).isOpen_compl⟩,
    ⟨(curveι T).base u₀, ?_, ?_⟩, ?_⟩
  · rintro ⟨u, hu, he⟩
    exact hu ((curveι T).isClosedEmbedding.injective he ▸ hu₀)
  · rw [← hTc]
    exact ⟨u₀, rfl⟩
  · rintro y ⟨hyV, hyT⟩
    rw [← hTc] at hyT
    obtain ⟨u, rfl⟩ := hyT
    exact ⟨u, not_not.1 fun h ↦ hyV ⟨u, h, rfl⟩, rfl⟩

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **From the fibre cycle to the component sums on a general fibre.** Let `r : Z ⟶ Y` be a
curve-and-point exceptional model, `L E` a `ℚ`-divisor on each component `E` of `F`, and `T` a
curve in `Y`. Suppose that the class of the fibre cycle `∑_E ∑_P c_P [P ×_Y t]_1` (Stacks,
Tag 02QU) vanishes in `H_2(F_t, ℚ)` for every `ℂ`-point `t` of a dense open of `T`. Then there is
an open `U ⊆ Y` meeting `T` such that, at every closed point `y ∈ U ∩ T`, the
sum `∑_E ∑_P c_P ∑_C cl(C)` vanishes in the homology of the reduced fibre `r⁻¹(y)`,
`C = closure {x}` running over the curves which are maximal irreducible subsets of `P ∩ r⁻¹(y)`
and `cl(C)` its cycle class `MMP.Chow.pointCycleClass`. -/
theorem IsCurvePointExceptionalModel.exists_opens_sum_rationalCycleClass_eq_zero
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1)
    (hfib : ∃ U : (curveScheme T).Opens, Dense (U : Set (curveScheme T)) ∧
        ∀ (t : ComplexPoints (U.ι ≫ curveι T ≫ sY))
          [IsComplexScheme (pointFibre sY r U t)],
          Chow.rationalCycleClass (pointFibre sY r U t) 1
            (∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
              (1 : ℚ) ⊗ₜ[ℤ] @Stacks.Chow.cycleAssociatedToClosedSubscheme
                (Stacks.Chow.fieldChowSituation ℂ) _ _ (pointFibre sY r U t ↘ Spec (.of ℂ)) _
                (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r)
                  (t.hom ≫ U.ι ≫ curveι T) r (t.hom ≫ U.ι ≫ curveι T)
                  (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
                  ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
                  ((Category.comp_id _).trans (Category.id_comp _).symm))
                (isClosedImmersion_pullback_map_of_comp_eq
                  (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _)
                  (t.hom ≫ U.ι ≫ curveι T)) ((1 : ℕ) : ℤ)) = 0) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
        ∀ y ∈ (U : Set Y) ∩ T, ∀ hy : IsClosed {y},
        (∑ E : F.support, (L E).sum fun P c ↦ c •
          ∑ᶠ (x : {x : (Scheme.IdealSheafData.vanishingIdeal
                ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                ((Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme ↘ Spec (.of ℂ)) x =
                (1 : ℕ)})
            (_ : Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ (Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subschemeι.base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
              (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2) = 0 := by
  have : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  have : AlgebraicGeometry.IsVariety ℂ sY := hr.isResolution.1
  have : IsIntegral (curveScheme T) :=
    isIntegral_subscheme_vanishingIdeal ⟨(T : Set Y), T.isClosed⟩ T.isIrreducible
  obtain ⟨U₀, hU₀, h₀⟩ := hfib
  choose Ured hUne hUred using
    fun (E : F.support) (P : Mori.PrimeDivisor E.1.idealSheaf.subscheme) ↦
      hr.exists_nonempty_open_isReduced_pullback T hT1 E P
  set U' : Set (curveScheme T) :=
    (U₀ : Set (curveScheme T)) ∩ ⋂ E : F.support, ⋂ P ∈ (L E).support,
      (Ured E P : Set (curveScheme T))
  have hU'o : IsOpen U' := U₀.isOpen.inter <|
    isOpen_iInter_of_finite fun E ↦ isOpen_biInter_finset fun P _ ↦ (Ured E P).isOpen
  set η := genericPoint (curveScheme T)
  have hmemη : ∀ V : (curveScheme T).Opens, (V : Set (curveScheme T)).Nonempty → η ∈ V :=
    fun V hV ↦ ((genericPoint_spec (curveScheme T)).mem_open_set_iff V.isOpen).2
      (by rwa [Set.univ_inter])
  have hηU' : η ∈ U' :=
    ⟨hmemη _ hU₀.nonempty, Set.mem_iInter.2 fun E ↦ Set.mem_iInter₂.2 fun P _ ↦
      hmemη _ (hUne E P)⟩
  obtain ⟨V, hV, hVT⟩ := exists_opens_inter_nonempty_subset_image hU'o ⟨η, hηU'⟩
  refine ⟨V, hV, fun y hyVT hy ↦ ?_⟩
  obtain ⟨u, huU', rfl⟩ := hVT hyVT
  obtain ⟨v, hv⟩ : u ∈ Set.range U₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact huU'.1
  obtain ⟨t, htv⟩ := exists_complexPoints_hom_base_eq (U₀.ι ≫ curveι T ≫ sY) (U₀.ι ≫ curveι T)
    ((curveι T).isClosedEmbedding.injective.comp U₀.ι.isOpenEmbedding.injective)
    (by rwa [Scheme.Hom.comp_apply, hv])
  set g := t.hom ≫ U₀.ι ≫ curveι T with hgdef
  have hg : g ≫ sY = 𝟙 _ := by simp [hgdef]
  have hgy : g.base (IsLocalRing.closedPoint ℂ) = (curveι T).base u := hv ▸ htv ▸ rfl
  let : (pullback r g).Over (Spec (.of ℂ)) := ⟨pullback.snd r g⟩
  have : IsClosedImmersion g := isClosedImmersion_of_comp_eq_id sY g hg
  have : (pullback.fst r g).IsOver (Spec (.of ℂ)) := isOver_pullback_fst_of_comp_eq_id hr.comp_eq hg
  have hcx : IsComplexScheme (pullback r g) := .of_isClosedImmersion (pullback.fst r g)
  have hred : ∀ E : F.support, ∀ P ∈ (L E).support,
      IsReduced (pullback (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r) g) :=
    fun E P hP ↦ by
      simpa only [Category.assoc] using hUred E P ℂ (t.hom ≫ U₀.ι) (by
        rintro _ ⟨a, rfl⟩
        rw [Subsingleton.elim a (IsLocalRing.closedPoint ℂ)]
        change U₀.ι.base (t.hom.base (IsLocalRing.closedPoint ℂ)) ∈ _
        rw [htv, hv]
        exact Set.mem_iInter₂.1 (Set.mem_iInter.1 huU'.2 E) P hP)
  exact sum_rationalCycleClass_fibreComponents_eq_zero_of_isReduced hr.comp_eq L g hg hgy hy
    hred (@h₀ t hcx)

end MMP.Fourfold
