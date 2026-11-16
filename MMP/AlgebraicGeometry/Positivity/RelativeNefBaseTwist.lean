module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ConvexGeography
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RayLength
public import MMP.AlgebraicGeometry.Intersection.N1CartierCoordinates

section

/-!
# A relatively nef klt adjoint becomes nef after a base twist

Let `(X, B)` be a klt pair with `B` an effective `ℚ`-divisor on a projective variety `X` of
dimension `n` over an algebraically closed field `k` of characteristic zero, and let
`f : X ⟶ Z` be a morphism over `k` to a projective variety `Z`. If `D = K_X + B` is `f`-nef,
then for every ample Cartier divisor `A` on `Z` and every integer `N ≥ 2n` the divisor
`D + N f^*A` is nef.

If it were not, the cone theorem would give a `(D + N f^*A)`-negative extremal ray of `NE̅(X)`;
since `f^*A` is nef, the ray is `D`-negative, so it is spanned by a rational curve `C` with
`0 < -D · C ≤ 2n`. Relative nefness of `D` forbids `C` to be contracted by `f`, so by the
projection formula `f^*A · C ≥ 1`, and `(D + N f^*A) · C ≥ N - 2n ≥ 0`, a contradiction.

## Main results

* `MMP.Fourfold.IsKltPair.isNef_add_zsmul_of_isRelativelyNef`: the statement above.

## Implementation notes

* The klt condition is `MMP.Mori.IsKltPair` with a canonical divisor `K` of dimension `n`, which
  pins `n = dim X`; effectivity of `B` is `0 ≤ B`.
* `Z` is not assumed normal, so `A` is a Cartier divisor in the sense of
  `Scheme.CartierDivisor`, ample when its invertible sheaf is. The pull-back `f^*A`
  enters through its invertible sheaf: it is any divisor `G` on `X` with
  `𝒪_X(G) ≅ f^*𝒪_Z(A)`. Such a `G` is determined up to linear equivalence, which does not change
  nefness, and the statement is made for every such `G`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.FourfoldProofs.FourfoldKltRelativeNefGlobalBaseTwistProof

open MMP MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Curves -/

section Curves

variable {k : Type} [Field k] {X : Scheme.{0}}

/-- The kernel of a closed immersion from a reduced scheme is the vanishing ideal of its range. -/
private theorem ker_eq_vanishingIdeal_of_isReduced {Y W : Scheme.{0}} (ι : Y ⟶ W)
    [IsClosedImmersion ι] [IsReduced Y] (T : Closeds W) (hT : (T : Set W) = Set.range ι) :
    ι.ker = Scheme.IdealSheafData.vanishingIdeal T := by
  have hrad : ι.ker.radical = ι.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.mpr (IsReduced.eq_zero _ ⟨n, hn⟩)
  have : ι.ker.support = T := Closeds.ext (by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq, hT])
  rw [← this, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- A closed immersion from an integral scheme is, up to isomorphism over the target, the reduced
closed subscheme on the closure of the image of its generic point. -/
private theorem exists_iso_curveSubschemeAt {Y W : Scheme.{0}} [IsIntegral Y] (ι : Y ⟶ W)
    [IsClosedImmersion ι] :
    ∃ e : Y ≅ curveSubschemeAt (ι (genericPoint Y)), e.hom ≫ curveSubschemeAtι _ = ι := by
  have hrange : Set.range ι = closure {ι (genericPoint Y)} := by
    rw [← Set.image_singleton, ι.isClosedEmbedding.closure_image_eq, (genericPoint_spec Y).def]
    simp
  have hker : ι.ker = (curveSubschemeAtι (ι (genericPoint Y))).ker := by
    rw [ker_eq_vanishingIdeal_of_isReduced ι (Closeds.closure {ι (genericPoint Y)})
      hrange.symm, Scheme.IdealSheafData.ker_subschemeι]
  have := IsClosedImmersion.isIso_of_ker_eq ι (curveSubschemeAtι _) _
    (IsClosedImmersion.lift_fac _ _ hker.ge) hker
  exact ⟨asIso (IsClosedImmersion.lift _ ι hker.ge), IsClosedImmersion.lift_fac _ _ _⟩

variable [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]

/-- Every closed curve `i : C ⟶ X` proper over `k` is, for intersection numbers, a proper curve
`T ⊆ X`: the closure of the image of the generic point of `C`. -/
private theorem exists_properCurve_intersectionNumber_eq {C : Scheme.{0}} (i : C ⟶ X)
    [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)] (hC : topologicalKrullDim C = 1) :
    ∃ T : ProperCurve sX, ∀ (D : QDivisor X) (hD : D.IsQCartier),
      D.intersectionNumber k sX i hC.le hD = D.intersectionNumber k sX T.ι T.dim_le hD := by
  obtain ⟨e, he⟩ := exists_iso_curveSubschemeAt i
  have hdim : topologicalKrullDim (curveSubschemeAt (i (genericPoint C))) = 1 := by
    rw [← hC]
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm
  have hprop : IsProper (curveSubschemeAtι (i (genericPoint C)) ≫ sX) := by
    have h1 : IsProper (e.hom ≫ curveSubschemeAtι (i (genericPoint C)) ≫ sX) := by
      rw [← Category.assoc, he]; infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom _).mp h1
  refine ⟨⟨i (genericPoint C), hdim, hprop⟩, fun D hD => ?_⟩
  have := QuasiCompact.compactSpace_of_compactSpace sX
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i _ hC.le _ e he]

end Curves

/-! ### Curve forms -/

section CurveForm

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- The curve form is additive in the divisor. -/
private theorem curveForm_add (D D' : QDivisor X) (hD : D.IsQCartier) (hD' : D'.IsQCartier)
    (hDD' : (D + D').IsQCartier) :
    QDivisor.curveForm sX (D + D') hDD' =
      QDivisor.curveForm sX D hD + QDivisor.curveForm sX D' hD' :=
  ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => by
    simp only [LinearMap.add_apply, ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_add' k sX C.ι C.dim_le D D' hD hD' hDD']
    push_cast
    ring

/-- The curve form of an integral multiple. -/
private theorem curveForm_zsmul (D : QDivisor X) (hD : D.IsQCartier) (N : ℤ)
    (hND : (N • D).IsQCartier) :
    QDivisor.curveForm sX (N • D) hND = (N : ℝ) • QDivisor.curveForm sX D hD :=
  ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => by
    have h := QDivisor.intersectionNumber_smul k sX C.ι C.dim_le (N : ℚ) D hD
      (by rwa [Int.cast_smul_eq_zsmul])
    simp only [Int.cast_smul_eq_zsmul] at h
    simp only [LinearMap.smul_apply, ProgramBaseChange.curveForm_numericalClass_cycle, h,
      smul_eq_mul]
    push_cast
    ring

end CurveForm

/-! ### Pull-backs of ample divisors -/

section Pullback

variable {k : Type} [Field k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sZ] {f : X ⟶ Z}
  (hf : f ≫ sZ = sX) {A : Z.CartierDivisor}
  (hA : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A))

include hf hA

/-- The pull-back of an ample Cartier divisor has nonnegative degree on every proper curve. -/
private theorem degree_pullback_nonneg (T : ProperCurve sX) :
    0 ≤ T.degree k
      ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A)) := by
  rw [ProperCurve.degree_pullback f hf T]
  split_ifs with h
  · exact mul_nonneg (Int.natCast_nonneg _)
      (Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple
        (AlgebraicGeometry.IsProjectiveVariety.toIsVariety (f := sZ)) A hA ⟨_, h⟩).le
  · exact le_rfl

/-- The pull-back of an ample Cartier divisor has positive, hence at least one, degree on every
proper curve that `f` does not contract. -/
private theorem one_le_degree_pullback (T : ProperCurve sX) (hT : ¬ T.IsContractedBy f) :
    1 ≤ T.degree k
      ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A)) := by
  have h0 := degree_pullback_nonneg hf hA T
  have hne : T.degree k
      ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A)) ≠ 0 :=
    fun h => hT (ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hf _
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple Z _).mpr hA) T h)
  omega

end Pullback

/-! ### Divisors attached to `f` -/

section Twist

variable {k : Type} [Field k] {X Z : Scheme.{0}} [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} [CompactSpace X] [QuasiCompact sX] (f : X ⟶ Z)

/-- A divisor whose sheaf is the pull-back of an invertible sheaf on `Z` is Cartier. -/
private theorem isCartier_of_iso_pullback [IsIntegral X] (A : Z.CartierDivisor) (G : Divisor X)
    (eG : G.divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A)) :
    G.IsCartier := fun x => by
  obtain ⟨U, hxU, ψ, hψ⟩ := exists_isLocalEquation_preimage_of_iso_pullback f _ eG (f x)
  exact ⟨f ⁻¹ᵁ U, hxU, ψ, hψ⟩

/-- The curve form of an `f`-nef divisor is nonnegative on the curves `f` contracts. -/
private theorem curveForm_nonneg_of_isRelativelyNef {D : QDivisor X}
    (hD : D.IsRelativelyNef sX f) (hDq : D.IsQCartier) (T : ProperCurve sX)
    (hT : T.IsContractedBy f) :
    0 ≤ QDivisor.curveForm sX D hDq (OneCycle.numericalClass sX (T.cycle ℝ)) := by
  obtain ⟨h, hh⟩ := hD
  refine (hh T hT).trans_eq ?_
  simp only [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun E _ => ?_
  have := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  rw [LinearMap.smul_apply, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
    ProperCurve.degree_divisorialSheaf T _ (Divisor.mem_cartierSubgroup.mp E.2), smul_eq_mul]

/-- If `𝒪_X(G) ≅ f^* 𝒪_Z(A)`, then `G · T = deg_T f^* 𝒪_Z(A)` for every proper curve `T`. -/
private theorem curveForm_numericalClass_eq_degree {A : Z.CartierDivisor} {G : Divisor X}
    (hGc : G.IsCartier)
    (eG : G.divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A))
    (T : ProperCurve sX) :
    QDivisor.curveForm sX (Divisor.toQDivisor G) (QDivisor.isQCartier_toQDivisor hGc)
      (OneCycle.numericalClass sX (T.cycle ℝ)) = (T.degree k
        ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A)) : ℝ) := by
  have := hGc.isInvertibleModule_divisorialSheaf
  rw [ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_toQDivisor k sX T.ι T.dim_le G hGc,
    ← ProperCurve.degree_divisorialSheaf T G hGc, ProperCurve.degree, ProperCurve.degree,
    degreeOn_eq_of_iso k sX T.ι T.dim_le eG]
  push_cast
  rfl

end Twist

/-! ### The closed cone of curves -/

section Cone

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
  (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]

/-- Every linear form on `N₁(X)` is continuous for the numerical topology. -/
private theorem continuous_linearMap (φ : NumericalCurveClasses sX →ₗ[ℝ] ℝ) : Continuous φ := by
  obtain ⟨hfd, -, hext, hcoord, -⟩ :=
    NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety sX
  obtain ⟨t, -, ht, htspan⟩ := hext ∅ (linearIndepOn_empty _ _)
  rw [Set.image_eq_range] at htspan
  obtain ⟨⟨Φ, -⟩, -⟩ := hcoord (fun E : t => (E : X.CartierDivisor)) ht htspan
  have := hfd
  have : Fintype t := @Fintype.ofFinite _ ht.finite
  have : (φ : NumericalCurveClasses sX → ℝ) = (φ ∘ₗ Φ.symm.toLinearMap) ∘ Φ := by
    ext w; simp
  rw [this]
  exact (LinearMap.continuous_of_finiteDimensional _).comp Φ.continuous

/-- A linear form that is nonnegative on every proper curve is nonnegative on `NE̅(X)`. -/
private theorem nonneg_of_mem_closedConeOfCurves (φ : NumericalCurveClasses sX →ₗ[ℝ] ℝ)
    (hφ : ∀ T : ProperCurve sX, 0 ≤ φ (OneCycle.numericalClass sX (T.cycle ℝ)))
    {w : NumericalCurveClasses sX} (hw : w ∈ closedConeOfCurves sX) : 0 ≤ φ w := by
  have hsub : (coneOfCurves sX : Set (NumericalCurveClasses sX)) ⊆ {w | 0 ≤ φ w} := by
    intro w hw
    change w ∈ PointedCone.hull ℝ _ at hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨C, rfl⟩ := hx; exact hφ C
    | zero => simp
    | add x y _ _ hx hy => simpa using add_nonneg hx hy
    | smul c x _ hx =>
      change 0 ≤ φ ((c : ℝ) • x)
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg c.2 hx
  exact closure_minimal hsub (isClosed_le continuous_const (continuous_linearMap sX φ)) hw

/-- **A linear form negative on a curve is negative on an extremal ray of `NE̅(X)`.** On a
projective variety, a linear form on `N₁(X)` that is negative on the class of some proper curve
is negative on every nonzero element of some extremal ray of the closed cone of curves. -/
private theorem exists_isExtremalRay_neg (e : NumericalCurveClasses sX →ₗ[ℝ] ℝ)
    (he : ∃ T : ProperCurve sX, e (OneCycle.numericalClass sX (T.cycle ℝ)) < 0) :
    ∃ R : Set (NumericalCurveClasses sX),
      IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R ∧
      ∀ u ∈ R, u ≠ 0 → e u < 0 := by
  obtain ⟨T₀, hT₀⟩ := he
  -- Cartier coordinates `Φ : N₁(X) ≃ ℝ^t`
  obtain ⟨hfd, -, hext, hcoord, -⟩ :=
    NumericalCurveClasses.exists_cartier_coordinates_of_isProperVariety sX
  obtain ⟨t, -, ht, htspan⟩ := hext ∅ (linearIndepOn_empty _ _)
  rw [Set.image_eq_range] at htspan
  obtain ⟨⟨Φ, -⟩, -⟩ := hcoord (fun E : t => (E : X.CartierDivisor)) ht htspan
  have : Fintype t := @Fintype.ofFinite _ ht.finite
  set NE := (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
  -- an ample form, positive on `NE̅(X) \ {0}`
  obtain ⟨H, hH⟩ := IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf (sX := sX)
  set a := NumericalCurveClasses.intersectionNumber (sX := sX) (KCartierDivisor.ofCartier ℝ H)
  have ha : ∀ w ∈ NE, w ≠ 0 → 0 < a w := fun w hw hw0 => by
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX w
    rw [NumericalCurveClasses.intersectionNumber_numericalClass]
    exact closedConeOfCurves_diff_zero_subset_posHalfspace sX H hH ⟨hw, hw0⟩ Z rfl
  -- the image of `NE̅(X)` in coordinates, a closed cone
  set Cc : PointedCone ℝ (t → ℝ) :=
    (closedConeOfCurves sX).map (Φ : NumericalCurveClasses sX →ₗ[ℝ] t → ℝ)
  have hCc : (Cc : Set (t → ℝ)) = Φ '' NE := Submodule.map_coe _ _
  obtain ⟨R', hR', hR'neg⟩ := exists_isExtremalRay_neg_of_exists_neg Cc
    (by rw [hCc]; exact Φ.toHomeomorph.isClosedMap _ isClosed_closure)
    (a ∘ₗ (Φ.symm : (t → ℝ) →ₗ[ℝ] NumericalCurveClasses sX))
    (fun x hx hx0 => by
      obtain ⟨w, hw, rfl⟩ : x ∈ Φ '' NE := hCc ▸ hx
      simpa using ha w hw (by rintro rfl; simp at hx0))
    (e ∘ₗ (Φ.symm : (t → ℝ) →ₗ[ℝ] NumericalCurveClasses sX))
    ⟨Φ (OneCycle.numericalClass sX (T₀.cycle ℝ)), show _ ∈ (Cc : Set (t → ℝ)) by
      rw [hCc]
      exact ⟨_, coneOfCurves_le_closedConeOfCurves sX
        (numericalClass_cycle_mem_coneOfCurves sX T₀), rfl⟩, by simpa using hT₀⟩
  -- back in `N₁(X)`
  refine ⟨Φ.symm '' R', ?_, ?_⟩
  · have := ProgramBaseChange.isExtremalRay_image Φ.symm.toLinearEquiv (hCc ▸ hR')
    simpa [Set.image_image] using this
  · rintro _ ⟨u', hu', rfl⟩ hu0
    simpa using hR'neg u' hu' (by rintro rfl; simp at hu0)

end Cone

end MMP.FourfoldProofs.FourfoldKltRelativeNefGlobalBaseTwistProof

end

public section

open AlgebraicGeometry CategoryTheory MMP.Mori

namespace MMP.Fourfold

open MMP.FourfoldProofs.FourfoldKltRelativeNefGlobalBaseTwistProof in
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **A base twist makes a relatively nef klt adjoint nef.** Let `(X, B)` be a klt pair, with
`B ≥ 0` a `ℚ`-divisor and `K` a canonical divisor of dimension `n`, on a projective variety `X`
over an algebraically closed field `k` of characteristic zero, and let `f : X ⟶ Z` be a morphism
over `k` to a projective variety `Z` such that `K + B` is `f`-nef. Then for every ample Cartier
divisor `A` on `Z`, every divisor `G` on `X` with `𝒪_X(G) ≅ f^*𝒪_Z(A)` and every integer
`N ≥ 2n`, the divisor `K + B + N G` is nef. -/
@[mmp "lem_fourfold_klt_relative_nef_global_base_twist"]
public theorem IsKltPair.isNef_add_zsmul_of_isRelativelyNef {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sX]
    [QuasiCompact sX] {sZ : Z ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sZ]
    {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    (hD : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) (A : Z.CartierDivisor)
    (hA : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf A)) (G : Divisor X)
    (hG : Nonempty (G.divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A)))
    (N : ℤ) (hN : 2 * (n : ℤ) ≤ N) :
    (Divisor.toQDivisor K + B + N • Divisor.toQDivisor G).IsNef k sX := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨eG⟩ := hG
  have hGc := isCartier_of_iso_pullback f A G eG
  set D := Divisor.toQDivisor K + B
  have hDq : D.IsQCartier := hklt.1.2.2
  have hGq := QDivisor.isQCartier_toQDivisor hGc
  have hNGq : (N • Divisor.toQDivisor G).IsQCartier := by
    rw [← map_zsmul]; exact QDivisor.isQCartier_toQDivisor (hGc.zsmul N)
  set d := QDivisor.curveForm sX D hDq
  set g := QDivisor.curveForm sX (Divisor.toQDivisor G) hGq
  have he : QDivisor.curveForm sX (D + N • Divisor.toQDivisor G) (hDq.add hNGq) =
      d + (N : ℝ) • g := by
    rw [curveForm_add sX _ _ hDq hNGq, curveForm_zsmul sX _ hGq]
  have hgT := curveForm_numericalClass_eq_degree (sX := sX) f hGc eG
  -- it suffices to test the classes of proper curves
  suffices H : ∀ T : ProperCurve sX,
      0 ≤ (d + (N : ℝ) • g) (OneCycle.numericalClass sX (T.cycle ℝ)) by
    refine ⟨hDq.add hNGq, fun C i _ _ _ hC => ?_⟩
    obtain ⟨T, hT⟩ := exists_properCurve_intersectionNumber_eq (sX := sX) i hC
    have := H T
    rw [← he, ProgramBaseChange.curveForm_numericalClass_cycle] at this
    rw [hT]
    exact_mod_cast this
  by_contra! hneg
  -- `D + N G` is negative on an extremal ray `R` of `NE̅(X)`; as `G` is nef, `R` is `D`-negative
  obtain ⟨R, hR, heR⟩ := exists_isExtremalRay_neg sX _ hneg
  have hN0 : (0 : ℝ) ≤ N := by exact_mod_cast (by omega : (0 : ℤ) ≤ N)
  have hRneg : IsNegativeExtremalRayOf sX D R := ⟨hDq, hR, fun u hu hu0 => by
    have h1 := heR u hu hu0
    have h2 : 0 ≤ g u := nonneg_of_mem_closedConeOfCurves sX g
      (fun C => hgT C ▸ by exact_mod_cast degree_pullback_nonneg hf hA C) (hR.1.1 hu)
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    nlinarith⟩
  -- the length theorem: `R` is spanned by a rational curve `T` with `0 < -D · T ≤ 2n`
  obtain ⟨T, -, hRT, hpos, hle⟩ :=
    exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf_of_isAlgClosed sX hklt hB hRneg
  have hT0 : OneCycle.numericalClass sX (T.cycle ℝ) ≠ 0 := by
    intro h; rw [h, map_zero] at hpos; simp at hpos
  have heT := heR _ (hRT ▸ ⟨1, zero_le_one, one_smul _ _⟩) hT0
  -- `f` does not contract `T`, so `G · T ≥ 1`, and `(D + N G) · T ≥ N - 2n ≥ 0`
  have hTc : ¬ T.IsContractedBy f := fun hc => by
    linarith [curveForm_nonneg_of_isRelativelyNef f hD hDq T hc]
  have hgT1 : (1 : ℝ) ≤ g (OneCycle.numericalClass sX (T.cycle ℝ)) := by
    rw [hgT T]; exact_mod_cast one_le_degree_pullback hf hA T hTc
  have hNn : (2 * n : ℝ) ≤ N := by exact_mod_cast hN
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at heT
  nlinarith

end MMP.Fourfold

end
