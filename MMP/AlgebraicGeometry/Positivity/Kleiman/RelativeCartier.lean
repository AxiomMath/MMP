module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.RelativeNumericalDuality
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowup
public import MMP.AlgebraicGeometry.Morphisms.ClosedPointsDense
public import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

section

/-!
# The relative Kleiman criterion for Cartier divisors

Let `k` be algebraically closed of characteristic zero, `f : Y ⟶ X` a projective morphism of
`k`-varieties and `D` a Cartier divisor on `Y`. Then `D` is `f`-ample if and only if
`(z · D) > 0` for every nonzero `z` in the closed relative cone of curves `NE̅(Y/X)`.

If `D` is `f`-ample and `z ≠ 0`, some Cartier divisor `E` has `(z · E) ≠ 0`, since Cartier
divisors separate `N₁(Y/X)` on the integral `Y`. For `n ≫ 0` both `nD + E` and `nD - E` are
`f`-ample (Stacks Tag 0C4K for `𝟙 ≫ f`), and an `f`-ample divisor has positive degree on every
contracted curve, hence is nonnegative on `NE̅(Y/X)`; so `n (z · D) ≥ |(z · E)| > 0`.

Conversely, let `A` be an `f`-ample Cartier divisor. Since `N₁(Y/X)` is finite-dimensional, `D`
has a positive minimum and `A` is bounded on the intersection of `NE̅(Y/X)` with a sphere, so
`L = mD - A` is nonnegative on every contracted curve for some `m > 0`. On the fibre `Y_y` over a
closed point `y`, a projective scheme over `κ(y) ≅ k`, every integral curve is a contracted curve
of `Y`, so `L` is nef there, and `A` is ample there. For every integral closed `V ⊆ Y_y` of
dimension `d > 0` the multilinear expansion of `((A + L)^d · V)`, whose mixed terms are
nonnegative by Kleiman's theorem, gives `((mD)^d · V) ≥ (A^d · V) > 0`. By the Nakai criterion
`mD` is ample on `Y_y`, hence ample over a neighbourhood of `y`; these neighbourhoods cover `X`, so
`mD` is `f`-ample, and so is `D`.

## Main results

* `MMP.Fourfold.exists_isRelativelyAmple_nsmul_add`: if `D` is `f`-ample, then `nD + E` is
  `f`-ample for `n ≫ 0` (Stacks Tag 0C4K).
* `MMP.Mori.isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos`: the
  relative Kleiman criterion for Cartier divisors.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.37, 1.38,
  1.41, 1.44
-/

namespace MMP.FourfoldProofs.MmpFoundationRelativeCartierKleimanCharZeroProof

open AlgebraicGeometry CategoryTheory MMP.Mori

open RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple

/-! ### Sheaf-level preliminaries -/

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private noncomputable def modulePullbackIso {X Y : Scheme.{0}} (f : X ⟶ Y) (F : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj F ≅ (Scheme.Modules.pullback f).obj F :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app F

/-- The twist `𝒪_X(E) ⊗ 𝒪_X(L)^{⊗ n}` is `𝒪_X(nL + E)`. -/
private noncomputable def twistIso {X : Scheme.{0}} (L E : X.CartierDivisor) :
    (n : ℕ) → tensorModules X (MMP.CartierDivisor.sheaf E)
      (tensorPowModule X (CartierDivisor.sheaf L) (n : ℤ)) ≅ CartierDivisor.sheaf (n • L + E)
  | 0 => tensorModulesMapIso X (Iso.refl _) (tensorPowModuleZeroIso X _) ≪≫
      Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor X _ ≪≫ eqToIso (by simp)
  | n + 1 =>
      tensorModulesMapIso X (Iso.refl _)
        (tensorPowModuleCongr X _ (by push_cast; ring) ≪≫
          (tensorPowModuleAddIso X _ (n : ℤ) 1).symm ≪≫
          tensorModulesMapIso X (Iso.refl _) (tensorPowModuleOneIso X _)) ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesAssociator X _ _ _).symm ≪≫
      tensorModulesMapIso X (twistIso L E n) (Iso.refl _) ≪≫
      MMP.CartierDivisorSheaf.sheafMulIso (n • L + E) L ≪≫ eqToIso (by rw [succ_nsmul]; abel_nf)

/-- `𝒪_X((n + 1)L) ≅ 𝒪_X(L)^{⊗ (n + 1)}`. -/
private noncomputable def succNsmulIso {X : Scheme.{0}} (L : X.CartierDivisor) (n : ℕ) :
    MMP.CartierDivisor.sheaf ((n + 1) • L) ≅
      tensorPowModule X (MMP.CartierDivisor.sheaf L) ((n + 1 : ℕ) : ℤ) :=
  eqToIso (by rw [succ_nsmul]) ≪≫ (twistIso L L n).symm ≪≫
    tensorModulesMapIso X (tensorPowModuleOneIso X _).symm (Iso.refl _) ≪≫
    tensorPowModuleAddIso X _ 1 (n : ℤ) ≪≫ tensorPowModuleCongr X _ (by push_cast; ring)

end MMP.FourfoldProofs.MmpFoundationRelativeCartierKleimanCharZeroProof

/-! ### Relative twists -/

namespace MMP.Fourfold

open AlgebraicGeometry CategoryTheory MMP.Mori RingedSpaceModuleAdjunction Stacks.Ample
  Stacks.RelativeVeryAmple
open MMP.FourfoldProofs.MmpFoundationRelativeCartierKleimanCharZeroProof

/-- For a quasi-compact morphism, `f`-ampleness in the local form gives ampleness over every
affine open of the base. -/
public theorem stacks_of_isRelativelyAmple {X S : Scheme.{0}} (f : X ⟶ S) [QuasiCompact f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L inferInstance hL

/-- Every invertible module is ample relative to the identity. -/
public theorem isRelativelyAmple_id {Y : Scheme.{0}} (L : Y.Modules) [IsInvertibleModule Y L] :
    Stacks.RelativeAmple.IsRelativelyAmple (𝟙 Y) L := by
  refine ⟨inferInstance, fun V hV => ?_⟩
  haveI : IsAffine ((𝟙 Y) ⁻¹ᵁ V) := hV.preimage (𝟙 Y)
  have hinv : IsInvertibleModule ((𝟙 Y) ⁻¹ᵁ V).toScheme
      ((modulePullback ((𝟙 Y) ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) := inferInstance
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _ _ hinv)

/-- **Relative twists.** If `D` is `f`-ample over a quasi-compact base, then `nD + E` is `f`-ample
for all large `n`, for every Cartier divisor `E` (Stacks Tag 0C4K for `𝟙 ≫ f`). -/
public theorem exists_isRelativelyAmple_nsmul_add {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    [CompactSpace X] {D : Y.CartierDivisor} (hD : IsRelativelyAmple f (MMP.CartierDivisor.sheaf D))
    (E : Y.CartierDivisor) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsRelativelyAmple f (MMP.CartierDivisor.sheaf (n • D + E)) := by
  obtain ⟨n₀, hn₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp (𝟙 Y) f
    (MMP.CartierDivisor.sheaf E) (MMP.CartierDivisor.sheaf D) (isRelativelyAmple_id _)
    (stacks_of_isRelativelyAmple f _ hD)
  refine ⟨n₀, fun n hn => ?_⟩
  have h := hn₀ n hn
  rw [Category.id_comp] at h
  have e : Stacks.AmplePullbackPart1.tensorPullbackPowModule (𝟙 Y) (MMP.CartierDivisor.sheaf E)
      (MMP.CartierDivisor.sheaf D) n ≅ MMP.CartierDivisor.sheaf (n • D + E) :=
    tensorModulesMapIso Y (Iso.refl _)
      (modulePullbackIso (𝟙 Y) _ ≪≫ (Scheme.Modules.pullbackId Y).app _) ≪≫ twistIso D E n
  exact IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ e).mp h)

end MMP.Fourfold

namespace MMP.FourfoldProofs.MmpFoundationRelativeCartierKleimanCharZeroProof

open AlgebraicGeometry CategoryTheory MMP.Mori RingedSpaceModuleAdjunction Stacks.Ample
  Stacks.RelativeVeryAmple

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### The pairing with Cartier divisors -/

section Pairing

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X}

/-- `(z · 1 · E)` is the degree of `𝒪_Y(E)` on `z`. -/
private theorem intersectionNumber_ofCartier_eq_degree (E : Y.CartierDivisor) :
    RelativeNumericalCurveClasses.intersectionNumber (sX := sY) (f := f)
        (KCartierDivisor.ofCartier ℝ E) =
      RelativeNumericalCurveClasses.degree sY f (MMP.CartierDivisor.sheaf E) :=
  Submodule.linearMap_qext _
    (LinearMap.ext fun Z => OneCycle.intersectionNumber_ofCartier (Z : OneCycle ℝ sY) E)

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add (C : ProperCurve sY) (E E' : Y.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) + C.degree k (MMP.CartierDivisor.sheaf E') := by
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
        Y.toRingedSpace.IsSheaf⟩).obj (CartierDivisor.sheaf E)).obj (CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible Y.presheaf Y.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sY C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
        Y.toRingedSpace.IsSheaf⟩).obj (CartierDivisor.sheaf E)).obj (CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

variable (f) in
/-- The pairing `E ↦ (z · E)` with a fixed class `z ∈ N₁(Y/X)`, additive on Cartier divisors. -/
private noncomputable def pairing (z : RelativeNumericalCurveClasses sY f) :
    Y.CartierDivisor →+ ℝ :=
  AddMonoidHom.mk' (fun E => RelativeNumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z) fun E E' => by
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sY f z
    simp only [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_apply]
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun C _ => ?_
    rw [degree_cartierSheaf_add]
    push_cast
    ring

private theorem pairing_apply (z : RelativeNumericalCurveClasses sY f) (E : Y.CartierDivisor) :
    pairing f z E = RelativeNumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z := rfl

/-- An `f`-ample Cartier divisor is nonnegative on the closed relative cone of curves. -/
private theorem pairing_nonneg_of_isRelativelyAmple (hY : MMP.Mori.IsVariety k sY)
    {F : Y.CartierDivisor} (hF : IsRelativelyAmple f (MMP.CartierDivisor.sheaf F))
    {z : RelativeNumericalCurveClasses sY f} (hz : z ∈ relativeClosedConeOfCurves sY f) :
    0 ≤ pairing f z F := by
  rw [pairing_apply, intersectionNumber_ofCartier_eq_degree]
  have hS : IsClosed {z : RelativeNumericalCurveClasses sY f |
      0 ≤ RelativeNumericalCurveClasses.degree sY f (MMP.CartierDivisor.sheaf F) z} :=
    isClosed_le continuous_const (RelativeNumericalCurveClasses.continuous_degree sY f _)
  refine closure_minimal (fun w hw => ?_) hS hz
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    show 0 ≤ OneCycle.degree ℝ sY _ (C.cycle ℝ)
    rw [OneCycle.degree_cycle]
    exact_mod_cast (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hY f _ hF C hC).le
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
    exact add_nonneg hx hy
  | smul a x _ hx =>
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [show a • x = (a : ℝ) • x from rfl, map_smul, smul_eq_mul]
    exact mul_nonneg a.2 hx

/-- Cartier divisors separate `N₁(Y/X)` on an integral `Y`. -/
private theorem exists_pairing_ne_zero [IsIntegral Y] {z : RelativeNumericalCurveClasses sY f}
    (hz0 : z ≠ 0) : ∃ E : Y.CartierDivisor, pairing f z E ≠ 0 := by
  by_contra! h
  apply hz0
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sY f z
  refine (Submodule.Quotient.mk_eq_zero _).mpr
    (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have h0 := h E
  simp only [pairing_apply, RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree] at h0
  rw [← h0, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sY C.ι C.dim_le e)

/-- On the class of a contracted proper curve `C`, the pairing with `E` is `deg_C 𝒪_Y(E)`. -/
private theorem pairing_relativeClass {C : ProperCurve sY} (hC : C.IsContractedBy f)
    (E : Y.CartierDivisor) :
    pairing f (C.relativeClass f hC) E = C.degree k (MMP.CartierDivisor.sheaf E) := by
  rw [pairing_apply, intersectionNumber_ofCartier_eq_degree]
  exact OneCycle.degree_cycle ℝ _ C

variable (sY f) in
/-- Linear maps from a coordinate space into `N₁(Y/X)` are continuous for its weak topology. -/
private theorem continuous_linearMap {ι : Type} [Finite ι]
    (g : (ι → ℝ) →ₗ[ℝ] RelativeNumericalCurveClasses sY f) : Continuous g :=
  continuous_iInf_rng.2 fun M => continuous_iInf_rng.2 fun _ => continuous_induced_rng.2 <|
    LinearMap.continuous_of_finiteDimensional ((RelativeNumericalCurveClasses.degree sY f M).comp g)

end Pairing

/-! ### Ample implies positive -/

/-- **Kleiman's argument**: an `f`-ample Cartier divisor is positive on every nonzero class of
the closed relative cone of curves. -/
private theorem pos_of_isRelativelyAmple {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (hX : MMP.Mori.IsVariety k sX)
    (hY : MMP.Mori.IsVariety k sY) (f : Y ⟶ X) [QuasiCompact f] (D : Y.CartierDivisor)
    (hD : IsRelativelyAmple f (MMP.CartierDivisor.sheaf D)) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 →
      0 < RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z := by
  intro z hz hz0
  haveI : IsIntegral Y := (show AlgebraicGeometry.IsVariety k sY from hY).toIsIntegral
  haveI := (show AlgebraicGeometry.IsVariety k sX from hX).toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨E, hE⟩ := exists_pairing_ne_zero hz0
  obtain ⟨n₁, h₁⟩ := MMP.Fourfold.exists_isRelativelyAmple_nsmul_add f hD E
  obtain ⟨n₂, h₂⟩ := MMP.Fourfold.exists_isRelativelyAmple_nsmul_add f hD (-E)
  set n := max n₁ n₂ + 1
  have a := pairing_nonneg_of_isRelativelyAmple hY (h₁ n (by omega)) hz
  have b := pairing_nonneg_of_isRelativelyAmple hY (h₂ n (by omega)) hz
  rw [map_add, map_nsmul, nsmul_eq_mul] at a
  rw [map_add, map_nsmul, nsmul_eq_mul, map_neg] at b
  rw [← pairing_apply]
  have hn : (0 : ℝ) < n := by positivity
  rcases lt_or_gt_of_ne hE with h | h <;> nlinarith

/-! ### Intersection numbers on a closed subscheme -/

section Restrict

open Stacks.SheafOfModules.Invertible

/-- Integer tensor powers depend only on the isomorphism class of the invertible module. -/
private noncomputable def tensorPowerIsoOfIso {X : Scheme.{0}} (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (e : M ≅ N) (m : ℤ) :
    tensorPower X.presheaf X.ringCatSheaf.2 M m ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N m :=
  Stacks.Equivalence.powIntertwineObj
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, 0, 0, 0}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj M).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, 0, 0, 0}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj N).asEquivalence (𝟭 _)
    (fun A => ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, 0, 0, 0}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj A).mapIso e) m
    (SheafOfModules.unit _)

/-- Isomorphic families of invertible modules give isomorphic twists. -/
private noncomputable def twistListFamilyIso {X : Scheme.{0}} {r : ℕ} (L L' : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' i)]
    (e : ∀ i, L i ≅ L' i) (n : Fin r → ℤ) :
    ∀ (l : List (Fin r)) {M M' : X.Modules}, (M ≅ M') →
      (twistList L n l M ≅ twistList L' n l M')
  | [], _, _, ε => ε
  | i :: t, _, _, ε => twistListFamilyIso L L' e n t
      (tensorProductIso X.presheaf X.ringCatSheaf.2 ε
        (tensorPowerIsoOfIso (L i) (L' i) (e i) (n i)))

/-- Intersection numbers along a closed subscheme are computed on it. -/
private theorem intersectionNumber_pullback_comp (k : Type) [Field k] {X W Z : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : W ⟶ X) [IsClosedImmersion i] (j : Z ⟶ W)
    [IsClosedImmersion j] (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    intersectionNumber k (i ≫ f) j d hd (fun q => (Scheme.Modules.pullback i).obj (L q)) =
      intersectionNumber k f (j ≫ i) d hd L := by
  unfold intersectionNumber
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  refine finsum_congr fun n => ?_
  congr 2
  rw [← Category.assoc]
  exact finrank_cohomologyOverField_eq_of_iso k _
    (twistListFamilyIso (fun q => (Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback i).obj (L q)))
      (fun q => (Scheme.Modules.pullback (j ≫ i)).obj (L q))
      (fun q => (Scheme.Modules.pullbackComp j i).app (L q)) _ _ (Iso.refl _)) n

private theorem intersectionNumber_congr_immersion (k : Type) [Field k] {X Z : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {i i' : Z ⟶ X} [IsClosedImmersion i]
    [IsClosedImmersion i'] (h : i = i') (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (L : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    intersectionNumber k f i d hd L = intersectionNumber k f i' d hd L := by
  subst h
  rfl

end Restrict

/-! ### Expanding `(A ⊗ L)^d` -/

/-- The family with `M` in the slots of `S` and `F` elsewhere. -/
private def selFam {X : Scheme.{0}} {d : ℕ} (S : Finset (Fin d)) (M : X.Modules)
    (F : Fin d → X.Modules) : Fin d → X.Modules := fun q => if q ∈ S then M else F q

private theorem selFam_of_mem {X : Scheme.{0}} {d : ℕ} {S : Finset (Fin d)} {M : X.Modules}
    {F : Fin d → X.Modules} {q : Fin d} (h : q ∈ S) : selFam S M F q = M := if_pos h

private theorem selFam_of_notMem {X : Scheme.{0}} {d : ℕ} {S : Finset (Fin d)} {M : X.Modules}
    {F : Fin d → X.Modules} {q : Fin d} (h : q ∉ S) : selFam S M F q = F q := if_neg h

private theorem isInvertible_selFam {X : Scheme.{0}} {d : ℕ} (S : Finset (Fin d)) (M : X.Modules)
    (F : Fin d → X.Modules) [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [hF : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)] (q : Fin d) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (selFam S M F q) := by
  unfold selFam
  split_ifs <;> infer_instance

attribute [local instance] isInvertible_selFam

/-- If `P ≅ A ⊗ L` and every mixed intersection number `(L^{|T|} · A^{d - |T|} · V)` is
nonnegative, then `(A^d · V) ≤ (P^d · V)`: expand `P^d` slot by slot. -/
private theorem intersectionNumber_le_of_iso_tensor (κ : Type) [Field κ] {F V : Scheme.{0}}
    (g : F ⟶ Spec (.of κ)) [IsProper g] (i : V ⟶ F) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim V ≤ d) (A L P : F.Modules)
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 P]
    (e : P ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨F.presheaf, F.IsSheaf⟩).obj A).obj L)
    (hmix : ∀ T : Finset (Fin d),
      0 ≤ intersectionNumber κ g i d hd (selFam T L fun _ => A)) :
    intersectionNumber κ g i d hd (fun _ => A) ≤ intersectionNumber κ g i d hd (fun _ => P) := by
  classical
  have key : ∀ S T : Finset (Fin d), Disjoint S T →
      intersectionNumber κ g i d hd (selFam T L fun _ => A) ≤
        intersectionNumber κ g i d hd (selFam S P (selFam T L fun _ => A)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro T _
      exact le_of_eq (intersectionNumber_congr_family κ g i d hd (funext fun q =>
        (selFam_of_notMem (Finset.notMem_empty q)).symm))
    | insert a s ha ih =>
      intro T hdisj
      have haT : a ∉ T := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a s)
      have hs : Disjoint s T := Finset.disjoint_of_subset_left (Finset.subset_insert a s) hdisj
      have hs' : Disjoint s (insert a T) := Finset.disjoint_insert_right.mpr ⟨ha, hs⟩
      have h := intersectionNumber_tensor κ g i d hd a
        (selFam (insert a s) P (selFam T L fun _ => A))
        (selFam s P (selFam T L fun _ => A))
        (selFam s P (selFam (insert a T) L fun _ => A))
        (fun q hq => by simp [selFam, Finset.mem_insert, hq])
        (fun q hq => by simp [selFam, Finset.mem_insert, hq])
        (eqToIso (by simp [selFam]) ≪≫ e ≪≫ eqToIso (by simp [selFam, ha, haT] <;> rfl))
      rw [h]
      linarith [ih T hs, ih (insert a T) hs', hmix (insert a T)]
  refine le_of_eq_of_le (intersectionNumber_congr_family κ g i d hd (funext fun q => ?_))
    ((key Finset.univ ∅ (Finset.disjoint_empty_right _)).trans_eq
      (intersectionNumber_congr_family κ g i d hd (funext fun q => ?_)))
  · exact (selFam_of_notMem (M := L) (F := fun _ => A) (Finset.notMem_empty q)).symm
  · exact selFam_of_mem (Finset.mem_univ q)

/-! ### Ample plus nef is ample on a projective scheme over a field -/

private theorem isProjective_comp {X Z S : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (hf : IsProjective f) : IsProjective (i ≫ f) := by
  obtain ⟨E, h1, h2, hqc, i', hi', hcomp⟩ := hf
  exact ⟨E, h1, h2, hqc, i ≫ i', inferInstance, by rw [Category.assoc, hcomp]⟩

/-- Nefness restricts to closed subschemes. -/
private theorem isNef_pullback (κ : Type) [Field κ] {F W : Scheme.{0}} (g : F ⟶ Spec (.of κ))
    (iW : W ⟶ F) [IsClosedImmersion iW] (L : F.Modules)
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L] (hL : IsNef κ g L) :
    IsNef κ (iW ≫ g) ((Scheme.Modules.pullback iW).obj L) := by
  intro C c _ _ _ hC
  haveI : IsProper ((c ≫ iW) ≫ g) := by
    rw [Category.assoc]
    infer_instance
  rw [degreeOn_pullback_eq_degreeOn_comp (iW ≫ g) g iW c rfl hC.le L]
  exact hL C (c ≫ iW) hC

/-- **Kleiman's theorem on closed subschemes.** On a projective `κ`-scheme a nef invertible sheaf
has nonnegative degree `(L^j · W)` on every integral closed subscheme `W` of dimension `j`. -/
private theorem intersectionNumber_nonneg_of_isNef (κ : Type) [Field κ] {F : Scheme.{0}}
    (g : F ⟶ Spec (.of κ)) (hg : IsProjective g) (L : F.Modules)
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L] (hL : IsNef κ g L)
    (W : Scheme.{0}) (iW : W ⟶ F) [IsClosedImmersion iW] [IsIntegral W] (j : ℕ)
    (hW : topologicalKrullDim W = j) :
    haveI := hg.isProper
    0 ≤ intersectionNumber κ g iW j hW.le (fun _ => L) := by
  haveI := hg.isProper
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact (intersectionNumber_pos_of_topologicalKrullDim_eq_zero κ g iW hW _).le
  have hproj : MMP.Mori.IsProjectiveVariety κ (iW ≫ g) := by
    refine (MMP.Mori.isProjectiveVariety_iff κ _).2 ⟨(MMP.Mori.isVariety_iff κ _).2
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, ?_⟩
    exact isProjectiveMorphism_of_isProjective_of_isAffine _ (isProjective_comp iW g hg)
  have h := MMP.Mori.sheafSelfIntersectionNumber_nonneg_of_isNef κ (iW ≫ g) hproj
    ((Scheme.Modules.pullback iW).obj L) (isNef_pullback κ g iW L hL) W (𝟙 W) hW
  unfold sheafSelfIntersectionNumber at h
  rwa [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_pullback_comp κ g iW (𝟙 W),
    intersectionNumber_congr_immersion κ g (Category.id_comp iW)] at h

/-- **Ample plus nef is ample.** On a projective scheme `F` over a field `κ`, if `A` is ample and
`L` is nef, then every `P ≅ A ⊗ L` is ample: by the Nakai criterion, since
`(P^d · V) ≥ (A^d · V) > 0` for every integral closed subscheme `V` of dimension `d > 0`. -/
private theorem isAmple_of_iso_tensor (κ : Type) [Field κ] {F : Scheme.{0}}
    (g : F ⟶ Spec (.of κ)) (hg : IsProjective g) (A L P : F.Modules) [IsInvertibleModule F A]
    [IsInvertibleModule F L] [IsInvertibleModule F P] (hA : IsAmple F A) (hL : IsNef κ g L)
    (e : P ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨F.presheaf, F.IsSheaf⟩).obj A).obj L) :
    IsAmple F P := by
  haveI := hg.isProper
  refine isAmple_of_sheafSelfIntersectionNumber_pos_of_dim_pos κ g hg P
    fun V i _ _ d hd hd0 => ?_
  have hpos := MMP.Threefold.Mori.sheafSelfIntersectionNumber_pos_of_isAmple κ g A hA V i d hd
  unfold sheafSelfIntersectionNumber at hpos ⊢
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber] at hpos ⊢
  refine hpos.trans_le (intersectionNumber_le_of_iso_tensor κ g i d _ A L P e fun T => ?_)
  classical
  refine MMP.Threefold.Mori.intersectionNumber_nonneg_of_isAmple κ g L A hA T.card
    (fun W iW _ _ hW => intersectionNumber_nonneg_of_isNef κ g hg L hL W iW T.card hW) i d _
    (selFam T L fun _ => A) (Finset.univ \ T) (fun q hq => ?_) (fun q hq => ?_) ?_
  · exact selFam_of_notMem (Finset.mem_sdiff.1 hq).2
  · exact selFam_of_mem (by simpa using hq)
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin]
    have := T.card_le_univ
    rw [Fintype.card_fin] at this
    omega

/-! ### Curves in a closed fibre -/

/-- The kernel of a closed immersion from a reduced scheme is the vanishing ideal of its range. -/
private theorem ker_eq_vanishingIdeal_of_isReduced {Y W : Scheme.{0}} (ι : Y ⟶ W)
    [IsClosedImmersion ι] [IsReduced Y] (T : TopologicalSpace.Closeds W)
    (hT : (T : Set W) = Set.range ι) :
    ι.ker = Scheme.IdealSheafData.vanishingIdeal T := by
  have hrad : ι.ker.radical = ι.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
    rw [RingHom.mem_ker, map_pow] at hn
    rw [RingHom.mem_ker]
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  have : ι.ker.support = T := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq, hT]
  rw [← this, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- A closed immersion from an integral scheme is, up to isomorphism, the closed immersion of the
closure of the image of the generic point. -/
private theorem exists_iso_curveSubschemeAt {Y W : Scheme.{0}} [IsIntegral Y] (ι : Y ⟶ W)
    [IsClosedImmersion ι] :
    ∃ e : Y ≅ curveSubschemeAt (ι (genericPoint Y)), e.hom ≫ curveSubschemeAtι _ = ι := by
  have hrange : Set.range ι = closure {ι (genericPoint Y)} := by
    rw [← Set.image_singleton, ι.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec Y).def]
    simp
  have hker : ι.ker = (curveSubschemeAtι (ι (genericPoint Y))).ker := by
    rw [ker_eq_vanishingIdeal_of_isReduced ι (TopologicalSpace.Closeds.closure
      {ι (genericPoint Y)}) hrange.symm]
    unfold curveSubschemeAtι
    rw [Scheme.IdealSheafData.ker_subschemeι]
  have hf : IsIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq ι (curveSubschemeAtι _) _
      (IsClosedImmersion.lift_fac _ _ _) hker
  exact ⟨asIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- An integral curve `c : C ⟶ Y` closed in `Y` and proper over `k`, whose image is contained in
the fibre `f⁻¹(y)`, has nonnegative degree against `L` if every contracted proper curve does. -/
private theorem degreeOn_nonneg_of_range_subset {k : Type} [Field k] {X Y C : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hL : ∀ C₀ : ProperCurve sY, C₀.IsContractedBy f → 0 ≤ C₀.degree k L) (y : X)
    (c : C ⟶ Y) [IsClosedImmersion c] [IsIntegral C] [IsProper (c ≫ sY)]
    (hC : topologicalKrullDim C = 1) (hc : Set.range c ⊆ f ⁻¹' {y}) :
    0 ≤ degreeOn k sY c hC.le L := by
  obtain ⟨e, he⟩ := exists_iso_curveSubschemeAt c
  have hι : curveSubschemeAtι (c (genericPoint C)) = e.inv ≫ c := (Iso.eq_inv_comp e).mpr he
  have hdim : topologicalKrullDim (curveSubschemeAt (c (genericPoint C))) = 1 := by
    rw [← hC]
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.inv.homeomorph.isHomeomorph)
  have hprop : IsProper (curveSubschemeAtι (c (genericPoint C)) ≫ sY) := by
    rw [hι, Category.assoc]
    infer_instance
  let C₀ : ProperCurve sY := ⟨c (genericPoint C), ⟨hdim, hprop⟩⟩
  have hcontr : C₀.IsContractedBy f := by
    intro x hx
    have hx' : x ∈ Set.range c := by
      rw [← range_curveSubschemeAtι] at hx
      obtain ⟨z, rfl⟩ := hx
      exact ⟨e.inv z, by rw [hι]; rfl⟩
    rw [hc hx', hc ⟨genericPoint C, rfl⟩]
  have h := hL C₀ hcontr
  unfold ProperCurve.degree at h
  rwa [← MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sY c C₀.ι hC.le C₀.dim_le e he] at h

/-- The fibre of `f` over a closed point `y` of a scheme of finite type over an algebraically
closed field `k`: its closed immersion into `Y` and the comparison of its structure morphism over
`κ(y) ≅ k` with that of `Y`. -/
private theorem fiber_facts {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    (hfs : f ≫ sX = sY) (y : X) (hy : IsClosed {y}) :
    IsClosedImmersion (f.fiberι y) ∧
      ∃ φ : CommRingCat.of k ⟶ X.residueField y, IsIso φ ∧
        f.fiberToSpecResidueField y ≫ Spec.map φ = f.fiberι y ≫ sY := by
  haveI : IsClosedImmersion (X.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have hpb := IsPullback.of_hasPullback f (X.fromSpecResidueField y)
  refine ⟨MorphismProperty.of_isPullback hpb.flip ‹_›,
    Spec.preimage (X.fromSpecResidueField y ≫ sX), (residueFieldIsoBase sX y hy).isIso_inv, ?_⟩
  rw [Spec.map_preimage, ← hfs, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ sX) hpb.w.symm

/-- **Nefness on a closed fibre.** If every proper curve of `Y` contracted by `f` has nonnegative
degree against `L`, then `L` restricts to a nef sheaf on the fibre over every closed point. -/
private theorem isNef_fiber {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    (hfs : f ≫ sX = sY) (L : Y.Modules) [IsInvertibleModule Y L]
    (hL : ∀ C₀ : ProperCurve sY, C₀.IsContractedBy f → 0 ≤ C₀.degree k L) (y : X)
    (hy : IsClosed {y}) :
    IsNef (X.residueField y) (f.fiberToSpecResidueField y)
      (Stacks.AmpleLocallyClosed.pullbackModule (f.fiberι y) L) := by
  obtain ⟨hι, φ, hφi, hsq⟩ := fiber_facts sX sY f hfs y hy
  have hφ : Function.Bijective φ := (ConcreteCategory.isIso_iff_bijective φ).mp hφi
  intro C c _ _ _ hC
  haveI : IsProper ((c ≫ f.fiberToSpecResidueField y) ≫ Spec.map φ) := inferInstance
  haveI : IsProper ((c ≫ f.fiberι y) ≫ sY) := by
    rw [Category.assoc, ← hsq, ← Category.assoc]
    infer_instance
  rw [degreeOn_eq_of_iso _ _ c hC.le (modulePullbackIso (f.fiberι y) L),
    degreeOn_eq_invertibleCurveDegree,
    ← MMP.Threefold.Resolution.invertibleCurveDegree_comp_specMap (X.residueField y) _ φ hφ,
    invertibleCurveDegree_eq_of_iso k _ hC.le
      (L' := (Scheme.Modules.pullback (c ≫ f.fiberι y)).obj L)
      (show (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback (f.fiberι y)).obj L) ≅
        (Scheme.Modules.pullback (c ≫ f.fiberι y)).obj L from
        (Scheme.Modules.pullbackComp c (f.fiberι y)).app L),
    invertibleCurveDegree_congr_structure (show (c ≫ f.fiberToSpecResidueField y) ≫ Spec.map φ =
      (c ≫ f.fiberι y) ≫ sY by rw [Category.assoc, hsq, Category.assoc])]
  refine degreeOn_nonneg_of_range_subset sY f L hL y (c ≫ f.fiberι y) hC ?_
  rintro _ ⟨z, rfl⟩
  rw [← Scheme.Hom.range_fiberι f y]
  exact ⟨c z, rfl⟩

/-- A relatively ample sheaf restricts to an ample sheaf on a fibre which is closed in the
source. -/
private theorem isAmple_fiber_of_isRelativelyAmple {X Y : Scheme.{0}} (f : Y ⟶ X)
    (A : Y.Modules) [IsInvertibleModule Y A] (hA : Stacks.RelativeAmple.IsRelativelyAmple f A)
    (y : X) [IsClosedImmersion (f.fiberι y)] :
    IsAmple (f.fiber y) (Stacks.AmpleLocallyClosed.pullbackModule (f.fiberι y) A) := by
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  have hrange : Set.range (f.fiberι y) ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    rw [Scheme.Hom.range_fiberι, Scheme.Opens.range_ι]
    rintro x rfl
    exact hyV
  set j := IsOpenImmersion.lift (f ⁻¹ᵁ V).ι (f.fiberι y) hrange
  have hj : j ≫ (f ⁻¹ᵁ V).ι = f.fiberι y := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (j ≫ (f ⁻¹ᵁ V).ι) := by rw [hj]; infer_instance
  haveI : IsClosedImmersion j := IsClosedImmersion.of_comp j (f ⁻¹ᵁ V).ι
  have h := Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding j _
    (hA.2 V hV) (Or.inl ⟨inferInstance, inferInstance⟩)
  exact (isAmple_congr _ _ (modulePullbackIso j _ ≪≫
    (Scheme.Modules.pullback j).mapIso (modulePullbackIso _ A) ≪≫
    (Scheme.Modules.pullbackComp j (f ⁻¹ᵁ V).ι).app A ≪≫ (Scheme.Modules.pullbackCongr hj).app A ≪≫
    (modulePullbackIso (f.fiberι y) A).symm)).mp h

/-- **Ampleness on a closed fibre.** If `A` is `f`-ample and `L` has nonnegative degree on every
contracted proper curve, then `A + L` is ample on the fibre of `f` over every closed point. -/
private theorem isAmple_fiber_add {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    (hf : IsProjective f) (hfs : f ≫ sX = sY) (A L : Y.CartierDivisor)
    (hA : Stacks.RelativeAmple.IsRelativelyAmple f (MMP.CartierDivisor.sheaf A))
    (hL : ∀ C₀ : ProperCurve sY, C₀.IsContractedBy f → 0 ≤ C₀.degree k (MMP.CartierDivisor.sheaf L))
    {P : Y.CartierDivisor} (hP : A + L = P) (y : X) (hy : IsClosed {y}) :
    IsAmple (f.fiber y)
      (Stacks.AmpleLocallyClosed.pullbackModule (f.fiberι y) (MMP.CartierDivisor.sheaf P)) := by
  subst hP
  obtain ⟨hι, -⟩ := fiber_facts sX sY f hfs y hy
  have hg : IsProjective (f.fiberToSpecResidueField y) :=
    IsProjective.of_isPullback (IsPullback.of_hasPullback f (X.fromSpecResidueField y)).flip hf
  refine isAmple_of_iso_tensor (X.residueField y) (f.fiberToSpecResidueField y) hg _ _ _
    (isAmple_fiber_of_isRelativelyAmple f _ hA y) (isNef_fiber sX sY f hfs _ hL y hy) ?_
  exact (modulePullback (f.fiberι y).toLRSHom.toShHom).mapIso
      (MMP.CartierDivisorSheaf.sheafMulIso A L).symm ≪≫
    pullbackTensorModulesIso (f.fiberι y) (MMP.CartierDivisor.sheaf A) (MMP.CartierDivisor.sheaf L)

/-- **Ampleness spreads from the closed fibres.** For a proper morphism to a scheme of finite type
over a field, an invertible sheaf ample on every closed fibre is relatively ample. -/
private theorem isRelativelyAmple_of_isAmple_fiber {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f] (P : Y.Modules)
    [IsInvertibleModule Y P]
    (h : ∀ y : X, IsClosed {y} →
      IsAmple (f.fiber y) (Stacks.AmpleLocallyClosed.pullbackModule (f.fiberι y) P)) :
    Stacks.RelativeAmple.IsRelativelyAmple f P := by
  choose V hyV hV using fun y : {y : X // IsClosed {y}} =>
    Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre f P y.1 (h y.1 y.2)
  have htop : (⨆ y, V y) = ⊤ := MMP.Resolution.Bridges.eq_top_of_closedPoints_subset sX _
    fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyV _⟩
  refine Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_of_forall_exists_isRelativelyAmple f P
    inferInstance fun x => ?_
  have hx : x ∈ ⨆ y, V y := htop ▸ trivial
  obtain ⟨y, hy⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨V y, hy, hV y⟩

private theorem eq_norm_mul_apply_inv_norm_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (e : V ≃ₗ[ℝ] (Fin n → ℝ)) (χ : V →ₗ[ℝ] ℝ) (z : V) :
    χ z = ‖e z‖ * χ (e.symm (‖e z‖⁻¹ • e z)) := by
  rcases eq_or_ne (e z) 0 with h0 | h0
  · obtain rfl : z = 0 := by simpa using h0
    simp
  rw [map_smul, LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_mul]

private theorem inv_norm_smul_mem_preimage_inter_sphere {V : Type*} [AddCommGroup V]
    [Module ℝ V] {n : ℕ} (e : V ≃ₗ[ℝ] (Fin n → ℝ)) {K : Set V}
    (hcone : ∀ z ∈ K, ∀ t : ℝ, 0 < t → t • z ∈ K) {z : V} (hz : z ∈ K) (hz0 : z ≠ 0) :
    ‖e z‖⁻¹ • e z ∈ e.symm ⁻¹' K ∩ Metric.sphere 0 1 := by
  have hez : e z ≠ 0 := by simpa using hz0
  refine ⟨?_, by simp [norm_smul, norm_ne_zero_iff.2 hez]⟩
  change e.symm (‖e z‖⁻¹ • e z) ∈ K
  rw [map_smul, LinearEquiv.symm_apply_apply]
  exact hcone z hz _ (inv_pos.2 (norm_pos_iff.2 hez))

/-- **A positive form dominates every form on a closed cone.** In a finite-dimensional real vector
space whose topology makes the linear maps from `ℝⁿ` continuous, if `φ` is positive on the nonzero
vectors of a closed cone `K`, then every linear form `ψ` satisfies `ψ ≤ m φ` on `K` for some
positive integer `m`. -/
private theorem exists_nat_le_mul_of_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace V]
    (hcont : ∀ g : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] V, Continuous g) {K : Set V}
    (hK : IsClosed K) (hcone : ∀ z ∈ K, ∀ t : ℝ, 0 < t → t • z ∈ K) (φ ψ : V →ₗ[ℝ] ℝ)
    (hφ : ∀ z ∈ K, z ≠ 0 → 0 < φ z) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ K, ψ z ≤ m * φ z := by
  let e := (Module.finBasis ℝ V).equivFun
  set K' : Set (Fin (Module.finrank ℝ V) → ℝ) := e.symm ⁻¹' K
  have hK' : IsClosed K' := hK.preimage (hcont e.symm.toLinearMap)
  let φ' := φ.comp e.symm.toLinearMap
  let ψ' := ψ.comp e.symm.toLinearMap
  have hunit : ∀ z ∈ K, z ≠ 0 → ‖e z‖⁻¹ • e z ∈ K' ∩ Metric.sphere 0 1 :=
    fun _ => inv_norm_smul_mem_preimage_inter_sphere e hcone
  by_cases hS : (K' ∩ Metric.sphere (0 : Fin (Module.finrank ℝ V) → ℝ) 1).Nonempty
  swap
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    by_cases hz0 : z = 0
    · simp [hz0]
    · exact absurd ⟨_, hunit z hz hz0⟩ hS
  have hφc : Continuous φ' := LinearMap.continuous_of_finiteDimensional φ'
  obtain ⟨w0, hw0, hmin⟩ :=
    ((isCompact_sphere (0 : Fin (Module.finrank ℝ V) → ℝ) 1).inter_left hK').exists_isMinOn hS
      hφc.continuousOn
  have hw00 : e.symm w0 ≠ 0 := by
    intro h
    obtain rfl : w0 = 0 := by simpa using h
    simp at hw0
  have hc : 0 < φ' w0 := hφ _ hw0.1 hw00
  set C := ‖LinearMap.toContinuousLinearMap ψ'‖
  obtain ⟨m, hm⟩ := exists_nat_gt (C / φ' w0)
  refine ⟨m + 1, by omega, fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · simp [hz0]
  have hu := hunit z hz hz0
  set u := ‖e z‖⁻¹ • e z
  have hnu : ‖u‖ = 1 := by simpa using hu.2
  have h1 : φ' w0 ≤ φ' u := hmin hu
  have h2 : ψ' u ≤ C := by
    have := (LinearMap.toContinuousLinearMap ψ').le_opNorm u
    rw [hnu, mul_one] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  have h3 : C ≤ m * φ' w0 := ((div_lt_iff₀ hc).1 hm).le
  rw [eq_norm_mul_apply_inv_norm_smul e ψ z, eq_norm_mul_apply_inv_norm_smul e φ z]
  calc ‖e z‖ * ψ (e.symm u) = ‖e z‖ * ψ' u := rfl
    _ ≤ ‖e z‖ * ((m + 1 : ℕ) * φ' u) :=
      mul_le_mul_of_nonneg_left (by push_cast; nlinarith) (norm_nonneg _)
    _ = ((m + 1 : ℕ) : ℝ) * (‖e z‖ * φ (e.symm u)) := by
      show ‖e z‖ * ((m + 1 : ℕ) * φ (e.symm u)) = _
      ring

end MMP.FourfoldProofs.MmpFoundationRelativeCartierKleimanCharZeroProof

end

section

/-!
# The relative Kleiman criterion for Cartier divisors in characteristic zero

Let `k` be an algebraically closed field of characteristic zero, `f : Y ⟶ X` a projective
morphism of `k`-varieties and `D` a Cartier divisor on `Y`. Write `N₁(Y/X)` for the real
1-cycles supported on curves contracted by `f` modulo numerical equivalence, and `NE̅(Y/X)` for
the closure of the convex cone spanned by the classes of contracted curves. Then `D` is
`f`-ample if and only if `(z · D) > 0` for every nonzero `z ∈ NE̅(Y/X)`. Neither `Y` nor `X`
needs to be proper over `k`.

## Main results

* `MMP.Mori.isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos`: the
  relative Kleiman criterion.

## Implementation notes

`f`-ampleness of `D` is `MMP.Mori.IsRelativelyAmple` of its invertible sheaf `𝒪_Y(D)`;
`N₁(Y/X)` is `MMP.Mori.RelativeNumericalCurveClasses`, `NE̅(Y/X)` is
`MMP.Mori.relativeClosedConeOfCurves` (the closure for the coarsest topology making every
degree form continuous, which on the finite-dimensional `N₁(Y/X)` is the Euclidean one), and
`D(z)` is `MMP.Mori.RelativeNumericalCurveClasses.intersectionNumber` of the `ℝ`-Cartier
divisor `1 · D`. Projectivity of `f` is `AlgebraicGeometry.IsProjective` (a closed immersion over
`X` into the projective bundle of a finite-type quasi-coherent module), and `f` is a morphism
over `k`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.44
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.FourfoldProofs.MmpFoundationRelativeCartierKleimanCharZeroProof RingedSpaceModuleAdjunction
  Stacks.Ample Stacks.RelativeVeryAmple in
/-- **Relative Kleiman criterion.** Let `k` be algebraically closed of characteristic zero,
`f : Y ⟶ X` a projective morphism of `k`-varieties and `D` a Cartier divisor on `Y`. Then `D` is
`f`-ample if and only if `(z · D) > 0` for every nonzero class `z` of the closed relative cone of
curves `NE̅(Y/X) ⊆ N₁(Y/X)`. -/
@[mmp "lem_mmp_foundation_relative_cartier_kleiman_char_zero"]
public theorem isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]
    (f : Y ⟶ X) (hf : IsProjective f) (hfs : f ≫ sX = sY) (D : Y.CartierDivisor) :
    IsRelativelyAmple f (MMP.CartierDivisor.sheaf D) ↔
      ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 →
        0 < RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z := by
  haveI : IsProper f := hf.isProper
  refine ⟨pos_of_isRelativelyAmple sX sY ‹_› ‹_› f D, fun hpos => ?_⟩
  haveI := (show AlgebraicGeometry.IsVariety k sX from ‹_›).toLocallyOfFiniteType
  haveI : IsIntegral Y := (show AlgebraicGeometry.IsVariety k sY from ‹_›).toIsIntegral
  obtain ⟨⟨L, hLinv, hLamp, hLA⟩, -⟩ := MMP.Foundations.IsProjective.exists_isRelativelyAmple hf
  obtain ⟨A, ⟨eA⟩⟩ := hLA inferInstance
  have hA : Stacks.RelativeAmple.IsRelativelyAmple f (MMP.CartierDivisor.sheaf A) :=
    (isRelativelyAmple_congr _ _ _ eA).mpr hLamp
  haveI := (RelativeNumericalCurveClasses.exists_linearEquiv_dual_of_isProper sY sX f hfs).1
  obtain ⟨m, hm, hbound⟩ := exists_nat_le_mul_of_pos (continuous_linearMap sY f)
    (isClosed_closure : IsClosed (closure (relativeConeOfCurves sY f :
      Set (RelativeNumericalCurveClasses sY f))))
    (fun z hz t ht => (relativeClosedConeOfCurves sY f).smul_mem ht.le hz)
    (RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D))
    (RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ A)) hpos
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hL : ∀ C₀ : ProperCurve sY, C₀.IsContractedBy f →
      0 ≤ C₀.degree k (MMP.CartierDivisor.sheaf ((n + 1) • D + -A)) := by
    intro C₀ hC₀
    have h := hbound _ (subset_closure (relativeClass_mem_relativeConeOfCurves hC₀))
    rw [← pairing_apply, ← pairing_apply] at h
    have h' := pairing_relativeClass hC₀ ((n + 1) • D + -A)
    rw [map_add, map_nsmul, map_neg, nsmul_eq_mul] at h'
    have : (0 : ℝ) ≤ (C₀.degree k (CartierDivisor.sheaf ((n + 1) • D + -A)) : ℝ) := by
      rw [← h']
      linarith
    exact_mod_cast this
  have hrel := isRelativelyAmple_of_isAmple_fiber sX f (MMP.CartierDivisor.sheaf ((n + 1) • D))
    fun y hy => isAmple_fiber_add sX sY f hf hfs A _ hA hL (P := (n + 1) • D) (by abel) y hy
  exact IsRelativelyAmple.of_stacks _ _
    ((Stacks.Tag01VUReduction.isRelativelyAmple_iff_isRelativelyAmple_tensorPowModule f _ (n + 1)
      (by omega)).mpr ((isRelativelyAmple_congr _ _ _ (succNsmulIso D n)).mp hrel))

end MMP.Mori

end
