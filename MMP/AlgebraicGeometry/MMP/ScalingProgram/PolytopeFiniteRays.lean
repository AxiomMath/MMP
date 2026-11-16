module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.KltConeDatum
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.AbstractConeTheorem
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.ConeDatumBasis
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.AmpleStrictlyPositive
public import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

/-!
# Finitely many candidate rays for a fixed boundary polytope

Let `f : X ⟶ Z` be a morphism of projective varieties over an algebraically closed field of
characteristic zero, with `X` normal and `ℚ`-factorial, let `A` be an `f`-ample `ℚ`-divisor and
let `B₁, …, B_s` be boundaries such that every `(X, Bⱼ)` is klt. There is a finite set of nonzero
classes `ξ` of `NE̅(X/Z)`, lying in the numerical curve lattice of `X` and each spanning an
extremal ray of `NE̅(X/Z)`, such that for every `B` in the convex hull of the `Bⱼ` every
`(K_X + A + B)`-negative extremal ray of `NE̅(X/Z)` is one of the rays `ℝ_{≥0} ξ`.

## Main results

* `MMP.Fourfold.exists_finset_isExtremalRay_of_isKltPair`: the statement above.

## Implementation notes

A point of the polytope is `B = ∑ⱼ tⱼ Bⱼ` with real weights `tⱼ ≥ 0`, `∑ⱼ tⱼ = 1`, and the
degree of `K_X + A + B` on a class `u ∈ N₁(X/Z)` is `∑ⱼ tⱼ ((K_X + A + Bⱼ) · u)`, the degree of
each `ℚ`-Cartier `ℚ`-divisor `K_X + A + Bⱼ` being `MMP.Fourfold.QDivisor.curveForm` evaluated at
the image of `u` under the natural map `N₁(X/Z) → N₁(X)` (`MMP.Mori.relativeToAbsolute`). Real
weights cover the rational points of the polytope and the real ones alike. A class of `N₁(X/Z)`
lies in the lattice if its image in `N₁(X)` lies in `MMP.Mori.numericalCurveLattice`; the natural
map is injective, so this is the lattice of `X` restricted to `N₁(X/Z)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.7 and 3.25
-/

@[expose] public section

section

/-!
## Proof: Finitely many candidate rays for a fixed boundary polytope

Let `f : X ⟶ Z` be a morphism of projective varieties over an algebraically closed field of
characteristic zero, `X` normal and `ℚ`-factorial, `A` an `f`-ample `ℚ`-Cartier divisor and
`B₁, …, B_s` boundaries with every `(X, Bⱼ)` klt. Finitely many nonzero lattice classes of
`NE̅(X/Z)`, each spanning an extremal ray, account for every `(K_X + A + B)`-negative extremal
ray of `NE̅(X/Z)`, for `B` in the convex hull of the `Bⱼ`.

The proof twists `A` by a large multiple of the pull-back of an ample divisor on `Z` to an ample
form `A'` agreeing with `A` on relative classes, applies the abstract cone theorem to the cone
datum of each non-nef `K_X + Bⱼ` with the positive form `A'`, and collects the finitely many
lattice generators of the `(K_X + Bⱼ + A')`-negative rays.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.7 and 3.25
-/

open AlgebraicGeometry CategoryTheory TensorProduct

namespace MMP.FourfoldProofs.FourfoldFixedModelFiniteRaysProof

open MMP.Mori MMP.Positivity

section Convex

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Two rays sharing a nonzero point coincide. -/
private theorem ray_eq_of_mem {v w y : V} (hy : y ≠ 0)
    (hv : y ∈ {u | ∃ c : ℝ, 0 ≤ c ∧ c • v = u}) (hw : y ∈ {u | ∃ c : ℝ, 0 ≤ c ∧ c • w = u}) :
    {u | ∃ c : ℝ, 0 ≤ c ∧ c • v = u} = {u | ∃ c : ℝ, 0 ≤ c ∧ c • w = u} := by
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb, hab⟩ := hw
  have ha0 : 0 < a := lt_of_le_of_ne ha fun h => hy (by rw [← h, zero_smul])
  have hb0 : 0 < b := lt_of_le_of_ne hb fun h => hy (by rw [← hab, ← h, zero_smul])
  rw [← setOf_exists_smul_smul_eq_of_pos ha0 v, ← hab,
    setOf_exists_smul_smul_eq_of_pos hb0 w]

/-- The image of a ray under a linear map is the ray of the image. -/
private theorem image_ray {W : Type*} [AddCommGroup W] [Module ℝ W] (g : V →ₗ[ℝ] W) (v : V) :
    g '' {u | ∃ c : ℝ, 0 ≤ c ∧ c • v = u} = {u | ∃ c : ℝ, 0 ≤ c ∧ c • g v = u} := by
  ext u
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, (map_smul g c v).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c • v, ⟨c, hc, rfl⟩, map_smul g c v⟩

/-- If a finite sum of points of a pointed cone `C` lies in an extremal face `F` of `C`, so does
every summand. -/
private theorem mem_of_sum_mem {C : PointedCone ℝ V} {F : Set V}
    (hF : IsExtremalFace ℝ (C : Set V) F) {α : Type*} (s : Finset α) (x : α → V)
    (hx : ∀ a ∈ s, x a ∈ C) (hs : ∑ a ∈ s, x a ∈ F) : ∀ a ∈ s, x a ∈ F := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.sum_insert hb] at hs
    have hsC : ∑ a ∈ s, x a ∈ C := C.sum_mem fun a ha => hx a (Finset.mem_insert_of_mem ha)
    obtain ⟨h1, h2⟩ := hF.2.2.2 _ (hx b (Finset.mem_insert_self b s)) _ hsC hs
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact h1
    · exact ih (fun a ha => hx a (Finset.mem_insert_of_mem ha)) h2 a ha

end Convex

section Vertex

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Λ : AddSubgroup V}
  [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

/-- **Finitely many negative rays of a cone datum.** Let `C ⊆ V` be a pointed cone, `Λ ⊆ V` a
lattice with `ℝ ⊗ Λ ≅ V` through the inclusion, `D` a cone datum on `Λ` whose cone is the preimage
of `C` and whose form is `K`, and `G` a form positive on `C ∖ {0}`. Then finitely many points of
`Λ` generate every extremal ray of `C` on which `K + G` is negative. -/
private theorem exists_finset_of_coneDatum {C : PointedCone ℝ V}
    (hφ : Function.Bijective (LinearMap.liftBaseChange ℝ Λ.subtype.toIntLinearMap :
      ℝ ⊗[ℤ] Λ →ₗ[ℝ] V))
    (D : ConeDatum Λ)
    (hD : (D.cone : Set (ℝ ⊗[ℤ] Λ)) =
      LinearMap.liftBaseChange ℝ Λ.subtype.toIntLinearMap ⁻¹' (C : Set V))
    (K : V →ₗ[ℝ] ℝ) (hK : ∀ z : Λ, ((D.form z : ℚ) : ℝ) = K z)
    (G : V →ₗ[ℝ] ℝ) (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) :
    ∃ T : Finset V, (∀ w ∈ T, w ∈ Λ) ∧
      ∀ R : Set V, IsExtremalRay ℝ (C : Set V) R → (∀ u ∈ R, u ≠ 0 → K u + G u < 0) →
        ∃ w ∈ T, R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • w = u} := by
  classical
  set φ : ℝ ⊗[ℤ] Λ →ₗ[ℝ] V := LinearMap.liftBaseChange ℝ Λ.subtype.toIntLinearMap with hφdef
  have hφt : ∀ (r : ℝ) (z : Λ), φ (r ⊗ₜ z) = r • (z : V) := fun r z => by
    simp [hφdef]
  have hDC : ∀ {z}, z ∈ D.cone → φ z ∈ C := fun {z} hz => (Set.ext_iff.mp hD z).mp hz
  -- the form of the datum is `K ∘ φ`
  have hKφ : ∀ x, realOfRatForm Λ D.form x = K (φ x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r z => rw [realOfRatForm_tmul, hφt, map_smul, smul_eq_mul, hK]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  obtain ⟨S, hS, hcone⟩ := ConeDatum.cone_eq_nonneg_add_sum_rays D
    (G := G ∘ₗ φ) (fun z hz hz0 => hG _ (hDC hz) fun h => hz0 (hφ.1 (h.trans (map_zero φ).symm)))
    one_pos
  have hSmem : ∀ R ∈ S, R ∈ D.negativeRationalRays := fun R hR =>
    (Set.ext_iff.mp hS R |>.mp hR).1
  choose ξ hξ using fun R (hR : R ∈ S) =>
    (ConeDatum.exists_integral_generator D (hSmem R hR)).imp fun _ h => h.2
  refine ⟨S.attach.image fun R => ((ξ R.1 R.2 : Λ) : V), ?_, ?_⟩
  · intro w hw
    obtain ⟨R, -, rfl⟩ := Finset.mem_image.mp hw
    exact (ξ R.1 R.2).2
  intro R hR hneg
  obtain ⟨hRface, v, hv0, hRv⟩ := hR
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul ℝ v⟩
  obtain ⟨x, rfl⟩ := hφ.2 v
  have hxD : x ∈ (D.cone : Set (ℝ ⊗[ℤ] Λ)) := (Set.ext_iff.mp hD x).mpr (hRface.1 hvR)
  rw [hcone] at hxD
  obtain ⟨c, hc, hc0, r, hr, hx⟩ := hxD
  -- every summand lies in `C`
  have hrC : ∀ R' ∈ S, φ (r R') ∈ C := fun R' hR' => by
    obtain ⟨-, -, -, L, -, hRL⟩ := hSmem R' hR'
    exact hDC (Set.ext_iff.mp hRL _ |>.mp (hr R' hR')).1
  have hsum : φ c + ∑ R' ∈ S, φ (r R') ∈ R := by
    rwa [← map_sum, ← map_add, ← hx]
  obtain ⟨hcR, hsR⟩ := hRface.2.2.2 _ (hDC hc) _ (C.sum_mem hrC) hsum
  -- the nonnegative part vanishes, as `K + G` is negative on `R ∖ {0}`
  have hc0' : φ c = 0 := by
    by_contra hne
    have h1 := hneg _ hcR hne
    rw [hKφ] at hc0
    simp only [LinearMap.comp_apply, one_mul] at hc0
    linarith
  have hsum0 : ∑ R' ∈ S, φ (r R') ≠ 0 := fun h => hv0 (by
    rw [hx, map_add, map_sum, hc0', h, add_zero])
  obtain ⟨R', hR', hR'0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum0
  refine ⟨((ξ R' hR' : Λ) : V), Finset.mem_image.mpr ⟨⟨R', hR'⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
  have hy2 : φ (r R') ∈ {u | ∃ c : ℝ, 0 ≤ c ∧ c • ((ξ R' hR' : Λ) : V) = u} := by
    obtain ⟨c', hc', hc'e⟩ := (Set.ext_iff.mp (hξ R' hR') (r R')).mp (hr R' hR')
    refine ⟨c', hc', ?_⟩
    rw [← hc'e, map_smul, hφt, one_smul]
  rw [hRv]
  exact ray_eq_of_mem hR'0 (hRv ▸ mem_of_sum_mem hRface S _ hrC hsR R' hR') hy2

end Vertex

section Geometry

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}

/-- The curve form depends only on the divisor. -/
private theorem curveForm_congr {D D' : QDivisor X} (e : D = D') (h : D.IsQCartier)
    (h' : D'.IsQCartier) :
    MMP.Fourfold.QDivisor.curveForm sX D h = MMP.Fourfold.QDivisor.curveForm sX D' h' := by
  subst e
  rfl

/-- The curve form is additive in the divisor. -/
private theorem curveForm_add [QuasiCompact sX] (D D' : QDivisor X) (hD : D.IsQCartier)
    (hD' : D'.IsQCartier) (hDD' : (D + D').IsQCartier) :
    MMP.Fourfold.QDivisor.curveForm sX (D + D') hDD' =
      MMP.Fourfold.QDivisor.curveForm sX D hD + MMP.Fourfold.QDivisor.curveForm sX D' hD' := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.add_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le D D' hD hD' hDD']
  push_cast
  rfl

/-- A nef `ℚ`-divisor is nonnegative on `NE̅(X)`. -/
private theorem curveForm_nonneg_of_isNef [QuasiCompact sX] {D : QDivisor X}
    (hD : QDivisor.IsNef k sX D) (h : D.IsQCartier) {z : NumericalCurveClasses sX}
    (hz : z ∈ closedConeOfCurves sX) : 0 ≤ MMP.Fourfold.QDivisor.curveForm sX D h z := by
  obtain ⟨hD', hpos⟩ := hD
  set F := MMP.Fourfold.QDivisor.curveForm sX D h with hF
  have hFc : Continuous F := by
    rw [hF, MMP.Fourfold.QDivisor.curveForm, Finsupp.sum, LinearMap.coe_sum]
    rw [Finset.sum_fn]
    refine continuous_finset_sum _ fun E _ => ?_
    haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    rw [LinearMap.coe_smul]
    exact (NumericalCurveClasses.continuous_degree sX (E : Divisor X).divisorialSheaf).const_smul _
  have hcone : ∀ y ∈ coneOfCurves sX, 0 ≤ F y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨C, rfl⟩ := hy
      rw [hF, MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
      exact_mod_cast hpos C.scheme C.ι C.dim_eq
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
    | smul c x _ hx =>
      change 0 ≤ F ((c : ℝ) • x)
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg c.2 hx
  have hcl : closure (coneOfCurves sX : Set (NumericalCurveClasses sX)) ⊆ {y | 0 ≤ F y} :=
    closure_minimal hcone (isClosed_le continuous_const hFc)
  exact hcl ((coe_closedConeOfCurves sX).subst (motive := fun S => z ∈ S) hz)

/-- Isomorphic invertible sheaves have the same degree form on `N₁(X)`. -/
private theorem degree_eq_of_iso {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    NumericalCurveClasses.degree sX L = NumericalCurveClasses.degree sX L' := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [NumericalCurveClasses.degree_numericalClass, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_cycle, OneCycle.degree_cycle]
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

variable (sX) in
/-- The pairing of `N₁(X)` with Cartier divisors, additive in the divisor. -/
private noncomputable def cartierPairing :
    X.CartierDivisor →+ (NumericalCurveClasses sX →ₗ[ℝ] ℝ) :=
  AddMonoidHom.mk' (fun E => NumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E)) fun E E' => by
    simp only [NumericalCurveClasses.intersectionNumber_ofCartier]
    refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
    haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
          X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
            (MMP.CartierDivisor.sheaf E')) :=
      Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
    rw [LinearMap.add_apply, NumericalCurveClasses.degree_numericalClass,
      NumericalCurveClasses.degree_numericalClass, NumericalCurveClasses.degree_numericalClass,
      OneCycle.degree_cycle, OneCycle.degree_cycle, OneCycle.degree_cycle]
    unfold ProperCurve.degree
    rw [← Int.cast_add, ← degreeOn_tensorSheaf]
    exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le
      (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E'))
      (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

private theorem cartierPairing_apply (E : X.CartierDivisor) :
    cartierPairing sX E =
      NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf E) :=
  NumericalCurveClasses.intersectionNumber_ofCartier E

/-- Relative ampleness of an invertible sheaf depends only on its isomorphism class. -/
private theorem isRelativelyAmple_of_iso {Y : Scheme.{0}} {g : X ⟶ Y} {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : MMP.Mori.IsRelativelyAmple g L) : MMP.Mori.IsRelativelyAmple g L' := fun y => by
  obtain ⟨V, hV, hyV, hA⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (g ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).mp hA⟩

/-- For a Cartier divisor `L = mA`, the degree form of `𝒪_X(L)` is `m` times the curve form
of `A`. -/
private theorem degree_divisorialSheaf_eq_smul_curveForm [QuasiCompact sX] {A : QDivisor X}
    (hA : A.IsQCartier) {m : ℕ} (hm : 0 < m) {L : Divisor X} (hL : L.IsCartier)
    (hLA : Divisor.toQDivisor L = (m : ℤ) • A) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    NumericalCurveClasses.degree sX L.divisorialSheaf =
      (m : ℝ) • MMP.Fourfold.QDivisor.curveForm sX A hA := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.smul_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
    ProperCurve.degree_divisorialSheaf C L hL,
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul k sX C.ι C.dim_le
      (Divisor.degreeOn_add k sX C.ι C.dim_le) A hA hm L hL hLA]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  rw [smul_eq_mul, mul_div_cancel₀ _ this]

/-- **The twisted ample form.** An `f`-ample `ℚ`-Cartier divisor `A` agrees on relative classes
with a form positive on `NE̅(X) ∖ {0}`: the form of `A + ν f^*H` for an ample `H` on `Z` and
`ν ≫ 0`. -/
private theorem exists_pos_form_eq_curveForm {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))
    (f : X ⟶ Z) (hf : IsProjectiveSetting k sX sZ f) {A : QDivisor X} (hA : A.IsQCartier)
    (hAf : A.HasRelativelyAmpleMultiple f) :
    ∃ G : NumericalCurveClasses sX →ₗ[ℝ] ℝ,
      (∀ z ∈ closedConeOfCurves sX, z ≠ 0 → 0 < G z) ∧
      ∀ u, G (relativeToAbsolute sX f u) =
        MMP.Fourfold.QDivisor.curveForm sX A hA (relativeToAbsolute sX f u) := by
  have hX : MMP.Mori.IsProjectiveVariety k sX := hf.isProjectiveVariety_source
  have hY : MMP.Mori.IsProjectiveVariety k sZ := hf.isProjectiveVariety_target
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hX
  haveI : IsIntegral Z := hY.toIsVariety.toIsIntegral
  haveI : QuasiCompact sX := inferInstance
  obtain ⟨m, hm, L, hL, hLA, hLamp⟩ := hAf
  haveI := hL.isInvertibleModule_divisorialSheaf
  obtain ⟨EL, ⟨eL⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L.divisorialSheaf
  have hEL : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf EL) :=
    isRelativelyAmple_of_iso eL hLamp
  -- an ample `M` on `Z` and a Cartier divisor `B` with `𝒪_X(B) ≅ f^* 𝒪_Z(M)`
  obtain ⟨⟨LY, _, hLYrel, hLYA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple hY.isProjective.isProjective
  obtain ⟨M, ⟨eM⟩⟩ := hLYA inferInstance
  have hM : Stacks.Ample.IsAmple Z (MMP.CartierDivisor.sheaf M) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ eM).mpr
      (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sZ LY hLYrel)
  obtain ⟨B, ⟨eB⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf M))
  obtain ⟨ν, hν⟩ := (MMP.Foundations.isAmple_add_zsmul_pullback k hX hY hf.comp_eq hM hEL
    ⟨eB.symm⟩).exists
  have hE : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (EL + ν • B)) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (Iso.refl (MMP.CartierDivisor.sheaf (EL + ν • B))).symm).mpr hν
  refine ⟨(m : ℝ)⁻¹ • cartierPairing sX (EL + ν • B), fun z hz hz0 => ?_, fun u => ?_⟩
  · obtain ⟨Zc, hZc⟩ := OneCycle.numericalClass_surjective sX z
    have := closedConeOfCurves_diff_zero_subset_posHalfspace sX (EL + ν • B) hE ⟨hz, hz0⟩ Zc hZc
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine mul_pos (by positivity) ?_
    change 0 < NumericalCurveClasses.intersectionNumber _ z
    rwa [← hZc, NumericalCurveClasses.intersectionNumber_numericalClass]
  · have hB0 : cartierPairing sX B (relativeToAbsolute sX f u) = 0 := by
      rw [cartierPairing_apply, degree_eq_of_iso eB.symm,
        ← NumericalCurveClasses.degree_pushforward f hf.comp_eq,
        LinearMap.mem_ker.1 (range_relativeToAbsolute_le_ker_pushforward f hf.comp_eq ⟨u, rfl⟩),
        map_zero]
    rw [LinearMap.smul_apply, map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, hB0,
      smul_zero, add_zero, cartierPairing_apply, ← degree_eq_of_iso eL,
      degree_divisorialSheaf_eq_smul_curveForm hA hm hL hLA, LinearMap.smul_apply, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]

/-- **The finite list of one vertex.** For a klt pair `(X, Δ)` with `Δ` effective and a form `G`
positive on `NE̅(X) ∖ {0}`, finitely many lattice points generate every extremal ray of `NE̅(X)` on
which `K_X + Δ + G` is negative. -/
private theorem exists_finset_of_isKltPair [IsAlgClosed k] [CharZero k] [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : MMP.Mori.IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    (G : NumericalCurveClasses sX →ₗ[ℝ] ℝ) (hG : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 → 0 < G z) :
    ∃ T : Finset (NumericalCurveClasses sX), (∀ w ∈ T, w ∈ numericalCurveLattice sX) ∧
      ∀ R : Set (NumericalCurveClasses sX),
        IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R →
        (∀ u ∈ R, u ≠ 0 →
          MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 u + G u < 0) →
        ∃ w ∈ T, R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • w = u} := by
  by_cases hnef : QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ)
  · refine ⟨∅, by simp, ?_⟩
    rintro R ⟨⟨hRC, -⟩, v, hv0, hRv⟩ hneg
    have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul ℝ v⟩
    have h1 := hneg v hvR hv0
    have h2 := curveForm_nonneg_of_isNef hnef hklt.1.2.2 (hRC hvR)
    have h3 := hG v (hRC hvR) hv0
    linarith
  obtain ⟨m, hm, hmC⟩ := hklt.1.2.2.exists_pos
  obtain ⟨hfree, hfin, hbij, -, D, hDcone, hDform, -⟩ :=
    exists_coneDatum_numericalCurveLattice_of_isKltPair hklt hΔ hnef (a := m)
      (by exact_mod_cast hm) hmC
  exact exists_finset_of_coneDatum hbij D hDcone _ hDform G hG

end Geometry

end MMP.FourfoldProofs.FourfoldFixedModelFiniteRaysProof

end

section

open AlgebraicGeometry CategoryTheory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

open MMP.FourfoldProofs.FourfoldFixedModelFiniteRaysProof MMP.Positivity in
/-- **Finitely many candidate rays for a fixed boundary polytope.** Let `f : X ⟶ Z` be a
morphism of projective varieties over an algebraically closed field of characteristic zero, with
`X` normal and `ℚ`-factorial and canonical divisor `K`, let `A` be an `f`-ample `ℚ`-Cartier
`ℚ`-divisor and let `Bⱼ` (`j ∈ ι`, finitely many) be boundaries with every `(X, Bⱼ)` klt. Then
there is a finite set `S` of nonzero classes of `NE̅(X/Z)`, each in the numerical curve lattice and
spanning an extremal ray of `NE̅(X/Z)`, such that for all weights `tⱼ ≥ 0` with `∑ tⱼ = 1`, every
extremal ray `R` of `NE̅(X/Z)` on which `K + A + ∑ tⱼ Bⱼ` is negative is `ℝ_{≥0} ξ` for some
`ξ ∈ S`. -/
@[mmp "lem_fourfold_fixed_model_finite_rays"]
public theorem exists_finset_isExtremalRay_of_isKltPair
    {k : Type} [Field k] {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (f : X ⟶ Z)
    (hf : IsProjectiveSetting k sX sZ f) (hX : IsQFactorial sX)
    {K : Divisor X} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    {A : QDivisor X} (hA : A.IsQCartier) (hAf : A.HasRelativelyAmpleMultiple f)
    {ι : Type*} [Fintype ι] (B : ι → QDivisor X) (hB : ∀ j P, (B j).coeff P ≤ 1)
    (hklt : ∀ j, IsKltPair sX (B j)) :
    ∃ S : Finset (RelativeNumericalCurveClasses sX f),
      (∀ ξ ∈ S, ξ ≠ 0 ∧ ξ ∈ relativeClosedConeOfCurves sX f ∧
        relativeToAbsolute sX f ξ ∈ numericalCurveLattice sX ∧
        IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set _)
          {w | ∃ c : ℝ, 0 ≤ c ∧ c • ξ = w}) ∧
      ∀ t : ι → ℝ, (∀ j, 0 ≤ t j) → ∑ j, t j = 1 →
        ∀ R : Set (RelativeNumericalCurveClasses sX f),
          IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set _) R →
          (∃ h : ∀ j, (Divisor.toQDivisor K + A + B j).IsQCartier, ∀ u ∈ R, u ≠ 0 →
            ∑ j, t j * QDivisor.curveForm sX (Divisor.toQDivisor K + A + B j) (h j)
              (relativeToAbsolute sX f u) < 0) →
          ∃ ξ ∈ S, R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • ξ = w} := by
  classical
  haveI := hf.isAlgClosed
  haveI := hf.charZero
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hf.isProjectiveVariety_source
  haveI : AlgebraicGeometry.IsProjectiveVariety k sZ := hf.isProjectiveVariety_target
  haveI : QuasiCompact sX := inferInstance
  obtain ⟨n, hKn⟩ := hK
  have hkltM : ∀ j, MMP.Mori.IsKltPair sX n K (B j) := fun j =>
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hKn (hklt j).1).mp (hklt j)
  obtain ⟨G, hGpos, hGA⟩ := exists_pos_form_eq_curveForm sZ f hf hA hAf
  choose T hTl hT using fun j =>
    exists_finset_of_isKltPair (hkltM j) (fun P => (hklt j).1.nonneg P) G hGpos
  have hinj : Function.Injective (relativeToAbsolute sX f) :=
    (existsUnique_isNaturalRelativeMap_and_injective sX f).2 _
      (isNaturalRelativeMap_relativeToAbsolute sX f)
  set U : Finset (NumericalCurveClasses sX) := Finset.univ.biUnion T with hU
  set Sset : Set (RelativeNumericalCurveClasses sX f) := {ρ | ρ ≠ 0 ∧
    ρ ∈ relativeClosedConeOfCurves sX f ∧
    IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set _)
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • ρ = w} ∧ relativeToAbsolute sX f ρ ∈ U} with hSset
  have hSfin : Sset.Finite :=
    ((U : Set (NumericalCurveClasses sX)).toFinite.preimage hinj.injOn).subset
      fun ρ hρ => hρ.2.2.2
  refine ⟨hSfin.toFinset, fun ξ hξ => ?_, fun t ht _ R hR ⟨h, hneg⟩ => ?_⟩
  · obtain ⟨h0, hC, hext, hU'⟩ := hSfin.mem_toFinset.mp hξ
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hU'
    exact ⟨h0, hC, hTl j _ hj, hext⟩
  obtain ⟨hRface, v, hv0, hRv⟩ := hR
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul ℝ v⟩
  -- a vertex on which `K + A + Bⱼ` is negative at `v`
  obtain ⟨j, hj⟩ : ∃ j, MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + A + B j) (h j)
      (relativeToAbsolute sX f v) < 0 := by
    by_contra hcon
    push Not at hcon
    have := hneg v hvR hv0
    have : 0 ≤ ∑ j, t j * MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + A + B j)
        (h j) (relativeToAbsolute sX f v) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (ht j) (hcon j)
    linarith
  have hsplit : ∀ u, MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + A + B j) (h j)
      (relativeToAbsolute sX f u) =
      MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + B j) (hkltM j).1.2.2
        (relativeToAbsolute sX f u) + G (relativeToAbsolute sX f u) := fun u => by
    rw [hGA, curveForm_congr (by abel : Divisor.toQDivisor K + A + B j =
        (Divisor.toQDivisor K + B j) + A) (h j) ((hkltM j).1.2.2.add hA),
      curveForm_add _ _ (hkltM j).1.2.2 hA, LinearMap.add_apply]
  have hRabs := isExtremalRay_image_relativeToAbsolute sX sZ f hf.comp_eq ⟨hRface, v, hv0, hRv⟩
  have himg : relativeToAbsolute sX f '' R =
      {u | ∃ c : ℝ, 0 ≤ c ∧ c • relativeToAbsolute sX f v = u} := by
    rw [hRv, image_ray]
  obtain ⟨w, hwT, hw⟩ := hT j _ hRabs (fun u hu hu0 => by
    rw [himg] at hu
    obtain ⟨c, hc, rfl⟩ := hu
    have hc0 : 0 < c := lt_of_le_of_ne hc fun h0 => hu0 (by rw [← h0, zero_smul])
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_add, ← hsplit]
    exact mul_neg_of_pos_of_neg hc0 hj)
  have hwR : w ∈ relativeToAbsolute sX f '' R := hw ▸ ⟨1, zero_le_one, one_smul ℝ w⟩
  obtain ⟨ρ, hρR, rfl⟩ := hwR
  have hRρ : R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • ρ = u} :=
    Set.image_injective.mpr hinj (hw.trans (image_ray _ ρ).symm)
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    apply hv0
    rw [hRρ] at hvR
    obtain ⟨c, -, hc⟩ := hvR
    rw [← hc, smul_zero]
  refine ⟨ρ, hSfin.mem_toFinset.mpr ⟨hρ0, hRface.1 hρR, hRρ ▸ ⟨hRface, v, hv0, hRv⟩, ?_⟩, hRρ⟩
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hwT⟩

end MMP.Fourfold

end
