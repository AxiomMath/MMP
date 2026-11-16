module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.Positivity.FreeDivisorSteinFactorization
public import MMP.AlgebraicGeometry.MMP.Contraction.CurveFactorization
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
public import MMP.AlgebraicGeometry.Modules.FiniteLocallyFreeRankOne
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

section

/-!
# A semiample supporting divisor contracts a negative relative extremal ray

Proof of `MMP.Fourfold.exists_isNegativeRelativeRayContraction_of_isSupportingDivisor`. The
generated multiple `mL` is free, so it defines a morphism `Φ` to a projective bundle over `k`;
its Stein factorization `X ⟶ Z ⟶ ℙ` gives the contraction `c : X ⟶ Z`, with an ample divisor
`A` on `Z` and `𝒪_X(mL) ≅ c^* 𝒪_Z(A)`. A curve is contracted by `c` exactly when its `L`-degree
vanishes, that is, when its class lies on the image of `R`; such curves are contracted by `h`
(test against an ample sheaf on `S`), so rigidity factors `h` through `c`. The closed relative
cone of `c` maps into the ray of `R`, which gives `ρ(X/Z) = 1` and, by the relative Kleiman
criterion, the `c`-ampleness of `-D`.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP.Mori.QDivisor

/-- If `L = m D` with `m ≠ 0`, then `D = m⁻¹ L` as `ℝ`-divisors. -/
public theorem toRDivisor_eq_inv_smul {X : Scheme.{u}} {D : QDivisor X} {m : ℤ} (hm : m ≠ 0)
    {L : Divisor X} (hL : L.toQDivisor = m • D) :
    D.toRDivisor = ((m : ℝ)⁻¹) • L.toRDivisor := by
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

/-- A Cartier divisor ample over an affine neighbourhood of every point of the target is ample
over every affine open of the target. -/
private theorem isRelativelyAmpleCartier_of_isRelativelyAmple {X Y : Scheme.{u}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} [QuasiCompact f]
    {L : Divisor X} (hL : L.IsCartier) (h : L.IsRelativelyAmple f hL) :
    MMP.Flips.IsRelativelyAmpleCartier f L := by
  have := hL.isInvertibleModule_divisorialSheaf
  exact ⟨hL, fun U hU =>
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
      inferInstance h).2 U hU⟩

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-ample as an `ℝ`-divisor: the
passage from `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple` to `MMP.Flips.IsRelativelyAmple`. -/
public theorem HasRelativelyAmpleMultiple.isRelativelyAmple_toRDivisor {X Y : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} [QuasiCompact f]
    {D : QDivisor X} (h : D.HasRelativelyAmpleMultiple f) :
    MMP.Flips.IsRelativelyAmple f D.toRDivisor := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  refine ⟨1, fun _ => ((m : ℤ) : ℝ)⁻¹, fun _ => L, le_rfl, fun _ => by positivity,
    fun _ => isRelativelyAmpleCartier_of_isRelativelyAmple hL hamp, ?_⟩
  rw [Fin.sum_univ_one]
  exact toRDivisor_eq_inv_smul (by exact_mod_cast hm.ne') hLD

end MMP.Mori.QDivisor

namespace MMP.FourfoldProofs.MmpProjectiveLcSemiampleSupportContractsProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

/-! ### Divisors and pull-backs -/

section Divisors

private theorem isLocalEquationAt_zero_one (Z : Scheme.{0}) (x : Z) :
    MMP.Intersection.IsLocalEquationAt (0 : Z.CartierDivisor) x 1 :=
  ⟨⊤, trivial, 1, MMP.Intersection.isLocalEquationOn_one _, by simp⟩

/-- The zero Cartier divisor pulls back to the zero Cartier divisor. -/
private theorem isPullback_zero {X Y : Scheme.{0}} (g : Y ⟶ X) :
    MMP.Intersection.IsPullback g (0 : X.CartierDivisor) 0 := by
  refine ⟨fun η _ => ?_, fun y => ⟨1, 1,
    ⟨1, isLocalEquationAt_zero_one _ _, MMP.Intersection.isFraction_one_one_one _⟩,
    ?_, ?_, 1, isLocalEquationAt_zero_one _ _, ?_⟩⟩
  · simp [MMP.Intersection.cartierSupport]
  · simp
  · simp
  · simpa only [map_one] using MMP.Intersection.isFraction_one_one_one y

/-- The degree of `𝒪_X(nD)` on a curve is `n` times that of `𝒪_X(D)`. -/
private theorem degree_sheaf_nsmul {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (D : X.CartierDivisor) {n : ℕ} (hn : 1 ≤ n) :
    C.degree k (MMP.CartierDivisor.sheaf (n • D)) =
      n * C.degree k (MMP.CartierDivisor.sheaf D) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [succ_nsmul]
    unfold ProperCurve.degree at *
    haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((MMP.CartierDivisor.sheaf (n • D)).tensorObj
          (MMP.CartierDivisor.sheaf D)) :=
      Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
    rw [degreeOn_eq_of_iso k sX C.ι C.dim_le
      (MMP.CartierDivisorSheaf.sheafMulIso (n • D) D).symm]
    refine (degreeOn_tensorSheaf k sX C.ι C.dim_le _ _ (hLM := this)).trans ?_
    rw [ih]
    push_cast
    ring

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : QDivisor X} (h : D.IsQCartier) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := h
  refine ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, ?_⟩
  rw [Fin.sum_univ_one]
  exact QDivisor.toRDivisor_eq_inv_smul hm hL

/-- An `f`-ample Cartier divisor is ample over an affine neighbourhood of every point. -/
private theorem isRelativelyAmple_of_isRelativelyAmpleCartier {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {W : Divisor Y}
    (hW : MMP.Flips.IsRelativelyAmpleCartier f W) : W.IsRelativelyAmple f hW.1 := by
  obtain ⟨hWc, hamp⟩ := hW
  have := hWc.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, hamp V hV⟩

/-- The projection of `ℙ(G) = Proj_Z(Sym G)` is proper when `G` is quasi-coherent of finite
type. -/
private theorem isProper_relativeProj_toBase {Z : Scheme.{0}} (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] :
    IsProper (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.SymGraded.schemeSheafGradedAlgebra G
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G))).toBase := by
  have h := Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType Z G
  rw [← Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase G] at h
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp h

end Divisors

/-! ### Numerical classes -/

section Classes

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- Numerical classes are separated by the degree forms of invertible sheaves. -/
private theorem numericalCurveClasses_ext {z z' : NumericalCurveClasses sX}
    (h : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      NumericalCurveClasses.degree sX L z = NumericalCurveClasses.degree sX L z') : z = z' := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  obtain ⟨Z', rfl⟩ := OneCycle.numericalClass_surjective sX z'
  rw [← sub_eq_zero, ← map_sub]
  refine (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  have := h L
  simp only [NumericalCurveClasses.degree_numericalClass] at this
  rw [map_sub, this, sub_self]

/-- A ray `ℝ_{≥0} · v`, `v ≠ 0`, is closed in `N₁(X)` for the numerical topology. -/
private theorem isClosed_ray {v : NumericalCurveClasses sX} (hv : v ≠ 0) :
    IsClosed {w : NumericalCurveClasses sX | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
  obtain ⟨L₀, hL₀, hv₀⟩ : ∃ (L₀ : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 L₀), NumericalCurveClasses.degree sX L₀ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (numericalCurveClasses_ext sX fun L _ => by rw [hcon L, map_zero])
  set a := NumericalCurveClasses.degree sX L₀ v
  have hS : {w : NumericalCurveClasses sX | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} =
      {w | 0 ≤ NumericalCurveClasses.degree sX L₀ w / a} ∩
        ⋂ (L : X.Modules) (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
          {w | NumericalCurveClasses.degree sX L w =
            NumericalCurveClasses.degree sX L₀ w / a * NumericalCurveClasses.degree sX L v} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hca : NumericalCurveClasses.degree sX L₀ (c • v) / a = c := by
        rw [map_smul, smul_eq_mul, mul_div_assoc, div_self hv₀, mul_one]
      refine ⟨by rwa [hca], fun L _ => ?_⟩
      rw [hca, map_smul, smul_eq_mul]
    · rintro ⟨hc, hL⟩
      refine ⟨_, hc, numericalCurveClasses_ext sX fun L _ => ?_⟩
      rw [map_smul, smul_eq_mul, hL L]
  rw [hS]
  have hc₀ := NumericalCurveClasses.continuous_degree sX L₀
  refine (isClosed_le continuous_const (hc₀.div_const a)).inter
    (isClosed_iInter fun L => isClosed_iInter fun h => ?_)
  exact isClosed_eq (NumericalCurveClasses.continuous_degree sX L)
    ((hc₀.div_const a).mul continuous_const)

variable (f : X ⟶ Y)

/-- The relative degree form of `L` is the absolute one composed with `N₁(X/Y) → N₁(X)`. -/
private theorem relativeDegree_eq_comp (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    RelativeNumericalCurveClasses.degree sX f L =
      (NumericalCurveClasses.degree sX L).comp (relativeToAbsolute sX f) := by
  apply Submodule.linearMap_qext
  rfl

private theorem continuous_relativeToAbsolute : Continuous (relativeToAbsolute sX f) := by
  refine continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => continuous_induced_rng.2 ?_
  have := h
  have hc := RelativeNumericalCurveClasses.continuous_degree sX f L
  rwa [relativeDegree_eq_comp sX f L, LinearMap.coe_comp] at hc

private theorem injective_relativeToAbsolute : Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  have hZ : OneCycle.numericalClass sX (Z : OneCycle ℝ sX) = 0 := LinearMap.mem_ker.mp hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hZ)

/-- A relative class lies on the ray `ℝ≥0 · v` exactly when its image in `N₁(X)` lies on the ray
spanned by the image of `v`. -/
private theorem exists_smul_relativeToAbsolute_eq_iff (v z : RelativeNumericalCurveClasses sX f) :
    (∃ t : ℝ, 0 ≤ t ∧ t • relativeToAbsolute sX f v = relativeToAbsolute sX f z) ↔
      ∃ t : ℝ, 0 ≤ t ∧ t • v = z := by
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [← map_smul]
  exact (injective_relativeToAbsolute sX f).eq_iff

/-- `f`-ampleness of an invertible sheaf only depends on its isomorphism class. -/
private theorem isRelativelyAmple_of_iso {L L' : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L') (h : IsRelativelyAmple f L) :
    IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (Functor.mapIso _ e)).mp hA⟩

/-- If every curve contracted by `f` has its class on the ray `ℝ≥0 · v`, then so does the image
in `N₁(X)` of every class of the closed relative cone `NE̅(X/Y)`. -/
private theorem relativeToAbsolute_mem_ray {v : NumericalCurveClasses sX} (hv : v ≠ 0)
    (hcontr : ∀ C : ProperCurve sX, C.IsContractedBy f →
      ∃ c : ℝ, 0 ≤ c ∧ c • v = OneCycle.numericalClass sX (C.cycle ℝ))
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    ∃ c : ℝ, 0 ≤ c ∧ c • v = relativeToAbsolute sX f z := by
  set ι := relativeToAbsolute sX f
  have hsub : (relativeConeOfCurves sX f : Set _) ⊆ ι ⁻¹' {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hcontr C hC
    | zero => exact ⟨0, le_rfl, by rw [zero_smul, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨c', hc', hcy⟩ := hy
      exact ⟨c + c', add_nonneg hc hc', by rw [add_smul, hcx, hcy, map_add]⟩
    | smul a x _ hx =>
      obtain ⟨c, hc, hcx⟩ := hx
      refine ⟨a * c, mul_nonneg a.2 hc, ?_⟩
      rw [mul_smul, hcx]
      exact (map_smul ι (a : ℝ) x).symm
  exact closure_minimal hsub
    ((isClosed_ray sX hv).preimage (continuous_relativeToAbsolute sX f)) hz

/-- If the Cartier divisor `A` has sheaf `𝒪_X(-E)`, its relative intersection form is minus the
degree form of `𝒪_X(E)` read through `N₁(X/Y) → N₁(X)`. -/
private theorem intersectionNumber_ofCartier_eq_neg_degree [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {E : Divisor X} (hE : E.IsCartier)
    [Stacks.Ample.IsInvertibleModule X E.divisorialSheaf]
    [Stacks.Ample.IsInvertibleModule X (-E).divisorialSheaf] {A : X.CartierDivisor}
    (e : (-E).divisorialSheaf ≅ MMP.CartierDivisor.sheaf A)
    (z : RelativeNumericalCurveClasses sX f) :
    RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ A) z =
      -NumericalCurveClasses.degree sX E.divisorialSheaf (relativeToAbsolute sX f z) := by
  have hdeg (C : ProperCurve sX) : C.degree k (MMP.CartierDivisor.sheaf A) =
      -C.degree k E.divisorialSheaf := by
    rw [ProperCurve.degree, ProperCurve.degree, ← degreeOn_eq_of_iso k sX C.ι C.dim_le e]
    exact Divisor.degreeOn_neg' k sX C.ι C.dim_le _ hE
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber_ofCartier]
  change OneCycle.degree ℝ sX _ (Z : OneCycle ℝ sX) =
    -(OneCycle.degree ℝ sX E.divisorialSheaf (Z : OneCycle ℝ sX))
  simp only [OneCycle.degree_apply, Finsupp.sum, hdeg, Int.cast_neg, mul_neg,
    Finset.sum_neg_distrib]

/-- The numerical class of a curve pairs with an invertible sheaf by its degree. -/
private theorem degree_numericalClass_cycle (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (C : ProperCurve sX) :
    NumericalCurveClasses.degree sX L (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (C.degree k L : ℝ) := by
  rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_apply, ProperCurve.cycle,
    Finsupp.sum_single_index (by simp), one_mul]

/-- The numerical class of a curve pairs with a Cartier divisor by its degree. -/
private theorem intersectionNumber_numericalClass_cycle (L : X.CartierDivisor)
    (C : ProperCurve sX) :
    NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ L)
        (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (C.degree k (MMP.CartierDivisor.sheaf L) : ℝ) := by
  rw [NumericalCurveClasses.intersectionNumber_numericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
    ← NumericalCurveClasses.degree_numericalClass, degree_numericalClass_cycle]

end Classes

/-! ### Ample sheaves on projective varieties -/

section Ample

/-- A Cartier divisor ample over `Spec k` is ample. -/
private theorem isAmple_of_isRelativelyAmpleCartier {k : Type} [Field k] {Z : Scheme.{0}}
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] (sZ : Z ⟶ Spec (.of k))
    [QuasiCompact sZ] {A : Divisor Z} (hA : MMP.Flips.IsRelativelyAmpleCartier sZ A) :
    haveI := hA.1.isInvertibleModule_divisorialSheaf
    Scheme.Modules.IsAmple Z A.divisorialSheaf := by
  haveI := hA.1.isInvertibleModule_divisorialSheaf
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp
    ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple sZ _).mp
      (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple sZ _
        inferInstance (isRelativelyAmple_of_isRelativelyAmpleCartier hA)))

end Ample

/-! ### The relative Picard number -/

/-- **A contraction whose contracted curves span one line has relative Picard number one.** If
`C₀` is contracted by `c`, its class is nonzero, and every curve contracted by `c` has class a
multiple of that of `C₀`, then `ρ(X/Z) = 1`: the numerically `c`-trivial divisors are the kernel
of the nonzero linear form `B ↦ (B · C₀)`. -/
private theorem relativePicardNumber_eq_one_of_forall_isContractedBy {k : Type} [Field k]
    {X Z : Scheme.{0}} [IsIntegral X] (sX : X ⟶ Spec (.of k)) (c : X ⟶ Z) (C₀ : ProperCurve sX)
    (hC₀ : C₀.IsContractedBy c) (hw₀ : OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0)
    (hray : ∀ C : ProperCurve sX, C.IsContractedBy c → ∃ t : ℝ,
      t • OneCycle.numericalClass sX (C₀.cycle ℝ) = OneCycle.numericalClass sX (C.cycle ℝ)) :
    MMP.Flips.relativePicardNumber sX c = 1 := by
  set ψ : KCartierDivisor ℝ X →ₗ[ℝ] ℝ := (OneCycle.intersectionPairing (sX := sX)).flip (C₀.cycle ℝ)
  have hψ (B) : ψ B = (C₀.cycle ℝ).intersectionNumber B := rfl
  have hker : MMP.Flips.relativeNumericallyTrivialDivisors sX c = LinearMap.ker ψ := by
    ext B
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors, LinearMap.mem_ker, hψ]
    refine ⟨fun hB => hB C₀ hC₀, fun hB C hC => ?_⟩
    obtain ⟨t, hzt⟩ := hray C hC
    rw [← NumericalCurveClasses.intersectionNumber_numericalClass, ← hzt, map_smul,
      NumericalCurveClasses.intersectionNumber_numericalClass, hB, smul_zero]
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, ψ B₀ ≠ 0 := by
    have hnt : C₀.cycle ℝ ∉ OneCycle.numericallyTrivial sX := fun hmem =>
      hw₀ ((Submodule.Quotient.mk_eq_zero _).mpr hmem)
    rw [OneCycle.mem_numericallyTrivial] at hnt
    push Not at hnt
    obtain ⟨L', hL', hdeg⟩ := hnt
    obtain ⟨E', ⟨e'⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L'
    refine ⟨KCartierDivisor.ofCartier ℝ E', ?_⟩
    rw [hψ, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
      ← NumericalCurveClasses.degree_numericalClass, degree_numericalClass_cycle]
    rw [← NumericalCurveClasses.degree_numericalClass, degree_numericalClass_cycle] at hdeg
    rwa [ProperCurve.degree, ← degreeOn_eq_of_iso k sX C₀.ι C₀.dim_le e']
  have hsurj : Function.Surjective ψ := fun y =>
    ⟨(y / ψ B₀) • B₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hB₀]⟩
  have hrank :=
    ((Submodule.quotEquivOfEq _ _ hker).trans (ψ.quotKerEquivOfSurjective hsurj)).lift_rank_eq
  rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at hrank
  rw [MMP.Flips.relativePicardNumber, hrank, map_one]

/-! ### Anti-ampleness over the contraction -/

/-- **`-D` is ample over a contraction of a `D`-negative ray.** Let `c : X ⟶ Z` be projective
and suppose every curve contracted by `c` has class on the ray `ℝ≥0 · w₀`, `w₀ ≠ 0`, on which
the Cartier multiple `E = (index D) • D` is negative. Then `-D` has a `c`-ample Cartier multiple,
namely `-E`: by the relative Kleiman criterion it suffices that `-E` is positive on the nonzero
classes of `NE̅(X/Z)`, and these map onto positive multiples of `w₀`. -/
private theorem hasRelativelyAmpleMultiple_neg_of_forall_isContractedBy {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X] (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sZ] (c : X ⟶ Z)
    (hc : IsProjective c) (hcomp : c ≫ sZ = sX) {D : QDivisor X}
    (hq : D.IsQCartier) {w₀ : NumericalCurveClasses sX} (hw₀ : w₀ ≠ 0)
    (hray : ∀ C : ProperCurve sX, C.IsContractedBy c →
      ∃ t : ℝ, 0 ≤ t ∧ t • w₀ = OneCycle.numericalClass sX (C.cycle ℝ))
    (hdeg : haveI := (Divisor.mem_cartierSubgroup.mp
        (D.cartierIndexSMul hq).2).isInvertibleModule_divisorialSheaf
      NumericalCurveClasses.degree sX ((D.cartierIndexSMul hq : Divisor X)).divisorialSheaf w₀ <
        0) :
    (-D).HasRelativelyAmpleMultiple c := by
  set E := D.cartierIndexSMul hq
  have hEc : (E : Divisor X).IsCartier := Divisor.mem_cartierSubgroup.mp E.2
  refine ⟨_, QDivisor.cartierIndex_pos hq, -(E : Divisor X), hEc.neg,
    by rw [map_neg, QDivisor.toQDivisor_cartierIndexSMul, smul_neg], ?_⟩
  haveI := hEc.neg.isInvertibleModule_divisorialSheaf
  haveI := hEc.isInvertibleModule_divisorialSheaf
  obtain ⟨A', ⟨e'⟩⟩ :=
    MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf (-(E : Divisor X)).divisorialSheaf
  rw [Divisor.isRelativelyAmple_iff]
  refine isRelativelyAmple_of_iso c e'.symm <|
    (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sZ sX c hc
      hcomp A').mpr fun z hz hz0 => ?_
  obtain ⟨t, ht, htz⟩ := relativeToAbsolute_mem_ray sX c hw₀ hray hz
  have ht0 : 0 < t := ht.lt_of_ne <| by
    rintro rfl
    rw [zero_smul] at htz
    exact hz0 (injective_relativeToAbsolute sX c (htz.symm.trans (map_zero _).symm))
  rw [intersectionNumber_ofCartier_eq_neg_degree sX c hEc e', ← htz, map_smul, smul_eq_mul]
  nlinarith

/-! ### The contraction -/

/-- The generator of an extremal ray `ℝ≥0 · v` is nonzero. -/
private theorem ne_zero_of_isExtremalRay {V : Type*} [AddCommGroup V] [Module ℝ V] {N R : Set V}
    {v : V} (hext : IsExtremalRay ℝ N R) (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w}) : v ≠ 0 := by
  intro h0
  obtain ⟨u, hu, hRu⟩ := hext.2
  have huR : u ∈ R := hRu ▸ ⟨1, zero_le_one, one_smul _ _⟩
  rw [hR] at huR
  obtain ⟨t, -, ht⟩ := huR
  rw [h0, smul_zero] at ht
  exact hu ht.symm

/-- If `L` supports the image of the ray `R = ℝ≥0 · [C₀]`, the curves of `L`-degree zero are those
whose class lies on the ray of `[C₀]`. -/
private theorem degree_eq_zero_iff_mem_ray {k : Type} [Field k] {X S : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [IsProper sX]
    {h : X ⟶ S} {C₀ : ProperCurve sX} {hC₀ : C₀.IsContractedBy h}
    {R : Set (RelativeNumericalCurveClasses sX h)}
    (hRC : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • C₀.relativeClass h hC₀ = w})
    {L : X.CartierDivisor} (hL : IsSupportingDivisor k sX (relativeToAbsolute sX h '' R) L)
    (C : ProperCurve sX) :
    C.degree k (MMP.CartierDivisor.sheaf L) = 0 ↔
      ∃ t : ℝ, 0 ≤ t ∧ t • OneCycle.numericalClass sX (C₀.cycle ℝ) =
        OneCycle.numericalClass sX (C.cycle ℝ) := by
  have hvw : relativeToAbsolute sX h (C₀.relativeClass h hC₀) =
      OneCycle.numericalClass sX (C₀.cycle ℝ) := rfl
  have himage : relativeToAbsolute sX h '' R =
      {w | ∃ t : ℝ, 0 ≤ t ∧ t • OneCycle.numericalClass sX (C₀.cycle ℝ) = w} := by
    rw [hRC]
    ext w
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, by rw [map_smul, hvw]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t • C₀.relativeClass h hC₀, ⟨t, ht, rfl⟩, by rw [map_smul, hvw]⟩
  change _ ↔ OneCycle.numericalClass sX (C.cycle ℝ) ∈
    {w | ∃ t : ℝ, 0 ≤ t ∧ t • OneCycle.numericalClass sX (C₀.cycle ℝ) = w}
  rw [← himage, ← hL.2]
  simp only [Set.mem_setOf_eq, intersectionNumber_numericalClass_cycle]
  exact ⟨fun h0 => ⟨subset_closure (numericalClass_cycle_mem_coneOfCurves sX C),
    by exact_mod_cast h0⟩, fun h0 => by exact_mod_cast h0.2⟩

/-- If `𝒪_X(mL) ≅ c^* 𝒪_Z(A)` with `A` ample and `m > 0`, the curves contracted by `c` are those
of `L`-degree zero. -/
private theorem isContractedBy_iff_degree_eq_zero {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Z : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sZ] [IsProper sX]
    [IsProper sZ] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    (c : X ⟶ Z) [IsProper c] (hcomp : c ≫ sZ = sX)
    {A : Divisor Z} (hA : MMP.Flips.IsRelativelyAmpleCartier sZ A) {L : X.CartierDivisor} {m : ℕ}
    (hm : 0 < m) (eM : MMP.CartierDivisor.sheaf ((m : ℤ) • L) ≅
        (Scheme.Modules.pullback c).obj A.divisorialSheaf) (C : ProperCurve sX) :
    C.IsContractedBy c ↔ C.degree k (MMP.CartierDivisor.sheaf L) = 0 := by
  haveI := hA.1.isInvertibleModule_divisorialSheaf
  have hdm : C.degree k (MMP.CartierDivisor.sheaf ((m : ℤ) • L)) =
      m * C.degree k (MMP.CartierDivisor.sheaf L) := by
    rw [natCast_zsmul]
    exact degree_sheaf_nsmul C L hm
  have hdA : C.degree k (MMP.CartierDivisor.sheaf ((m : ℤ) • L)) =
      C.degree k ((Scheme.Modules.pullback c).obj A.divisorialSheaf) :=
    degreeOn_eq_of_iso k sX C.ι C.dim_le eM
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · intro hC
    have h0 := ProperCurve.degree_pullback_eq_zero_of_isContractedBy c hcomp C hC
      A.divisorialSheaf
    rw [← hdA, hdm] at h0
    exact (mul_eq_zero.mp h0).resolve_left hm0
  · intro h0
    exact MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero c hcomp _
      (isAmple_of_isRelativelyAmpleCartier sZ hA) C (by rw [← hdA, hdm, h0, mul_zero])

/-- A curve whose class is a multiple of that of a curve contracted by `h : X ⟶ S`, `S`
projective, is contracted by `h`: test against an ample sheaf on `S`. -/
private theorem isContractedBy_of_smul_numericalClass {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X S : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sS] [IsProper sX]
    [IsProper sS] (hSp : MMP.Mori.IsProjectiveVariety k sS) (h : X ⟶ S) (hh : h ≫ sS = sX)
    {C₀ C : ProperCurve sX} (hC₀ : C₀.IsContractedBy h) {t : ℝ}
    (hzt : t • OneCycle.numericalClass sX (C₀.cycle ℝ) = OneCycle.numericalClass sX (C.cycle ℝ)) :
    C.IsContractedBy h := by
  obtain ⟨H, hHinv, hHamp⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hSp
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback h).obj H) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback h.toLRSHom.toShHom _
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero h hh H hHamp C ?_
  have h1 := degree_numericalClass_cycle sX ((Scheme.Modules.pullback h).obj H) C
  have h2 := degree_numericalClass_cycle sX ((Scheme.Modules.pullback h).obj H) C₀
  rw [ProperCurve.degree_pullback_eq_zero_of_isContractedBy h hh C₀ hC₀ H] at h2
  rw [← hzt, map_smul, h2] at h1
  exact_mod_cast (by simpa using h1.symm)

/-- Rigidity of the structure morphisms: if `c ≫ g = h`, `h ≫ s_S = s_X = c ≫ s_Z` and `c` is an
isomorphism on global sections, then `g ≫ s_S = s_Z`. -/
private theorem comp_eq_of_comp_eq_of_isIso_appTop {k : Type} [Field k] {X Z S : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sS : S ⟶ Spec (.of k)} {c : X ⟶ Z}
    {g : Z ⟶ S} {h : X ⟶ S} [IsIso c.appTop] (hg : c ≫ g = h) (hh : h ≫ sS = sX)
    (hcomp : c ≫ sZ = sX) : g ≫ sS = sZ := by
  apply ext_of_isAffine
  have h1 : (c ≫ g ≫ sS).appTop = (c ≫ sZ).appTop := by
    rw [← Category.assoc, hg, hh, hcomp]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h1
  exact (cancel_mono _).mp h1

/-- `-D` is ample over a projective contraction `c` of the curves whose class lies on the ray
spanned by a relative class `v₀` on which `D` is negative. -/
private theorem hasRelativelyAmpleMultiple_neg_of_relativeCurveForm_neg {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X S Z : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X] {sX : X ⟶ Spec (.of k)} (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sZ] [IsProper sX]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) {h : X ⟶ S} {D : QDivisor X} (hq : D.IsQCartier)
    {v₀ : RelativeNumericalCurveClasses sX h} (hv₀ : relativeToAbsolute sX h v₀ ≠ 0)
    (hneg : QDivisor.relativeCurveForm sX h D hq v₀ < 0) (c : X ⟶ Z) (hcomp : c ≫ sZ = sX)
    (hray : ∀ C : ProperCurve sX, C.IsContractedBy c →
      ∃ t : ℝ, 0 ≤ t ∧ t • relativeToAbsolute sX h v₀ = OneCycle.numericalClass sX (C.cycle ℝ)) :
    (-D).HasRelativelyAmpleMultiple c := by
  have hcP : IsProjective c := IsProjective.of_comp c sZ <| by
    rw [hcomp]
    exact ((isProjectiveVariety_iff_isProjective' k sX).mp hXp).2
  refine hasRelativelyAmpleMultiple_neg_of_forall_isContractedBy sX sZ c hcP hcomp hq hv₀ hray ?_
  rw [QDivisor.relativeCurveForm, QDivisor.associatedCartier,
    CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp), LinearMap.smul_apply,
    relativeDegree_eq_comp sX h, LinearMap.comp_apply] at hneg
  have := QDivisor.cartierIndex_pos hq
  exact neg_of_smul_neg_left hneg (by positivity)

/-- The core of the proof: given the Stein factor `c : X ⟶ Z` of the morphism defined by `mL`,
with an ample divisor `A` on `Z` such that `𝒪_X(mL) ≅ c^* 𝒪_Z(A)`, the morphism `c` is the
contraction of `R` over `S`. -/
private theorem exists_isNegativeRelativeRayContraction_of_steinFactor {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k]
    {X S Z : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    (hX : MMP.Mori.IsNormalVariety k sX) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hSp : MMP.Mori.IsProjectiveVariety k sS)
    (h : X ⟶ S) (hh : h ≫ sS = sX)
    {D : QDivisor X} {R : Set (RelativeNumericalCurveClasses sX h)}
    (hR : IsNegativeRelativeExtremalRayOf sX h D R)
    (C₀ : ProperCurve sX) (hC₀ : C₀.IsContractedBy h)
    (hRC : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • C₀.relativeClass h hC₀ = w})
    {L : X.CartierDivisor} (hL : IsSupportingDivisor k sX (relativeToAbsolute sX h '' R) L)
    (c : X ⟶ Z) (hZ : MMP.Mori.IsNormalVariety k sZ) (hcomp : c ≫ sZ = sX) [IsProper c]
    [Surjective c] [IsIso c.c] [IsProper sZ] [IsLocallyNoetherian Z] [IsNormal Z]
    [CompactSpace Z] (hcapp : ∀ U : Z.Opens, IsIso (c.app U))
    (A : Divisor Z) (hA : MMP.Flips.IsRelativelyAmpleCartier sZ A) (m : ℕ) (hm : 0 < m)
    (eM : MMP.CartierDivisor.sheaf ((m : ℤ) • L) ≅
        (Scheme.Modules.pullback c).obj A.divisorialSheaf) :
    ∃ g : Z ⟶ S, IsNegativeRelativeRayContraction sX h sZ D R c g ∧ IsProjectiveMorphism c ∧
      g ≫ sS = sZ := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
  haveI : AlgebraicGeometry.IsProjectiveVariety k sS := hSp
  haveI : AlgebraicGeometry.IsVariety k sX := hXp.toIsVariety
  haveI : AlgebraicGeometry.IsVariety k sS := hSp.toIsVariety
  haveI : AlgebraicGeometry.IsVariety k sZ := hZ.1
  haveI : IsIntegral X := hXp.toIsIntegral
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hXp.isProjective
  haveI : IsProper sS := isProper_of_isProjectiveMorphism _ hSp.isProjective
  haveI := hA.1.isInvertibleModule_divisorialSheaf
  obtain ⟨hq, hext, hneg⟩ := hR
  set v₀ := C₀.relativeClass h hC₀
  set w₀ := OneCycle.numericalClass sX (C₀.cycle ℝ)
  have hv₀R : v₀ ∈ R := hRC ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hv₀ : v₀ ≠ 0 := ne_zero_of_isExtremalRay hext hRC
  have hw₀ : w₀ ≠ 0 := fun h0 =>
    hv₀ (injective_relativeToAbsolute sX h (by rw [map_zero]; exact h0))
  have hc_ray (C : ProperCurve sX) : C.IsContractedBy c ↔
      ∃ t : ℝ, 0 ≤ t ∧ t • w₀ = OneCycle.numericalClass sX (C.cycle ℝ) :=
    (isContractedBy_iff_degree_eq_zero c hcomp hA hm eM C).trans
      (degree_eq_zero_iff_mem_ray hRC hL C)
  have hvert (C : ProperCurve sX) (hC : C.IsContractedBy c) : C.IsContractedBy h :=
    let ⟨_, _, hzt⟩ := (hc_ray C).1 hC
    isContractedBy_of_smul_numericalClass sS hSp h hh hC₀ hzt
  haveI : IsQuasiProjectiveVariety k sX := IsProjectiveVariety.isQuasiProjectiveVariety k sX
  have hcproj : IsProjectiveMorphism c :=
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sX sZ c hcomp
  have hZp : MMP.Mori.IsProjectiveVariety k sZ :=
    (isProjectiveVariety_iff_isProjective' k sZ).mpr ⟨inferInstance,
      MMP.isProjective_of_isProper_of_isRelativelyAmple sZ A.divisorialSheaf
        (isRelativelyAmple_of_isRelativelyAmpleCartier hA)⟩
  obtain ⟨g, hg, -⟩ := existsUnique_comp_eq_of_isContractedBy hXp hZp hSp hcproj hcomp hh hvert
  haveI : IsIso c.appTop := hcapp ⊤
  have hgS : g ≫ sS = sZ := comp_eq_of_comp_eq_of_isIso_appTop hg hh hcomp
  haveI : AlgebraicGeometry.IsProjectiveVariety k sZ := hZp
  haveI : IsQuasiProjectiveVariety k sZ := IsProjectiveVariety.isQuasiProjectiveVariety k sZ
  haveI : IsProper (g ≫ sS) := hgS ▸ inferInstance
  haveI : IsProper g := IsProper.of_comp g sS
  have hanti : (-D).HasRelativelyAmpleMultiple c :=
    hasRelativelyAmpleMultiple_neg_of_relativeCurveForm_neg sZ hXp hq hw₀ (hneg v₀ hv₀R hv₀) c
      hcomp fun C hC => (hc_ray C).1 hC
  refine ⟨g, ⟨⟨hq, hext, hneg⟩, ⟨hext.1,
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sZ sS g hgS, hg, hcapp,
      fun C hC => ?_⟩, ⟨hX, hZ, isCartierCombination_toRDivisor hq,
        ⟨hZ.1, hX.1, hcomp, inferInstance, hcapp⟩, ?_,
        relativePicardNumber_eq_one_of_forall_isContractedBy sX c C₀
          ((hc_ray C₀).2 ⟨1, zero_le_one, one_smul _ _⟩) hw₀
          fun C hC => ((hc_ray C).1 hC).imp fun _ => And.right⟩⟩, hcproj, hgS⟩
  · rw [hc_ray C, hRC]
    exact exists_smul_relativeToAbsolute_eq_iff sX h v₀ (C.relativeClass h hC)
  · change MMP.Flips.IsRelativelyAmple c (-(QDivisor.toRDivisor D))
    rw [← map_neg]
    exact hanti.isRelativelyAmple_toRDivisor

/-- The Stein step: a Stein factorization of the morphism `Φ : X ⟶ P` defined by `mL`
supplies the data of `exists_isNegativeRelativeRayContraction_of_steinFactor`. -/
private theorem exists_steinFactor {k : Type} [Field k] {X P : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX] (M : X.CartierDivisor)
    (πP : P ⟶ Spec (.of k)) (hπ : IsProper πP) (Φ : X ⟶ P) [IsProper Φ] (hΦ : Φ ≫ πP = sX)
    (hall : ∀ (YL : Scheme.{0}) (ρ : X ⟶ YL) (τ : YL ⟶ P),
      Stacks.SteinFactorization.IsSteinFactorization Φ ρ τ →
        MMP.Mori.IsNormalVariety k (τ ≫ πP ≫ 𝟙 (Spec (.of k))) ∧
          (∀ U : YL.Opens, IsIso (ρ.app U)) ∧ IsFinite τ ∧
          ∃ (_ : IsLocallyNoetherian YL) (_ : IsNormal YL) (_ : CompactSpace YL)
            (A : Divisor YL), MMP.Flips.IsRelativelyAmpleCartier (τ ≫ πP) A ∧
            Nonempty (MMP.CartierDivisor.sheaf M ≅
              (Scheme.Modules.pullback ρ).obj A.divisorialSheaf)) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (c : X ⟶ Z) (_ : MMP.Mori.IsNormalVariety k sZ)
      (_ : c ≫ sZ = sX) (_ : IsProper c) (_ : Surjective c) (_ : IsIso c.c) (_ : IsProper sZ)
      (_ : IsLocallyNoetherian Z) (_ : IsNormal Z) (_ : CompactSpace Z)
      (_ : ∀ U : Z.Opens, IsIso (c.app U)) (A : Divisor Z),
      MMP.Flips.IsRelativelyAmpleCartier sZ A ∧
        Nonempty (MMP.CartierDivisor.sheaf M ≅
          (Scheme.Modules.pullback c).obj A.divisorialSheaf) := by
  haveI := hπ
  obtain ⟨Z, c, τ, ⟨hSt⟩, hcp, hcs, hcapp, -, hτ, -, -, -, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX (πP ≫ 𝟙 _) Φ
      (by rw [Category.comp_id, hΦ])
  obtain ⟨hZn, -, -, i1, i2, i3, A, hA, hMA⟩ := hall Z c τ hSt
  have hZn' : MMP.Mori.IsNormalVariety k (τ ≫ πP) := by
    simpa only [Category.comp_id] using hZn
  exact ⟨Z, τ ≫ πP, c, hZn', by rw [← Category.assoc, hSt.comp, hΦ], hcp, hcs,
    hSt.structureSheaf, inferInstance, i1, i2, i3, hcapp, A, hA, hMA⟩

end MMP.FourfoldProofs.MmpProjectiveLcSemiampleSupportContractsProof

end

section

/-!
# A semiample supporting divisor contracts a negative relative extremal ray

Let `h : X ⟶ S` be a morphism of normal projective varieties over an algebraically closed field
`k` of characteristic zero, `D` a `ℚ`-Cartier `ℚ`-divisor on `X`, and `R` a `D`-negative extremal
ray of the closed relative cone `NE̅(X/S)` spanned by the class of a curve `C₀ ⊆ X` contracted by
`h`. Suppose `L` is a nef Cartier divisor on `X` whose zero face `NE̅(X) ∩ L^⊥` is the image of
`R` under the natural map `N₁(X/S) → N₁(X)`, and some positive multiple `mL` is globally
generated. Then the Stein factorization `c : X ⟶ Z` of the morphism defined by `|mL|` is a
projective contraction of `R` over `S`: there is a projective `g : Z ⟶ S` with `c ≫ g = h`,
`Z` is a normal variety, `c_* 𝒪_X = 𝒪_Z`, a curve contracted by `h` is contracted by `c`
exactly when its class lies in `R`, `ρ(X/Z) = 1` and `-D` is `c`-ample.

## Main results

* `MMP.Fourfold.exists_isNegativeRelativeRayContraction_of_isSupportingDivisor`: the statement
  above.

## Implementation notes

The ray is generated by an actual curve: `R = ℝ_{≥0} [C₀]` for a proper curve `C₀` contracted by
`h`. The zero face is spelled with `MMP.Mori.IsSupportingDivisor` applied to the image of `R`
under `MMP.Mori.relativeToAbsolute`, and global generation of `𝒪_X(mL)` is Mathlib's
`SheafOfModules.IsGeneratedByGlobalSections`. The conclusion is
`MMP.Fourfold.IsNegativeRelativeRayContraction` together with projectivity of `c` and the
compatibility `g ≫ s_S = s_Z` of the structure morphisms.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3, 3.25
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

open MMP.FourfoldProofs.MmpProjectiveLcSemiampleSupportContractsProof in
/-- **A semiample supporting divisor contracts a negative relative extremal ray.** Let
`h : X ⟶ S` be a morphism of normal projective varieties over an algebraically closed field of
characteristic zero, `D` a `ℚ`-Cartier `ℚ`-divisor on `X` and `R` a `D`-negative extremal ray of
`NE̅(X/S)` spanned by the class of a curve contracted by `h`. If `L` is a nef Cartier divisor on
`X` with `NE̅(X) ∩ L^⊥` equal to the image of `R` in `N₁(X)` and `𝒪_X(mL)` is globally generated
for some `m > 0`, then there are a normal variety `Z`, a projective contraction `c : X ⟶ Z` and
a projective `g : Z ⟶ S` with `c ≫ g = h` such that `c` is the contraction of `R` over `S`,
`ρ(X/Z) = 1` and `-D` is `c`-ample. -/
@[mmp "lem_mmp_projective_lc_semiample_support_contracts"]
public theorem exists_isNegativeRelativeRayContraction_of_isSupportingDivisor
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X S : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (_hS : IsNormalVariety k sS) (hSp : MMP.Mori.IsProjectiveVariety k sS)
    (h : X ⟶ S) (hh : h ≫ sS = sX)
    {D : QDivisor X} {R : Set (RelativeNumericalCurveClasses sX h)}
    (hR : IsNegativeRelativeExtremalRayOf sX h D R)
    (hRC : ∃ (C₀ : ProperCurve sX) (hC₀ : C₀.IsContractedBy h),
      R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • C₀.relativeClass h hC₀ = w})
    {L : X.CartierDivisor} (hL : IsSupportingDivisor k sX (relativeToAbsolute sX h '' R) L)
    (hLm : ∃ m : ℕ, 0 < m ∧
      SheafOfModules.IsGeneratedByGlobalSections (MMP.CartierDivisor.sheaf ((m : ℤ) • L))) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (c : X ⟶ Z) (g : Z ⟶ S),
      IsNegativeRelativeRayContraction sX h sZ D R c g ∧ IsProjectiveMorphism c ∧
        g ≫ sS = sZ := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
  haveI : AlgebraicGeometry.IsVariety k sX := hXp.toIsVariety
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hXp.isProjective
  obtain ⟨m, hm, hgg⟩ := hLm
  obtain ⟨C₀, hC₀, hRC⟩ := hRC
  set M : X.CartierDivisor := (m : ℤ) • L
  haveI : AlgebraicGeometry.IsVariety k (𝟙 (Spec (.of k))) := ⟨⟩
  have hfree : IsRelativelyFreeCartier sX M :=
    isRelativelyFreeCartier_of_isGeneratedByGlobalSections_add_pullback (sY := 𝟙 _)
      (Category.comp_id sX) M (isPullback_zero sX) (by rwa [add_zero])
  have key := IsRelativelyFreeCartier.steinFactor_isRelativelyAmpleCartier sX (𝟙 _) hX
    (inferInstance : AlgebraicGeometry.IsVariety k (𝟙 (Spec (.of k)))) sX
    (Category.comp_id sX) M hfree
  dsimp only at key
  obtain ⟨⟨Φ, hΦ, e, hdef⟩, hall⟩ := key
  obtain ⟨hΦp, hall⟩ := hall Φ hΦ e hdef
  haveI : ((Scheme.Modules.pushforward sX).obj
      (MMP.CartierDivisor.sheaf M)).IsQuasicoherent :=
    ProperCoherentFiniteType.isQuasicoherent_pushforward sX _ inferInstance
  haveI : ((Scheme.Modules.pushforward sX).obj
      (MMP.CartierDivisor.sheaf M)).IsFiniteType :=
    (AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward sX
      (MMP.CartierDivisor.sheaf M)).isFiniteType
  obtain ⟨Z, sZ, c, hZ, hcomp, _, _, _, _, _, _, _, hcapp, A, hA, ⟨eM⟩⟩ :=
    exists_steinFactor sX M _ (isProper_relativeProj_toBase _) Φ hΦ fun YL ρ τ hSt => by
      obtain ⟨h1, h2, h3, i1, i2, i3, A, hA, -, hM⟩ := hall YL ρ τ hSt
      exact ⟨h1, h2, h3, i1, i2, i3, A, hA, hM⟩
  exact ⟨Z, sZ, c, exists_isNegativeRelativeRayContraction_of_steinFactor sX sS sZ hX hXp hSp h
    hh hR C₀ hC₀ hRC hL c hZ hcomp hcapp A hA m hm eM⟩

end MMP.Fourfold

end
