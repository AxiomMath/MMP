module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering

/-!
# Removing the reduced part away from a flip

Let `(U, Δ)` be a projective `ℚ`-factorial dlt fourfold pair with rational boundary, `R` a
`(K_U + Δ)`-negative extremal ray of `NE̅(U)`, `f : U ⟶ V` a small contraction of `R` onto a
normal projective variety with `ρ(U/V) = 1`, and `f⁺ : U⁺ ⟶ V` a `(K_U + Δ)`-flip of `f` such that
`(U⁺, Δ⁺)` is again a projective `ℚ`-factorial dlt pair, `Δ⁺` the strict transform of `Δ`. If the
exceptional loci `Ex(f)` and `Ex(f⁺)` are disjoint from `⌊Δ⌋` and `⌊Δ⁺⌋` respectively, then
removing the reduced parts turns the flip into a permitted step of the klt pair
`(U, Δ - ⌊Δ⌋)`: the strict transform of `Δ - ⌊Δ⌋` is `Δ⁺ - ⌊Δ⁺⌋`, and
`U ⟶ V ⟵ U⁺` is a permitted step for `(U, Δ - ⌊Δ⌋)` and `R`.

## Main results

* `MMP.Fourfold.IsFlipOf.isPermittedStep_sub_roundDown`: away from the reduced parts, a flip of a
  dlt pair is a permitted step of `(U, Δ - ⌊Δ⌋)`.
* `MMP.Fourfold.relativePicardNumberN1_eq_zero`: an isomorphism has relative Picard number zero.
* `MMP.Fourfold.exists_properCurve_isContractedBy`: a birational contraction of a ray with
  `ρ(X/Z) = 1` contracts a proper curve.
* `MMP.Fourfold.isNegativeExtremalRayOf_of_hasRelativelyAmpleMultiple_neg`: if `-D'` is ample
  over the contraction of an extremal ray `R`, then `R` is `D'`-negative.

## Implementation notes

* `⌊Δ⌋` is `MMP.Mori.DivisorWithCoeffs.roundDown Δ`, a Weil divisor, regarded as a `ℚ`-divisor
  through `MMP.Mori.Divisor.toQDivisor`; its support is `MMP.Mori.DivisorWithCoeffs.supp`.
* The exceptional locus is `MMP.Mori.exceptionalSet`, the one in `MMP.Fourfold.IsSmallMorphism`.
* Strict transforms along `U ⟶ V ⟵ U⁺` are `MMP.Mori.flipTransform f f⁺`; the canonical divisor
  of `U⁺` is the strict transform of that of `U`, as in `MMP.Fourfold.IsPermittedStep`.
* The base field is any algebraically closed field of characteristic zero; the source works
  over `ℂ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-! ### Strict transforms -/

section FlipTransform

variable {k : Type} [Field k] {U V U' : Scheme.{0}} [IsIntegral U] [IsLocallyNoetherian U]
  [IsNormal U] [IsIntegral U'] [IsLocallyNoetherian U'] [IsNormal U']
  {sU' : U' ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} {f : U ⟶ V} {fp : U' ⟶ V}

/-- Along `U ⟶ V ⟵ U⁺`, with `f` proper birational surjective and `f⁺` small, every prime
divisor `P` of `U⁺` has a prime divisor `P⁻` of `U` whose coefficient in any divisor is the
coefficient of `P` in its strict transform. -/
private theorem exists_forall_coeff_flipTransform_eq [IsProper f] (hfb : IsBirationalMorphism f)
    (hsurj : Function.Surjective f) (hfp : IsSmallMorphism sU' sV fp)
    (P : MMP.Mori.PrimeDivisor U') :
    ∃ Pm : MMP.Mori.PrimeDivisor U, ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R U),
      (flipTransform f fp D).coeff P = D.coeff Pm := by
  obtain ⟨x, hx⟩ := hsurj (fp P.genericPoint)
  obtain ⟨Pm, -, hPm⟩ := exists_eq_genericPoint_flipTransform_apply hfb hfp P x hx
  exact ⟨Pm, hPm⟩

/-- The strict transform commutes with taking the reduced part. -/
private theorem flipTransform_sub_roundDown [IsProper f] (hfb : IsBirationalMorphism f)
    (hsurj : Function.Surjective f) (hfp : IsSmallMorphism sU' sV fp) (Δ : QDivisor U) :
    flipTransform f fp (Δ - Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ)) =
      flipTransform f fp Δ -
        Divisor.toQDivisor (DivisorWithCoeffs.roundDown (flipTransform f fp Δ)) := by
  ext P
  obtain ⟨Pm, hPm⟩ := exists_forall_coeff_flipTransform_eq hfb hsurj hfp P
  simp [hPm]

/-- The strict transform commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem flipTransform_toQDivisor [IsProper f] (hfb : IsBirationalMorphism f)
    (hsurj : Function.Surjective f) (hfp : IsSmallMorphism sU' sV fp) (K : Divisor U) :
    flipTransform f fp (Divisor.toQDivisor K) = Divisor.toQDivisor (flipTransform f fp K) := by
  ext P
  obtain ⟨Pm, hPm⟩ := exists_forall_coeff_flipTransform_eq hfb hsurj hfp P
  simp [hPm]

end FlipTransform

/-! ### Lowering the reduced part -/

/-- Removing the reduced part of the boundary of a `ℚ`-factorial dlt pair leaves a dlt pair. -/
private theorem isDltPair_sub_roundDown {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsQFactorial sX) {Δ : QDivisor X} (h : MMP.Intersection.IsDltPair sX Δ) :
    MMP.Intersection.IsDltPair sX (Δ - Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ)) := by
  have hcoeff : ∀ P, (Δ - Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ)) P =
      Δ P - ⌊Δ P⌋ := fun P => by simp [← DivisorWithCoeffs.coeff_apply]
  refine MMP.Intersection.IsDltPair.of_le sX h (fun P => ?_) (fun P => ?_)
    (isQCartier_of_isQFactorial sX hX _)
  · rw [Finsupp.coe_zero, Pi.zero_apply, hcoeff]
    exact sub_nonneg.mpr (Int.floor_le _)
  · rw [hcoeff]
    have : (0 : ℚ) ≤ ⌊Δ P⌋ := by exact_mod_cast Int.floor_nonneg.mpr (h.1.2.1 P)
    linarith

/-! ### Divisors away from the exceptional set are principal over the base -/

section LocalEquation

variable {X Y : Scheme.{0}}

/-- A morphism is injective over its biregular locus. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {f : X ⟶ Y} {x z : X}
    (hx : f x ∈ biregularLocus f) (h : f z = f x) : z = x := by
  haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  have key : ∀ a : (f ⁻¹ᵁ biregularLocus f).toScheme,
      (biregularLocus f).ι ((f ∣_ biregularLocus f) a) = f ((f ⁻¹ᵁ biregularLocus f).ι a) :=
    fun a => by rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hz : z ∈ f ⁻¹ᵁ biregularLocus f := show f z ∈ biregularLocus f from h ▸ hx
  let a : (f ⁻¹ᵁ biregularLocus f).toScheme := ⟨z, hz⟩
  let b : (f ⁻¹ᵁ biregularLocus f).toScheme := ⟨x, hx⟩
  have hab : a = b := (f ∣_ biregularLocus f).isOpenEmbedding.injective <|
    (biregularLocus f).ι.isOpenEmbedding.injective (by rw [key, key]; exact h)
  exact congrArg (fun c => (f ⁻¹ᵁ biregularLocus f).ι c) hab

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A Cartier divisor `B` whose components lie in a closed set `S` disjoint from `Ex(f)` is
principal over a neighbourhood of every point of the base of a closed morphism `f`. -/
private theorem exists_isLocalEquation_preimage_of_disjoint (f : X ⟶ Y) (hf : IsClosedMap f)
    {B : Divisor X} (hB : B.IsCartier) {S : Set X} (hS : IsClosed S)
    (hBS : ∀ E : MMP.Mori.PrimeDivisor X, B.coeff E ≠ 0 → (E.support : Set X) ⊆ S)
    (hdisj : Disjoint (exceptionalSet f : Set X) S) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ ψ : (RationalFunctions X)ˣ, B.IsLocalEquation (f ⁻¹ᵁ U) ψ := by
  by_cases hy : ∃ x ∈ S, f x = y
  · obtain ⟨x, hxS, rfl⟩ := hy
    have hxb : f x ∈ biregularLocus f := by
      by_contra hn
      exact Set.disjoint_left.mp hdisj (mem_exceptionalSet.mpr hn) hxS
    obtain ⟨W, hxW, φ, hφ⟩ := hB x
    refine ⟨⟨(f '' (W : Set X)ᶜ)ᶜ, (hf _ W.isOpen.isClosed_compl).isOpen_compl⟩, ?_, φ,
      hφ.mono ?_⟩
    · rintro ⟨z, hz, hzx⟩
      exact hz (eq_of_map_eq_of_mem_biregularLocus hxb hzx ▸ hxW)
    · intro z hz
      by_contra hzW
      exact hz ⟨z, hzW, rfl⟩
  · push Not at hy
    refine ⟨⟨(f '' S)ᶜ, (hf _ hS).isOpen_compl⟩, fun ⟨x, hx, hxy⟩ => hy x hx hxy, 1,
      fun E ⟨z, hzE, hzU⟩ => ?_⟩
    rw [PrimeDivisor.ord_one]
    by_contra hne
    exact hzU ⟨z, hBS E hne hzE, rfl⟩

end LocalEquation

/-! ### Twisting a relatively ample divisor by a divisor away from the exceptional set -/

section Twist

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- `𝒪_X(nL) ≅ 𝒪_X(L)^{⊗ n}` for a Cartier divisor `L` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {L : Divisor X} (hL : L.IsCartier) (n : ℕ)
    (hn : 1 ≤ n) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    Nonempty ((n • L).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule X L.divisorialSheaf (n : ℤ)) := by
  have := hL.isInvertibleModule_divisorialSheaf
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_nsmul L)) ≪≫
      (Stacks.Ample.tensorPowModuleOneIso X _).symm⟩
  | succ n hn ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul L n)) ≪≫
      ((hL.nsmul n).divisorialSheafTensorIso hL).symm ≪≫ ?_ ≪≫
      Stacks.Ample.tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; rfl)⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso X _).symm

/-- A positive multiple of an `f`-ample Cartier divisor is `f`-ample. -/
private theorem isRelativelyAmple_nsmul {f : X ⟶ Y} {L : Divisor X} (hL : L.IsCartier)
    (h : L.IsRelativelyAmple f hL) (n : ℕ) (hn : 0 < n) :
    (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  have := hL.isInvertibleModule_divisorialSheaf
  have := (hL.nsmul n).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  obtain ⟨e0⟩ := nonempty_divisorialSheaf_nsmul_iso hL n hn
  have := Stacks.Ample.isInvertibleModule_tensorPowModule (f ⁻¹ᵁ V).toScheme
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
      L.divisorialSheaf) (n : ℤ)
  let e := (RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e0 ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι _ n
  rw [Stacks.RelativeVeryAmple.isAmple_congr _ _ e]
  exact (Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn).1 hA

/-- **Twisting by a divisor away from the exceptional set.** On a `ℚ`-factorial variety, if `D`
is `f`-ample for a closed quasi-compact `f` and the support of the divisor `F` misses `Ex(f)`,
then `D + cF` is `f`-ample for every `c ∈ ℤ`. -/
private theorem hasRelativelyAmpleMultiple_add_zsmul {k : Type} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsQFactorial sX) (f : X ⟶ Y) [QuasiCompact f]
    (hf : IsClosedMap f) {D : QDivisor X} (hD : D.HasRelativelyAmpleMultiple f) (F : Divisor X)
    (hdisj : Disjoint (exceptionalSet f : Set X) F.supp) (c : ℤ) :
    (D + c • Divisor.toQDivisor F).HasRelativelyAmpleMultiple f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := hD
  obtain ⟨N, hN, hNF⟩ := hX.2 F
  set B : Divisor X := (c * m) • ((N : ℤ) • F) with hBdef
  have hBc : B.IsCartier := hNF.zsmul _
  have hBS : ∀ E : MMP.Mori.PrimeDivisor X, B.coeff E ≠ 0 → (E.support : Set X) ⊆ F.supp :=
    fun E hE => DivisorWithCoeffs.support_subset_supp fun h0 => hE (by simp [hBdef, h0])
  have hamp' := MMP.Threefold.Resolution.isRelativelyAmple_add_of_isLocalEquation_preimage f
    (hL.nsmul N) (isRelativelyAmple_nsmul hL hamp N hN) hBc
    (exists_isLocalEquation_preimage_of_disjoint f hf hBc (DivisorWithCoeffs.isClosed_supp F)
      hBS hdisj)
  refine ⟨N * m, Nat.mul_pos hN hm, N • L + B, (hL.nsmul N).add hBc, ?_, hamp'⟩
  ext P
  have hP := congrArg (DivisorWithCoeffs.coeff · P) hLD
  simp only [hBdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
    Divisor.coeff_toQDivisor, smul_eq_mul, nsmul_eq_mul, zsmul_eq_mul] at hP ⊢
  push_cast at hP ⊢
  rw [hP]
  ring

end Twist

/-! ### A curve contracted by `f` and the negativity of the ray -/

section Ray

section Picard

variable {k : Type} [Field k] {X Z : Scheme.{0}}

/-- For an isomorphism `f`, `f^* N¹(Z)_ℝ` is all of `N¹(X)_ℝ`. -/
theorem pullbackNumericalClasses_eq_top (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) [IsIso f] :
    pullbackNumericalClasses sX f = ⊤ := by
  refine eq_top_iff.mpr fun d _ => ?_
  obtain ⟨D, rfl⟩ := Submodule.mkQ_surjective _ d
  change numericalDivisorClass sX D ∈ _
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ =>
    rw [map_add]
    exact Submodule.add_mem _ (h₁ Submodule.mem_top) (h₂ Submodule.mem_top)
  | single E c =>
    have e : (Finsupp.single E c : KCartierDivisor ℝ X) = c • KCartierDivisor.ofCartier ℝ E := by
      simp [KCartierDivisor.ofCartier]
    rw [e, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨E, (Scheme.Modules.pullback (inv f)).obj (MMP.CartierDivisor.sheaf E),
      inferInstance, ⟨?_⟩, rfl⟩
    exact ((Scheme.Modules.pullbackId X).app _).symm ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id f)).symm.app _ ≪≫
      ((Scheme.Modules.pullbackComp f (inv f)).app _).symm

/-- An isomorphism has relative Picard number zero. -/
theorem relativePicardNumberN1_eq_zero (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) [IsIso f] :
    relativePicardNumberN1 sX f = 0 := by
  rw [relativePicardNumberN1, pullbackNumericalClasses_eq_top]
  simp

end Picard

section Contracted

variable {k : Type} [Field k] {X Z : Scheme.{0}}

/-- At a point where a morphism locally of finite type from a locally noetherian scheme is not
quasi-finite, its fibre has positive Krull dimension. -/
theorem topologicalKrullDim_preimage_pos_of_notMem_quasiFiniteLocus [IsLocallyNoetherian X]
    (f : X ⟶ Z) [LocallyOfFiniteType f] {x : X} (hx : x ∉ f.quasiFiniteLocus) :
    0 < topologicalKrullDim (f ⁻¹' {f x}) := by
  by_contra! hle
  apply hx
  change f.QuasiFiniteAt x
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    inferInstanceAs (IsLocallyNoetherian
      (CategoryTheory.Limits.pullback f (Z.fromSpecResidueField (f x))))
  have : IsLocallyArtinian (f.fiber (f x)) := IsLocallyArtinian.of_topologicalKrullDim_le_zero
    ((IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo (f x)).isHomeomorph).trans_le hle)
  have : DiscreteTopology (f.fiber (f x)) :=
    (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mp inferInstance).2
  exact isOpen_discrete _

/-- A proper morphism from a proper `k`-scheme which is not locally quasi-finite contracts a proper
curve. -/
theorem exists_properCurve_isContractedBy_of_not_locallyQuasiFinite
    {sX : X ⟶ Spec (.of k)} [IsProper sX] [IsLocallyNoetherian X] {f : X ⟶ Z} [IsProper f]
    (h : ¬ LocallyQuasiFinite f) : ∃ C : ProperCurve sX, C.IsContractedBy f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff] at h
  have hne : ((f.quasiFiniteLocus : Set X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro h'
    exact h (SetLike.coe_injective (h'.trans TopologicalSpace.Opens.coe_top.symm))
  obtain ⟨x, hx, hxc⟩ := f.quasiFiniteLocus.isOpen.isClosed_compl.exists_closed_singleton hne
  have hy : IsClosed ({f x} : Set Z) := by
    simpa [Set.image_singleton] using f.isClosedMap _ hxc
  have hF : IsClosed (f ⁻¹' {f x}) := hy.preimage f.continuous
  have hdim := topologicalKrullDim_preimage_pos_of_notMem_quasiFiniteLocus f hx
  rw [topologicalKrullDim, Order.krullDim_pos_iff] at hdim
  obtain ⟨A, B, hAB⟩ := hdim
  have hBirr : IsIrreducible (Subtype.val '' (B : Set (f ⁻¹' {f x}))) :=
    B.isIrreducible.image _ continuous_subtype_val.continuousOn
  set η := hBirr.genericPoint
  have hη : closure ({η} : Set X) = closure (Subtype.val '' (B : Set (f ⁻¹' {f x}))) :=
    hBirr.isGenericPoint_genericPoint_closure
  have hBF : closure (Subtype.val '' (B : Set (f ⁻¹' {f x}))) ⊆ f ⁻¹' {f x} :=
    closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact z.2) hF
  have hAcl : IsClosed (Subtype.val '' (A : Set (f ⁻¹' {f x}))) :=
    hF.isClosedEmbedding_subtypeVal.isClosedMap _ A.isClosed
  have hAne : (Subtype.val '' (A : Set (f ⁻¹' {f x}))).Nonempty :=
    A.isIrreducible.nonempty.image _
  obtain ⟨x₀, hx₀A, hx₀⟩ := hAcl.exists_closed_singleton hAne
  have hx₀B : x₀ ∈ closure (Subtype.val '' (B : Set (f ⁻¹' {f x}))) :=
    subset_closure (Set.image_mono hAB.le hx₀A)
  have hηx₀ : η ⤳ x₀ := specializes_iff_mem_closure.mpr (hη ▸ hx₀B)
  have hηne : η ∉ ({x₀} : Set X) := by
    intro hη₀
    rw [Set.mem_singleton_iff] at hη₀
    apply hAB.not_ge
    intro z hz
    have hz' : z.1 ∈ closure ({η} : Set X) := hη ▸ subset_closure ⟨z, hz, rfl⟩
    rw [hη₀, hx₀.closure_eq, Set.mem_singleton_iff] at hz'
    obtain ⟨a, ha, ha'⟩ := hx₀A
    have : z = a := Subtype.ext (hz'.trans ha'.symm)
    exact this ▸ ha
  obtain ⟨y', hηy', -, -, hcurve⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sX hηx₀ hx₀
    hx₀ (Set.mem_singleton _) hηne
  have hsub : closure ({y'} : Set X) ⊆ f ⁻¹' {f x} := by
    refine (closure_minimal (Set.singleton_subset_iff.mpr ?_) isClosed_closure).trans hBF
    exact hη ▸ specializes_iff_mem_closure.mp hηy'
  refine ⟨⟨y', hcurve⟩, fun z hz => ?_⟩
  have h1 : f z = f x := hsub hz
  have h2 : f y' = f x := hsub (subset_closure rfl)
  rw [h1, h2]

/-- If `f` is a birational contraction of a ray with `ρ(X/Z) = 1` on a projective variety `X`,
then `f` contracts some proper curve. -/
theorem exists_properCurve_isContractedBy {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] (hX : MMP.Mori.IsProjectiveVariety k sX)
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z} (hc : IsContractionOfRay sX sZ R f)
    (hb : IsBirationalMorphism f) (hρ : relativePicardNumberN1 sX f = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  by_contra hno
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  haveI : LocallyQuasiFinite f := Classical.byContradiction fun h =>
    hno (exists_properCurve_isContractedBy_of_not_locallyQuasiFinite h)
  haveI : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  have hZ := hc.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsIso f := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).2 inferInstance
  exact zero_ne_one ((relativePicardNumberN1_eq_zero sX f).symm.trans hρ)

end Contracted

variable {k : Type} [Field k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- `D · C < 0` for a curve `C` contracted by `f` when `-D` is `f`-ample. -/
theorem intersectionNumber_neg_of_isContractedBy {f : X ⟶ Z} {D : QDivisor X}
    (hamp : (-D).HasRelativelyAmpleMultiple f) (C : ProperCurve sX) (hC : C.IsContractedBy f)
    (hD : D.IsQCartier) : D.intersectionNumber k sX C.ι C.dim_le hD < 0 := by
  obtain ⟨m, hm, L, hL, hLeq, hamp⟩ := hamp
  have hpos : 0 < L.degreeOn k sX C.ι C.dim_le hL := by
    haveI := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hamp C hC
  have e : Divisor.toQDivisor L = (-(m : ℚ)) • D := by
    rw [hLeq, smul_neg, neg_smul, ← Int.cast_smul_eq_zsmul ℚ]
    rfl
  have hq : ((-(m : ℚ)) • D).IsQCartier := e ▸ QDivisor.isQCartier_toQDivisor hL
  have h1 := QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le L hL
    (QDivisor.isQCartier_toQDivisor hL)
  rw [MMP.Fourfold.intersectionNumber_congr sX C.ι C.dim_le _ hq e,
    MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le _ hD _ hq] at h1
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hpos' : (0 : ℚ) < (L.degreeOn k sX C.ι C.dim_le hL : ℚ) := by exact_mod_cast hpos
  nlinarith

/-- **Negativity transfers along the contraction.** If `f` is the contraction of an extremal ray
`R`, contracts a curve `C`, and `-D'` is `f`-ample, then `R` is `D'`-negative. -/
theorem isNegativeExtremalRayOf_of_hasRelativelyAmpleMultiple_neg (hX : IsQFactorial sX)
    {D D' : QDivisor X} {R : Set (NumericalCurveClasses sX)} (hR : IsNegativeExtremalRayOf sX D R)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) (hamp : (-D').HasRelativelyAmpleMultiple f) :
    IsNegativeExtremalRayOf sX D' R := by
  obtain ⟨-, hray, -⟩ := hR
  have hD' := isQCartier_of_isQFactorial sX hX D'
  refine ⟨hD', hray, fun u hu hu0 => ?_⟩
  obtain ⟨v, -, hRv⟩ := hray.2
  have hCR := (hf.isContractedBy_iff C).mp hC
  have hneg : QDivisor.curveForm sX D' hD' (OneCycle.numericalClass sX (C.cycle ℝ)) < 0 := by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    exact_mod_cast intersectionNumber_neg_of_isContractedBy hamp C hC hD'
  rw [hRv] at hCR hu
  obtain ⟨c₀, hc₀, hc₀v⟩ := hCR
  obtain ⟨c, hc, rfl⟩ := hu
  rw [← hc₀v, map_smul, smul_eq_mul] at hneg
  have hc0 : 0 < c := hc.lt_of_ne (by rintro rfl; exact hu0 (zero_smul _ _))
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg hc0 (neg_of_mul_neg_right hneg hc₀)

end Ray

/-- **Removing the reduced part away from the surgery.** Let `(U, Δ)` be a projective
`ℚ`-factorial dlt fourfold pair with canonical divisor `K`, `R` a `(K + Δ)`-negative extremal ray
of `NE̅(U)`, `f : U ⟶ V` a small contraction of `R` onto a normal projective variety with
`ρ(U/V) = 1` and `f⁺ : U⁺ ⟶ V` a `(K + Δ)`-flip of `f` such that `(U⁺, Δ⁺)`, `Δ⁺ = f⁺⁻¹_* f_* Δ`,
is a projective `ℚ`-factorial dlt pair with canonical divisor `f⁺⁻¹_* f_* K`. If
`Ex(f) ∩ ⌊Δ⌋ = ∅` and `Ex(f⁺) ∩ ⌊Δ⁺⌋ = ∅`, then the strict transform of `Δ - ⌊Δ⌋` is
`Δ⁺ - ⌊Δ⁺⌋` and `U ⟶ V ⟵ U⁺` is a permitted step for `(U, Δ - ⌊Δ⌋)` and `R`. -/
@[mmp "lem_oai4_c3_reduced_part_removal"]
theorem IsFlipOf.isPermittedStep_sub_roundDown
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {U V U' : Scheme.{0}}
    {sU : U ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} {sU' : U' ⟶ Spec (.of k)}
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    [IsIntegral U'] [CompactSpace U'] [IsLocallyNoetherian U'] [IsNormal U']
    {K : Divisor U} {Δ : QDivisor U} {R : Set (NumericalCurveClasses sU)}
    {f : U ⟶ V} {fp : U' ⟶ V}
    (h : IsProjectiveQFactorialDltPair sU K Δ) (hdim : topologicalKrullDim U = 4)
    (hR : IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Δ) R)
    (hf : IsContractionOfRay sU sV R f) (hfs : IsSmallMorphism sU sV f)
    (hV : MMP.Mori.IsProjectiveVariety k sV) (hρ : relativePicardNumberN1 sU f = 1)
    (hfp : IsFlipOf sU sV sU' (Divisor.toQDivisor K + Δ) f fp)
    (h' : IsProjectiveQFactorialDltPair sU' (flipTransform f fp K) (flipTransform f fp Δ))
    (hExc : Disjoint (exceptionalSet f : Set U) (DivisorWithCoeffs.roundDown Δ).supp)
    (hExc' : Disjoint (exceptionalSet fp : Set U')
      (DivisorWithCoeffs.roundDown (flipTransform f fp Δ)).supp) :
    flipTransform f fp (Δ - Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ)) =
        flipTransform f fp Δ -
          Divisor.toQDivisor (DivisorWithCoeffs.roundDown (flipTransform f fp Δ)) ∧
      IsPermittedStep sU sV sU' K (Δ - Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ)) R
        f fp := by
  haveI : IsProper f := hfs.isProper
  haveI : IsProper fp := hfp.isSmallMorphism_flip.isProper
  haveI : IsProper sU := isProper_of_isProjectiveMorphism _ h.isProjectiveVariety.isProjective
  have hsurj : Function.Surjective f := hf.surjective
  have hA := flipTransform_sub_roundDown hfs.isBirationalMorphism hsurj hfp.isSmallMorphism_flip Δ
  have hamp : (-(Divisor.toQDivisor K +
      (Δ - Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ)))).HasRelativelyAmpleMultiple f := by
    have := hasRelativelyAmpleMultiple_add_zsmul h.isQFactorial f f.isClosedMap
      hfp.hasRelativelyAmpleMultiple (DivisorWithCoeffs.roundDown Δ) hExc 1
    convert this using 1
    rw [one_smul]
    abel
  have hamp' : (Divisor.toQDivisor (flipTransform f fp K) +
      flipTransform f fp (Δ - Divisor.toQDivisor
        (DivisorWithCoeffs.roundDown Δ))).HasRelativelyAmpleMultiple fp := by
    have := hasRelativelyAmpleMultiple_add_zsmul h'.isQFactorial fp fp.isClosedMap
      hfp.hasRelativelyAmpleMultiple_flip (DivisorWithCoeffs.roundDown (flipTransform f fp Δ))
      hExc' (-1)
    convert this using 1
    rw [hA, map_add, flipTransform_toQDivisor hfs.isBirationalMorphism hsurj
      hfp.isSmallMorphism_flip, neg_one_smul]
    abel
  obtain ⟨C, hC⟩ := exists_properCurve_isContractedBy h.isProjectiveVariety hf
    hfs.isBirationalMorphism hρ
  exact ⟨hA,
    { isProjectiveVariety := h.isProjectiveVariety
      isLogCanonicalPair := (isDltPair_sub_roundDown h.isQFactorial h.isDltPair).1
      isCanonicalDivisor := h.isCanonicalDivisor
      isNegativeExtremalRayOf :=
        isNegativeExtremalRayOf_of_hasRelativelyAmpleMultiple_neg h.isQFactorial hR hf C hC hamp
      isContractionOfRay := hf
      isProjectiveVariety_target := hV
      relativePicardNumber_eq_one := hρ
      hasRelativelyAmpleMultiple := hamp
      isBirationalMorphism := hfs.isBirationalMorphism
      isProjectiveVariety_step := h'.isProjectiveVariety
      isSmallMorphism_step := hfp.isSmallMorphism_flip
      isProjectiveMorphism_step := hfp.isProjectiveMorphism_flip
      isLogCanonicalPair_step := hA ▸ (isDltPair_sub_roundDown h'.isQFactorial h'.isDltPair).1
      hasRelativelyAmpleMultiple_step := hamp' }⟩

end MMP.Fourfold

end
