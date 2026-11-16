module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.MMP.Flip.NullDivisorTransfer
import MMP.AlgebraicGeometry.MMP.ConeTheorem.RayLength
import MMP.AlgebraicGeometry.MMP.Contraction.RelativeContraction
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Transporting a flip between two negative adjoints

Let `X` be a normal `ℚ`-factorial projective variety and `f : X ⟶ W` a small contraction of an
extremal ray `R` of `NE̅(X)` which is negative for `K_X + C`, where `(X, C)` is a klt pair with
rational boundary. If `L` and `L'` are `ℚ`-Cartier `ℚ`-divisors which are both negative on `R`,
then every `L'`-flip of `f` is also an `L`-flip of `f`. Indeed `(L · R) = c (L' · R)` for a
positive rational `c`, the numerically trivial `L - c L'` descends along `f` by the contraction
theorem, `L ∼_ℚ c L' + f^* M`, and this relation persists on the small model `X⁺`, so the
transform `L⁺ ∼_ℚ c L'⁺ + (f⁺)^* M` is `ℚ`-Cartier and `f⁺`-ample.

## Main results

* `MMP.Fourfold.IsFlipOf.of_isNegativeExtremalRayOf`.

## Implementation notes

The source works over `ℂ`; the statement is made over any field `k`, the klt condition
`MMP.Fourfold.IsKltPair` already forcing `k` to be algebraically closed of characteristic zero.
The flip `f⁺ : X⁺ ⟶ W` is an arbitrary `MMP.Fourfold.IsFlipOf` of `f` for `L'`, and the
conclusion is the same predicate for `L`, along the same morphisms.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.7
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Relative ampleness of combinations of Cartier divisors -/

section Ample

variable {Y Z : Scheme.{0}} [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- `𝒪_Y(nL) ≅ 𝒪_Y(L)^{⊗ n}` for a Cartier divisor `L` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso_tensorPowModule {L : Divisor Y}
    (hL : L.IsCartier) (n : ℕ) (hn : 1 ≤ n) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    Nonempty ((n • L).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule Y L.divisorialSheaf (n : ℤ)) := by
  have := hL.isInvertibleModule_divisorialSheaf
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_nsmul L)) ≪≫
      (Stacks.Ample.tensorPowModuleOneIso Y _).symm⟩
  | succ n hn ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul L n)) ≪≫
      ((hL.nsmul n).divisorialSheafTensorIso hL).symm ≪≫ ?_ ≪≫
      Stacks.Ample.tensorPowModuleAddIso Y _ (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr Y _ (by push_cast; rfl)⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso Y _).symm

open RingedSpaceModuleAdjunction in
/-- A positive multiple of a `g`-ample Cartier divisor is `g`-ample. -/
private theorem isRelativelyAmple_nsmul {g : Y ⟶ Z} {L : Divisor Y} (hL : L.IsCartier)
    (h : L.IsRelativelyAmple g hL) (n : ℕ) (hn : 0 < n) :
    (n • L).IsRelativelyAmple g (hL.nsmul n) := by
  have := hL.isInvertibleModule_divisorialSheaf
  have := (hL.nsmul n).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  obtain ⟨e0⟩ := nonempty_divisorialSheaf_nsmul_iso_tensorPowModule hL n hn
  have := Stacks.Ample.isInvertibleModule_tensorPowModule (g ⁻¹ᵁ V).toScheme
    ((modulePullback (g ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L.divisorialSheaf) (n : ℤ)
  let e := (modulePullback (g ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e0 ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (g ⁻¹ᵁ V).ι _ n
  rw [Stacks.RelativeVeryAmple.isAmple_congr _ _ e]
  exact (Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn).1 hA

open RingedSpaceModuleAdjunction in
/-- Relative ampleness of a Cartier divisor only depends on its linear equivalence class. -/
private theorem isRelativelyAmple_of_linearlyEquivalent {g : Y ⟶ Z} {L L' : Divisor Y}
    (hL : L.IsCartier) (hL' : L'.IsCartier) (h : L.LinearlyEquivalent L')
    (ha : L'.IsRelativelyAmple g hL') : L.IsRelativelyAmple g hL := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := hL'.isInvertibleModule_divisorialSheaf
  have e := h.divisorialSheafIso
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := ha y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((modulePullback (g ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).mpr hA⟩

/-- **Ampleness modulo pull-backs.** Let `g : Y ⟶ Z` be a morphism of normal schemes with `Y`
integral and Noetherian, `D'` a `ℚ`-divisor with a `g`-ample Cartier multiple, `c > 0` rational
and `M` a `ℚ`-Cartier `ℚ`-divisor on `Z`. If `D - c D' ∼_ℚ g^* M`, then `D` is `ℚ`-Cartier and
has a `g`-ample Cartier multiple. -/
private theorem isQCartier_and_hasRelativelyAmpleMultiple_of_qLinearlyEquivalent [IsIntegral Y]
    [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] {g : Y ⟶ Z} {D D' : QDivisor Y}
    (hD' : D'.HasRelativelyAmpleMultiple g) {c : ℚ} (hc : 0 < c) {M : QDivisor Z}
    (hM : M.IsQCartier)
    (hgM : ∀ V : irreducibleComponents Y, g (componentGenericPoint Y V) ∉ M.supp)
    (h : (D - c • D').QLinearlyEquivalent (QDivisor.pullback M hM hgM)) :
    D.IsQCartier ∧ D.HasRelativelyAmpleMultiple g := by
  obtain ⟨m', hm', A, hAc, hA, hAamp⟩ := hD'
  obtain ⟨n, hn, φ, hφ⟩ := h
  obtain ⟨N, hN, E, hE, hEc⟩ := hM.exists_pos
  obtain ⟨E', hE', hE'pb⟩ := QDivisor.isPullback_pullback (f := g) hM hgM N hN E hE hEc
  have hE'c : E'.IsCartier := by
    rw [← hE'pb.pullback_eq hEc]
    exact hEc.isCartier_pullback g _
  set a : ℕ := c.num.natAbs with ha
  set b : ℕ := c.den with hb
  have hapos : 0 < a := by
    rw [ha]; exact Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hc.ne')
  have hac : (a : ℚ) = b * c := by
    rw [ha, hb, Nat.cast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hc.le), Rat.den_mul_eq_num]
  set T : ℕ := n * N * m' * b
  have hT : 0 < T := by positivity
  set Dint : Divisor Y := ((n * N * a : ℕ) • A + ((n * m' * b : ℕ) : ℤ) • E') +
    ((N * m' * b : ℕ) : ℤ) • principalDivisor φ
  have hDc : Dint.IsCartier :=
    ((hAc.nsmul _).add (hE'c.zsmul _)).add ((Divisor.isCartier_principalDivisor φ).zsmul _)
  have hDeq : Divisor.toQDivisor Dint = (T : ℤ) • D := by
    simp only [Dint, map_add, map_nsmul, map_zsmul, hA, hE', ← hφ]
    ext P
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_sub, smul_eq_mul, zsmul_eq_mul, nsmul_eq_mul, T]
    push_cast
    linear_combination (↑n * ↑N * ↑m' * DivisorWithCoeffs.coeff D' P) * hac
  have hBn : ∀ V : irreducibleComponents Y,
      g (componentGenericPoint Y V) ∉ (((n * m' * b : ℕ) : ℤ) • E).supp := by
    intro V hV
    refine hgM V ?_
    rwa [← Divisor.supp_toQDivisor, map_zsmul, hE, smul_smul,
      QDivisor.supp_zsmul (by positivity)] at hV
  have h1 := MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback g (hAc.nsmul _)
    (isRelativelyAmple_nsmul hAc hAamp (n * N * a) (by positivity)) (hEc.zsmul _)
    (hE'pb.zsmul hEc _ hBn) (hE'c.zsmul _)
  have hDamp : Dint.IsRelativelyAmple g hDc := by
    refine isRelativelyAmple_of_linearlyEquivalent hDc _ ⟨φ ^ (N * m' * b), ?_⟩ h1
    rw [Oai4C1.Main.principalDivisor_pow, add_sub_cancel_left, natCast_zsmul]
  exact ⟨⟨T, by exact_mod_cast hT.ne', Dint, hDeq, hDc⟩, T, hT, Dint, hDc, hDeq, hDamp⟩

end Ample

/-! ### Targets of morphisms with `ψ_* 𝒪_X = 𝒪_Z` -/

section Contraction

variable {X Z : Scheme.{0}} (ψ : X ⟶ Z) (hψ : ∀ V : Z.Opens, IsIso (ψ.app V))

include hψ

/-- If every `ψ.app V` is an isomorphism, nonempty opens have nonempty preimages. -/
private theorem nonempty_preimage_of_isIso_app (V : Z.Opens) [Nonempty V] :
    Nonempty (ψ ⁻¹ᵁ V) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hbot : ψ ⁻¹ᵁ V = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => hne.false ⟨x, hx⟩
  haveI := Scheme.component_nontrivial Z V
  haveI := hψ V
  haveI : Subsingleton Γ(X, ψ ⁻¹ᵁ V) := by rw [hbot]; infer_instance
  obtain ⟨a, b, hab⟩ := exists_pair_ne Γ(Z, V)
  exact hab ((ConcreteCategory.bijective_of_isIso (ψ.app V)).1 (Subsingleton.elim _ _))

/-- The target of a morphism from an integral scheme with `ψ_* 𝒪_X = 𝒪_Z` is integral. -/
private theorem isIntegral_of_isIso_app [IsIntegral X] : IsIntegral Z where
  nonempty := ⟨ψ (Nonempty.some inferInstance)⟩
  component_integral V _ := by
    haveI := nonempty_preimage_of_isIso_app ψ hψ V
    haveI := hψ V
    exact Function.Injective.isDomain (ψ.app V).hom
      (ConcreteCategory.bijective_of_isIso (ψ.app V)).1

/-- A morphism with `ψ_* 𝒪_X = 𝒪_Z` is dominant. -/
private theorem isDominant_of_isIso_app : IsDominant ψ := by
  refine ⟨dense_iff_inter_open.mpr fun V hV ⟨z, hz⟩ => ?_⟩
  haveI : Nonempty (⟨V, hV⟩ : Z.Opens) := ⟨⟨z, hz⟩⟩
  obtain ⟨⟨x, hx⟩⟩ := nonempty_preimage_of_isIso_app ψ hψ ⟨V, hV⟩
  exact ⟨ψ x, hx, x, rfl⟩

end Contraction

/-! ### Contractions of extremal rays over the base point -/

section Absolute

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- Every proper curve is contracted by the structure morphism. -/
private theorem isContractedBy_structure (C : ProperCurve sX) : C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

/-- Over the base point, the natural map `N₁(X / Spec k) → N₁(X)` is bijective. -/
private theorem relativeToAbsolute_bijective :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨?_, fun z => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    have hZ : Z ∈ relativeOneCycles sX sX :=
      (Finsupp.mem_supported ℝ Z).mpr fun C _ => isContractedBy_structure sX C
    exact ⟨relativeNumericalClass sX sX ⟨Z, hZ⟩,
      isNaturalRelativeMap_relativeToAbsolute sX sX ⟨Z, hZ⟩⟩

end Absolute

/-- Two contractions of the same extremal ray of `NE̅(X)` agree up to an isomorphism of their
targets over `k`. -/
private theorem exists_isIso_comp_eq_of_isContractionOfRay {k : Type} [Field k]
    {X Z Z' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsProjectiveVariety k sX)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {sZ : Z ⟶ Spec (.of k)} {sZ' : Z' ⟶ Spec (.of k)} {f : X ⟶ Z} {f' : X ⟶ Z'}
    (hf : IsContractionOfRay sX sZ R f) (hf' : IsContractionOfRay sX sZ' R f') :
    ∃ φ : Z ⟶ Z', IsIso φ ∧ f ≫ φ = f' ∧ φ ≫ sZ' = sZ := by
  have factor {W W' : Scheme.{0}} {sW : W ⟶ Spec (.of k)} {sW' : W' ⟶ Spec (.of k)} {g : X ⟶ W}
      {g' : X ⟶ W'} (hg : IsContractionOfRay sX sW R g) (hg' : IsContractionOfRay sX sW' R g') :
      ∃! h : W ⟶ W', g ≫ h = g' :=
    existsUnique_comp_eq_of_isContractionOfRay hX hg'.isProjectiveMorphism hg'.comp_eq hR
      (fun C hC => (hg'.isContractedBy_iff C).mpr hC) hg
  obtain ⟨φ, hφ, -⟩ := factor hf hf'
  obtain ⟨ψ, hψ, -⟩ := factor hf' hf
  have hφi : IsIso φ :=
    ⟨ψ, (factor hf hf).unique (by rw [← Category.assoc, hφ, hψ]) (Category.comp_id f),
      (factor hf' hf').unique (by rw [← Category.assoc, hψ, hφ]) (Category.comp_id f')⟩
  have : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
  have : IsIso f.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ f.c fun U => hf.isIso_app U.unop
  refine ⟨φ, hφi, hφ, (MMP.existsUnique_comp_eq_of_isIso_c f sX fun _ _ _ =>
    Subsingleton.elim (α := PrimeSpectrum k) _ _).unique ?_ hf.comp_eq⟩
  rw [← Category.assoc, hφ, hf'.comp_eq]

/-! ### The target of the contraction of a negative extremal ray -/

/-- A projective variety carries an ample invertible sheaf. -/
private theorem exists_isAmple {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    (hZ : MMP.Mori.IsProjectiveVariety k sZ) :
    ∃ (L : Z.Modules) (hL : Stacks.Ample.IsInvertibleModule Z L),
      letI : Stacks.Ample.IsInvertibleModule Z L := hL
      Stacks.Ample.IsAmple Z L := by
  have h := (isProjective_tfae_seven_of_exists_isAmple sZ
    ⟨Stacks.Ample.unitModule _, inferInstance,
      Stacks.Ample.isAmple_unitModule_of_isAffine _⟩).out 2 5
  exact (h.mp hZ.isProjective).2

/-- A proper morphism between projective varieties is projective. -/
private theorem isProjectiveMorphism_of_isProper {k : Type} [Field k] {V Z : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} (hV : MMP.Mori.IsProjectiveVariety k sV)
    (hZ : MMP.Mori.IsProjectiveVariety k sZ) (p : V ⟶ Z) [IsProper p] :
    IsProjectiveMorphism p := by
  have h := (isProjective_tfae_seven_of_exists_isAmple p (exists_isAmple hZ)).out 5 2
  exact h.mp ⟨inferInstance, exists_isAmple hV⟩

/-- **The target of the contraction of a negative extremal ray is projective.** Let `(X, C)` be
a projective klt pair over an algebraically closed field of characteristic zero and
`f : X ⟶ W` the contraction of a `(K + C)`-negative extremal ray `R`. Then `W` is projective. -/
private theorem isProjectiveVariety_of_isContractionOfRay {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X W : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
    {C : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ W}
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hklt : MMP.Mori.IsKltPair sX n K C)
    (hC0 : 0 ≤ C) (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + C) R)
    (hf : IsContractionOfRay sX sW R f) : MMP.Mori.IsProjectiveVariety k sW := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hXp.isProjective
  have hS : MMP.Mori.IsProjectiveVariety k (𝟙 (Spec (.of k))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr
      ⟨(MMP.Mori.isVariety_iff k _).mpr
          ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
        MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
  have hbij := relativeToAbsolute_bijective sX
  set e := LinearEquiv.ofBijective (relativeToAbsolute sX sX) hbij
  have hNimg : e '' (relativeClosedConeOfCurves sX sX : Set _) =
      (closedConeOfCurves sX : Set _) := by
    have := image_relativeClosedConeOfCurves_eq_inter_range sX (𝟙 (Spec (.of k))) sX
      (Category.comp_id sX)
    rw [hbij.2.range_eq, Set.inter_univ] at this
    exact this
  have hNpre : e.symm '' (closedConeOfCurves sX : Set _) =
      (relativeClosedConeOfCurves sX sX : Set _) := by
    rw [← hNimg, ← Set.image_comp]; simp
  obtain ⟨hD, hRay, hneg⟩ := hR
  have hFray : IsExtremalRay ℝ (relativeClosedConeOfCurves sX sX : Set _) (e ⁻¹' R) := by
    rw [← e.image_symm_eq_preimage, ← hNpre]
    exact MMP.ProgramBaseChange.isExtremalRay_image e.symm hRay
  obtain ⟨Z, ψ, g, hψ⟩ := MMP.Mori.exists_isRelativeContractionOfFace_of_isNegativeExtremalFace
    (sY := 𝟙 (Spec (.of k))) (f := sX) ⟨inferInstance, inferInstance, hXp, hS, Category.comp_id sX⟩
    hklt hC0 ⟨hFray.1, hFray.1.2.2.1, fun z hz hz0 =>
      hneg (e z) hz fun h => hz0 (e.injective (by rw [h, map_zero]))⟩
  have happ := hψ.isIso_app
  haveI : IsIntegral Z := isIntegral_of_isIso_app ψ happ
  have hgp := hψ.isProjectiveMorphism
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hgp
  have hZv : MMP.Mori.IsVariety k g := (MMP.Mori.isVariety_iff k g).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hZp : MMP.Mori.IsProjectiveVariety k g :=
    (AlgebraicGeometry.isProjectiveVariety_iff k g).mpr ⟨hZv, hgp⟩
  haveI : IsDominant ψ := isDominant_of_isIso_app ψ happ
  haveI : IsIso ψ.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ ψ.c fun U => happ U.unop
  haveI : IsProper (ψ ≫ g) := by rw [hψ.comp_eq]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ g
  have hψR : IsContractionOfRay sX g R ψ :=
    { isNormalVariety_source := hf.isNormalVariety_source
      isNormalVariety_target := ⟨hZv, MMP.Mori.isNormal_of_isIso_c g ψ hZv
        (by rw [hψ.comp_eq]; exact hXp.toIsVariety)⟩
      comp_eq := hψ.comp_eq
      isProjectiveMorphism := isProjectiveMorphism_of_isProper hXp hZp ψ
      surjective := ψ.surjective
      isIso_app := happ
      isContractedBy_iff := fun C => by
        rw [hψ.isContractedBy_iff C (isContractedBy_structure sX C)]
        change e (C.relativeClass sX _) ∈ R ↔ _
        rw [show e (C.relativeClass sX _) = OneCycle.numericalClass sX (C.cycle ℝ) from
          isNaturalRelativeMap_relativeToAbsolute sX sX _] }
  obtain ⟨φ, _, -, hφg⟩ := exists_isIso_comp_eq_of_isContractionOfRay hXp hRay hf hψR
  obtain ⟨m, i, hi, hic⟩ := hgp
  exact (AlgebraicGeometry.isProjectiveVariety_iff k sW).mpr
    ⟨hf.isNormalVariety_target.1, m, φ ≫ i, inferInstance, by rw [Category.assoc, hic, hφg]⟩

/-! ### The relative Picard number of the contraction of a ray -/

/-- **A morphism whose contracted curves span one line has relative Picard number one.** If
`C₀` is contracted by `c`, its class is nonzero, and every curve contracted by `c` has class a
multiple of that of `C₀`, then `ρ(X/Z) = 1`: the numerically `c`-trivial divisors are the kernel
of the nonzero linear form `B ↦ (B · C₀)`. -/
private theorem relativePicardNumber_eq_one_of_forall_isContractedBy {k : Type} [Field k]
    {X Z : Scheme.{0}} [IsIntegral X] (sX : X ⟶ Spec (.of k)) (c : X ⟶ Z) (C₀ : ProperCurve sX)
    (hC₀ : C₀.IsContractedBy c) (hw₀ : OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0)
    (hray : ∀ C : ProperCurve sX, C.IsContractedBy c → ∃ t : ℝ,
      t • OneCycle.numericalClass sX (C₀.cycle ℝ) = OneCycle.numericalClass sX (C.cycle ℝ)) :
    MMP.Flips.relativePicardNumber sX c = 1 := by
  set ψ : KCartierDivisor ℝ X →ₗ[ℝ] ℝ :=
    (OneCycle.intersectionPairing (sX := sX)).flip (C₀.cycle ℝ)
  have hψ (B) : ψ B = (C₀.cycle ℝ).intersectionNumber B := rfl
  have hker : MMP.Flips.relativeNumericallyTrivialDivisors sX c = LinearMap.ker ψ := by
    ext B
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors, LinearMap.mem_ker, hψ]
    refine ⟨fun hB => hB C₀ hC₀, fun hB C hC => ?_⟩
    obtain ⟨t, hzt⟩ := hray C hC
    rw [← NumericalCurveClasses.intersectionNumber_numericalClass, ← hzt, map_smul,
      NumericalCurveClasses.intersectionNumber_numericalClass, hB, smul_zero]
  have hdeg (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
      NumericalCurveClasses.degree sX L (OneCycle.numericalClass sX (C₀.cycle ℝ)) =
        (C₀.degree k L : ℝ) := by
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_apply, ProperCurve.cycle,
      Finsupp.sum_single_index (by simp), one_mul]
  -- `ψ ≠ 0`: the class of `C₀` is detected by an invertible sheaf, i.e. a Cartier divisor
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, ψ B₀ ≠ 0 := by
    have hnt : C₀.cycle ℝ ∉ OneCycle.numericallyTrivial sX := fun hmem =>
      hw₀ ((Submodule.Quotient.mk_eq_zero _).mpr hmem)
    rw [OneCycle.mem_numericallyTrivial] at hnt
    push Not at hnt
    obtain ⟨L', hL', hdeg'⟩ := hnt
    obtain ⟨E', ⟨e'⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L'
    refine ⟨KCartierDivisor.ofCartier ℝ E', ?_⟩
    rw [hψ, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
      ← NumericalCurveClasses.degree_numericalClass, hdeg]
    rw [← NumericalCurveClasses.degree_numericalClass, hdeg] at hdeg'
    rwa [ProperCurve.degree, ← degreeOn_eq_of_iso k sX C₀.ι C₀.dim_le e']
  have hsurj : Function.Surjective ψ := fun y =>
    ⟨(y / ψ B₀) • B₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hB₀]⟩
  have hrank :=
    ((Submodule.quotEquivOfEq _ _ hker).trans (ψ.quotKerEquivOfSurjective hsurj)).lift_rank_eq
  rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at hrank
  rw [MMP.Flips.relativePicardNumber, hrank, map_one]

/-! ### Two divisors negative on the same ray -/

section Ratio

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- A `ℚ`-divisor negative on the extremal ray `R` has negative degree on every curve whose
nonzero class lies in `R`. -/
private theorem intersectionNumber_neg_of_isNegativeExtremalRayOf
    {R : Set (NumericalCurveClasses sX)} {D : QDivisor X} (hD : IsNegativeExtremalRayOf sX D R)
    (T : ProperCurve sX) (hTR : OneCycle.numericalClass sX (T.cycle ℝ) ∈ R)
    (hT0 : OneCycle.numericalClass sX (T.cycle ℝ) ≠ 0) :
    D.intersectionNumber k sX T.ι T.dim_le hD.1 < 0 := by
  have := hD.2.2 _ hTR hT0
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at this
  exact_mod_cast this

/-- **Two negative divisors on a ray differ by a numerically trivial one, up to scaling.** On a
`ℚ`-factorial `X`, let `L`, `L'` be negative on the ray `R` spanned by the nonzero class of a
curve `T`, and let every curve contracted by `f` have class a multiple of `[T]`. Then
`c = (L · T) / (L' · T)` is a positive rational and `L - c L'` is numerically `f`-trivial. -/
private theorem exists_pos_curveForm_sub_smul_eq_zero (hXQ : IsQFactorial sX) {S : Scheme.{0}}
    {f : X ⟶ S} {R : Set (NumericalCurveClasses sX)} {L L' : QDivisor X}
    (hL : IsNegativeExtremalRayOf sX L R) (hL' : IsNegativeExtremalRayOf sX L' R)
    (T : ProperCurve sX) (hTR : OneCycle.numericalClass sX (T.cycle ℝ) ∈ R)
    (hT0 : OneCycle.numericalClass sX (T.cycle ℝ) ≠ 0)
    (hray : ∀ A : ProperCurve sX, A.IsContractedBy f → ∃ t : ℝ,
      t • OneCycle.numericalClass sX (T.cycle ℝ) = OneCycle.numericalClass sX (A.cycle ℝ)) :
    ∃ c : ℚ, 0 < c ∧ ∀ A : ProperCurve sX, A.IsContractedBy f →
      QDivisor.curveForm sX (L - c • L') (isQCartier_of_isQFactorial sX hXQ _)
        (OneCycle.numericalClass sX (A.cycle ℝ)) = 0 := by
  have hQ := isQCartier_of_isQFactorial sX hXQ
  have ha := intersectionNumber_neg_of_isNegativeExtremalRayOf hL T hTR hT0
  have ha' := intersectionNumber_neg_of_isNegativeExtremalRayOf hL' T hTR hT0
  set c := L.intersectionNumber k sX T.ι T.dim_le hL.1 /
    L'.intersectionNumber k sX T.ι T.dim_le hL'.1
  refine ⟨c, div_pos_of_neg_of_neg ha ha', fun A hA => ?_⟩
  obtain ⟨t, ht⟩ := hray A hA
  rw [← ht, map_smul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.Fourfold.intersectionNumber_congr sX T.ι T.dim_le (hQ _) (hQ _)
      (D' := L + (-c) • L') (by rw [neg_smul, sub_eq_add_neg]),
    QDivisor.intersectionNumber_add' k sX T.ι T.dim_le L _ hL.1 (hQ _) (hQ _),
    MMP.Fourfold.intersectionNumber_smul sX T.ι T.dim_le L' hL'.1 (-c) (hQ _), neg_mul,
    div_mul_cancel₀ _ ha'.ne, add_neg_cancel]
  simp

/-- A curve contracted by `f` has nonzero numerical class when some `ℚ`-Cartier `ℚ`-divisor has
an `f`-ample multiple. -/
private theorem numericalClass_ne_zero_of_hasRelativelyAmpleMultiple {S : Scheme.{0}}
    {f : X ⟶ S} {D : QDivisor X} (hD : D.IsQCartier) (ha : D.HasRelativelyAmpleMultiple f)
    (A : ProperCurve sX) (hA : A.IsContractedBy f) :
    OneCycle.numericalClass sX (A.cycle ℝ) ≠ 0 := fun h0 => by
  have hpos := MMP.Fourfold.Oai4C1.TwoEnds.intersectionNumber_pos_of_hasRelativelyAmpleMultiple
    sX hD ha A hA
  have := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX D hD A
  rw [h0, map_zero] at this
  have : (0 : ℝ) < (D.intersectionNumber k sX A.ι A.dim_le hD : ℝ) := by exact_mod_cast hpos
  linarith

end Ratio

/-- **Transporting a flip between two negative adjoints.** Let `X` be a normal `ℚ`-factorial
projective variety with canonical divisor `K`, `(X, C)` a klt pair with `ℚ`-boundary `C`, `R` a
`(K + C)`-negative extremal ray of `NE̅(X)` and `f : X ⟶ W` its contraction. If
`L`, `L'` are `ℚ`-Cartier `ℚ`-divisors negative on `R`, then every `L'`-flip `f⁺ : X⁺ ⟶ W` of `f`
is an `L`-flip of `f`. -/
@[mmp "lem_fourfold_projective_negative_adjoint_flip_transfer"]
public theorem IsFlipOf.of_isNegativeExtremalRayOf {k : Type} [Field k]
    {X W X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hXQ : IsQFactorial sX)
    {K : Divisor X} {C : QDivisor X} (hC : IsKltPair sX C)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + C) R)
    {f : X ⟶ W} (hf : IsContractionOfRay sX sW R f)
    {L L' : QDivisor X} (hL : IsNegativeExtremalRayOf sX L R)
    (hL' : IsNegativeExtremalRayOf sX L' R)
    {fp : X' ⟶ W} (hflip : IsFlipOf sX sW sX' L' f fp) :
    IsFlipOf sX sW sX' L f fp := by
  haveI := hC.1.isAlgClosed
  haveI := hC.1.charZero
  obtain ⟨n, hKn⟩ := hK
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
  haveI : QuasiCompact sX := hXp.toIsVariety.toQuasiCompact
  have hklt : MMP.Mori.IsKltPair sX n K C := (isKltPair_iff_mori_isKltPair sX hKn hC.1).mp hC
  have hC0 : 0 ≤ C := hC.1.nonneg
  have hWp := isProjectiveVariety_of_isContractionOfRay hXp hklt hC0 hR hf
  have hWn := hflip.isSmallMorphism.isNormalVariety_target
  haveI : IsNormal W := hWn.2
  haveI : QuasiCompact sW := hWn.1.toQuasiCompact
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsIntegral X' := hflip.isSmallMorphism_flip.isNormalVariety_source.1.toIsIntegral
  -- the ray is spanned by the class of a curve `T`
  obtain ⟨T, -, hRT, hTneg, -⟩ :=
    exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf_of_isAlgClosed sX hklt hC0 hR
  have hT0 : OneCycle.numericalClass sX (T.cycle ℝ) ≠ 0 := fun h => by
    rw [h, map_zero, neg_zero] at hTneg
    exact lt_irrefl _ hTneg
  have hTR : OneCycle.numericalClass sX (T.cycle ℝ) ∈ R := hRT ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hray : ∀ A : ProperCurve sX, A.IsContractedBy f → ∃ t : ℝ,
      t • OneCycle.numericalClass sX (T.cycle ℝ) = OneCycle.numericalClass sX (A.cycle ℝ) :=
    fun A hA => by
      obtain ⟨t, -, ht⟩ := hRT ▸ (hf.isContractedBy_iff A).mp hA
      exact ⟨t, ht⟩
  -- `P = L - c L'` is numerically `f`-trivial, so it and its flip transform descend to `W`
  obtain ⟨c, hc, hP0⟩ := exists_pos_curveForm_sub_smul_eq_zero hXQ hL hL' T hTR hT0 hray
  obtain ⟨-, M, hM, -, hfpM, -, hPp⟩ :=
    IsFlipOf.exists_qLinearlyEquivalent_pullback_of_curveForm_eq_zero hflip hXp hWp hXQ
      (relativePicardNumber_eq_one_of_forall_isContractedBy sX f T
        ((hf.isContractedBy_iff T).mpr hTR) hT0 hray) hKn hC
      ⟨hR.1, fun A hA => hR.2.2 _ ((hf.isContractedBy_iff A).mp hA)
        (numericalClass_ne_zero_of_hasRelativelyAmpleMultiple
          (isQCartier_of_isQFactorial sX hXQ _) hflip.hasRelativelyAmpleMultiple A hA)⟩
      _ hP0
  rw [map_sub, map_rat_smul] at hPp
  have hplus := isQCartier_and_hasRelativelyAmpleMultiple_of_qLinearlyEquivalent
    hflip.hasRelativelyAmpleMultiple_flip hc hM hfpM hPp
  -- `-L` is `f`-ample by the relative Kleiman criterion, applied to `L = K + (L - K)`
  have hamp : (-L).HasRelativelyAmpleMultiple f := by
    have e : Divisor.toQDivisor K + (L - Divisor.toQDivisor K) = L := add_sub_cancel _ _
    obtain ⟨hQL, hRay, hneg⟩ := e.symm ▸ hL
    simpa only [e] using hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX sW
      hf.isNormalVariety_source hXp hWp ⟨n, hKn⟩ hQL hRay (fun v hv hv0 => by
        simpa [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply] using hneg v hv hv0)
      f hf.comp_eq fun A hA => (hf.isContractedBy_iff A).mp hA
  exact
    { isQCartier := hL.1
      isContraction := hflip.isContraction
      isSmallMorphism := hflip.isSmallMorphism
      hasRelativelyAmpleMultiple := hamp
      isSmallMorphism_flip := hflip.isSmallMorphism_flip
      isProjectiveMorphism_flip := hflip.isProjectiveMorphism_flip
      isQCartier_flip := hplus.1
      hasRelativelyAmpleMultiple_flip := hplus.2 }

end MMP.Fourfold
