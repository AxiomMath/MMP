module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryStepDiagram
public import MMP.AlgebraicGeometry.MMP.Contraction.DltRayContraction
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.SpecialTermination
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.KltTermination
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
public import MMP.AlgebraicGeometry.MMP.Termination.Defs
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.StepSequenceCycleRank
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ExceptionalValuations
public import MMP.AlgebraicGeometry.MMP.Flip.ReducedPartRemoval
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Termination of elementary dlt programs of fourfolds

Let `(X, Δ)` be a projective `ℚ`-factorial dlt fourfold pair over `ℂ` with rational boundary.
Every elementary dlt program from `(X, Δ)` (`MMP.Fourfold.ElementaryDltProgram`) is finite,
whatever the successive choices of `(K_j + Δ_j)`-negative extremal rays: its number of steps is
a natural number.

## Main results

* `MMP.Fourfold.ElementaryDltProgram.n_ne_top`: an elementary dlt program from a complex
  fourfold has finitely many steps.

## References

* [OAI4], Termination for projective lc fourfolds.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter

namespace Proof_thm_oai4_dlt_termination

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP MMP.Mori MMP.Fourfold MMP.Positivity

/-- Over a point outside the image of `Ex(f)`, a proper birational morphism onto a normal
integral Noetherian scheme is an isomorphism nearby. -/
private theorem mem_biregularLocus_of_notMem_image {X Z : Scheme.{0}} [IsNoetherian Z] [IsIntegral Z]
    [IsNormal Z] [IsReduced X] {f : X ⟶ Z} [IsProper f] (hb : AlgebraicGeometry.IsBirational f)
    {z : Z} (hz : z ∉ f '' MMP.Flips.exceptionalSet f) :
    z ∈ MMP.Mori.biregularLocus f := by
  have hfib : f ⁻¹' {z} ⊆ (MMP.Flips.exceptionalSet f)ᶜ := by
    rintro y rfl hyE
    exact hz ⟨y, hyE, rfl⟩
  have hfin : (f ⁻¹' {z}).Finite := by
    have hcpt : IsCompact (f ⁻¹' {z}) :=
      f.isProperMap.isCompact_preimage isCompact_singleton
    have hU : ∀ y ∈ f ⁻¹' {z}, ∃ U : X.Opens, y ∈ U ∧ IsOpenImmersion (U.ι ≫ f) :=
      fun y hy => MMP.Flips.exists_isOpenImmersion_of_notMem_exceptionalSet (hfib hy)
    choose! U hyU hU using hU
    obtain ⟨t, hts, hcov⟩ := hcpt.elim_nhds_subcover (fun y => (U y : Set X))
      (fun y hy => (U y).isOpen.mem_nhds (hyU y hy))
    refine t.finite_toSet.subset fun w hw => ?_
    obtain ⟨y, hyt, hwy⟩ := Set.mem_iUnion₂.mp (hcov hw)
    have hy := hts y hyt
    have := hU y hy
    have hwy' : (⟨w, hwy⟩ : (U y).toScheme) = ⟨y, hyU y hy⟩ :=
      ((U y).ι ≫ f).isOpenEmbedding.injective (hw.trans hy.symm)
    have := congrArg Subtype.val hwy'
    simp only at this
    rw [this]
    exact hyt
  have := IsNormal.stalk_normal (X := Z) z
  obtain ⟨U, hzU, hUiso⟩ := exists_isIso_restrict_of_finite_fiber_of_normal f hb z hfin
  exact MMP.Mori.le_biregularLocus hUiso hzU

/-- For a proper morphism with connected fibres between Jacobson schemes, a point at which `f` is
a local open immersion is not in the fibre of any point of `Ex(f)`. -/
private theorem map_notMem_image_exceptionalSet {X Z : Scheme.{0}} [JacobsonSpace X] [JacobsonSpace Z]
    {f : X ⟶ Z} [IsProper f] (happ : ∀ U : Z.Opens, IsIso (f.app U)) {x : X}
    (hx : x ∉ MMP.Flips.exceptionalSet f) : f x ∉ f '' MMP.Flips.exceptionalSet f := by
  set E := MMP.Flips.exceptionalSet f
  have hE : IsClosed E := MMP.Flips.isClosed_exceptionalSet f
  have hO : IsOpen (f '' Eᶜ) := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨V, hyV, hV⟩ := MMP.Flips.exists_isOpenImmersion_of_notMem_exceptionalSet hy
    refine ⟨Set.range (V.ι ≫ f), ?_, (V.ι ≫ f).isOpenEmbedding.isOpen_range, ⟨⟨y, hyV⟩, rfl⟩⟩
    rintro _ ⟨w, rfl⟩
    refine ⟨w.1, fun hw => hw ⟨V, w.2, hV⟩, rfl⟩
  have hW : IsClosed (f '' E) := f.isClosedMap _ hE
  intro hxW
  obtain ⟨z₀, ⟨hz₀W, hz₀O⟩, hz₀c⟩ := (jacobsonSpace_iff_locallyClosed (X := Z)).mp inferInstance
    (f '' E ∩ f '' Eᶜ) ⟨f x, hxW, x, hx, rfl⟩ (hW.isLocallyClosed.inter hO.isLocallyClosed)
  obtain ⟨e, he, rfl⟩ := hz₀W
  obtain ⟨y, hy, hye⟩ := hz₀O
  obtain ⟨V, hyV, hV⟩ := MMP.Flips.exists_isOpenImmersion_of_notMem_exceptionalSet hy
  have hF : IsClosed (f ⁻¹' {f e}) := (mem_closedPoints_iff.mp hz₀c).preimage
    f.continuous
  have hVF : (V : Set X) ∩ f ⁻¹' {f e} = {y} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun ⟨hwV, hw⟩ => ?_, fun h => h ▸ ⟨hyV, hye⟩⟩
    have := ((V.ι ≫ f).isOpenEmbedding.injective (a₁ := ⟨w, hwV⟩) (a₂ := ⟨y, hyV⟩)
      (hw.trans hye.symm))
    exact congrArg Subtype.val this
  have hyc : IsClosed ({y} : Set X) := isClosed_singleton_of_isLocallyClosed_singleton
    (hVF ▸ V.isOpen.isLocallyClosed.inter hF.isLocallyClosed)
  have hconn := (Scheme.Hom.isConnected_preimage_singleton_of_isIso_app f happ (f e)).isPreconnected
  rcases (isPreconnected_iff_subset_of_disjoint.mp hconn) V {y}ᶜ V.isOpen hyc.isOpen_compl
    (fun w _ => by
      by_cases h : w = y
      · exact Or.inl (h ▸ hyV)
      · exact Or.inr h)
    (Set.eq_empty_iff_forall_notMem.mpr fun w ⟨hw, hwV, hne⟩ => hne (by
      have h' : w ∈ (V : Set X) ∩ f ⁻¹' {f e} := ⟨hwV, hw⟩
      rw [hVF] at h'
      exact h')) with
    h | h
  · have heV : e ∈ (V : Set X) ∩ f ⁻¹' {f e} := ⟨h rfl, rfl⟩
    rw [hVF] at heV
    exact hy (heV ▸ he)
  · exact h hye rfl

/-- For a proper birational morphism of normal complex varieties with `f_* 𝒪_X = 𝒪_Z`, the
exceptional set `X ∖ f⁻¹(V_f)` lies in the set of points near which `f` is not an open
immersion. -/
private theorem mori_exceptionalSet_subset {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hX : IsNormalVariety ℂ sX) (hZ : IsNormalVariety ℂ sZ)
    [IsProper f] (happ : ∀ U : Z.Opens, IsIso (f.app U))
    (hb : IsBirationalMorphism f) :
    (MMP.Mori.exceptionalSet f : Set X) ⊆ MMP.Flips.exceptionalSet f := by
  intro x hx
  by_contra hx'
  haveI := hX.1.toLocallyOfFiniteType
  haveI := hZ.1.toLocallyOfFiniteType
  haveI := hZ.1.toQuasiCompact
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsIntegral X := hX.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNoetherian Z := ⟨⟩
  exact hx (mem_biregularLocus_of_notMem_image
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
    (map_notMem_image_exceptionalSet happ hx'))

section Contraction

variable {k : Type} [Field k] {U V V' : Scheme.{0}} (sU : U ⟶ Spec (.of k))

/-- The pull-back classes along `g ≫ a` and along `g` agree for an isomorphism `a`. -/
private theorem pullbackNumericalClasses_comp_isIso (g : U ⟶ V') (a : V' ⟶ V) [IsIso a] :
    pullbackNumericalClasses sU (g ≫ a) = pullbackNumericalClasses sU g := by
  unfold pullbackNumericalClasses
  congr 1
  ext d
  constructor
  · rintro ⟨E, M, hM, ⟨e⟩, rfl⟩
    refine ⟨E, (Scheme.Modules.pullback a).obj M, inferInstance, ⟨?_⟩, rfl⟩
    exact e ≪≫ ((Scheme.Modules.pullbackComp g a).app M).symm
  · rintro ⟨E, M, hM, ⟨e⟩, rfl⟩
    refine ⟨E, (Scheme.Modules.pullback (inv a)).obj M, inferInstance, ⟨?_⟩, rfl⟩
    exact e ≪≫ (Scheme.Modules.pullbackCongr (show (g ≫ a) ≫ inv a = g by simp)).symm.app M ≪≫
      ((Scheme.Modules.pullbackComp (g ≫ a) (inv a)).app M).symm

/-- The relative Picard number does not change under composition with an isomorphism. -/
private theorem relativePicardNumberN1_comp_isIso (g : U ⟶ V') (a : V' ⟶ V) [IsIso a] :
    relativePicardNumberN1 sU (g ≫ a) = relativePicardNumberN1 sU g := by
  rw [relativePicardNumberN1, relativePicardNumberN1, pullbackNumericalClasses_comp_isIso]

/-- Relative ampleness is unchanged under composition with an isomorphism of the target. -/
private theorem isRelativelyAmple_comp_isIso {g : U ⟶ V'} (a : V' ⟶ V) [IsIso a] (L : U.Modules)
    [Stacks.Ample.IsInvertibleModule U L] (h : MMP.Mori.IsRelativelyAmple g L) :
    MMP.Mori.IsRelativelyAmple (g ≫ a) L := by
  intro y
  obtain ⟨W, hW, hyW, hamp⟩ := h (inv a y)
  refine ⟨(inv a) ⁻¹ᵁ W, hW.preimage (inv a), hyW, ?_⟩
  have e : (g ≫ a) ⁻¹ᵁ ((inv a) ⁻¹ᵁ W) = g ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have key : ∀ O₁ O₂ : U.Opens, O₁ = O₂ →
      Stacks.Ample.IsAmple O₁.toScheme
        ((RingedSpaceModuleAdjunction.modulePullback O₁.ι.toLRSHom.toShHom).obj L) →
      Stacks.Ample.IsAmple O₂.toScheme
        ((RingedSpaceModuleAdjunction.modulePullback O₂.ι.toLRSHom.toShHom).obj L) := by
    rintro _ _ rfl h
    exact h
  exact key _ _ e.symm hamp

/-- A `ℚ`-divisor with an `g`-ample multiple has a `g ≫ a`-ample multiple for an isomorphism
`a`. -/
private theorem hasRelativelyAmpleMultiple_comp_isIso [CompactSpace U] [IsLocallyNoetherian U]
    [IsNormal U] {D : QDivisor U} {g : U ⟶ V'} (a : V' ⟶ V) [IsIso a]
    (h : D.HasRelativelyAmpleMultiple g) : D.HasRelativelyAmpleMultiple (g ≫ a) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  haveI := hL.isInvertibleModule_divisorialSheaf
  exact ⟨m, hm, L, hL, hLD, isRelativelyAmple_comp_isIso a _ hamp⟩

/-- A contraction `f` of a negative extremal ray of a projective `ℚ`-factorial dlt pair has
projective target, relative Picard number one and `-(K + Δ)` relatively ample. -/
private theorem contraction_props {U V : Scheme.{0}} [IsIntegral U] [CompactSpace U]
    [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    {K : Divisor U} {Δ : QDivisor U}
    (hU : IsProjectiveQFactorialDltPair sU K Δ) {R : Set (NumericalCurveClasses sU)}
    (hR : IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Δ) R) {f : U ⟶ V}
    (hf : IsContractionOfRay sU sV R f) :
    MMP.Mori.IsProjectiveVariety ℂ sV ∧ relativePicardNumberN1 sU f = 1 ∧
      (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f := by
  obtain ⟨V', sV', g, hg, hV', hρ', hamp'⟩ := hU.exists_isContractionOfRay hR
  have hUp := hU.isProjectiveVariety
  have hray := hR.2.1
  have hfac : ∀ {W W' : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sW' : W' ⟶ Spec (.of ℂ)}
      {u : U ⟶ W} {u' : U ⟶ W'}, IsContractionOfRay sU sW R u → IsContractionOfRay sU sW' R u' →
      ∃! h' : W ⟶ W', u ≫ h' = u' := fun hu hu' =>
    existsUnique_comp_eq_of_isContractionOfRay hUp hu'.isProjectiveMorphism hu'.comp_eq hray
      (fun C hC => (hu'.isContractedBy_iff C).mpr hC) hu
  obtain ⟨b, hb, -⟩ := hfac hf hg
  obtain ⟨a, ha, -⟩ := hfac hg hf
  have hba : b ≫ a = 𝟙 V := (hfac hf hf).unique (by rw [← Category.assoc, hb, ha]) (by simp)
  have hab : a ≫ b = 𝟙 V' := (hfac hg hg).unique (by rw [← Category.assoc, ha, hb]) (by simp)
  haveI : IsIso a := ⟨⟨b, hab, hba⟩⟩
  have hsV : a ≫ sV = sV' := by
    have h1 : g ≫ a ≫ sV = sU := by rw [← Category.assoc, ha, hf.comp_eq]
    haveI : IsProper g := isProper_of_isProjectiveMorphism _ hg.isProjectiveMorphism
    haveI : IsIso g.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ g.c fun W => hg.isIso_app W.unop
    exact (MMP.existsUnique_comp_eq_of_isIso_c g sU fun x x' _ => Subsingleton.elim _ _).unique
      h1 hg.comp_eq
  refine ⟨?_, ?_, ?_⟩
  · have hvar : AlgebraicGeometry.IsVariety ℂ sV := hf.isNormalVariety_target.1
    exact (Mori.isProjectiveVariety_iff ℂ sV).mpr ⟨hvar, IsProjectiveMorphism.of_iso (asIso a)
      (Iso.refl _) (by simpa using hsV) hV'.isProjective⟩
  · rw [← ha, relativePicardNumberN1_comp_isIso, hρ']
  · rw [← ha]
    exact hasRelativelyAmpleMultiple_comp_isIso a hamp'

end Contraction

section PicardOne

variable {Xm Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {fm : Xm ⟶ Z}
  {R : Set (NumericalCurveClasses sXm)}

/-- The contraction of an extremal ray `R` which contracts a proper curve `C₀` with nonzero class
has relative Picard number one: `N ↦ N · C₀` identifies `N¹(X/Z)` with `ℝ`. -/
private theorem relativePicardNumber_eq_one
    (hray : IsExtremalRay ℝ (closedConeOfCurves sXm : Set (NumericalCurveClasses sXm)) R)
    (hcontr : IsContractionOfRay sXm sZ R fm) (C₀ : ProperCurve sXm)
    (hC₀ : C₀.IsContractedBy fm) (hne : OneCycle.numericalClass sXm (C₀.cycle ℝ) ≠ 0) :
    Flips.relativePicardNumber sXm fm = 1 := by
  obtain ⟨-, v, -, hRv⟩ := hray
  have hC₀R := (hcontr.isContractedBy_iff C₀).mp hC₀
  rw [hRv] at hC₀R
  obtain ⟨c₀, hc₀, hc₀v⟩ := hC₀R
  have hc₀' : c₀ ≠ 0 := by rintro rfl; rw [zero_smul] at hc₀v; exact hne hc₀v.symm
  let φ : KCartierDivisor ℝ Xm →ₗ[ℝ] ℝ :=
    (OneCycle.intersectionPairing (sX := sXm)).flip (C₀.cycle ℝ)
  have hφ : ∀ D, φ D = (C₀.cycle ℝ).intersectionNumber D := fun _ => rfl
  have hker : LinearMap.ker φ = Flips.relativeNumericallyTrivialDivisors sXm fm := by
    ext D
    rw [LinearMap.mem_ker, Flips.mem_relativeNumericallyTrivialDivisors, hφ]
    refine ⟨fun hD C hC => ?_, fun h => h C₀ hC₀⟩
    have hCR := (hcontr.isContractedBy_iff C).mp hC
    rw [hRv] at hCR
    obtain ⟨c, -, hc⟩ := hCR
    have hCC₀ : OneCycle.numericalClass sXm (C.cycle ℝ) =
        (c / c₀) • OneCycle.numericalClass sXm (C₀.cycle ℝ) := by
      rw [← hc, ← hc₀v, smul_smul, div_mul_cancel₀ _ hc₀']
    rw [← NumericalCurveClasses.intersectionNumber_numericalClass, hCC₀, map_smul,
      NumericalCurveClasses.intersectionNumber_numericalClass, hD, smul_zero]
  have hsurj : Function.Surjective φ := by
    obtain ⟨L, _, hL⟩ : ∃ (L : Xm.Modules) (_ : SheafOfModules.IsInvertible Xm.presheaf
        Xm.ringCatSheaf.2 L), OneCycle.degree ℝ sXm L (C₀.cycle ℝ) ≠ 0 := by
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
      rwa [← degreeOn_eq_of_iso ℂ sXm C₀.ι C₀.dim_le e]
    intro r
    exact ⟨(r / φ (KCartierDivisor.ofCartier ℝ E)) • KCartierDivisor.ofCartier ℝ E, by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hE]⟩
  rw [Flips.relativePicardNumber,
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivOfSurjective hsurj)).rank_eq, Module.rank_self]
  simp

end PicardOne

section Copies

variable {X Y : Scheme.{0}}

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
private theorem isCartierCombination_toRDivisor [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (h : D.IsQCartier) : Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := h
  exact ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, by
    rw [Fin.sum_univ_one]; exact toRDivisor_eq_inv_smul hm hL⟩

/-- Relative ampleness of an invertible sheaf, checked on an affine open cover of the target,
holds over every affine open of the target. -/
private theorem isRelativelyAmpleCartier_of_isRelativelyAmple [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} [QuasiCompact f]
    {L : Divisor X} (hL : L.IsCartier) (h : L.IsRelativelyAmple f hL) :
    Flips.IsRelativelyAmpleCartier f L := by
  have := hL.isInvertibleModule_divisorialSheaf
  exact ⟨hL, fun U hU =>
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
      inferInstance h).2 U hU⟩

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-ample as an `ℝ`-divisor. -/
private theorem isRelativelyAmple_toRDivisor [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] {f : X ⟶ Y} [QuasiCompact f] {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) : Flips.IsRelativelyAmple f (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  refine ⟨1, fun _ => ((m : ℤ) : ℝ)⁻¹, fun _ => L, le_rfl, fun _ => by positivity,
    fun _ => isRelativelyAmpleCartier_of_isRelativelyAmple hL hamp, ?_⟩
  rw [Fin.sum_univ_one]
  exact toRDivisor_eq_inv_smul (by exact_mod_cast hm.ne') hLD

/-- `K + B` as an `ℝ`-divisor. -/
private theorem logCanonicalDivisor_eq (K : Divisor X) (B : QDivisor X) :
    Flips.logCanonicalDivisor K (QDivisor.toRDivisor B) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + B) := by
  rw [Flips.logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

variable {X Y : Scheme.{0}} in
/-- A separated complex scheme is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {s : X ⟶ Spec (.of ℂ)} [IsSeparated s] :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  have : (X ↘ ⊤_ Scheme) = s ≫ Limits.terminal.from (Spec (.of ℂ)) := Subsingleton.elim _ _
  rw [this]
  infer_instance

/-- A small morphism (exceptional set of codimension `≥ 2`) with `𝒪_Z ≅ f_* 𝒪_X` is a small
birational contraction: the open-immersion exceptional set is contained in the biregular one. -/
private theorem isSmall_of_isSmallMorphism {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    (happ : ∀ U : Z.Opens, IsIso (f.app U)) : Flips.IsSmall ℂ sZ sX f := by
  have := hf.isNormalVariety_target.2
  have := hf.isProper
  have := hf.isNormalVariety_source.1
  have := hf.isNormalVariety_target.1
  have hbc : Flips.IsBirationalContraction ℂ sZ sX f :=
    { isVariety_target := hf.isNormalVariety_target.1
      isVariety_source := hf.isNormalVariety_source.1
      comp_eq := hf.comp_eq
      isProper := hf.isProper
      isIso_app := happ
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX
        hf.isBirationalMorphism).symm }
  refine (Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
  have h := hf.two_le_codimension
  rw [Flips.le_closedsCodimension_iff_le_coheight] at h ⊢
  intro x hx
  refine h x fun hx' => hx ⟨f ⁻¹ᵁ biregularLocus f, by simpa [exceptionalSet] using hx', ?_⟩
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  rw [← morphismRestrict_ι]
  infer_instance

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {R S : Type*} [AddCommGroup R]
    [AddCommGroup S] (φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with changing coefficients. -/
private theorem flipTransform_mapCoeffsAddMonoidHom {X' : Scheme.{0}} {R S : Type*}
    [AddCommGroup R] [AddCommGroup S] (fm : X ⟶ Y) (fp : X' ⟶ Y) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
    flipTransform fm fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (flipTransform fm fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

end Copies

/-- The strict transform `(f⁺)⁻¹_* f_* K` of a canonical divisor along `X ⟶ V ⟵ X⁺`, `f` proper
birational and `f⁺` small, is a canonical divisor. -/
private theorem isCanonicalDivisor_flipTransform {X V X' : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} {f : X ⟶ V} {fp : X' ⟶ V} (hX : IsNormalVariety ℂ sX)
    (hc : f ≫ sV = sX) [IsProper f] (hf : IsBirationalMorphism f)
    (hfp : IsSmallMorphism sX' sV fp) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K) := by
  have hV := hfp.isNormalVariety_target
  have hX' := hfp.isNormalVariety_source
  haveI : IsIntegral V := hV.1.toIsIntegral
  haveI : IsNormal V := hV.2
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : QuasiCompact sV := hV.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  haveI := hf.isDominant
  haveI := hfp.isBirationalMorphism.isDominant
  haveI : IsProper fp := hfp.isProper
  haveI : MMP.Mori.IsVariety ℂ sV := hV.1
  haveI : MMP.Mori.IsVariety ℂ sX' := hX'.1
  have hcp := hfp.comp_eq
  subst hc hcp
  haveI : LocallyOfFiniteType (f ≫ sV) := hX.1.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ (f ≫ sV) := hX.1
  have hdimV : topologicalKrullDim V = n := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV (f ≫ sV) hf]
    exact hK.topologicalKrullDim_eq
  obtain ⟨ω, hω0, hω⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_divisorOfForm_eq_transformDivisor hV hX hf hdimV hK
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sV) hdimV
  have hbp := hfp.isBirationalMorphism
  have hτ0 := MMP.Fourfold.Oai4C1.Main.pullbackRationalPluriForms_ne_zero fp
    hbp.functionFieldMap_bijective hd hω0
  have hdiv : divisorOfForm (pullbackRationalPluriForms sV fp ω) = flipTransform f fp K := by
    ext P
    obtain ⟨-, Q, -, -, hPQ⟩ :=
      exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hV hf hfp P
    have hPQ' := MMP.Fourfold.map_genericPoint_eq_of_image_eq P Q hPQ
    haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hbp hPQ'
    change P.ordForm _ = (flipTransform f fp K).coeff P
    rw [ordForm_pullbackRationalPluriForms_of_isIso fp hbp.functionFieldMap_bijective hd P Q
      hPQ' ω]
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [DivisorWithCoeffs.coeff_apply, MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint hPQ'
      (hPQ' ▸ MMP.Fourfold.Oai4C1.map_genericPoint_mem_biregularLocus hfp.two_le_codimension P),
      ← hω]
    rfl
  have hdimX' : topologicalKrullDim X' = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV (fp ≫ sV) hbp]
    exact hdimV
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (fp ≫ sV) hX' hdimX'
  have hle := linearlyEquivalent_divisorOfForm_zsmul hX' hK₀ hτ0
  rw [one_smul, hdiv] at hle
  exact hK₀.of_linearlyEquivalent hle

section Picard

variable {k : Type} [Field k] {X Z : Scheme.{0}}

/-- For an isomorphism `f`, `f^* N¹(Z)_ℝ` is all of `N¹(X)_ℝ`. -/
private theorem pullbackNumericalClasses_eq_top (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) [IsIso f] :
    pullbackNumericalClasses sX f = ⊤ := by
  refine eq_top_iff.mpr fun d _ => ?_
  obtain ⟨D, rfl⟩ := Submodule.mkQ_surjective _ d
  change numericalDivisorClass sX D ∈ _
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ =>
    rw [map_add]; exact Submodule.add_mem _ (h₁ Submodule.mem_top) (h₂ Submodule.mem_top)
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
private theorem relativePicardNumberN1_eq_zero (sX : X ⟶ Spec (.of k)) (f : X ⟶ Z) [IsIso f] :
    relativePicardNumberN1 sX f = 0 := by
  rw [relativePicardNumberN1, pullbackNumericalClasses_eq_top]
  simp

end Picard

section Contracted

variable {k : Type} [Field k] {X Z : Scheme.{0}}

/-- A proper morphism from a proper `k`-scheme which is not locally quasi-finite contracts a proper
curve: at a closed point `x` where `f` is not quasi-finite the fibre `f⁻¹(f(x))` (closed, as
`f(x)` is a closed point) has positive dimension, and a curve through a closed point of a smaller
irreducible closed subset, in the closure of the generic point of a larger one, lies in the
fibre. -/
private theorem exists_properCurve_isContractedBy_of_not_locallyQuasiFinite
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
  have hdim : 0 < topologicalKrullDim (f ⁻¹' {f x}) := by
    by_contra hle
    replace hle := not_lt.mp hle
    apply hx
    change f.QuasiFiniteAt x
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have h' : topologicalKrullDim (f.fiber (f x)) ≤ 0 := by
      rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo (f x)).isHomeomorph]
      exact hle
    have : IsLocallyNoetherian
        (CategoryTheory.Limits.pullback f (Z.fromSpecResidueField (f x))) := inferInstance
    have : IsLocallyNoetherian (f.fiber (f x)) := this
    have : IsLocallyArtinian (f.fiber (f x)) := IsLocallyArtinian.of_topologicalKrullDim_le_zero h'
    have : DiscreteTopology (f.fiber (f x)) :=
      (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mp inferInstance).2
    exact isOpen_discrete _
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

/-- The contraction of a ray with `ρ(X/Z) = 1` and birational contraction contracts some curve:
otherwise `f` is locally quasi-finite, hence finite (being proper), hence an isomorphism (being
birational onto the normal variety `Z`), against `ρ(X/Z) = 1`. -/
private theorem exists_properCurve_isContractedBy {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] (hX : MMP.Mori.IsProjectiveVariety k sX)
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z} (hc : IsContractionOfRay sX sZ R f)
    (hb : IsBirationalMorphism f) (hρ : relativePicardNumberN1 sX f = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  by_contra hno
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  haveI : LocallyQuasiFinite f := by
    by_contra h
    exact hno (exists_properCurve_isContractedBy_of_not_locallyQuasiFinite h)
  haveI : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  have hZ := hc.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsIso f := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).2 inferInstance
  rw [relativePicardNumberN1_eq_zero] at hρ
  exact zero_ne_one hρ

end Contracted

section Ray

variable {k : Type} [Field k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- `D · C < 0` for a curve `C` contracted by `f` when `-D` is `f`-ample. -/
private theorem intersectionNumber_neg_of_isContractedBy {f : X ⟶ Z} {D : QDivisor X}
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
`R`, contracts a curve `C`, and `-D'` is `f`-ample, then `R` is `D'`-negative: the class of `C`
spans `R` and `D' · C < 0`. -/
private theorem isNegativeExtremalRayOf_of_hasRelativelyAmpleMultiple_neg (hX : IsQFactorial sX)
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
  have hv : QDivisor.curveForm sX D' hD' v < 0 := by
    by_contra hx
    exact absurd hneg (not_lt.mpr (mul_nonneg hc₀ (not_lt.mp hx)))
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg hc0 hv

end Ray

section Transfer

/-- The strict transform commutes with regarding divisors as `ℚ`-divisors. -/
private theorem flipTransform_toQDivisor {X Y X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    flipTransform f fp (Divisor.toQDivisor D) = Divisor.toQDivisor (flipTransform f fp D) := by
  exact flipTransform_mapCoeffsAddMonoidHom f fp _ D

/-- Linear equivalence is compatible with negation. -/
private theorem linearlyEquivalent_neg {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {K K' : Divisor X} (h : K.LinearlyEquivalent K') :
    (-K).LinearlyEquivalent (-K') := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ⁻¹, by rw [MMP.Mori.principalDivisor_inv, ← hφ]; abel⟩

/-- Relative ampleness of `-(K + Δ)` passes to `-(K' + Δ)` for `K ∼ K'`. -/
private theorem hasRelativelyAmpleMultiple_neg_of_linearlyEquivalent {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {K K' : Divisor X} {Δ : QDivisor X}
    {f : X ⟶ Y} (h : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f)
    (hK : K.LinearlyEquivalent K') :
    (-(Divisor.toQDivisor K' + Δ)).HasRelativelyAmpleMultiple f := by
  have e : ∀ K₀ : Divisor X, -(Divisor.toQDivisor K₀ + Δ) = Divisor.toQDivisor (-K₀) + -Δ :=
    fun K₀ => by rw [map_neg, neg_add]
  rw [e] at h ⊢
  exact MMP.Fourfold.Oai4C1.Main.hasRelativelyAmpleMultiple_add_of_linearlyEquivalent h
    (linearlyEquivalent_neg (X := X) hK)

end Transfer

section Step

/-- An isomorphism onto a normal variety is a small morphism. -/
private theorem isSmallMorphism_of_isIso {X V : Scheme.{0}} [IsIntegral X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hV : IsNormalVariety ℂ sV) {fp : X ⟶ V}
    [IsIso fp] (hc : fp ≫ sV = sX) : IsSmallMorphism sX sV fp := by
  subst hc
  haveI := hV.1
  have hvar : AlgebraicGeometry.IsVariety ℂ (fp ≫ sV) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  refine ⟨⟨hvar, inferInstance⟩, hV, rfl, inferInstance, isBirationalMorphism_of_isIso fp, ?_⟩
  rw [(exceptionalSet_eq_bot_iff fp).mpr inferInstance, le_closedsCodimension_iff]
  intro W hW
  obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
  exact absurd (hW hx) (by simp)

variable {X V X' : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
  [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sV : V ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K K' : Divisor X} {Δ : QDivisor X}
  {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V} {fp : X' ⟶ V} {Δ' : QDivisor X'}

/-- The positive side of an elementary step is small. -/
private theorem isSmallMorphism_fp_of_step (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ') :
    IsSmallMorphism sX' sV fp := by
  rcases h.flip_or_divisorial with ⟨-, hfl⟩ | ⟨-, hiso⟩
  · exact hfl.isSmallMorphism_flip
  · exact isSmallMorphism_of_isIso h.isContractionOfRay.isNormalVariety_target h.comp_eq

/-- The strict transform of a canonical divisor along an elementary step is a canonical
divisor. -/
private theorem isCanonicalDivisor_flipTransform_of_step
    (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ') {n : ℕ}
    (hK : K'.IsCanonicalDivisor sX n) :
    Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K') := by
  have hc := h.isContractionOfRay
  haveI := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  exact isCanonicalDivisor_flipTransform hc.isNormalVariety_source hc.comp_eq
    h.isBirationalMorphism (isSmallMorphism_fp_of_step h) hK

/-- An elementary step for the canonical divisor `K` is one for any other canonical divisor
`K'`. -/
private theorem step_rebase (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ') {n : ℕ}
    (hK' : K'.IsCanonicalDivisor sX n) :
    IsProjectiveElementaryDltStep sX sV sX' K' Δ R f fp Δ' := by
  have hpair := h.isProjectiveQFactorialDltPair
  have hX := hpair.isProjectiveVariety
  haveI : PerfectField ℂ := inferInstance
  obtain ⟨m, hK⟩ := hpair.isCanonicalDivisor
  have hlin : K.LinearlyEquivalent K' :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX
      h.isContractionOfRay.isNormalVariety_source hK hK'
  obtain ⟨hV, hρ, hamp⟩ := contraction_props hpair h.isNegativeExtremalRayOf h.isContractionOfRay
  have hamp' := hasRelativelyAmpleMultiple_neg_of_linearlyEquivalent hamp hlin
  obtain ⟨C, hC⟩ := exists_properCurve_isContractedBy hX h.isContractionOfRay
    h.isBirationalMorphism hρ
  have hpair' : IsProjectiveQFactorialDltPair sX K' Δ :=
    ⟨hX, hpair.isQFactorial, ⟨n, hK'⟩, hpair.isDltPair⟩
  refine ⟨hpair', isNegativeExtremalRayOf_of_hasRelativelyAmpleMultiple_neg hpair.isQFactorial
    h.isNegativeExtremalRayOf h.isContractionOfRay C hC hamp', h.isContractionOfRay,
    h.isBirationalMorphism, h.comp_eq, h.eq_flipTransform, ?_⟩
  rcases h.flip_or_divisorial with ⟨hs, hfl⟩ | hd
  · refine Or.inl ⟨hs, ?_⟩
    have hfp := hfl.isSmallMorphism_flip
    haveI := isProper_of_isProjectiveMorphism _ h.isContractionOfRay.isProjectiveMorphism
    have hcan := isCanonicalDivisor_flipTransform h.isContractionOfRay.isNormalVariety_source
      h.isContractionOfRay.comp_eq h.isBirationalMorphism hfp hK
    have hcan' := isCanonicalDivisor_flipTransform h.isContractionOfRay.isNormalVariety_source
      h.isContractionOfRay.comp_eq h.isBirationalMorphism hfp hK'
    have hlin' : Divisor.LinearlyEquivalent (flipTransform f fp K) (flipTransform f fp K') :=
      MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX'
        hfp.isNormalVariety_source hcan hcan'
    have e : ∀ K₀ : Divisor X, flipTransform f fp (Divisor.toQDivisor K₀ + Δ) =
        Divisor.toQDivisor (flipTransform f fp K₀) + flipTransform f fp Δ := fun K₀ => by
      rw [map_add, flipTransform_toQDivisor]
    have hq := hfl.isQCartier_flip
    have ha := hfl.hasRelativelyAmpleMultiple_flip
    rw [e] at hq ha
    refine ⟨(QDivisor.isQCartier_add_iff_of_linearlyEquivalent hlin).mp hfl.isQCartier,
      hfl.isContraction, hs, hamp', hfp, hfl.isProjectiveMorphism_flip, ?_, ?_⟩
    · rw [e]; exact (QDivisor.isQCartier_add_iff_of_linearlyEquivalent hlin').mp hq
    · rw [e]
      exact MMP.Fourfold.Oai4C1.Main.hasRelativelyAmpleMultiple_add_of_linearlyEquivalent ha hlin'
  · exact Or.inr hd

end Step

section Step

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
  {R : Set (NumericalCurveClasses sXm)}

/-- The birational map `(f⁺)⁻¹ ∘ f` of a step diagram, composed of partial isomorphisms
representing the birational morphisms `f` and `f⁺`, is a modification of `f` into `f⁺`. -/
private theorem exists_isModificationOf (hD : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) :
    ∃ φ : Xm.RationalMap Xp, Flips.IsModificationOf fm fp φ := by
  obtain ⟨em, hm⟩ := hD.isBirationalMorphism_minus
  obtain ⟨ep, hp⟩ := hD.isSmallMorphism_plus.isBirationalMorphism
  have : IsSeparated sZ := hD.isProjectiveVariety_target.1.toIsSeparated
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em fm (𝟙 Z) hm
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep fp (𝟙 Z) hp
  simp only [Category.comp_id] at h1 h2
  set e := em.trans ep.symm
  have H : e.IsOver fm fp := h1.trans h2.symm
  refine ⟨e.toRationalMap, ⟨e, rfl⟩, ?_⟩
  rw [Flips.RationalMap.IsOver, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change Xm.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fp =
    Xm.homOfLE (le_top : e.source ≤ ⊤) ≫ Xm.topIso.hom ≫ fm
  rw [Category.assoc, H]
  simp

/-- A step diagram with small negative side is a flip in the sense of `MMP.Mori.IsFlip`. -/
private theorem isFlip_of_isFourfoldStepDiagram (hD : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hsmall : IsSmallMorphism sXm sZ fm) : MMP.Mori.IsFlip sXm sZ sXp K B fm fp :=
  { isFlippingContraction :=
      { isNormalVariety_source := hD.isNormalVariety_minus
        isNormalVariety_target := hD.isNormalVariety_target
        comp_eq := hD.comp_eq_minus
        isCanonicalDivisor := hD.isCanonicalDivisor
        isQCartier := hD.isQCartier_minus
        isProper := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
        isBirationalMorphism := hD.isBirationalMorphism_minus
        two_le_codimension := hsmall.two_le_codimension
        hasRelativelyAmpleMultiple := hD.hasRelativelyAmpleMultiple_minus }
    isNormalVariety := hD.isNormalVariety_plus
    comp_eq := hD.comp_eq_plus
    isProper := hD.isProper_plus
    isBirationalMorphism := hD.isBirationalMorphism_plus
    isQCartier := hD.isQCartier_plus
    hasRelativelyAmpleMultiple := hD.hasRelativelyAmpleMultiple_plus
    two_le_codimension := hD.isSmallMorphism_plus.two_le_codimension }

/-- For a step diagram with small negative side, the transform of divisors under a modification
of `f` into `f⁺` is the strict transform `(f⁺)⁻¹_* f_*`. -/
private theorem transformDivisor_eq_flipTransform (hD : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hsmall : IsSmallMorphism sXm sZ fm) {φ : Xm.RationalMap Xp}
    (hφ : Flips.IsModificationOf fm fp φ) {R' : Type*} [AddCommMonoid R']
    (D : DivisorWithCoeffs R' Xm) :
    Mori.RationalMap.transformDivisor φ D = flipTransform fm fp D := by
  have hfl := isFlip_of_isFourfoldStepDiagram hD hsmall
  haveI : IsProper fm := hfl.isFlippingContraction.isProper
  have : IsSeparated sXp := hD.isNormalVariety_plus.1.toIsSeparated
  haveI : IsSeparated (Xp ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sXp)
  obtain ⟨V, hV1, hV2, hXV, hX'V, -⟩ := hfl.exists_opens_isIso
  haveI := hV1
  haveI := hV2
  exact MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hD.isNormalVariety_target
    (hD.comp_eq_minus ▸ hD.isNormalVariety_minus) hD.isBirationalMorphism_minus V hXV hX'V hφ.2 D

/-- A small step diagram whose negative side is the contraction of a negative extremal ray
contracting a curve with nonzero class is a flip in the sense of sequences of flips. -/
private theorem exists_isFlip (hD : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hsmall : IsSmallMorphism sXm sZ fm)
    (hneg : IsNegativeExtremalRayOf sXm (Divisor.toQDivisor K + B) R)
    (hcontr : IsContractionOfRay sXm sZ R fm) (C₀ : ProperCurve sXm)
    (hC₀ : C₀.IsContractedBy fm) (hne : OneCycle.numericalClass sXm (C₀.cycle ℝ) ≠ 0) :
    Flips.IsNegativeExtremalContraction ℂ sXm sZ
        (Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) fm ∧
      Flips.IsSmall ℂ sZ sXm fm ∧
      ∃ φ : Xm.RationalMap Xp,
        Flips.IsFlip ℂ sXm sZ sXp (Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) fm fp φ ∧
          flipTransform fm fp B = Mori.RationalMap.transformDivisor φ B := by
  haveI := isProper_of_isProjectiveMorphism fm hD.isProjectiveMorphism_minus
  have hE : Flips.IsNegativeExtremalContraction ℂ sXm sZ
      (Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) fm := by
    rw [logCanonicalDivisor_eq]
    exact
      { isNormalVariety_source := hD.isNormalVariety_minus
        isNormalVariety_target := hD.isNormalVariety_target
        isCartierCombination := isCartierCombination_toRDivisor hD.isQCartier_minus
        isContraction :=
          { isVariety_target := hD.isNormalVariety_target.1
            isVariety_source := hD.isNormalVariety_minus.1
            comp_eq := hD.comp_eq_minus
            isProper := inferInstance
            isIso_app := hD.isIso_app_minus }
        isRelativelyAntiAmple := by
          rw [Flips.IsRelativelyAntiAmple, ← map_neg]
          exact isRelativelyAmple_toRDivisor hD.hasRelativelyAmpleMultiple_minus
        relativePicardNumber_eq_one := relativePicardNumber_eq_one hneg.2.1 hcontr C₀ hC₀ hne }
  have hS := isSmall_of_isSmallMorphism hsmall hD.isIso_app_minus
  obtain ⟨φ, hmod⟩ := exists_isModificationOf hD
  have := hD.isSmallMorphism_plus.isProper
  have htrE : Mori.RationalMap.transformDivisor φ
      (Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) =
        QDivisor.toRDivisor
          (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B) := by
    rw [transformDivisor_eq_flipTransform hD hsmall hmod, logCanonicalDivisor_eq, map_add,
      map_add]
    simp only [QDivisor.toRDivisor, Divisor.toQDivisor, flipTransform_mapCoeffsAddMonoidHom]
    exact (map_add _ _ _).symm
  refine ⟨hE, hS, φ,
    { isNormalVariety_source := hD.isNormalVariety_minus
      isNormalVariety_target := hD.isNormalVariety_target
      isNormalVariety_flip := hD.isNormalVariety_plus
      isContraction := hE.isContraction
      isCartierCombination := hE.isCartierCombination
      isRelativelyAntiAmple := hE.isRelativelyAntiAmple
      isProper := inferInstance
      isModificationOf := hmod
      isMorphismInCodimOne :=
        Flips.RationalMap.isMorphismInCodimOne_of_isOver hD.isNormalVariety_minus fm fp φ hmod.2
      isSmall := isSmall_of_isSmallMorphism hD.isSmallMorphism_plus hD.isIso_app_plus
      isCartierCombination_transform := by
        rw [htrE]; exact isCartierCombination_toRDivisor hD.isQCartier_plus
      isRelativelyAmple_transform := by
        rw [htrE]; exact isRelativelyAmple_toRDivisor hD.hasRelativelyAmpleMultiple_plus
      isSmall_source := hS },
    (transformDivisor_eq_flipTransform hD hsmall hmod B).symm⟩

end Step

/-! ### The main argument -/

/-- A contraction of a negative extremal ray of a projective `ℚ`-factorial dlt pair with
birational contraction and `ρ = 1` contracts a curve with nonzero numerical class. -/
private theorem exists_properCurve_numericalClass_ne_zero {U V : Scheme.{0}} [IsIntegral U]
    [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)}
    {sV : V ⟶ Spec (.of ℂ)} {K : Divisor U} {Δ : QDivisor U}
    (hU : IsProjectiveQFactorialDltPair sU K Δ) {R : Set (NumericalCurveClasses sU)}
    {f : U ⟶ V} (hf : IsContractionOfRay sU sV R f) (hb : IsBirationalMorphism f)
    (hρ : relativePicardNumberN1 sU f = 1)
    (hamp : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f) :
    ∃ C : ProperCurve sU, C.IsContractedBy f ∧ OneCycle.numericalClass sU (C.cycle ℝ) ≠ 0 := by
  obtain ⟨C, hC⟩ := exists_properCurve_isContractedBy hU.isProjectiveVariety hf hb hρ
  refine ⟨C, hC, fun h0 => ?_⟩
  haveI : QuasiCompact sU := hU.isProjectiveVariety.toQuasiCompact
  have hq := isQCartier_of_isQFactorial sU hU.isQFactorial (Divisor.toQDivisor K + Δ)
  have hneg := intersectionNumber_neg_of_isContractedBy hamp C hC hq
  have h1 := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sU _ hq C
  rw [h0, map_zero] at h1
  have h2 : ((Divisor.toQDivisor K + Δ).intersectionNumber ℂ sU C.ι C.dim_le hq : ℝ) < 0 := by
    exact_mod_cast hneg
  linarith

/-- **Termination of elementary dlt programs**, assuming termination for klt fourfolds. -/
private theorem n_ne_top_of_kltTermination
    (hklt : ∀ {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X]
      [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X},
      topologicalKrullDim X = 4 → IsKltPair sX B → ∀ P : Program sX K B, P.n ≠ ⊤)
    {X : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {Δ : QDivisor X} (hdim : topologicalKrullDim X = 4)
    (P : ElementaryDltProgram sX K Δ) : P.n ≠ ⊤ := by
  intro htop
  have hlt : ∀ j : ℕ, (j : ℕ∞) < P.n := fun j => htop ▸ ENat.coe_lt_top j
  have hstep := fun j => P.isProjectiveElementaryDltStep j (hlt j)
  -- the canonical divisors cut out by one rational top form
  let KY' : ∀ j, Divisor (P.Y j) := fun j => Nat.rec (motive := fun j => Divisor (P.Y j))
    (flipTransform (P.f 0) (P.fp 0) K) (fun j D => flipTransform (P.f (j + 1)) (P.fp (j + 1)) D) j
  let KS : ∀ j, Divisor (modelSeq X P.Y j) := divisorSeq K KY'
  have hKS : ∀ j, KS (j + 1) = flipTransform (P.f j) (P.fp j) (KS j) := by
    intro j; cases j <;> rfl
  have hcan : ∀ j, (KS j).IsCanonicalDivisor (modelStr sX P.sY j) 4 := by
    intro j
    induction j with
    | zero =>
      obtain ⟨m, hm⟩ := P.isProjectiveQFactorialDltPair_zero.isCanonicalDivisor
      obtain rfl : m = 4 := by exact_mod_cast hm.topologicalKrullDim_eq.symm.trans hdim
      exact hm
    | succ j ih =>
      rw [hKS]
      exact isCanonicalDivisor_flipTransform_of_step (hstep j) ih
  have hdimj : ∀ j, topologicalKrullDim (modelSeq X P.Y j) = 4 := fun j => by
    exact_mod_cast (hcan j).topologicalKrullDim_eq
  have hstep' := fun j => step_rebase (hstep j) (hcan j)
  have hpair := fun j => (hstep' j).isProjectiveQFactorialDltPair
  have hprops := fun j => contraction_props (hpair j) (hstep' j).isNegativeExtremalRayOf
    (hstep' j).isContractionOfRay
  have hdiag := fun j => (hstep' j).isFourfoldStepDiagram (hdimj j) (hprops j).1 (hprops j).2.1
    (hprops j).2.2
  -- the step sequence of the program
  let S : StepSequence :=
    { X := modelSeq X P.Y
      sX := modelStr sX P.sY
      K := KS
      B := divisorSeq Δ P.ΔY
      Z := P.V
      sZ := P.sV
      f := P.f
      fp := P.fp
      isFourfoldStepDiagram := hdiag
      K_eq := hKS
      B_eq := fun j => (hstep j).eq_flipTransform }
  -- only finitely many steps are divisorial
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ j, N₀ ≤ j →
      IsSmallMorphism (modelStr sX P.sY j) (P.sV j) (P.f j) := by
    have hfin := S.finite_setOf_exists_primeDivisor_isExceptionalValuation
    have hsub : {j | ¬ IsSmallMorphism (modelStr sX P.sY j) (P.sV j) (P.f j)} ⊆
        {i | ∃ (E : MMP.Mori.PrimeDivisor (S.X i))
          (ξ : Valuation (S.X (i + 1)).functionField (WithZero (Multiplicative ℤ))),
          S.IsTransportedValuation i E.divisorialValuation ξ ∧
            MMP.Intersection.IsExceptionalValuation ℂ (S.sX (i + 1)) ξ} := by
      intro j hj
      obtain ⟨E, v, hv, hcomap⟩ :=
        (hdiag j).exists_isExceptionalValuation_of_not_isSmallMorphism hj
      exact ⟨E, v, hcomap, hv⟩
    obtain ⟨N, hN⟩ := (hfin.subset hsub).bddAbove
    exact ⟨N + 1, fun j hj => by_contra fun h => absurd (hN h) (by omega)⟩
  -- the tail from `N₀` is a sequence of flips
  have hcurve := fun j => exists_properCurve_numericalClass_ne_zero (hpair j)
    (hstep' j).isContractionOfRay (hstep' j).isBirationalMorphism (hprops j).2.1 (hprops j).2.2
  choose C hC hCne using hcurve
  have hfl := fun k => exists_isFlip (hdiag (N₀ + k)) (hN₀ (N₀ + k) (Nat.le_add_right _ _))
    (hstep' (N₀ + k)).isNegativeExtremalRayOf (hstep' (N₀ + k)).isContractionOfRay
    (C (N₀ + k)) (hC (N₀ + k)) (hCne (N₀ + k))
  choose φ hφ using fun k => (hfl k).2.2
  let S' : Flips.SequenceOfFlips (modelStr sX P.sY N₀) 4 (KS N₀) (divisorSeq Δ P.ΔY N₀) :=
    { isNormalVariety := (hdiag N₀).isNormalVariety_minus
      isCanonicalDivisor := ⟨inferInstance, inferInstance, hcan N₀⟩
      isQCartier := ⟨inferInstance, inferInstance, (hdiag N₀).isQCartier_minus⟩
      length := ⊤
      one_le_length := le_top
      model := fun k => ⟨modelSeq X P.Y (N₀ + k), modelStr sX P.sY (N₀ + k), KS (N₀ + k),
        divisorSeq Δ P.ΔY (N₀ + k)⟩
      model_zero := rfl
      isNormalVariety_model := fun i _ => (hdiag (N₀ + i)).isNormalVariety_minus
      isLocallyNoetherian_model := fun i => inferInstanceAs (IsLocallyNoetherian
        (modelSeq X P.Y (N₀ + i)))
      isNormal_model := fun i => inferInstanceAs (IsNormal (modelSeq X P.Y (N₀ + i)))
      compactSpace_model := fun i => inferInstanceAs (CompactSpace (modelSeq X P.Y (N₀ + i)))
      isCanonicalDivisor_model := fun i _ => hcan (N₀ + i)
      base := fun k => P.V (N₀ + k)
      baseStr := fun k => P.sV (N₀ + k)
      contraction := fun k => P.f (N₀ + k)
      flip := fun k => P.fp (N₀ + k)
      flipMap := φ
      isNegativeExtremalContraction := fun i _ => (hfl i).1
      isSmall := fun i _ => (hfl i).2.1
      isFlip := fun i _ => (hφ i).1
      transform_eq := fun i _ => (hstep (N₀ + i)).eq_flipTransform.trans (hφ i).2 }
  haveI : LocallyOfFiniteType (modelStr sX P.sY N₀) :=
    (hpair N₀).isProjectiveVariety.toLocallyOfFiniteType
  have hST := SequenceOfFlips.eventually_disjoint_exceptionalSet_supp_roundDown
    (hpair N₀).isProjectiveVariety (hdimj N₀) (hpair N₀).isQFactorial (hpair N₀).isDltPair S' rfl
    (fun i => (hprops (N₀ + i)).1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hST
  -- from `N₁` on, the flipping and flipped loci avoid the reduced boundaries
  have hdisj : ∀ j, N₀ + M ≤ j →
      Disjoint (MMP.Mori.exceptionalSet (P.f j) : Set (modelSeq X P.Y j))
          (DivisorWithCoeffs.roundDown (divisorSeq Δ P.ΔY j)).supp ∧
        Disjoint (MMP.Mori.exceptionalSet (P.fp j) : Set (P.Y j))
          (DivisorWithCoeffs.roundDown (P.ΔY j)).supp := by
    intro j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right N₀ M) hj)
    obtain ⟨h1, h2⟩ := hM i (by omega)
    have hD := hdiag (N₀ + i)
    haveI := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
    haveI := hD.isProper_plus
    exact ⟨h1.mono_left (mori_exceptionalSet_subset hD.isNormalVariety_minus
        hD.isNormalVariety_target hD.isIso_app_minus hD.isBirationalMorphism_minus),
      h2.mono_left (mori_exceptionalSet_subset hD.isNormalVariety_plus hD.isNormalVariety_target
        hD.isIso_app_plus hD.isBirationalMorphism_plus)⟩
  -- removing the reduced boundaries gives permitted steps of klt pairs
  set N₁ := N₀ + M with hN₁
  let Δ'' : ∀ j, QDivisor (modelSeq X P.Y j) := fun j =>
    divisorSeq Δ P.ΔY j - Divisor.toQDivisor (DivisorWithCoeffs.roundDown (divisorSeq Δ P.ΔY j))
  have hperm : ∀ j, N₁ ≤ j →
      flipTransform (P.f j) (P.fp j) (Δ'' j) = Δ'' (j + 1) ∧
        IsPermittedStep (modelStr sX P.sY j) (P.sV j) (P.sY j) (KS j) (Δ'' j) (P.R j) (P.f j)
          (P.fp j) := by
    intro j hj
    have hsm := hN₀ j (by omega)
    have heq := (hstep j).eq_flipTransform
    obtain ⟨hE1, hE2⟩ := hdisj j hj
    have h' : IsProjectiveQFactorialDltPair (P.sY j) (flipTransform (P.f j) (P.fp j) (KS j))
        (flipTransform (P.f j) (P.fp j) (divisorSeq Δ P.ΔY j)) := by
      rw [← hKS, ← heq]; exact hpair (j + 1)
    have hE2' : Disjoint (MMP.Mori.exceptionalSet (P.fp j) : Set (P.Y j))
        (DivisorWithCoeffs.roundDown (flipTransform (P.f j) (P.fp j)
          (divisorSeq Δ P.ΔY j))).supp := by
      rw [← heq]; exact hE2
    obtain ⟨hA, hB⟩ := IsFlipOf.isPermittedStep_sub_roundDown (hpair j) (hdimj j)
      (hstep' j).isNegativeExtremalRayOf (hstep' j).isContractionOfRay hsm (hprops j).1
      (hprops j).2.1 ((hstep' j).isFlipOf_of_isSmallMorphism hsm) h' hE1 hE2'
    refine ⟨?_, hB⟩
    rw [hA, ← heq]
    rfl
  -- the klt program of the tail
  let Y' : ℕ → Scheme.{0} := fun i => P.Y (N₁ + i)
  let sY' : ∀ i, Y' i ⟶ Spec (.of ℂ) := fun i => P.sY (N₁ + i)
  let R' : ∀ i, Set (NumericalCurveClasses (modelStr (modelStr sX P.sY N₁) sY' i)) := fun i =>
    match i with
    | 0 => P.R N₁
    | i + 1 => P.R (N₁ + i + 1)
  let f' : ∀ i, modelSeq (modelSeq X P.Y N₁) Y' i ⟶ P.V (N₁ + i) := fun i =>
    match i with
    | 0 => P.f N₁
    | i + 1 => P.f (N₁ + i + 1)
  have hperm' : ∀ i, IsPermittedStep (modelStr (modelStr sX P.sY N₁) sY' i) (P.sV (N₁ + i))
      (sY' i) (divisorSeq (KS N₁) (fun i => KS (N₁ + i + 1)) i)
      (divisorSeq (Δ'' N₁) (fun i => Δ'' (N₁ + i + 1)) i) (R' i) (f' i) (P.fp (N₁ + i)) := by
    intro i
    rcases i with _ | i
    · exact (hperm N₁ le_rfl).2
    · exact (hperm (N₁ + i + 1) (by omega)).2
  let P' : Program (modelStr sX P.sY N₁) (KS N₁) (Δ'' N₁) :=
    { n := ⊤
      Y := Y'
      sY := sY'
      isIntegral := fun i => inferInstanceAs (IsIntegral (P.Y (N₁ + i)))
      compactSpace := fun i => inferInstanceAs (CompactSpace (P.Y (N₁ + i)))
      isLocallyNoetherian := fun i => inferInstanceAs (IsLocallyNoetherian (P.Y (N₁ + i)))
      isNormal := fun i => inferInstanceAs (IsNormal (P.Y (N₁ + i)))
      KY := fun i => KS (N₁ + i + 1)
      BY := fun i => Δ'' (N₁ + i + 1)
      R := R'
      Z := fun i => P.V (N₁ + i)
      sZ := fun i => P.sV (N₁ + i)
      f := f'
      fp := fun i => P.fp (N₁ + i)
      isProjectiveVariety := (hpair N₁).isProjectiveVariety
      isLogCanonicalPair := (hperm N₁ le_rfl).2.isLogCanonicalPair
      isCanonicalDivisor := ⟨4, hcan N₁⟩
      isPermittedStep := fun i _ => hperm' i
      KY_eq := fun i _ => by
        rcases i with _ | i
        · exact hKS N₁
        · exact hKS (N₁ + i + 1)
      BY_eq := fun i _ => by
        rcases i with _ | i
        · exact (hperm N₁ le_rfl).1.symm
        · exact (hperm (N₁ + i + 1) (by omega)).1.symm
      hasFinal := False
      finalRay := ∅
      T := modelSeq (modelSeq X P.Y N₁) Y' (⊤ : ℕ∞).toNat
      sT := modelStr (modelStr sX P.sY N₁) sY' (⊤ : ℕ∞).toNat
      g := 𝟙 _
      final_spec := fun h => h.elim }
  -- the klt start
  have hdlt := (hpair N₁).isDltPair
  have hcoeff : ∀ Q, (Δ'' N₁) Q = (divisorSeq Δ P.ΔY N₁) Q - ⌊(divisorSeq Δ P.ΔY N₁) Q⌋ :=
    fun Q => by simp [Δ'', ← DivisorWithCoeffs.coeff_apply]
  have hdlt' : MMP.Intersection.IsDltPair (modelStr sX P.sY N₁) (Δ'' N₁) := by
    refine MMP.Intersection.IsDltPair.of_le (modelStr sX P.sY N₁) hdlt (fun Q => ?_) (fun Q => ?_)
      (isQCartier_of_isQFactorial _ (hpair N₁).isQFactorial _)
    · rw [Finsupp.coe_zero, Pi.zero_apply, hcoeff]
      exact sub_nonneg.mpr (Int.floor_le _)
    · rw [hcoeff]
      have : (0 : ℚ) ≤ ⌊(divisorSeq Δ P.ΔY N₁) Q⌋ := by
        exact_mod_cast Int.floor_nonneg.mpr (hdlt.1.2.1 Q)
      linarith
  have hkltN : IsKltPair (modelStr sX P.sY N₁) (Δ'' N₁) :=
    MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one hdlt' fun Q => by
      rw [DivisorWithCoeffs.coeff_apply, hcoeff]
      linarith [Int.lt_floor_add_one ((divisorSeq Δ P.ΔY N₁) Q)]
  exact hklt (hdimj N₁) hkltN P' rfl

private theorem solution : ∀ {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {Δ : QDivisor X} (hdim : topologicalKrullDim X = 4)
    (P : ElementaryDltProgram sX K Δ), P.n ≠ ⊤ :=
  fun hdim P => n_ne_top_of_kltTermination
    (fun hdim hB P => Program.n_ne_top_of_isKltPair hdim hB P) hdim P

end Proof_thm_oai4_dlt_termination

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Termination of elementary dlt programs.** Every elementary dlt program from a projective
`ℚ`-factorial dlt fourfold pair `(X, Δ)` over `ℂ` with rational boundary is finite, whatever the
successive choices of negative extremal rays: its number of steps `P.n` is not `⊤`. -/
@[mmp "thm_oai4_dlt_termination"]
public theorem ElementaryDltProgram.n_ne_top {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {Δ : QDivisor X} (hdim : topologicalKrullDim X = 4)
    (P : ElementaryDltProgram sX K Δ) : P.n ≠ ⊤ :=
      by revert X sX K Δ hdim P; first | exact Proof_thm_oai4_dlt_termination.solution | exact Proof_thm_oai4_dlt_termination.solution _ | exact Proof_thm_oai4_dlt_termination.solution _ _ | exact Proof_thm_oai4_dlt_termination.solution _ _ _ | exact Proof_thm_oai4_dlt_termination.solution _ _ _ _

end MMP.Fourfold

