module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.OrderPullback
public import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Resolution.TransformRestriction
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderIso
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.NineClauses
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasiAffineDivisorRepresentation
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.StandardResolution
public import StacksFrontier.AlgebraicGeometry.NodalContraction.DvrStalk
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineOpenSideCondition
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.TensorTotalComplex

/-!
# Zariski sequences, sections avoiding finitely many points, and flips

This file collects three groups of results from Kollár–Mori.

**Zariski sequences** (Kollár–Mori, Lemma 2.45). Let `X` be an integral scheme and `R ⊆ k(X)` a
valuation ring, not a field, dominating the local ring `𝒪_{x₀,X}`. A Zariski sequence
`(Xᵢ, βᵢ, fᵢ)` of `Spec R ⟶ Spec 𝒪_{x₀,X} ⟶ X` blows up, at each step, the closure of the centre
of `R`. Such a sequence exists, and along it every `Xᵢ` is integral and `R` dominates every local
ring `𝒪ᵢ = 𝒪_{xᵢ,Xᵢ}` at the centre. When `X` is of finite type over a field `k₀` and `R` is a
discrete valuation ring, the `𝒪ᵢ` form an increasing chain of subrings of `R` with union `R`. If
moreover the residue field of `R` has transcendence degree `dim X - 1`, the chain reaches `R`:
the valuation of `R` is the order of vanishing along a prime divisor of some blow-up `Xₙ`.

**Sections avoiding points** (Kollár–Mori, §1.4). Let `X` be proper over a field `K`, `A` an
ample and `L` an arbitrary Cartier divisor. For `m ≫ 0`, some global section of `𝒪_X(L + mA)`
does not vanish at any point of a given finite set. Applied to the associated points, its divisor
is an effective Cartier divisor `B` with `𝒪_X(B) ≅ 𝒪_X(L + mA)` containing no associated point,
hence no irreducible component of `X`.

**Flips** (Kollár–Mori, §3.3). Let `f⁺ : X⁺ ⟶ Y` be a `(K + D)`-flip of a flipping contraction
`f : X ⟶ Y`. The birational map `X ⤏ X⁺` is an isomorphism in codimension one, and a divisor
over `X` is exceptional over `X⁺` exactly when it is exceptional over `X`, and is then
exceptional over `Y`.

## Main results

* `MMP.Mori.ZariskiSequence.nonempty_and_forall_isIntegral`: Zariski sequences exist, and every
  one consists of integral schemes whose local rings at the centre are dominated by `R`.
* `MMP.Mori.ZariskiSequence.iSup_range_stalkClosedPointTo_eq_top`: the local rings `𝒪ᵢ`,
  embedded in `R`, form an increasing chain with union `R`.
* `MMP.Mori.ZariskiSequence.exists_isIso_stalkClosedPointTo`: for a divisorial valuation, some
  stalk map `𝒪_{xₙ,Xₙ} ⟶ R` is an isomorphism.
* `MMP.Mori.eventually_exists_forall_mem_nonvanishingLocus_sheaf_add_nsmul`: for `m ≫ 0`, a
  section of `𝒪_X(L + mA)` not vanishing at finitely many given points.
* `MMP.Mori.eventually_exists_isEffective_sheaf_iso_disjoint_schemeAssociatedPoints`: for
  `m ≫ 0`, an effective divisor in `|L + mA|` avoiding the associated points.
* `MMP.Mori.IsFlipRationalMap.isIsomorphismInCodimOne`: a flip is an isomorphism in
  codimension one.
* `MMP.Mori.IsFlip.isExceptional_iff_and_isExceptional_comp`: exceptional divisors of a flip
  correspond.

## Implementation notes

The inclusions `𝒪ᵢ ⊆ R` are expressed through the stalk maps
`Scheme.stalkClosedPointTo (S.mor i)`, which avoids identifying each `k(Xᵢ)` with `k(X)`; the
equality `𝒪ₙ = R` is the isomorphism of that stalk map. In the divisorial case, the equation
`trdeg = dim X - 1` is written `trdeg + 1 = dim X` in `WithBot ℕ∞`. The exhaustion is proved by
well-founded induction on divisibility in `R`: each blow-up divides the maximal ideal of `𝒪ₙ`
by a fixed non-unit inside `𝒪ₙ₊₁`. The divisorial case shows `dim 𝒪ₙ ≤ 1` for `n ≫ 0` by the
dimension formula, and then that the integral closure of `𝒪ₙ` in `R`, a Dedekind domain because
`𝒪ₙ` is Nagata, lies in some `𝒪_p`, whence `𝒪_p = R`.

"Projective over `K`" is stated as proper over `K` together with the ampleness of `𝒪_X(A)`,
which is equivalent (Hartshorne II.7.6, II.4.9). The value `s(x)` of a section is non-zero
exactly when `x` lies in its nonvanishing locus `Stacks.Ample.nonvanishingLocus`. For closed
points, the source surjects `H⁰(X, 𝒪_X(L + mA))` onto `⊕ 𝒪_X(L + mA) ⊗ κ(y)` through
`H¹(X, I_T(L + mA)) = 0`; here the section is instead a sum `∑ σ_y b_y`, with `b_y` a section of
a multiple of `A` vanishing on the other points and `σ_y` given by Serre's global generation.

A divisor over `X⁺` is identified with a divisor `E` over `X` when their valuations agree on
`k(Y)`. Exceptionality is read through coheights: a prime divisor `E` of a normal scheme is
exceptional for `g` exactly when `g(η_E)` has coheight at least two.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §1.4, Lemma
  2.45, §3.3, Corollary 3.42
* [R. Hartshorne, *Algebraic geometry*], II.6.13, II.6.17, II.7.6
* [M. F. Atiyah, I. G. Macdonald, *Introduction to commutative algebra*], 4.7
* [Stacks Project, Tags 01Q3, 02OK, 05AH, 09NV]
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori.ZariskiSequence

/-! ### Existence of Zariski sequences -/

section Existence

open IsLocalRing TopologicalSpace

variable {A : Type u} [CommRing A] [IsDomain A]

/-- The specialisation map of stalks into the generic point of an integral scheme is
injective. -/
private lemma stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y] {w z : Y}
    (hw : IsGenericPoint w Set.univ) (h : w ⤳ z) :
    Function.Injective (Y.presheaf.stalkSpecializes h) := by
  obtain rfl : w = genericPoint Y := hw.eq (genericPoint_spec Y)
  exact IsFractionRing.injective (Y.presheaf.stalk z) Y.functionField

private lemma stalkSpecializes_bijective_of_eq {Y : Scheme.{u}} {a b : Y} (hab : a = b)
    (h : a ⤳ b) : Function.Bijective (Y.presheaf.stalkSpecializes h) := by
  subst hab
  rw [show h = specializes_refl a from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

/-- The image of the point of the spectrum of a field under an injective map is the generic
point. -/
private lemma Spec_map_apply_eq_genericPoint {K : Type u} [Field K] (φ : A →+* K)
    (hφ : Function.Injective φ) (q : Spec (.of K)) :
    Spec.map (CommRingCat.ofHom φ) q = genericPoint (Spec (.of A)) := by
  rw [genericPoint_eq_bot_of_affine]
  refine PrimeSpectrum.ext ?_
  change Ideal.comap φ q.asIdeal = ⊥
  haveI := q.isPrime
  rw [Ideal.eq_bot_of_prime q.asIdeal]
  exact Ideal.comap_bot_of_injective φ hφ

/-- The stalk maps of `g` are injective as soon as the one at the generic point is. -/
private lemma stalkMap_injective {Y : Scheme.{u}} [IsIntegral Y] (g : Spec (.of A) ⟶ Y)
    (ha : IsGenericPoint (g (genericPoint (Spec (.of A)))) Set.univ)
    (hb : Function.Injective (g.stalkMap (genericPoint (Spec (.of A))))) (p : Spec (.of A)) :
    Function.Injective (g.stalkMap p) := by
  have hηp : genericPoint (Spec (.of A)) ⤳ p := (genericPoint_spec _).specializes trivial
  intro s t hst
  apply stalkSpecializes_injective ha (g.base.hom.map_specializes hηp)
  apply hb
  rw [g.stalkSpecializes_stalkMap_apply _ _ hηp, g.stalkSpecializes_stalkMap_apply _ _ hηp, hst]

/-- If the stalk map at the generic point is surjective and `A` is not a field, the closed
point does not go to the generic point. -/
private lemma not_isGenericPoint_closedPoint [IsLocalRing A] {Y : Scheme.{u}}
    (g : Spec (.of A) ⟶ Y) (hA : ¬ IsField A)
    (ha : IsGenericPoint (g (genericPoint (Spec (.of A)))) Set.univ)
    (hb : Function.Surjective (g.stalkMap (genericPoint (Spec (.of A))))) :
    ¬ IsGenericPoint (g (closedPoint A)) Set.univ := by
  intro hy
  let y : Spec (.of A) := closedPoint A
  have hηy : genericPoint (Spec (.of A)) ⤳ y := (genericPoint_spec _).specializes trivial
  have hsurj : Function.Surjective ((Spec (.of A)).presheaf.stalkSpecializes hηy) := by
    intro t
    obtain ⟨s, rfl⟩ := hb t
    obtain ⟨s', rfl⟩ := (stalkSpecializes_bijective_of_eq (ha.eq hy)
      (g.base.hom.map_specializes hηy)).2 s
    exact ⟨g.stalkMap y s', (g.stalkSpecializes_stalkMap_apply _ _ hηy s').symm⟩
  let e₁ := RingEquiv.ofBijective ((Spec (.of A)).presheaf.stalkSpecializes hηy).hom
    ⟨stalkSpecializes_injective (genericPoint_spec (Spec (.of A))) hηy, hsurj⟩
  let e₂ := (stalkClosedPointIso (.of A)).commRingCatIsoToRingEquiv
  exact hA (MulEquiv.isField (Field.toIsField (Spec (.of A)).functionField)
    (e₂.symm.trans e₁).toMulEquiv)

/-- The property carried along a Zariski sequence. -/
private def Good (Y : Scheme.{u}) (g : Spec (.of A) ⟶ Y) : Prop :=
  IsIntegral Y ∧ IsLocallyNoetherian Y ∧ IsGenericPoint (g (genericPoint (Spec (.of A))))
    Set.univ ∧ Function.Bijective (g.stalkMap (genericPoint (Spec (.of A))))

private lemma good_of_comp {W Y : Scheme.{u}} (g : Spec (.of A) ⟶ W) (e : W ⟶ Y)
    [IsOpenImmersion e] (h : Good Y (g ≫ e)) : Good W g := by
  obtain ⟨hY, hYn, ha, hb⟩ := h
  have : Nonempty W := ⟨g (genericPoint _)⟩
  have hW : IsIntegral W := isIntegral_of_isOpenImmersion e
  refine ⟨hW, isLocallyNoetherian_of_isOpenImmersion e, ?_, ?_⟩
  · have h1 : e (g (genericPoint _)) = e (genericPoint W) := by
      rw [genericPoint_eq_of_isOpenImmersion e]
      exact ha.eq (genericPoint_spec Y)
    rw [e.isOpenEmbedding.injective h1]
    exact genericPoint_spec W
  · have hb' : Function.Bijective ((g.stalkMap _).hom ∘ (e.stalkMap (g (genericPoint _))).hom) := by
      rwa [Scheme.Hom.stalkMap_comp] at hb
    exact (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso _)).mp hb'

private lemma centerIdeal_ne_bot [IsLocalRing A] (hA : ¬ IsField A) {Y : Scheme.{u}}
    (g : Spec (.of A) ⟶ Y) (hg : Good Y g) : centerIdeal g ≠ ⊥ := by
  intro hI
  have h := support_centerIdeal g
  rw [hI, Scheme.IdealSheafData.support_bot] at h
  exact not_isGenericPoint_closedPoint g hA hg.2.2.1 hg.2.2.2.2
    (isGenericPoint_def.mpr (h.symm.trans TopologicalSpace.Closeds.coe_top))

/-- A point of the blow-up over the generic point of the base is the generic point. -/
private lemma eq_genericPoint_of_blowUpToBase_eq {Y : Scheme.{u}} [IsIntegral Y]
    (I : Y.IdealSheafData) (hI : I ≠ ⊥) [IsIntegral (blowUp I)] (z : blowUp I)
    (hz : blowUpToBase I z = genericPoint Y) : z = genericPoint (blowUp I) := by
  let W : Y.Opens := ⟨(I.support : Set Y)ᶜ, I.support.isClosed.isOpen_compl⟩
  have hiso : IsIso (blowUpToBase I ∣_ W) := isIso_blowUp_restrict_compl_support I
  have hzV : z ∈ blowUpToBase I ⁻¹ᵁ W := by
    change blowUpToBase I z ∈ W
    rw [hz]
    exact genericPoint_notMem_supportSet I hI
  have hgen : genericPoint (blowUp I) ∈ blowUpToBase I ⁻¹ᵁ W :=
    ((genericPoint_spec _).mem_open_set_iff (Opens.isOpen _)).mpr ⟨z, trivial, hzV⟩
  have hbgen : blowUpToBase I (genericPoint (blowUp I)) = genericPoint Y := by
    have := (isBirational_blowUpToBase I hI).bijOn.mapsTo
      (show genericPoint (blowUp I) ∈ genericPoints (blowUp I) by
        simp [genericPoints_eq_singleton])
    simpa [genericPoints_eq_singleton] using this
  have key : ∀ p : (blowUpToBase I ⁻¹ᵁ W).toScheme,
      W.ι ((blowUpToBase I ∣_ W) p) = blowUpToBase I p.1 := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
    rfl
  have : (⟨z, hzV⟩ : (blowUpToBase I ⁻¹ᵁ W).toScheme) = ⟨genericPoint _, hgen⟩ := by
    apply (blowUpToBase I ∣_ W).isOpenEmbedding.injective
    apply W.ι.isOpenEmbedding.injective
    exact (key _).trans (hz.trans (hbgen.symm.trans (key ⟨_, hgen⟩).symm))
  exact congrArg Subtype.val this

private lemma good_blowUp [IsLocalRing A] (hA : ¬ IsField A) {Y : Scheme.{u}}
    (g : Spec (.of A) ⟶ Y) (hg : Good Y g) (h : Spec (.of A) ⟶ blowUp (centerIdeal g))
    (hh : h ≫ blowUpToBase (centerIdeal g) = g) : Good (blowUp (centerIdeal g)) h := by
  have hI := centerIdeal_ne_bot hA g hg
  obtain ⟨hY, hYn, ha, hb⟩ := hg
  have hBI : IsIntegral (blowUp (centerIdeal g)) := isIntegral_blowUp _ hI
  have hz : h (genericPoint _) = genericPoint (blowUp (centerIdeal g)) :=
    eq_genericPoint_of_blowUpToBase_eq _ hI _ (by
      rw [← Scheme.Hom.comp_apply, hh]
      exact ha.eq (genericPoint_spec Y))
  refine ⟨hBI, LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase _), ?_, ?_⟩
  · rw [hz]
    exact genericPoint_spec _
  · have hb' : Function.Bijective ((h.stalkMap _).hom ∘
        ((blowUpToBase (centerIdeal g)).stalkMap (h (genericPoint _))).hom) := by
      rwa [← hh, Scheme.Hom.stalkMap_comp] at hb
    have : IsIso ((blowUpToBase (centerIdeal g)).stalkMap (h (genericPoint _))) := by
      rw [hz]
      exact (isBirational_blowUpToBase _ hI).isIso_stalkMap _
        (by simp [genericPoints_eq_singleton])
    exact (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso _)).mp hb'

private lemma exists_lift [ValuationRing A] (hA : ¬ IsField A) {Y : Scheme.{u}}
    (g : Spec (.of A) ⟶ Y) (hg : Good Y g) :
    ∃ h : Spec (.of A) ⟶ blowUp (centerIdeal g), h ≫ blowUpToBase (centerIdeal g) = g := by
  have hI := centerIdeal_ne_bot hA g hg
  obtain ⟨hY, hYn, ha, hb⟩ := hg
  set I := centerIdeal g
  set b := blowUpToBase I
  let K := FractionRing A
  let ι : Spec (.of K) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let W : Y.Opens := ⟨(I.support : Set Y)ᶜ, I.support.isClosed.isOpen_compl⟩
  have hiso : IsIso (b ∣_ W) := isIso_blowUp_restrict_compl_support I
  have hrange : Set.range (ι ≫ g) ⊆ Set.range W.ι := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply,
      Spec_map_apply_eq_genericPoint _ (IsFractionRing.injective A K),
      ha.eq (genericPoint_spec Y)]
    exact genericPoint_notMem_supportSet I hI
  let i₁ : Spec (.of K) ⟶ blowUp I :=
    IsOpenImmersion.lift W.ι (ι ≫ g) hrange ≫ inv (b ∣_ W) ≫ (b ⁻¹ᵁ W).ι
  have hi₁ : i₁ ≫ b = ι ≫ g := by
    simp only [i₁, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      IsOpenImmersion.lift_fac]
  have hE : ValuativeCriterion.Existence b :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed b)).1
  obtain ⟨⟨⟨l, -, hl⟩⟩⟩ := hE { R := A, K := K, i₁ := i₁, i₂ := g, commSq := ⟨hi₁⟩ }
  exact ⟨l, hl⟩

private lemma good_fromSpecOfStalkLE {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x₀ : X) (R : Subring X.functionField)
    (hS : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ R) :
    Good X (fromSpecOfStalkLE x₀ R hS) := by
  let ι : Spec (.of X.functionField) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom R.subtype)
  have hι : ι ≫ fromSpecOfStalkLE x₀ R hS = X.fromSpecStalk (genericPoint X) := by
    rw [fromSpecOfStalkLE, ← Category.assoc, ← Spec.map_comp,
      ← X.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)]
    rfl
  let pt : Spec (.of X.functionField) := closedPoint X.functionField
  have hpt : ι pt = genericPoint (Spec (.of R)) :=
    Spec_map_apply_eq_genericPoint _ Subtype.val_injective _
  refine ⟨‹_›, ‹_›, ?_, ?_⟩
  · rw [← hpt, ← Scheme.Hom.comp_apply, hι]
    rw [Scheme.fromSpecStalk_closedPoint]
    exact genericPoint_spec X
  · have h1 : Function.Bijective ((ι ≫ fromSpecOfStalkLE x₀ R hS).stalkMap pt) := by
      rw [hι]
      haveI := isIso_stalkMap_fromSpecStalk (genericPoint X) pt
      exact ConcreteCategory.bijective_of_isIso _
    have h1' : Function.Bijective ((ι.stalkMap pt).hom ∘
        ((fromSpecOfStalkLE x₀ R hS).stalkMap (ι pt)).hom) := by
      rwa [Scheme.Hom.stalkMap_comp] at h1
    have hfield : IsField ((Spec (.of R)).presheaf.stalk (ι pt)) := by
      rw [hpt]
      exact Field.toIsField (Spec (.of R)).functionField
    letI := hfield.toField
    have h2 : Function.Bijective ((fromSpecOfStalkLE x₀ R hS).stalkMap (ι pt)) :=
      ⟨h1'.1.of_comp, fun t => by
        obtain ⟨s, hs⟩ := h1'.2 ((ι.stalkMap pt).hom t)
        exact ⟨s, (ι.stalkMap pt).hom.injective hs⟩⟩
    rwa [hpt] at h2

private lemma good_topIso_inv {Y : Scheme.{u}} {g : Spec (.of A) ⟶ Y} (hg : Good Y g) :
    Good (⊤ : Y.Opens) (g ≫ (Scheme.topIso Y).inv) :=
  good_of_comp _ (Scheme.topIso Y).hom (by simpa using hg)

/-- The properties asserted of every term of a Zariski sequence follow from the carried one. -/
private lemma Good.conclusion [IsLocalRing A] (hA : ¬ IsField A) {Y : Scheme.{u}}
    {g : Spec (.of A) ⟶ Y} (hg : Good Y g) :
    IsIntegral Y ∧ IsGenericPoint (g (genericPoint (Spec (.of A)))) Set.univ ∧
      Function.Bijective (g.stalkMap (genericPoint (Spec (.of A)))) ∧
      ¬ IsGenericPoint (g (IsLocalRing.closedPoint A)) Set.univ ∧
      Function.Injective (g.stalkMap (IsLocalRing.closedPoint A)) := by
  obtain ⟨hY, -, ha, hb⟩ := hg
  exact ⟨hY, ha, hb, not_isGenericPoint_closedPoint g hA ha hb.2, stalkMap_injective g ha hb.1 _⟩

/-- **Kollár–Mori, Lemma 2.45.** For a valuation ring `R ⊆ k(X)`, not a field, dominating
`𝒪_{x₀,X}`, a Zariski sequence for `Spec R ⟶ X` exists; in every Zariski sequence each `Xᵢ` is
integral, `fᵢ` maps the generic point to the generic point inducing an isomorphism of function
fields, `fᵢ(y)` is not the generic point of `Xᵢ`, and the stalk map `𝒪_{fᵢ(y),Xᵢ} ⟶ R` is
injective. -/
@[mmp "lem_km1a_zariski_sequence_exists"]
public theorem nonempty_and_forall_isIntegral {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (x₀ : X) (R : Subring X.functionField) [ValuationRing R]
    (hR : ¬ IsField R)
    (hS : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ R)
    (hloc : IsLocalHom ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hS)) :
    Nonempty (ZariskiSequence X (fromSpecOfStalkLE x₀ R hS)) ∧
      ∀ (Z : ZariskiSequence X (fromSpecOfStalkLE x₀ R hS)) (i : ℕ),
        IsIntegral (Z.obj i) ∧
        IsGenericPoint (Z.mor i (genericPoint (Spec (.of R)))) Set.univ ∧
        Function.Bijective ((Z.mor i).stalkMap (genericPoint (Spec (.of R)))) ∧
        ¬ IsGenericPoint (Z.mor i (IsLocalRing.closedPoint R)) Set.univ ∧
        Function.Injective ((Z.mor i).stalkMap (IsLocalRing.closedPoint R)) := by
  have h0 := good_fromSpecOfStalkLE x₀ R hS
  refine ⟨?_, fun Z i => Good.conclusion hR ?_⟩
  · let step : (Σ Y : Scheme.{u}, {g : Spec (.of R) ⟶ Y // Good Y g}) →
        (Σ Y : Scheme.{u}, {g : Spec (.of R) ⟶ Y // Good Y g}) := fun P =>
      ⟨blowUp (centerIdeal (P.2.1 ≫ (Scheme.topIso P.1).inv)),
        (exists_lift hR _ (good_topIso_inv P.2.2)).choose,
        good_blowUp hR _ (good_topIso_inv P.2.2) _
          (exists_lift hR _ (good_topIso_inv P.2.2)).choose_spec⟩
    let seq : ℕ → (Σ Y : Scheme.{u}, {g : Spec (.of R) ⟶ Y // Good Y g}) :=
      fun n => Nat.rec ⟨X, fromSpecOfStalkLE x₀ R hS, h0⟩ (fun _ P => step P) n
    exact ⟨{
      obj := fun i => (seq i).1
      mor := fun i => (seq i).2.1
      obj_zero := rfl
      mor_zero := by simp [seq]
      U := fun _ => ⊤
      morOpen := fun i => (seq i).2.1 ≫ (Scheme.topIso _).inv
      morOpen_ι := fun i => by simp
      obj_succ := fun _ => rfl
      mor_succ_comp := fun i => (exists_lift hR _ (good_topIso_inv (seq i).2.2)).choose_spec }⟩
  · induction i with
    | zero =>
      refine good_of_comp _ (eqToHom Z.obj_zero) ?_
      rwa [Z.mor_zero]
    | succ i ih =>
      have hU : Good (Z.U i) (Z.morOpen i) :=
        good_of_comp _ (Z.U i).ι (by rwa [Z.morOpen_ι])
      exact good_of_comp _ (eqToHom (Z.obj_succ i)) <|
        good_blowUp hR _ hU _ (by simpa using Z.mor_succ_comp i)

end Existence

/-! ### The local rings of a Zariski sequence exhaust the valuation ring -/

section Exhaust

open IsLocalRing

/-- The algebraic core: an increasing chain of subrings of a domain with well-founded
divisibility, closed under inverses of units, in which each step divides the non-units of the
previous ring by a fixed nonzero non-unit, and whose first member has all of `R` as fractions,
exhausts `R`. -/
private theorem iSup_eq_top_of_step {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R]
    (S : ℕ → Subring R)
    (hunit : ∀ n, ∀ s ∈ S n, IsUnit s → ∃ t ∈ S n, s * t = 1)
    (hstep : ∀ n, ∀ y ∈ S n, y ≠ 0 → ¬ IsUnit y → ∃ w : R, w ≠ 0 ∧ ¬ IsUnit w ∧
      ∀ y ∈ S n, ¬ IsUnit y → ∃ y' ∈ S (n + 1), y = w * y')
    (hfrac : ∀ u : R, ∃ y₁ ∈ S 0, ∃ y₂ ∈ S 0, y₂ ≠ 0 ∧ y₁ = u * y₂) :
    ⨆ n, S n = ⊤ := by
  have key : ∀ y₂ : R, ∀ n, y₂ ∈ S n → y₂ ≠ 0 → ∀ u y₁, y₁ ∈ S n → y₁ = u * y₂ →
      u ∈ ⨆ n, S n := by
    intro y₂
    induction y₂ using WellFounded.induction (wellFounded_dvdNotUnit (α := R)) with
    | h y₂ ih =>
      intro n hy₂ hy₂0 u y₁ hy₁ he
      by_cases hu : IsUnit y₂
      · obtain ⟨t, ht, hst⟩ := hunit n y₂ hy₂ hu
        rw [show u = y₁ * t by rw [he, mul_assoc, hst, mul_one]]
        exact le_iSup S n (Subring.mul_mem _ hy₁ ht)
      · obtain ⟨w, hw0, hwu, hw⟩ := hstep n y₂ hy₂ hy₂0 hu
        obtain ⟨y₂', hy₂', rfl⟩ := hw y₂ hy₂ hu
        have hy₁u : ¬ IsUnit y₁ := by
          rw [he]
          intro h
          exact hwu (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h))
        obtain ⟨y₁', hy₁', rfl⟩ := hw y₁ hy₁ hy₁u
        have hy₂'0 : y₂' ≠ 0 := right_ne_zero_of_mul hy₂0
        have hlt : DvdNotUnit y₂' (w * y₂') := ⟨hy₂'0, w, hwu, mul_comm _ _⟩
        exact ih y₂' hlt (n + 1) hy₂' hy₂'0 u y₁' hy₁' (mul_left_cancel₀ hw0 (he.trans (by ring)))
  rw [eq_top_iff]
  intro u _
  obtain ⟨y₁, hy₁, y₂, hy₂, h0, he⟩ := hfrac u
  exact key y₂ 0 hy₂ h0 u y₁ hy₁ he

/-- Postcomposition can only shrink the image of the stalk map at the closed point. -/
private theorem range_stalkClosedPointTo_comp_le {B : CommRingCat.{u}} [IsLocalRing B]
    {Y Z : Scheme.{u}} (f : Spec B ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.stalkClosedPointTo (f ≫ g)).hom.range ≤ (Scheme.stalkClosedPointTo f).hom.range := by
  rw [Scheme.stalkClosedPointTo_comp]
  rintro _ ⟨a, rfl⟩
  exact ⟨_, rfl⟩

/-- Postcomposition with the inclusion of an open does not change the image of the stalk map at
the closed point. -/
private theorem range_stalkClosedPointTo_comp_ι {B : CommRingCat.{u}} [IsLocalRing B]
    {Y : Scheme.{u}} (U : Y.Opens) (f : Spec B ⟶ U) :
    (Scheme.stalkClosedPointTo (f ≫ U.ι)).hom.range = (Scheme.stalkClosedPointTo f).hom.range := by
  refine le_antisymm (range_stalkClosedPointTo_comp_le f U.ι) ?_
  have : IsIso (U.ι.stalkMap (f (closedPoint B))) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  rw [Scheme.stalkClosedPointTo_comp]
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap _)).2 a
  exact ⟨b, rfl⟩

/-- The stalk map at the closed point of a morphism to an open is injective when that of its
composite with the inclusion of the open is. -/
private theorem injective_stalkClosedPointTo_of_comp_ι {B : CommRingCat.{u}} [IsLocalRing B]
    {Y : Scheme.{u}} (U : Y.Opens) (f : Spec B ⟶ U)
    (h : Function.Injective (Scheme.stalkClosedPointTo (f ≫ U.ι)).hom) :
    Function.Injective (Scheme.stalkClosedPointTo f).hom := by
  have : IsIso (U.ι.stalkMap (f (closedPoint B))) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  rw [Scheme.stalkClosedPointTo_comp] at h
  exact (show Function.Injective (_ ∘ (U.ι.stalkMap _).hom) from h).of_comp_right
    (ConcreteCategory.bijective_of_isIso _).2

/-- The image of the stalk map at the closed point of `Spec.map χ ≫ Y.fromSpecStalk y` is the
image of `χ`. -/
private theorem range_stalkClosedPointTo_eq {B : CommRingCat.{u}} [IsLocalRing B] {Y : Scheme.{u}}
    (f : Spec B ⟶ Y) (y : Y) (χ : Y.presheaf.stalk y ⟶ B) [hχ : IsLocalHom χ.hom]
    (hf : f = Spec.map χ ≫ Y.fromSpecStalk y) :
    Set.range (Scheme.stalkClosedPointTo f).hom = Set.range χ.hom := by
  have h := (SpecToEquivOfLocalRing Y B).apply_symm_apply ⟨y, χ, hχ⟩
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp h
  subst hf
  have h₃ : Scheme.stalkClosedPointTo (Spec.map χ ≫ Y.fromSpecStalk y) =
      (Y.presheaf.stalkCongr _).hom ≫ χ := h₂
  rw [h₃, CommRingCat.hom_comp, RingHom.coe_comp, Set.range_comp]
  refine (congrArg _ (Set.range_eq_univ.mpr ?_)).trans (Set.image_univ)
  exact (ConcreteCategory.bijective_of_isIso _).2

/-- A subring of `K` which is a valuation ring with fraction field `K`, as a valuation
subring. -/
private def toValuationSubring {K : Type u} [Field K] (R : Subring K) [ValuationRing R]
    [IsFractionRing R K] : ValuationSubring K where
  __ := R
  mem_or_inv_mem' x := by
    rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact .inl (ha ▸ a.2)
    · exact .inr (ha ▸ a.2)

/-- The maximal ideal of a stalk of a locally noetherian scheme has a finite generating
family. -/
private theorem exists_generators {Y : Scheme.{u}} [IsLocallyNoetherian Y] (x : Y) :
    ∃ (r : ℕ) (z : Fin r → Y.presheaf.stalk x),
      Ideal.span (Set.range z) = maximalIdeal (Y.presheaf.stalk x) :=
  Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian _)

/-- One step of a Zariski sequence: for `h : Spec R ⟶ Y` whose stalk map `𝒪 ⟶ R` at the
closed point is injective with fraction field all of `K`, and a lift `h'` of `h` to the blow-up
of the closure of the centre, there is a nonzero non-unit `w` in the image of `𝒪` such that
every non-unit of the image of `𝒪` is `w` times an element of the image of `𝒪'`. -/
private theorem step {k₀ : Type u} [Field k₀] {Y : Scheme.{u}} [IsIntegral Y]
    (sY : Y ⟶ Spec (.of k₀)) [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    {K : Type u} [Field K] (R : Subring K) [ValuationRing R] [IsFractionRing R K]
    (h : Spec (.of R) ⟶ Y) (hgen : h (closedPoint R) ≠ genericPoint Y)
    (hinj : Function.Injective (Scheme.stalkClosedPointTo h).hom)
    (hsurj : ∀ k : K, ∃ a b, ((Scheme.stalkClosedPointTo h).hom b : K) ≠ 0 ∧
      ((Scheme.stalkClosedPointTo h).hom a : K) = k * (Scheme.stalkClosedPointTo h).hom b)
    (h' : Spec (.of R) ⟶ blowUp (centerIdeal h)) (hh' : h' ≫ blowUpToBase _ = h) :
    ∀ y ∈ (Scheme.stalkClosedPointTo h).hom.range, y ≠ 0 → ¬ IsUnit y →
      ∃ w : R, w ≠ 0 ∧ ¬ IsUnit w ∧ ∀ y ∈ (Scheme.stalkClosedPointTo h).hom.range, ¬ IsUnit y →
        ∃ y' ∈ (Scheme.stalkClosedPointTo h').hom.range, y = w * y' := by
  intro y₀ hy₀ hy₀0 hy₀u
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨t₀, ht₀⟩ := RingHom.mem_range.mp hy₀
  let φ := (Scheme.stalkClosedPointTo h).hom
  let ι : Y.presheaf.stalk (h (closedPoint R)) →+* K := R.subtype.comp φ
  have hι : Function.Injective ι := Subtype.val_injective.comp hinj
  let e : Y.functionField →+* K := IsFractionRing.lift hι
  have he : ∀ a, e (algebraMap _ _ a) = (φ a : K) := fun a => IsFractionRing.lift_algebraMap hι a
  have hesurj : Function.Surjective e := by
    intro k
    obtain ⟨a, b, hb, hab⟩ := hsurj k
    refine ⟨algebraMap _ _ a / algebraMap _ _ b, ?_⟩
    rw [map_div₀, he, he, hab]
    exact mul_div_cancel_right₀ k hb
  let E : Y.functionField ≃+* K := RingEquiv.ofBijective e ⟨e.injective, hesurj⟩
  have hE : ∀ a, E (algebraMap _ _ a) = (φ a : K) := he
  let R' : ValuationSubring Y.functionField := (toValuationSubring R).comap e
  let σ : R ≃+* R' :=
    { toFun r := ⟨E.symm r, by
        show E (E.symm r) ∈ R
        rw [E.apply_symm_apply]
        exact r.2⟩
      invFun q := ⟨e q, q.2⟩
      left_inv r := Subtype.ext (E.apply_symm_apply (r : K))
      right_inv q := Subtype.ext (E.symm_apply_apply (q : Y.functionField))
      map_mul' a b := Subtype.ext (by simp)
      map_add' a b := Subtype.ext (by simp) }
  have hσloc : IsLocalHom σ.toRingHom := ⟨fun a ha => (isUnit_map_iff σ a).mp ha⟩
  have hRd : Stacks.AffineBlowup.Dominates (Y.presheaf.stalk (h (closedPoint R))) R' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨s, rfl⟩
      show e (algebraMap _ _ s) ∈ R
      rw [he]
      exact (φ s).2
    · intro t ht
      let a : R' := ⟨algebraMap _ _ t, by show e _ ∈ R; rw [he]; exact (φ t).2⟩
      rw [ValuationSubring.mem_nonunits_iff]
      refine (R'.valuation_lt_one_iff a).mp ?_
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : σ.symm a = φ t := Subtype.ext (he t)
      have h2 : IsUnit (φ t) := h1 ▸ hu.map σ.symm
      exact (mem_maximalIdeal _).mp ht (isUnit_of_map_unit φ t h2)
  obtain ⟨r, z, hz⟩ := exists_generators (h (closedPoint R))
  have ht₀m : t₀ ∈ maximalIdeal (Y.presheaf.stalk (h (closedPoint R))) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hy₀u (ht₀ ▸ hu.map φ)
  have hmax : maximalIdeal (Y.presheaf.stalk (h (closedPoint R))) ≠ ⊥ := by
    have ht₀0 : t₀ ≠ 0 := by
      rintro rfl
      exact hy₀0 (by rw [← ht₀, map_zero])
    intro hbot
    rw [hbot] at ht₀m
    exact ht₀0 ((Submodule.mem_bot _).mp ht₀m)
  have hr : Nonempty (Fin r) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hmax (by rw [← hz, Set.range_eq_empty z, Ideal.span_empty])
  obtain ⟨i₀, hi₀⟩ :=
    Finite.exists_max (fun j => R'.valuation (algebraMap _ Y.functionField (z j)))
  have hz0 : z i₀ ≠ 0 := by
    intro h0
    refine hmax ?_
    rw [← hz, Ideal.span_eq_bot]
    rintro _ ⟨j, rfl⟩
    have h2 : R'.valuation (algebraMap _ Y.functionField (z j)) = 0 :=
      le_antisymm (by simpa [h0] using hi₀ j) zero_le'
    exact IsFractionRing.injective _ Y.functionField
      (by rw [(Valuation.zero_iff _).mp h2, map_zero])
  have hw0 : φ (z i₀) ≠ 0 := fun h0 => hz0 (hinj (by rw [h0, map_zero]))
  have hw0K : (φ (z i₀) : K) ≠ 0 := fun h0 => hw0 (Subtype.ext h0)
  have hwu : ¬ IsUnit (φ (z i₀)) := by
    intro hu
    have hm : z i₀ ∈ maximalIdeal (Y.presheaf.stalk (h (closedPoint R))) :=
      hz ▸ Ideal.subset_span ⟨i₀, rfl⟩
    exact (mem_maximalIdeal _).mp hm (isUnit_of_map_unit φ _ hu)
  have C := (MMP.Mori.blowUp_vanishingIdeal_closure_valuation_chart sY (h (closedPoint R)) hgen z
    hz).2.2.2 R' hRd i₀ hi₀
  let g : Spec (.of R') ⟶ blowUp (centerIdeal h) := Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ h'
  have hcomp : Scheme.stalkClosedPointTo h ≫ CommRingCat.ofHom σ.toRingHom =
      CommRingCat.ofHom ((algebraMap _ Y.functionField).codRestrict R'.toSubring
        (fun s => hRd.1 ⟨s, rfl⟩)) := by
    ext t
    show E.symm (φ t) = algebraMap _ _ t
    rw [RingEquiv.symm_apply_eq]
    exact (hE t).symm
  have hg : g ≫ blowUpToBase _ = fromSpecOfStalkLE (h (closedPoint R)) R'.toSubring
      (fun s => hRd.1 ⟨s, rfl⟩) := by
    calc g ≫ blowUpToBase _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ h := by
          simp only [g, Category.assoc, hh']
      _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          (Spec.map (Scheme.stalkClosedPointTo h) ≫ Y.fromSpecStalk _) := by
          rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
      _ = _ := by rw [← Spec.map_comp_assoc, hcomp]; rfl
  have C2 := C.2 g hg
  dsimp only at C2
  obtain ⟨-, hrange⟩ := C2
  have hg' : g = Spec.map (Scheme.stalkClosedPointTo h' ≫ CommRingCat.ofHom σ.toRingHom) ≫
      (blowUp (centerIdeal h)).fromSpecStalk _ := by
    rw [Spec.map_comp_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hloc' : IsLocalHom (Scheme.stalkClosedPointTo h' ≫ CommRingCat.ofHom σ.toRingHom).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  have hψ := range_stalkClosedPointTo_eq g _ _ (hχ := hloc') hg'
  have hdiv : ∀ j, ∃ c ∈ (Scheme.stalkClosedPointTo h').hom.range, φ (z j) = φ (z i₀) * c := by
    intro j
    have hmem : algebraMap _ Y.functionField (z j) / algebraMap _ Y.functionField (z i₀) ∈
        {y | ∃ a ∈ Algebra.adjoin (Y.presheaf.stalk (h (closedPoint R)))
          (Set.range fun j => algebraMap _ Y.functionField (z j) /
            algebraMap _ Y.functionField (z i₀)),
          ∃ s ∈ Algebra.adjoin (Y.presheaf.stalk (h (closedPoint R)))
          (Set.range fun j => algebraMap _ Y.functionField (z j) /
            algebraMap _ Y.functionField (z i₀)), R'.valuation s = 1 ∧ y * s = a} :=
      ⟨_, Algebra.subset_adjoin ⟨j, rfl⟩, 1, one_mem _, map_one _, mul_one _⟩
    rw [← hrange] at hmem
    obtain ⟨t, ht⟩ := hmem
    have hmem2 : (Scheme.stalkClosedPointTo g).hom t ∈
        Set.range (Scheme.stalkClosedPointTo h' ≫ CommRingCat.ofHom σ.toRingHom).hom :=
      hψ ▸ ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hmem2
    refine ⟨(Scheme.stalkClosedPointTo h').hom s, ⟨s, rfl⟩, ?_⟩
    have h1 : E.symm ((Scheme.stalkClosedPointTo h').hom s) =
        algebraMap _ Y.functionField (z j) / algebraMap _ Y.functionField (z i₀) := by
      rw [← ht]
      exact congrArg Subtype.val hs
    have h3 : ((Scheme.stalkClosedPointTo h').hom s : K) =
        E (algebraMap _ Y.functionField (z j) / algebraMap _ Y.functionField (z i₀)) := by
      rw [← h1, E.apply_symm_apply]
    apply Subtype.ext
    rw [Subring.coe_mul, h3, map_div₀, hE, hE]
    field_simp
  refine ⟨φ (z i₀), hw0, hwu, ?_⟩
  intro y hy hyu
  obtain ⟨t, rfl⟩ := RingHom.mem_range.mp hy
  have htm : t ∈ maximalIdeal (Y.presheaf.stalk (h (closedPoint R))) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hyu (hu.map φ)
  rw [← hz] at htm
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp htm
  choose d hd hdz using hdiv
  have hle :
      (Scheme.stalkClosedPointTo h).hom.range ≤ (Scheme.stalkClosedPointTo h').hom.range := by
    have := range_stalkClosedPointTo_comp_le h' (blowUpToBase _)
    rwa [hh'] at this
  refine ⟨∑ j, φ (c j) * d j,
    Subring.sum_mem _ (fun j _ => Subring.mul_mem _ (hle (RingHom.mem_range.mpr ⟨c j, rfl⟩))
      (hd j)), ?_⟩
  rw [map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hdz j]; ring

/-- Restricting a separated morphism of finite type to a field to an open subscheme keeps it
separated and of finite type. -/
private theorem restrict_structure {k₀ : Type u} [Field k₀] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k₀)) [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX]
    (U : X.Opens) :
    IsSeparated (U.ι ≫ sX) ∧ LocallyOfFiniteType (U.ι ≫ sX) ∧ QuasiCompact (U.ι ≫ sX) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Let `X` be an integral scheme, separated and of finite type over a field `k₀`. For a Zariski
sequence of a discrete valuation ring `k₀ ⊆ R ⊆ k(X)` with fraction field `k(X)` dominating
`𝒪_{x₀,X}`, the stalk maps `𝒪_{xᵢ,Xᵢ} ⟶ R` are injective, their images increase, and the union
of the images is `R`. -/
@[mmp "lem_km1a_zariski_local_rings_exhaust"]
public theorem iSup_range_stalkClosedPointTo_eq_top {k₀ : Type u} [Field k₀]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k₀)) [IsIntegral X] [IsSeparated sX]
    [LocallyOfFiniteType sX] [QuasiCompact sX] (x₀ : X) (R : Subring X.functionField)
    [IsDiscreteValuationRing R] [IsFractionRing R X.functionField]
    (hk₀ : ∀ c : k₀, X.presheaf.germ ⊤ (genericPoint X) trivial
      (sX.appTop ((Scheme.ΓSpecIso (.of k₀)).inv c)) ∈ R)
    (hR : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ R)
    (hdom : IsLocalHom ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hR))
    (S : ZariskiSequence X (fromSpecOfStalkLE x₀ R hR)) :
    (∀ i, Function.Injective (Scheme.stalkClosedPointTo (S.mor i)).hom) ∧
      Monotone (fun i => (Scheme.stalkClosedPointTo (S.mor i)).hom.range) ∧
      ⨆ i, (Scheme.stalkClosedPointTo (S.mor i)).hom.range = ⊤ := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hnf : ¬ IsField R := IsDiscreteValuationRing.not_isField R
  have hE := (MMP.Mori.ZariskiSequence.nonempty_and_forall_isIntegral x₀ R hnf hR hdom).2 S
  have hinj : ∀ i, Function.Injective (Scheme.stalkClosedPointTo (S.mor i)).hom := by
    intro i
    rw [Scheme.stalkClosedPointTo, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).1.comp (hE i).2.2.2.2
  have hmono : Monotone (fun i => (Scheme.stalkClosedPointTo (S.mor i)).hom.range) := by
    refine monotone_nat_of_le_succ fun n => ?_
    have := range_stalkClosedPointTo_comp_le (S.mor (n + 1)) (S.β n)
    rwa [S.mor_succ_comp_β] at this
  have hint : ∀ n, IsIntegral (S.obj n) := fun n => (hE n).1
  have hgen : ∀ n, S.mor n (closedPoint R) ≠ genericPoint (S.obj n) := by
    intro n h0
    haveI := hint n
    exact (hE n).2.2.2.1 (h0 ▸ genericPoint_spec (S.obj n))
  have hU : ∀ n, IsIntegral (S.U n) := fun n =>
    haveI := hint n
    haveI : Nonempty (S.U n) := ⟨S.morOpen n (closedPoint R)⟩
    inferInstance
  have hrange : ∀ n, (Scheme.stalkClosedPointTo (S.morOpen n)).hom.range =
      (Scheme.stalkClosedPointTo (S.mor n)).hom.range := fun n => by
    have := range_stalkClosedPointTo_comp_ι (S.U n) (S.morOpen n)
    rw [S.morOpen_ι] at this
    exact this.symm
  have hinjU : ∀ n, Function.Injective (Scheme.stalkClosedPointTo (S.morOpen n)).hom :=
    fun n => injective_stalkClosedPointTo_of_comp_ι _ _ (by rw [S.morOpen_ι]; exact hinj n)
  have hgenU : ∀ n, S.morOpen n (closedPoint R) ≠ genericPoint (S.U n) := by
    intro n h0
    haveI := hint n
    haveI := hU n
    apply hgen n
    have h := (genericPoint_spec (S.U n)).image (S.U n).ι.continuous
    rw [Set.image_univ, Scheme.Opens.range_ι,
      ((S.U n).isOpen.dense ⟨_, S.mor_closedPoint_mem n⟩).closure_eq] at h
    rw [← S.morOpen_ι]
    change (S.U n).ι (S.morOpen n (closedPoint R)) = _
    rw [h0]
    exact h.eq (genericPoint_spec _)
  have hstr : ∀ n, ∃ s : S.obj n ⟶ Spec (.of k₀),
      IsSeparated s ∧ LocallyOfFiniteType s ∧ QuasiCompact s := by
    intro n
    induction n with
    | zero => exact ⟨eqToHom S.obj_zero ≫ sX, inferInstance, inferInstance, inferInstance⟩
    | succ n ih =>
      obtain ⟨s, _, _, _⟩ := ih
      obtain ⟨_, _, _⟩ := restrict_structure s (S.U n)
      haveI := hU n
      haveI : IsLocallyNoetherian (S.U n) :=
        LocallyOfFiniteType.isLocallyNoetherian ((S.U n).ι ≫ s)
      obtain ⟨r, z, hz⟩ := exists_generators (S.morOpen n (closedPoint R))
      haveI : IsProper (blowUpToBase (centerIdeal (S.morOpen n))) :=
        (MMP.Mori.blowUp_vanishingIdeal_closure_valuation_chart ((S.U n).ι ≫ s) _ (hgenU n) z
          hz).1.2.1
      exact ⟨eqToHom (S.obj_succ n) ≫ blowUpToBase _ ≫ (S.U n).ι ≫ s,
        inferInstance, inferInstance, inferInstance⟩
  have h0range : ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hR).range ≤
      (Scheme.stalkClosedPointTo (S.mor 0)).hom.range := by
    have h1 := range_stalkClosedPointTo_comp_le (S.mor 0) (eqToHom S.obj_zero)
    rw [S.mor_zero] at h1
    have h2 := range_stalkClosedPointTo_eq (fromSpecOfStalkLE x₀ R hR) x₀
      (CommRingCat.ofHom ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hR))
      (hχ := hdom) rfl
    intro a ha
    apply h1
    have : a ∈ Set.range (Scheme.stalkClosedPointTo (fromSpecOfStalkLE x₀ R hR)).hom := by
      rw [h2]
      exact RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr this
  have hfracK : ∀ k : X.functionField, ∃ a b : X.presheaf.stalk x₀,
      algebraMap _ X.functionField b ≠ 0 ∧
        algebraMap _ X.functionField a = k * algebraMap _ X.functionField b := by
    intro k
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (X.presheaf.stalk x₀) k
    have hb' : algebraMap _ X.functionField b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    exact ⟨a, b, hb', by field_simp⟩
  have hsub : ∀ n (a : X.presheaf.stalk x₀), ∃ a',
      (Scheme.stalkClosedPointTo (S.morOpen n)).hom a' =
        (algebraMap _ X.functionField).codRestrict R hR a :=
    fun n a => RingHom.mem_range.mp (hrange n ▸
      hmono (Nat.zero_le n) (h0range (RingHom.mem_range.mpr ⟨a, rfl⟩)))
  have hsurjn : ∀ n, ∀ k : X.functionField, ∃ a b,
      ((Scheme.stalkClosedPointTo (S.morOpen n)).hom b : X.functionField) ≠ 0 ∧
      ((Scheme.stalkClosedPointTo (S.morOpen n)).hom a : X.functionField) =
        k * (Scheme.stalkClosedPointTo (S.morOpen n)).hom b := by
    intro n k
    obtain ⟨a, b, hb, hab⟩ := hfracK k
    obtain ⟨a', ha'⟩ := hsub n a
    obtain ⟨b', hb'⟩ := hsub n b
    refine ⟨a', b', ?_, ?_⟩
    · rwa [hb']
    · rwa [ha', hb']
  refine ⟨hinj, hmono, iSup_eq_top_of_step _ ?_ ?_ ?_⟩
  · intro n s hs hsu
    obtain ⟨t, rfl⟩ := RingHom.mem_range.mp hs
    have htu : IsUnit t := isUnit_of_map_unit _ t hsu
    refine ⟨(Scheme.stalkClosedPointTo (S.mor n)).hom ↑htu.unit⁻¹,
      RingHom.mem_range.mpr ⟨_, rfl⟩, ?_⟩
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  · intro n y hy hy0 hyu
    haveI := hU n
    obtain ⟨s, _, _, _⟩ := hstr n
    obtain ⟨_, _, _⟩ := restrict_structure s (S.U n)
    rw [← hrange] at hy ⊢
    obtain ⟨w, hw0, hwu, hw⟩ := step ((S.U n).ι ≫ s) R (S.morOpen n) (hgenU n) (hinjU n) (hsurjn n)
      (S.mor (n + 1) ≫ eqToHom (S.obj_succ n))
      (by rw [Category.assoc]; exact S.mor_succ_comp n) y hy hy0 hyu
    refine ⟨w, hw0, hwu, fun y hy hyu => ?_⟩
    obtain ⟨y', hy', rfl⟩ := hw y hy hyu
    exact ⟨y', range_stalkClosedPointTo_comp_le _ _ hy', rfl⟩
  · intro u
    obtain ⟨a, b, hb, hab⟩ := hfracK u
    refine ⟨_, h0range (RingHom.mem_range.mpr ⟨a, rfl⟩), _,
      h0range (RingHom.mem_range.mpr ⟨b, rfl⟩), fun h => hb (congrArg Subtype.val h),
      Subtype.ext hab⟩

end Exhaust

/-! ### A divisorial valuation is reached -/

section Divisorial

open IsLocalRing

/-- If every element of the domain `R` is a fraction of elements of a Japanese subring `B`, then
the integral closure of `B` in `R` is a finite `B`-module: it embeds in the integral closure of
`B` in `Frac R`, which is a finite extension of `Frac B`. -/
private theorem finite_integralClosure {R : Type u} [CommRing R] [IsDomain R] (B : Subring R)
    [IsNoetherianRing B] [IsJapaneseRing B] (hfrac : ∀ x : R, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) :
    Module.Finite B (integralClosure B R) := by
  let K := FractionRing R
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr <| by
    rw [IsScalarTower.algebraMap_eq B R K]
    exact (IsFractionRing.injective R K).comp Subtype.val_injective
  letI : Algebra (FractionRing B) K := FractionRing.liftAlgebra B K
  have hR : ∀ r : R, ∃ w : FractionRing B, algebraMap (FractionRing B) K w = algebraMap R K r := by
    intro r
    obtain ⟨a, ha, b, hb, hb0, hrb⟩ := hfrac r
    refine ⟨algebraMap B (FractionRing B) ⟨a, ha⟩ / algebraMap B (FractionRing B) ⟨b, hb⟩, ?_⟩
    have hb0' : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply B R K, IsScalarTower.algebraMap_apply B R K,
      div_eq_iff (by simpa using hb0')]
    change algebraMap R K a = algebraMap R K r * algebraMap R K b
    rw [← map_mul, hrb]
  have : FiniteDimensional (FractionRing B) K := Module.Finite.of_surjective
    (Algebra.linearMap (FractionRing B) K) fun z => by
      obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := R) z
      obtain ⟨wx, hwx⟩ := hR x
      obtain ⟨wy, hwy⟩ := hR y
      exact ⟨wx / wy, by simp [map_div₀, hwx, hwy]⟩
  have : Module.Finite B (integralClosure B K) := IsJapaneseRing.finite K
  let g : integralClosure B R →ₗ[B] integralClosure B K :=
    { toFun := fun x => ⟨algebraMap R K x, x.2.map (IsScalarTower.toAlgHom B R K)⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun b x => by
        ext
        exact map_smul (IsScalarTower.toAlgHom B R K) b (x : R) }
  exact Module.Finite.of_injective g fun x y hxy =>
    Subtype.ext (IsFractionRing.injective R K (congrArg Subtype.val hxy))

/-- In a local domain `R`, a fraction `a / b` of elements of a Dedekind subalgebra `C` can be
rewritten with a denominator in `C` that is a unit of `R`: the localization of `C` at
`𝔪_R ∩ C` is a valuation ring, unless that prime is zero and `b` is already a unit. -/
private theorem exists_mul_eq_notMem_maximalIdeal {S R : Type u} [CommRing S] [CommRing R]
    [IsDomain R] [IsLocalRing R] [Algebra S R] (C : Subalgebra S R) [IsDedekindDomain C]
    {x a b : R} (ha : a ∈ C) (hb : b ∈ C) (hb0 : b ≠ 0) (hxb : x * b = a) :
    ∃ a ∈ C, ∃ s ∈ C, s ∉ maximalIdeal R ∧ x * s = a := by
  let q : Ideal C := (maximalIdeal R).comap (algebraMap C R)
  by_cases hq : q = ⊥
  · refine ⟨a, ha, b, hb, fun hbm => hb0 ?_, hxb⟩
    have : (⟨b, hb⟩ : C) ∈ q := hbm
    rw [hq, Ideal.mem_bot] at this
    exact congrArg Subtype.val this
  let L := Localization.AtPrime q
  have : IsDomain L := IsLocalization.isDomain_localization q.primeCompl_le_nonZeroDivisors
  have : IsDiscreteValuationRing L :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hq L
  have hinj := IsLocalization.injective L q.primeCompl_le_nonZeroDivisors
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap C L ⟨a, ha⟩) (algebraMap C L ⟨b, hb⟩)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := L) q.primeCompl c
  have hs : (s : R) ∉ maximalIdeal R := s.2
  have hspec := IsLocalization.mk'_spec L r s
  rcases hc with hc | hc
  · have h1 : a * r = b * s := congrArg Subtype.val (hinj (by
      rw [map_mul, map_mul, ← hspec, ← mul_assoc, hc]) : (⟨a, ha⟩ : C) * r = ⟨b, hb⟩ * s)
    have hxr : x * r = s := mul_left_cancel₀ hb0 (by rw [← h1, ← hxb]; ring)
    refine ⟨s, s.1.2, r, r.2, fun hr => hs ?_, hxr⟩
    rw [← hxr]
    exact Ideal.mul_mem_left _ _ hr
  · have h1 : b * r = a * s := congrArg Subtype.val (hinj (by
      rw [map_mul, map_mul, ← hspec, ← mul_assoc, hc]) : (⟨b, hb⟩ : C) * r = ⟨a, ha⟩ * s)
    exact ⟨r, r.2, s, s.1.2, hs, mul_left_cancel₀ hb0 (by rw [h1, ← hxb]; ring)⟩

/-- The algebraic core: an increasing chain of local subrings `A i` of a discrete valuation
ring `R`, dominated by `R`, with union `R` and fraction field that of `R`, reaches `R` as soon as
one of its members is a Japanese noetherian domain of dimension at most one. -/
private theorem exists_eq_top {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : ℕ → Subring R) (hmono : Monotone A) (hsup : ⨆ i, A i = ⊤)
    (hloc : ∀ i, ∀ a ∈ A i, ∀ b : R, a * b = 1 → b ∈ A i)
    (hfrac : ∀ x : R, ∃ a ∈ A 0, ∃ b ∈ A 0, b ≠ 0 ∧ x * b = a)
    (n : ℕ) [IsNoetherianRing (A n)] [Ring.KrullDimLE 1 (A n)] [IsJapaneseRing (A n)] :
    ∃ p, A p = ⊤ := by
  set B := A n
  set R' := integralClosure B R
  have hfracB : ∀ x : R, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a := fun x => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfrac x
    exact ⟨a, hmono (Nat.zero_le n) ha, b, hmono (Nat.zero_le n) hb, hb0, h⟩
  have : Module.Finite B R' := finite_integralClosure B hfracB
  -- the integral closure lies in some `A p`
  obtain ⟨p, hR'p⟩ : ∃ p, ∀ x ∈ R', x ∈ A p := by
    obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := B) (M := R')
    choose i hi using fun t : R' =>
      (Subring.mem_iSup_of_directed hmono.directed_le).mp (hsup ▸ Subring.mem_top (t : R))
    refine ⟨max n (T.sup i), fun x hx => ?_⟩
    suffices H : ∀ y ∈ Submodule.span B (T : Set R'), (y : R) ∈ A (max n (T.sup i)) from
      H ⟨x, hx⟩ (hT ▸ Submodule.mem_top)
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact hmono ((Finset.le_sup ht).trans (le_max_right _ _)) (hi t)
    | zero => simp
    | add y z _ _ hy hz => simpa using add_mem hy hz
    | smul b y _ hy => exact mul_mem (hmono (le_max_left _ _) b.2) hy
  have : Ring.DimensionLEOne B := ⟨fun {_} hne hp => hp.isMaximal_of_ne_bot hne⟩
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing B R'
  have : IsIntegrallyClosedIn R' R := .of_isIntegralClosure B
  have : IsIntegrallyClosed R' := .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ R
  have : IsDedekindDomain R' := { }
  refine ⟨p, eq_top_iff.mpr fun x _ => ?_⟩
  obtain ⟨a, ha, b, hb, hb0, hxb⟩ := hfracB x
  obtain ⟨a, ha, s, hs, hsm, hxs⟩ := exists_mul_eq_notMem_maximalIdeal R'
    (isIntegral_algebraMap (R := B) (A := R) (x := ⟨a, ha⟩) :)
    (isIntegral_algebraMap (R := B) (A := R) (x := ⟨b, hb⟩) :) hb0 hxb
  -- `s` lies in `A p` and is a unit of `R`, hence a unit of `A p`
  obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.mp hsm
  have hinv : (u : R) * ↑u⁻¹ = 1 := by simp
  have := mul_mem (hR'p a ha) (hloc p _ (hR'p _ hs) _ hinv)
  rwa [← hxs, mul_assoc, hinv, mul_one] at this

/-- The global sections of a morphism from the spectrum of a local ring, read through the
stalk at the image of the closed point. -/
private theorem germ_top_stalkClosedPointTo {B : Type u} [CommRing B] [IsLocalRing B]
    {Y : Scheme.{u}} (g : Spec (.of B) ⟶ Y) :
    Y.presheaf.germ ⊤ (g (closedPoint B)) trivial ≫ Scheme.stalkClosedPointTo g =
      g.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom := by
  rw [Scheme.germ_stalkClosedPointTo g ⊤ trivial]
  simp only [Scheme.Hom.appTop]
  congr 1

/-- The structure morphisms `Xᵢ ⟶ Z` of a Zariski sequence over a morphism `X ⟶ Z`. -/
private noncomputable def strMap {B : Type u} [CommRing B] [IsLocalRing B] {X Z : Scheme.{u}}
    {f : Spec (.of B) ⟶ X} (S : ZariskiSequence X f) (s : X ⟶ Z) : ∀ i, S.obj i ⟶ Z
  | 0 => eqToHom S.obj_zero ≫ s
  | i + 1 => S.β i ≫ strMap S s i

private theorem mor_comp_strMap {B : Type u} [CommRing B] [IsLocalRing B] {X Z : Scheme.{u}}
    {f : Spec (.of B) ⟶ X} (S : ZariskiSequence X f) (s : X ⟶ Z) :
    ∀ i, S.mor i ≫ strMap S s i = f ≫ s
  | 0 => by rw [strMap, ← Category.assoc, S.mor_zero]
  | i + 1 => by rw [strMap, ← Category.assoc, S.mor_succ_comp_β, mor_comp_strMap S s i]

private theorem locallyOfFiniteType_strMap {B : Type u} [CommRing B] [IsLocalRing B]
    {X Z : Scheme.{u}} [IsLocallyNoetherian Z] {f : Spec (.of B) ⟶ X} (S : ZariskiSequence X f)
    (s : X ⟶ Z) [LocallyOfFiniteType s] : ∀ i, LocallyOfFiniteType (strMap S s i)
  | 0 => by rw [strMap]; infer_instance
  | i + 1 => by
    have := locallyOfFiniteType_strMap S s i
    have : IsLocallyNoetherian (S.obj i) := LocallyOfFiniteType.isLocallyNoetherian (strMap S s i)
    have : LocallyOfFiniteType (S.β i) := by rw [S.β_eq]; infer_instance
    rw [strMap]; infer_instance

/-- Dimension through a point mapped generically with bijective stalk map. -/
private theorem topologicalKrullDim_eq_trdeg_of_bijective {k : Type u} [Field k]
    {B : CommRingCat.{u}} {Y : Scheme.{u}} [IrreducibleSpace Y] (σ : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType σ] (g : Spec B ⟶ Y) (p : Spec B) (hp : IsGenericPoint (g p) Set.univ)
    (hbij : Function.Bijective (g.stalkMap p)) :
    letI : Algebra k ((Spec B).residueField p) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ σ).appTop ≫ (Spec B).Γevaluation p).hom.toAlgebra
    topologicalKrullDim Y = (Cardinal.toENat (Algebra.trdeg k ((Spec B).residueField p)) :
      WithBot ℕ∞) := by
  letI : Algebra k ((Spec B).residueField p) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ σ).appTop ≫ (Spec B).Γevaluation p).hom.toAlgebra
  letI : Algebra k (Y.residueField (g p)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ σ.appTop ≫ Y.Γevaluation (g p)).hom.toAlgebra
  rw [topologicalKrullDim_eq_trdeg_residueField k Y σ (g p) hp]
  have hsurj : Function.Surjective (g.residueFieldMap p) := by
    intro z
    obtain ⟨w, rfl⟩ := (Spec B).residue_surjective p z
    obtain ⟨v, rfl⟩ := hbij.2 w
    exact ⟨Y.residue _ v, by
      simpa using congrArg (fun φ => φ.hom v) (Scheme.residue_residueFieldMap g p)⟩
  let e : Y.residueField (g p) ≃ₐ[k] (Spec B).residueField p :=
    { RingEquiv.ofBijective (g.residueFieldMap p).hom
        ⟨(g.residueFieldMap p).hom.injective, hsurj⟩ with
      commutes' := fun c => by
        refine (Scheme.Γevaluation_naturality_apply g p _).trans ?_
        rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.comp_appTop]
        rfl }
  rw [e.trdeg_eq]

/-- At the image `x` of the closed point under `g : Spec R ⟶ Y`, the residue field `κ(x)` embeds
in that of `R` over `k`; it has transcendence degree at least the size of any algebraically
independent set lifting into the image of `𝒪_{x,Y}`, and `dim Y = trdeg κ(x) + dim 𝒪_{x,Y}`. -/
private theorem exists_trdeg_residueField {k : Type u} [Field k] {R : Type u} [CommRing R]
    [IsLocalRing R] {Y : Scheme.{u}} [IrreducibleSpace Y] (σ : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType σ] (g : Spec (.of R) ⟶ Y) (ι : k →+* R)
    (hι : (Scheme.ΓSpecIso (.of k)).inv ≫ σ.appTop ≫
      Y.presheaf.germ ⊤ (g (closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo g =
        CommRingCat.ofHom ι)
    (s : Set (ResidueField R))
    (hs : letI := ((residue R).comp ι).toAlgebra; AlgebraicIndependent k ((↑) : s → ResidueField R))
    (hsr : ∀ b ∈ s, ∃ c, residue R ((Scheme.stalkClosedPointTo g).hom c) = b) :
    letI := ((residue R).comp ι).toAlgebra
    ∃ t : Cardinal, Cardinal.mk s ≤ t ∧ t ≤ Algebra.trdeg k (ResidueField R) ∧
      topologicalKrullDim Y = (t.toENat : WithBot ℕ∞) +
        ringKrullDim (Y.presheaf.stalk (g (closedPoint R))) := by
  letI : Algebra k (ResidueField R) := ((residue R).comp ι).toAlgebra
  set x := g (closedPoint R)
  letI : Algebra k (Y.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ σ.appTop ≫ Y.Γevaluation x).hom.toAlgebra
  set χ := (Scheme.stalkClosedPointTo g).hom
  let ψ : Y.residueField x →ₐ[k] ResidueField R :=
    { ResidueField.map χ with
      commutes' := fun c => by
        change ResidueField.map χ (residue _ ((Y.presheaf.germ ⊤ x trivial).hom
          (σ.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)))) = residue R (ι c)
        rw [ResidueField.map_residue]
        exact congrArg (residue R) (congrArg (fun φ => φ.hom c) hι) }
  refine ⟨Algebra.trdeg k (Y.residueField x), ?_, trdeg_le_of_injective ψ ψ.toRingHom.injective, ?_⟩
  · choose c hc using hsr
    let v : s → Y.residueField x := fun b => residue _ (c b b.2)
    have hv : ψ ∘ v = ((↑) : s → ResidueField R) := by
      funext b
      change ResidueField.map χ (residue _ (c b b.2)) = b
      rw [ResidueField.map_residue, hc]
    exact (AlgebraicIndependent.of_comp ψ (hv ▸ hs)).cardinalMk_le_trdeg
  · rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y σ x]
    exact topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y σ x

/-- The local rings of a Nagata scheme are Nagata rings. -/
private theorem isNagataRing_stalk {X : Scheme.{u}} (hX : IsNagataScheme X) (x : X) :
    IsNagataRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, -⟩ := hX x
  let y : U.1 := ⟨x, hxU⟩
  let : Algebra Γ(X, U.1) (X.presheaf.stalk (y : X)) :=
    X.presheaf.algebra_section_stalk y
  let : IsLocalization.AtPrime (X.presheaf.stalk (y : X)) (U.2.primeIdealOf y).asIdeal :=
    U.2.isLocalization_stalk y
  exact isNagata_of_isLocalization Γ(X, U.1) (U.2.primeIdealOf y).asIdeal.primeCompl
    (X.presheaf.stalk (y : X)) (IsNagataScheme.isNagataRing_sections hX U)

/-- A scheme locally of finite type over a field has finite dimension. -/
private theorem topologicalKrullDim_ne_top {k : Type u} [Field k] {X : Scheme.{u}}
    [IrreducibleSpace X] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X) :
    topologicalKrullDim X ≠ ⊤ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  rw [topologicalKrullDim_eq_of_isOpen k X sX U U.2 ⟨x, hxU⟩]
  exact topologicalKrullDim_ne_top_of_locallyOfFiniteType k (Scheme.Opens.ι U ≫ sX)

/-- If `d + 1 = d + r` in `WithBot ℕ∞` with `d` finite, then `r ≤ 1`. -/
private theorem le_one_of_coe_add_one_eq_add {d : ℕ∞} (hd : d ≠ ⊤) {r : WithBot ℕ∞}
    (h : ((d + 1 : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞) + r) : r ≤ 1 := by
  lift d to ℕ using hd
  induction r using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe r =>
    induction r using ENat.recTopCoe with
    | top => norm_cast at h
    | coe r =>
      norm_cast at h ⊢
      omega

/-- The image of a local ring homomorphism is closed under taking inverses of units of the
target. -/
private theorem mem_range_of_mul_eq_one {A R : Type*} [CommRing A] [CommRing R] (φ : A →+* R)
    [IsLocalHom φ] {a b : R} (ha : a ∈ φ.range) (h : a * b = 1) : b ∈ φ.range := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨u, rfl⟩ := isUnit_of_map_unit φ c (.of_mul_eq_one b h)
  exact ⟨↑u⁻¹, by
    rw [← mul_one (φ _), ← h, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]⟩

/-- **Kollár–Mori, Lemma 2.45.** Let `X` be a variety over a field `k` (integral, separated and of
finite type), and `R ⊆ k(X)` a discrete valuation ring dominating `𝒪_{x₀,X}` whose residue
field has transcendence degree `dim X - 1` over `k`. Then in every Zariski sequence of
`fromSpecOfStalkLE x₀ R hR` some stalk map `𝒪_{xₙ,Xₙ} ⟶ R` is an isomorphism. -/
@[mmp "lem_km1a_zariski_divisor_reached_by_blowups"]
public theorem exists_isIso_stalkClosedPointTo {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsIntegral X] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] (x₀ : X)
    (R : Subring X.functionField) [IsDiscreteValuationRing R]
    (hR : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ R)
    (hdom : IsLocalHom ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hR))
    (htrdeg :
      letI : Algebra k (IsLocalRing.ResidueField R) :=
        ((IsLocalRing.residue R).comp
          (((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hR).comp
            ((X.presheaf.germ ⊤ x₀ trivial).hom.comp
              ((X ↘ Spec (.of k)).appTop.hom.comp
                (Scheme.ΓSpecIso (.of k)).inv.hom)))).toAlgebra
      (((Algebra.trdeg k (IsLocalRing.ResidueField R)).toENat + 1 : ℕ∞) : WithBot ℕ∞) =
        topologicalKrullDim X)
    (S : ZariskiSequence X (fromSpecOfStalkLE x₀ R hR)) :
    ∃ n, IsIso (Scheme.stalkClosedPointTo (S.mor n)) := by
  set sX := X ↘ Spec (.of k)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let cR := (algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hR
  have : IsFractionRing R X.functionField := by
    refine IsFractionRing.of_field (R := R) (K := X.functionField) (surj := fun z => ?_)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x₀) z
    exact ⟨⟨_, hR a⟩, ⟨_, hR b⟩, rfl⟩
  have hnf : ¬ IsField R := IsDiscreteValuationRing.not_isField R
  have hSE := (MMP.Mori.ZariskiSequence.nonempty_and_forall_isIntegral x₀ R hnf hR hdom).2 S
  have hk₀ : ∀ c : k, X.presheaf.germ ⊤ (genericPoint X) trivial
      (sX.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) ∈ R := fun c => by
    convert hR (X.presheaf.germ ⊤ x₀ trivial (sX.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
      using 1
    exact (X.presheaf.germ_stalkSpecializes_apply _ _ _).symm
  obtain ⟨hinj, hmono, hsup⟩ :=
    MMP.Mori.ZariskiSequence.iSup_range_stalkClosedPointTo_eq_top sX x₀ R hk₀ hR hdom S
  set A : ℕ → Subring R := fun i => (Scheme.stalkClosedPointTo (S.mor i)).hom.range with hA
  set ι : k →+* R := cR.comp ((X.presheaf.germ ⊤ x₀ trivial).hom.comp
    (sX.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))
  letI : Algebra k (ResidueField R) := ((residue R).comp ι).toAlgebra
  have : ∀ i, IsIntegral (S.obj i) := fun i => (hSE i).1
  have : ∀ i, LocallyOfFiniteType (strMap S sX i) := locallyOfFiniteType_strMap S sX
  -- the structure maps are compatible with `ι`
  have hι : ∀ i, (Scheme.ΓSpecIso (.of k)).inv ≫ (strMap S sX i).appTop ≫
      (S.obj i).presheaf.germ ⊤ (S.mor i (closedPoint R)) trivial ≫
        Scheme.stalkClosedPointTo (S.mor i) = CommRingCat.ofHom ι := by
    intro i
    have h2 := germ_top_stalkClosedPointTo (fromSpecOfStalkLE x₀ R hR)
    have h3 : X.presheaf.germ ⊤ _ trivial ≫
        Scheme.stalkClosedPointTo (fromSpecOfStalkLE x₀ R hR) =
          X.presheaf.germ ⊤ x₀ trivial ≫ CommRingCat.ofHom cR :=
      Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ ⊤ trivial
    rw [germ_top_stalkClosedPointTo, ← Scheme.Hom.comp_appTop_assoc, mor_comp_strMap,
      Scheme.Hom.comp_appTop_assoc, ← h2, h3]
    rfl
  -- all the `Xᵢ` have the dimension of `X`
  have hdimX : ∀ i, topologicalKrullDim (S.obj i) = topologicalKrullDim X := by
    have key : ∀ i, topologicalKrullDim (S.obj i) = topologicalKrullDim (S.obj 0) := by
      intro i
      have h := topologicalKrullDim_eq_trdeg_of_bijective (strMap S sX i) (S.mor i)
        (genericPoint _) (hSE i).2.1 (hSE i).2.2.1
      have h0 := topologicalKrullDim_eq_trdeg_of_bijective (strMap S sX 0) (S.mor 0)
        (genericPoint _) (hSE 0).2.1 (hSE 0).2.2.1
      rw [mor_comp_strMap] at h h0
      rw [h, h0]
    intro i
    rw [key i, S.obj_zero]
  -- a finite transcendence basis of the residue field of `R`
  have hfinX := topologicalKrullDim_ne_top sX x₀
  have hd : (Algebra.trdeg k (ResidueField R)).toENat ≠ ⊤ := by
    intro h
    apply hfinX
    rw [← htrdeg, h]
    rfl
  have : FaithfulSMul k (ResidueField R) :=
    (faithfulSMul_iff_algebraMap_injective k _).mpr (RingHom.injective _)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k (ResidueField R)
  have hsd := hs.cardinalMk_eq_trdeg
  have hsfin : s.Finite := by
    rw [← Cardinal.lt_aleph0_iff_set_finite, hsd]
    by_contra h
    exact hd (Cardinal.toENat_eq_top.mpr (not_lt.mp h))
  have hmemA : ∀ x : R, ∃ i, x ∈ A i := fun x =>
    (Subring.mem_iSup_of_directed hmono.directed_le).mp (hsup ▸ Subring.mem_top x)
  choose j hj using fun b : ResidueField R => hmemA (Classical.choose (residue_surjective b))
  set n := hsfin.toFinset.sup j
  have hsr : ∀ b ∈ s, ∃ c, residue R ((Scheme.stalkClosedPointTo (S.mor n)).hom c) = b := by
    intro b hb
    obtain ⟨c, hc⟩ := hmono (Finset.le_sup (hsfin.mem_toFinset.mpr hb)) (hj b)
    refine ⟨c, ?_⟩
    rw [hc]
    exact Classical.choose_spec (residue_surjective b)
  obtain ⟨t, hst, htd, hdim⟩ :=
    exists_trdeg_residueField (strMap S sX n) (S.mor n) ι (hι n) s hs.1 hsr
  have ht : t = Algebra.trdeg k (ResidueField R) := le_antisymm htd (hsd ▸ hst)
  -- hence `dim 𝒪ₙ ≤ 1`
  have hle : ringKrullDim ((S.obj n).presheaf.stalk (S.mor n (closedPoint R))) ≤ 1 := by
    rw [hdimX n, ← htrdeg, ht] at hdim
    exact le_one_of_coe_add_one_eq_add hd hdim
  -- transfer to `A n`
  let e := RingEquiv.ofBijective (Scheme.stalkClosedPointTo (S.mor n)).hom.rangeRestrict
    ⟨fun a b h => hinj n (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  have hNag : IsNagataRing (A n) := MonogenicN1.isNagataRing_of_ringEquiv e
    (isNagataRing_stalk
      (isNagataScheme_of_locallyOfFiniteType_over_field k (strMap S sX n)) _)
  have : IsNoetherianRing (A n) := hNag.1
  have : IsJapaneseRing (A n) := MonogenicN1.isJapaneseRing_of_isNagataRing hNag
  have hle' : ringKrullDim (A n) ≤ 1 := by
    rwa [← ringKrullDim_eq_of_ringEquiv e]
  have : Ring.KrullDimLE 1 (A n) := ⟨hle'⟩
  -- domination and fractions
  have hloc : ∀ i, ∀ a ∈ A i, ∀ b : R, a * b = 1 → b ∈ A i := fun i _ ha _ h =>
    mem_range_of_mul_eq_one _ ha h
  have hfrac : ∀ x : R, ∃ a ∈ A 0, ∃ b ∈ A 0, b ≠ 0 ∧ x * b = a := by
    have hr : ∀ c, cR c ∈ A 0 := by
      intro c
      have h1 := range_stalkClosedPointTo_comp_le (S.mor 0) (eqToHom S.obj_zero)
      have h2 := range_stalkClosedPointTo_eq (fromSpecOfStalkLE x₀ R hR) x₀
        (CommRingCat.ofHom cR) rfl
      rw [S.mor_zero] at h1
      have h3 : cR c ∈ Set.range (Scheme.stalkClosedPointTo (fromSpecOfStalkLE x₀ R hR)).hom := by
        rw [h2]
        exact ⟨c, rfl⟩
      exact h1 h3
    intro x
    obtain ⟨a, b, hb, hab⟩ :=
      IsFractionRing.div_surjective (A := X.presheaf.stalk x₀) (x : X.functionField)
    have hb0 : algebraMap (X.presheaf.stalk x₀) X.functionField b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨cR a, hr a, cR b, hr b, fun h => hb0 (congrArg Subtype.val h), Subtype.ext ?_⟩
    change (x : X.functionField) * algebraMap _ _ b = algebraMap _ _ a
    rw [← hab, div_mul_cancel₀ _ hb0]
  obtain ⟨p, hp⟩ := exists_eq_top A hmono hsup hloc hfrac n
  refine ⟨p, (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj p, fun z => ?_⟩⟩
  exact (show z ∈ A p from hp ▸ Subring.mem_top z)

end Divisorial

end MMP.Mori.ZariskiSequence

namespace MMP.Mori

/-! ### Sections avoiding finitely many points -/

section AvoidingPoints

open Filter

/-- In a quasi-compact `T₀` space every point specializes to a closed point. -/
private theorem exists_isClosed_singleton_specializes {X : Type*} [TopologicalSpace X]
    [T0Space X] [CompactSpace X] (x : X) :
    ∃ y : X, IsClosed ({y} : Set X) ∧ x ⤳ y := by
  obtain ⟨y, hy, hcl⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  exact ⟨y, hcl, specializes_iff_mem_closure.mpr hy⟩

/-- An isomorphism of modules carries the nonvanishing locus of a global section to the
nonvanishing locus of its image. -/
private theorem nonvanishingLocus_iso_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (s : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus N (e.hom.app ⊤ s) = Stacks.Ample.nonvanishingLocus M s := by
  ext x
  simp only [Stacks.Ample.mem_nonvanishingLocus_iff, ← Stacks.ModuleStalk.mapFun_Γgerm,
    Stacks.ModuleStalk.mem_maximalSmul_mapFun_iff]

/-- The product of global sections of `𝒪_X(D)` and `𝒪_X(E)` is a global section of
`𝒪_X(D + E)` whose nonvanishing locus is the intersection of theirs. -/
private theorem exists_nonvanishingLocus_eq_inter {X : Scheme.{u}} {D E F : X.CartierDivisor}
    (h : D + E = F) (s : Γ(MMP.CartierDivisor.sheaf D, ⊤)) (t : Γ(MMP.CartierDivisor.sheaf E, ⊤)) :
    ∃ w : Γ(MMP.CartierDivisor.sheaf F, ⊤), Stacks.Ample.nonvanishingLocus _ w =
      Stacks.Ample.nonvanishingLocus _ s ∩ Stacks.Ample.nonvanishingLocus _ t := by
  subst h
  let e := (Stacks.AmplePullbackPart1.tensorIsoTensorModules X _ _).trans
      (MMP.CartierDivisorSheaf.sheafMulIso D E)
  exact ⟨e.hom.app ⊤ (Stacks.SectionTensorFormula.tensorSection _ _ s t),
    (nonvanishingLocus_iso_app e _).trans
      (Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection s t)⟩

open Stacks.ModuleStalk in
/-- A globally generated invertible module has, at every point, a global section that does not
vanish there. -/
private theorem exists_mem_nonvanishingLocus_of_isGeneratedByGlobalSections {X : Scheme.{u}}
    (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F]
    (h : SheafOfModules.IsGeneratedByGlobalSections F) (x : X) :
    ∃ s : Γ(F, ⊤), x ∈ Stacks.Ample.nonvanishingLocus F s := by
  have hgg := MMP.Fourfold.isGloballyGenerated_of_isGeneratedByGlobalSections F h
  by_contra! hall
  obtain ⟨z, hz⟩ := Stacks.SectionProduct.exists_notMem_maximalSmul F x
  apply hz
  obtain ⟨U, hxU, t, ht⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) F.presheaf z
  obtain ⟨W, hWU, hxW, n, s, r, heq⟩ := hgg x trivial U hxU t
  rw [← ht, ← TopCat.Presheaf.germ_res_apply (C := Ab.{u}) F.presheaf (homOfLE hWU) x hxW, heq,
    map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [germ_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [TopCat.Presheaf.germ_res_apply (C := Ab.{u}) F.presheaf (homOfLE le_top) x hxW]
  exact not_not.mp (hall (s i))

/-- Serre's global generation, pointwise: for `m ≫ 0` every point of `X` lies in the
nonvanishing locus of some global section of `𝒪_X(L + mA)`. -/
private theorem eventually_forall_exists_mem_nonvanishingLocus {X : Scheme.{u}}
    (A L : X.CartierDivisor) (hA : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A)) :
    ∀ᶠ n : ℕ in atTop, ∀ z : X, ∃ σ : Γ(MMP.CartierDivisor.sheaf (L + n • A), ⊤),
      z ∈ Stacks.Ample.nonvanishingLocus _ σ := by
  have hqc := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule
      (MMP.CartierDivisor.sheaf L)
  have hft := Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule
      (MMP.CartierDivisor.sheaf L)
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple
      (MMP.CartierDivisor.sheaf A) hA).2 (MMP.CartierDivisor.sheaf L) hqc hft
  rw [eventually_atTop]
  refine ⟨n₀.toNat, fun n hn z => ?_⟩
  have hg := hn₀ (n : ℤ) (by omega)
  obtain ⟨e⟩ := MMP.Fourfold.nonempty_lineBundle_nat_smul_iso A n
  refine exists_mem_nonvanishingLocus_of_isGeneratedByGlobalSections _
    (Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso ?_ hg) z
  exact (Stacks.AmplePullbackPart1.tensorIsoTensorModules X _ _).trans
    ((Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl _) e.symm).trans
      (MMP.CartierDivisorSheaf.sheafMulIso L (n • A)))

/-- For a point `y` of a finite set `T` of closed points, some positive multiple `dA` of an ample
divisor has a global section of `𝒪_X(dA)` nonvanishing at `y` and vanishing at the other points
of `T`. -/
private theorem exists_mem_nonvanishingLocus_forall_notMem {X : Scheme.{u}} (A : X.CartierDivisor)
    (hA : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A)) {T : Set X} (hT : T.Finite)
    (hcl : ∀ y ∈ T, IsClosed ({y} : Set X)) {y : X} (hy : y ∈ T) :
    ∃ d : ℕ, ∃ b : Γ(MMP.CartierDivisor.sheaf (d • A), ⊤), y ∈ Stacks.Ample.nonvanishingLocus _ b ∧
      ∀ z ∈ T, z ≠ y → z ∉ Stacks.Ample.nonvanishingLocus _ b := by
  have hC : IsClosed (T \ {y}) := by
    have := (hT.diff (t := {y})).isClosed_biUnion (f := fun z => ({z} : Set X))
      (fun z hz => hcl z hz.1)
    rwa [Set.biUnion_of_singleton] at this
  obtain ⟨d, a, -, hyE, hW, -⟩ :=
    Stacks.SectionExtension.exists_affine_nvOpen_containing_finite_le_of_isAmple
        (MMP.CartierDivisor.sheaf A) hA
      (Set.finite_singleton y) ⟨_, hC.isOpen_compl⟩ (by simp [hy])
  obtain ⟨e⟩ := MMP.Fourfold.nonempty_lineBundle_nat_smul_iso A d
  let e' := (Stacks.AmplePullbackPart1.natTensorPowIsoTensorPowModule X (MMP.CartierDivisor.sheaf A)
      d).trans
    e.symm
  refine ⟨d, e'.hom.app ⊤ (Stacks.SectionProduct.globalSection X _ a), ?_, fun z hz hzy h => ?_⟩
  · rw [nonvanishingLocus_iso_app]
    exact hyE rfl
  · rw [nonvanishingLocus_iso_app] at h
    have : z ∈ ((Stacks.AmpleFiniteAvoidance.nvOpen (MMP.CartierDivisor.sheaf A) a : X.Opens) : Set
        X) := h
    exact hW this ⟨hz, hzy⟩

private theorem eventually_exists_forall_mem_nonvanishingLocus_of_isClosed {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] (A L : X.CartierDivisor)
    (hA : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A))
    {T : Set X} (hT : T.Finite) (hcl : ∀ y ∈ T, IsClosed ({y} : Set X)) :
    ∀ᶠ m : ℕ in atTop, ∃ s : Γ(MMP.CartierDivisor.sheaf (L + m • A), ⊤),
      ∀ y ∈ T, y ∈ Stacks.Ample.nonvanishingLocus
        (MMP.CartierDivisor.sheaf (L + m • A)) s := by
  classical
  have hA' : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A) := hA
  suffices H : ∀ᶠ m : ℕ in atTop, ∃ s : Γ(MMP.CartierDivisor.sheaf (L + m • A), ⊤),
      ∀ y ∈ T, y ∈ Stacks.Ample.nonvanishingLocus _ s by
    exact H
  choose! d b hb hb' using fun y (hy : y ∈ T) =>
    exists_mem_nonvanishingLocus_forall_notMem A hA' hT hcl hy
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_forall_exists_mem_nonvanishingLocus A L hA')
  rw [eventually_atTop]
  refine ⟨N + hT.toFinset.sup d, fun m hm => ?_⟩
  have hdm : ∀ y ∈ T, d y ≤ m ∧ N ≤ m - d y := fun y hy => by
    have := Finset.le_sup (f := d) (hT.mem_toFinset.mpr hy)
    omega
  have hp : ∀ y ∈ T, ∃ p : Γ(MMP.CartierDivisor.sheaf (L + m • A), ⊤),
      y ∈ Stacks.Ample.nonvanishingLocus _ p ∧
        ∀ z ∈ T, z ≠ y → z ∉ Stacks.Ample.nonvanishingLocus _ p := by
    intro y hy
    obtain ⟨σ, hσ⟩ := hN (m - d y) (hdm y hy).2 y
    obtain ⟨p, hp⟩ := exists_nonvanishingLocus_eq_inter (F := L + m • A)
      (by rw [add_assoc, ← add_smul, Nat.sub_add_cancel (hdm y hy).1]) σ (b y)
    exact ⟨p, hp ▸ ⟨hσ, hb y hy⟩, fun z hz hzy h => hb' y hy z hz hzy (hp ▸ h).2⟩
  choose! p hp1 hp2 using hp
  refine ⟨∑ y ∈ hT.toFinset, p y, fun y hy =>
    Stacks.QuasiAffineFiniteNonvanishing.mem_nonvanishingLocus_sum _ _
      (hT.mem_toFinset.mpr hy) (hp1 y hy) fun z hz hzy =>
        hp2 z (hT.mem_toFinset.mp hz) y hy fun h => hzy h.symm⟩

/-- **Sections avoiding finitely many points.** Let `X` be proper over a field `K`, `A` an ample
Cartier divisor and `L` a Cartier divisor on `X`, and `S` a finite set of points of `X`. Then for
all `m ≫ 0` there is a global section `s` of `𝒪_X(L + mA)` with `s(x) ≠ 0` in
`𝒪_X(L + mA) ⊗ κ(x)` for every `x ∈ S`. -/
@[mmp "lem_km1b_section_avoiding_points"]
public theorem eventually_exists_forall_mem_nonvanishingLocus_sheaf_add_nsmul
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f]
    (A L : X.CartierDivisor) (hA : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A))
    {S : Set X} (hS : S.Finite) :
    ∀ᶠ m : ℕ in atTop, ∃ s : Γ(MMP.CartierDivisor.sheaf (L + m • A), ⊤),
      ∀ x ∈ S, x ∈ Stacks.Ample.nonvanishingLocus
        (MMP.CartierDivisor.sheaf (L + m • A)) s := by
  have : CompactSpace X := hA.1
  choose! y hy hxy using fun x : X => exists_isClosed_singleton_specializes x
  have hT : (y '' S).Finite := hS.image y
  filter_upwards [eventually_exists_forall_mem_nonvanishingLocus_of_isClosed f A L hA hT
    (by rintro _ ⟨x, -, rfl⟩; exact hy x)] with m ⟨s, hs⟩
  exact ⟨s, fun x hx => (hxy x).mem_open (Stacks.NonvanishingOpen.isOpen_nonvanishingLocus _ _ s)
    (hs _ ⟨x, hx, rfl⟩)⟩

end AvoidingPoints

/-! ### Effective divisors avoiding the associated points -/

noncomputable section AssociatedPoints

open Filter Opposite TopologicalSpace
open MMP.CartierDivisorSheaf

variable {X : Scheme.{u}}

/-- A section of `𝒦_X` which is a unit locally is a unit. -/
private theorem isUnit_of_forall_exists_isUnit_resK (t : X.totalQuotientSheaf.obj.obj (op ⊤))
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      IsUnit (resK le_top t : X.totalQuotientSheaf.obj.obj (op V))) :
    IsUnit t := by
  let Y : RingedSpace := ⟨⟨X.toTopCat, X.totalQuotientSheaf.presheaf⟩, X.totalQuotientSheaf.property⟩
  refine RingedSpace.isUnit_of_isUnit_germ Y (U := ⊤) (show Y.presheaf.obj (op ⊤) from t)
    fun x hx => ?_
  obtain ⟨V, hxV, hV⟩ := h x
  have := hV.map (X.totalQuotientSheaf.presheaf.germ V x hxV).hom
  rwa [TopCat.Presheaf.germ_res_apply] at this

/-- A section of `𝒪_X` over an affine open which is a non-zero-divisor of the ring of sections
becomes a unit in `𝒦_X`. -/
private theorem isUnit_toK_of_mem_nonZeroDivisors {V : X.Opens} (hV : IsAffineOpen V)
    {a : Γ(X, V)} (ha : a ∈ nonZeroDivisors Γ(X, V)) : IsUnit (toK V a) := by
  rw [← submonoidPresheafOfStalk_obj_eq_nonZeroDivisors X V hV] at ha
  have h1 : IsUnit ((X.presheaf.toTotalQuotientPresheaf.app (op V)).hom a) :=
    IsLocalization.map_units (Localization ((X.presheaf.submonoidPresheafOfStalk
      (fun x ↦ nonZeroDivisors (X.presheaf.stalk x))).obj (op V))) ⟨a, ha⟩
  have h2 : toK V a = ((toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf).app (op V)).hom
        ((X.presheaf.toTotalQuotientPresheaf.app (op V)).hom a) := by
    simp only [toK, X.toTotalQuotientSheaf_hom]
    rfl
  rw [h2]
  exact h1.map _

/-- On an affine open `V` of a locally Noetherian scheme, a function whose germ is a unit at
every associated point of `X` in `V` is a non-zero-divisor of `Γ(X, V)`: it lies in no
associated prime of `Γ(X, V)`, and those are the associated points in `V` (Stacks 02OK). -/
private theorem mem_nonZeroDivisors_of_isUnit_germ [IsLocallyNoetherian X] {V : X.Opens}
    (hV : IsAffineOpen V) (a : Γ(X, V))
    (h : ∀ (y : X) (hy : y ∈ V), y ∈ Stacks.Divisors.schemeAssociatedPoints X →
      IsUnit (X.presheaf.germ V y hy a)) :
    a ∈ nonZeroDivisors Γ(X, V) := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  by_contra ha
  have hreg : a ∈ {r : Γ(X, V) | IsSMulRegular Γ(X, V) r}ᶜ := fun hr =>
    ha (isRegular_iff_mem_nonZeroDivisors.mp
      ⟨hr, fun x y hxy => hr (by simpa only [smul_eq_mul, mul_comm a] using hxy)⟩)
  rw [← biUnion_associatedPrimes_eq_compl_regular] at hreg
  obtain ⟨p, hp, hap⟩ := Set.mem_iUnion₂.mp hreg
  let P : PrimeSpectrum Γ(X, V) := ⟨p, hp.isPrime⟩
  have hyV : hV.fromSpec P ∈ V := hV.range_fromSpec.subset ⟨P, rfl⟩
  have hPy : hV.primeIdealOf ⟨hV.fromSpec P, hyV⟩ = P :=
    hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨_, hyV⟩)
  have hass : hV.fromSpec P ∈ Stacks.Divisors.schemeAssociatedPoints X := by
    refine isAssociatedPoint_of_isAssociatedPrime_sections _ V hV hyV ?_
    rw [hPy]
    obtain ⟨hprime, m, hm⟩ := (isAssociatedPrime_iff (R := Γ(X, V)) (M := Γ(X, V))).mp hp
    exact (⟨hprime, m, by rw [hm, Submodule.colon_span]⟩ :
      IsAssociatedPrimeStacks Γ(X, V) Γ(X, V) p)
  have hu := h _ hyV hass
  let : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec P)) :=
    (X.presheaf.germ V _ hyV).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨_, hyV⟩
  have hapQ : a ∈ (hV.primeIdealOf ⟨_, hyV⟩).asIdeal := by rwa [hPy]
  have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (X.presheaf.stalk (hV.fromSpec P)) _ a).mpr hapQ
  exact (IsLocalRing.mem_maximalIdeal _).mp hm hu

open scoped Stacks.ModuleStalk in
/-- Near every point, a section `s` of `𝒪_X(D)` not vanishing at the associated points of `X` is
`a f⁻¹` for a local equation `f` of `D` and a function `a` which is a unit in `𝒦_X` and whose
germ is a unit at every associated point. -/
private theorem exists_isLocalEquation_eq_mul [IsLocallyNoetherian X] (D : X.CartierDivisor)
    (s : Γ((MMP.CartierDivisor.sheaf D), ⊤))
    (hs : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints X,
      y ∈ Stacks.Ample.nonvanishingLocus (MMP.CartierDivisor.sheaf D) s) (x : X) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V)
      (f : (X.totalQuotientSheaf.obj.obj (op V))ˣ) (_ : MMP.Intersection.IsLocalEquationOn D _ f)
      (a : Γ(X, V)), toK V a = resK (le_top : V ≤ ⊤) (sectionVal (D := D) s) *
        (f : X.totalQuotientSheaf.obj.obj (op V)) ∧ IsUnit (toK V a) ∧
        ∀ (y : X) (hy : y ∈ V), y ∈ Stacks.Divisors.schemeAssociatedPoints X →
          IsUnit (X.presheaf.germ V y hy a) := by
  obtain ⟨U, hxU, f₀, hf₀⟩ := MMP.Intersection.exists_isLocalEquationOn D x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
  change IsAffineOpen V at hV
  have hf := isLocalEquation_restrict (show V ≤ U from hVU) hf₀
  set f := Units.map (resK (show V ≤ U from hVU)).toMonoidHom f₀
  let s' : (sheafVal D).obj (op V) := (MMP.CartierDivisor.sheaf D).val.map (homOfLE le_top).op s
  obtain ⟨a, ha⟩ := exists_eq_smul_gen hf s'
  have hval : toK V a * ↑f⁻¹ = resK (le_top : V ≤ ⊤) (sectionVal (D := D) s) :=
    congrArg sectionVal ha
  have hval' : toK V a = resK (le_top : V ≤ ⊤) (sectionVal (D := D) s) *
      (f : X.totalQuotientSheaf.obj.obj (op V)) := by
    rw [← hval, mul_assoc, Units.inv_mul, mul_one]
  have hgerm : ∀ (y : X) (hy : y ∈ V), y ∈ Stacks.Divisors.schemeAssociatedPoints X →
      IsUnit (X.presheaf.germ V y hy a) := by
    intro y hy hass
    by_contra hu
    apply hs y hass
    have h1 : ((CartierDivisor.sheaf D).presheaf.Γgerm y).hom s
        = ((CartierDivisor.sheaf D).presheaf.germ V y hy).hom s' :=
      (TopCat.Presheaf.germ_res_apply (CartierDivisor.sheaf D).presheaf (homOfLE le_top)
        y hy s).symm
    rw [h1, ← ha]
    convert (Stacks.ModuleStalk.smul_mem_maximalSmul_iff (M := (MMP.CartierDivisor.sheaf D)) _
      (((CartierDivisor.sheaf D).presheaf.germ V y hy).hom
          (show Γ(CartierDivisor.sheaf D, V) from gen hf))).mpr (Or.inl hu) using 1
    exact Stacks.ModuleStalk.germ_smul (MMP.CartierDivisor.sheaf D) y V hy (show Γ(X, V) from a)
      (show Γ((MMP.CartierDivisor.sheaf D), V) from gen hf)
  exact ⟨V, hV, hxV, f, hf, a, hval',
    isUnit_toK_of_mem_nonZeroDivisors hV (mem_nonZeroDivisors_of_isUnit_germ hV a hgerm), hgerm⟩

/-- `u⁻¹`, restricted to `V`. -/
private abbrev invRes (u : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) (V : X.Opens) :
    X.totalQuotientSheaf.obj.obj (op V) :=
  resK (le_top : V ≤ ⊤) ((u⁻¹ : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    X.totalQuotientSheaf.obj.obj (op ⊤))

private theorem invRes_mul_invRes_inv (u : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ)
    (V : X.Opens) : invRes u V * invRes u⁻¹ V = 1 := by
  simp only [invRes, inv_inv, ← map_mul, Units.inv_mul, map_one]

private theorem mem_add_principalDivisor_mul {D : X.CartierDivisor} {V : X.Opens}
    {σ : X.totalQuotientSheaf.obj.obj (op V)} (hσ : Mem D V σ)
    (u : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    Mem (D + MMP.Intersection.principalDivisor u) V (σ * invRes u V) :=
  mem_mul hσ ((mem_inv (MMP.Intersection.isLocalEquationOn_principalDivisor u)).res le_top)

private theorem mem_of_mem_add_principalDivisor {D : X.CartierDivisor} {V : X.Opens}
    (u : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) {τ : X.totalQuotientSheaf.obj.obj (op V)}
    (hτ : Mem (D + MMP.Intersection.principalDivisor u) V τ) :
    Mem D V (τ * invRes u⁻¹ V) := by
  have hneg : MMP.Intersection.IsLocalEquationOn (-MMP.Intersection.principalDivisor u) ⊤
      u⁻¹ :=
    (MMP.Intersection.isLocalEquationOn_principalDivisor u).inv
  have h := mem_mul hτ ((mem_inv hneg).res le_top)
  rwa [add_neg_cancel_right] at h

/-- Multiplication by `u⁻¹` on sections over `V`, `𝒪_X(D)(V) → 𝒪_X(D + div u)(V)`. -/
private def sheafAddPrincipalLinearEquiv (D : X.CartierDivisor)
    (u : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) (V : X.Opens) :
    (MMP.CartierDivisor.sheaf D).val.obj (op V) ≃ₗ[X.ringCatSheaf.obj.obj (op V)]
      (MMP.CartierDivisor.sheaf (D + MMP.Intersection.principalDivisor u)).val.obj (op V) where
  toFun σ := (⟨sectionVal σ * invRes u V,
    mem_add_principalDivisor_mul (show ↥((CartierDivisor.sheafSubmodule D).obj (op V)) from σ).2
      u⟩ : ↥((CartierDivisor.sheafSubmodule (D + MMP.Intersection.principalDivisor u)).obj
        (op V)))
  invFun τ := (⟨sectionVal τ * invRes u⁻¹ V,
    mem_of_mem_add_principalDivisor u
      (show ↥((CartierDivisor.sheafSubmodule
          (D + MMP.Intersection.principalDivisor u)).obj (op V)) from τ).2⟩ :
      ↥((MMP.CartierDivisor.sheafSubmodule D).obj (op V)))
  map_add' σ τ := sectionVal_injective (add_mul (sectionVal σ) (sectionVal τ) _)
  map_smul' c σ := sectionVal_injective (mul_assoc _ (sectionVal σ) _)
  left_inv σ := sectionVal_injective (by
    change sectionVal σ * invRes u V * invRes u⁻¹ V = sectionVal σ
    rw [mul_assoc, invRes_mul_invRes_inv, mul_one])
  right_inv τ := sectionVal_injective (by
    change sectionVal τ * invRes u⁻¹ V * invRes u V = sectionVal τ
    rw [mul_assoc, mul_comm (invRes u⁻¹ V), invRes_mul_invRes_inv, mul_one])

/-- Multiplication by `u⁻¹`, an isomorphism `𝒪_X(D) ≅ 𝒪_X(D + div u)` of subsheaves of `𝒦_X`. -/
private def sheafIsoSheafAddPrincipal (D : X.CartierDivisor)
    (u : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    (MMP.CartierDivisor.sheaf D)
        ≅ MMP.CartierDivisor.sheaf (D + MMP.Intersection.principalDivisor u) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V ↦ (sheafAddPrincipalLinearEquiv D u V.unop).toModuleIso)
      (by
        intro V V' g
        refine ModuleCat.hom_ext (LinearMap.ext fun σ ↦ sectionVal_injective ?_)
        change resK (leOfHom g.unop) (sectionVal (D := D) σ) * invRes u V'.unop =
          resK (leOfHom g.unop) (sectionVal (D := D) σ * invRes u V.unop)
        rw [map_mul, resK_resK]))

/-- **The divisor of a section avoiding the associated points.** On a locally Noetherian scheme,
a section `s` of `𝒪_X(D)` not vanishing at any associated point of `X` is a unit of `𝒦_X`, and
`B = D + div s` is an effective Cartier divisor with `𝒪_X(B) ≅ 𝒪_X(D)` whose support contains
no associated point. -/
private theorem exists_isEffective_sheaf_iso_disjoint [IsLocallyNoetherian X]
    (D : X.CartierDivisor) (s : Γ((MMP.CartierDivisor.sheaf D), ⊤))
    (hs : ∀ y ∈ Stacks.Divisors.schemeAssociatedPoints X,
      y ∈ Stacks.Ample.nonvanishingLocus (MMP.CartierDivisor.sheaf D) s) :
    ∃ B : X.CartierDivisor, MMP.Intersection.IsEffective B
        ∧ Nonempty (CartierDivisor.sheaf B ≅ CartierDivisor.sheaf D) ∧
      Disjoint (MMP.Intersection.cartierSupport B) (Stacks.Divisors.schemeAssociatedPoints X) := by
  choose V hV hxV f hf a ha hua hga using exists_isLocalEquation_eq_mul D s hs
  have hres : ∀ x, resK (le_top : V x ≤ ⊤) (sectionVal (D := D) s) =
      toK (V x) (a x) * ((f x)⁻¹ : (X.totalQuotientSheaf.obj.obj (op (V x)))ˣ) := by
    intro x
    rw [ha x, mul_assoc, Units.mul_inv, mul_one]
  have ht : IsUnit (sectionVal (D := D) s) :=
    isUnit_of_forall_exists_isUnit_resK _ fun x =>
      ⟨V x, hxV x, by rw [hres x]; exact (hua x).mul (Units.isUnit _)⟩
  let u := ht.unit
  have hP := MMP.Intersection.isLocalEquationOn_principalDivisor u
  have hg : ∀ x, MMP.Intersection.IsLocalEquationOn (D + MMP.Intersection.principalDivisor u) _
      (f x * Units.map (resK (le_top : V x ≤ ⊤)).toMonoidHom u) :=
    fun x => isLocalEquation_mul (hf x) (isLocalEquation_restrict le_top hP)
  have hgval : ∀ x, ((f x * Units.map (resK (le_top : V x ≤ ⊤)).toMonoidHom u :
      (X.totalQuotientSheaf.obj.obj (op (V x)))ˣ) : X.totalQuotientSheaf.obj.obj (op (V x))) =
        toK (V x) (a x) := by
    intro x
    rw [ha x, Units.val_mul, Units.coe_map, IsUnit.unit_spec, mul_comm]
    rfl
  have hunit : ∀ x, (hua x).unit = f x * Units.map (resK (le_top : V x ≤ ⊤)).toMonoidHom u :=
    fun x => Units.ext ((IsUnit.unit_spec _).trans (hgval x).symm)
  refine ⟨D + MMP.Intersection.principalDivisor u, fun x => ⟨V x, hxV x, a x, hua x, by
    rw [hunit x]; exact hg x⟩, ⟨(sheafIsoSheafAddPrincipal D u).symm⟩, ?_⟩
  refine Set.disjoint_left.mpr fun y hyB hyA => ?_
  set w := (hga y y (hxV y) hyA).unit
  have hloc : MMP.Intersection.IsLocalEquationAt (D + MMP.Intersection.principalDivisor u) y
      (MMP.Intersection.stalkToTotalQuotient y (w : X.presheaf.stalk y)) := by
    refine ⟨V y, hxV y, _, hg y, ?_⟩
    rw [hgval y, IsUnit.unit_spec]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (V y) y (hxV y)
      X.toTotalQuotientSheaf.hom (a y)).symm
  have h1 := hloc.mul_units w⁻¹
  rw [← map_mul, Units.mul_inv, map_one] at h1
  exact MMP.Intersection.notMem_cartierSupport_of_isLocalEquationAt_one h1 hyB

/-- In an irreducible space of dimension at most `n + 1`, a proper closed subset has dimension
at most `n`: a chain of irreducible closed subsets of it extends by the whole space. -/
private theorem topologicalKrullDim_le_of_isClosed_ne_univ {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {A : Set T} (hA : IsClosed A) (hne : A ≠ Set.univ) (n : ℕ)
    (hT : topologicalKrullDim T ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim A ≤ n := by
  let g := IrreducibleCloseds.map (Subtype.val : A → T) continuous_subtype_val
  have hg : StrictMono g :=
    IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let top : IrreducibleCloseds T := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
  have hlt : ∀ c, g c < top := by
    intro c
    refine lt_of_le_of_ne (fun _ _ => trivial) fun h => hne ?_
    have h' : (g c : Set T) = Set.univ := congrArg SetLike.coe h
    have hsub : (g c : Set T) ⊆ A :=
      closure_minimal (by rintro _ ⟨x, -, rfl⟩; exact x.2) hA
    exact Set.eq_univ_of_univ_subset (h' ▸ hsub)
  have htop : (Order.height top : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) :=
    (Order.height_le_krullDim top).trans hT
  unfold topologicalKrullDim
  rw [Order.krullDim_eq_iSup_height]
  refine iSup_le fun c => ?_
  have h1 : Order.height c + 1 ≤ Order.height top :=
    (add_le_add_left (Order.height_le_height_apply_of_strictMono g hg c) 1).trans
      (Order.height_add_one_le (hlt c))
  have h2 : Order.height top ≤ ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast htop
  have h3 : Order.height c ≤ n := by
    have h4 := h1.trans h2
    push_cast at h4
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h4
  exact_mod_cast h3

/-- A closed set `S` not containing the irreducible closed set `Z`, of
finite positive dimension, meets it in a set of smaller dimension. -/
private theorem topologicalKrullDim_inter_lt {T : Type*} [TopologicalSpace T]
    {S Z : Set T} (hS : IsClosed S) (hZ : IsIrreducible Z) (hne : ¬ Z ⊆ S)
    (hfin : topologicalKrullDim Z ≠ ⊤) (hpos : 0 < topologicalKrullDim Z) :
    topologicalKrullDim ↑(S ∩ Z) < topologicalKrullDim Z := by
  haveI : IrreducibleSpace Z := Subtype.irreducibleSpace hZ
  let A : Set Z := Subtype.val ⁻¹' S
  have hA : IsClosed A := hS.preimage continuous_subtype_val
  have hAne : A ≠ Set.univ := fun h => hne fun z hz =>
    show (⟨z, hz⟩ : Z) ∈ A from h ▸ Set.mem_univ _
  obtain ⟨k, hk⟩ : ∃ k : ℕ, topologicalKrullDim Z = k := by
    cases h : topologicalKrullDim Z with
    | bot =>
      rw [h] at hpos
      exact absurd hpos not_lt_bot
    | coe m =>
      cases m with
      | top => exact absurd h hfin
      | coe k => exact ⟨k, rfl⟩
  rw [hk] at hpos ⊢
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact lt_irrefl _ hpos)
  let φ : ↑(S ∩ Z) → A := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  have hφ : Topology.IsInducing φ := .of_comp (g := fun a : A => (a.1.1 : T)) (by fun_prop)
    (by fun_prop) .subtypeVal
  calc topologicalKrullDim ↑(S ∩ Z) ≤ topologicalKrullDim A := hφ.topologicalKrullDim_le
    _ ≤ n := topologicalKrullDim_le_of_isClosed_ne_univ hA hAne n hk.le
    _ < ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast Nat.lt_succ_self n

end AssociatedPoints

open Filter in
/-- **Effective divisors avoiding the associated points.** Let `X` be proper over a field `K`,
`A` an ample Cartier divisor and `L` a Cartier divisor on `X`. Then for all `m ≫ 0` there is an
effective Cartier divisor `B` with `𝒪_X(B) ≅ 𝒪_X(L + mA)` whose support contains no associated
point of `X`; in particular, for every irreducible component `Z` of `X` of positive dimension
`dim (B ∩ Z) < dim Z`, and the support of `B` contains no irreducible component of `X`. -/
@[mmp "lem_km1b_section_avoiding_associated_points_divisor"]
public theorem eventually_exists_isEffective_sheaf_iso_disjoint_schemeAssociatedPoints
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f]
    (A L : X.CartierDivisor) (hA : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A)) :
    ∀ᶠ m : ℕ in atTop, ∃ B : X.CartierDivisor, MMP.Intersection.IsEffective B ∧
      Nonempty (MMP.CartierDivisor.sheaf B ≅ MMP.CartierDivisor.sheaf (L + m • A)) ∧
      Disjoint (MMP.Intersection.cartierSupport B) (Stacks.Divisors.schemeAssociatedPoints X) ∧
      (∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z →
        topologicalKrullDim ↑(MMP.Intersection.cartierSupport B ∩ Z) <
          topologicalKrullDim Z) ∧
      ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ MMP.Intersection.cartierSupport B := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := (isNoetherian_iff X).mpr ⟨inferInstance, inferInstance⟩
  filter_upwards [eventually_exists_forall_mem_nonvanishingLocus_sheaf_add_nsmul f A L hA
    (Stacks.Divisors.finite_schemeAssociatedPoints X)] with m hm
  obtain ⟨s, hs⟩ := hm
  obtain ⟨B, hBe, ⟨e⟩, hBd⟩ := exists_isEffective_sheaf_iso_disjoint (L + m • A) s hs
  have hgen : ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ MMP.Intersection.cartierSupport B :=
    fun Z hZ hsub => by
    obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
    exact Set.disjoint_left.mp hBd (hsub hη.mem)
      (mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent X hZ hη)
  exact ⟨B, hBe, ⟨e⟩, hBd, fun Z hZ hpos => topologicalKrullDim_inter_lt
    (MMP.Intersection.isClosed_cartierSupport B)
    hZ.1 (hgen Z hZ) (ne_top_of_le_ne_top (topologicalKrullDim_ne_top_of_isProper K f)
      (topologicalKrullDim_subspace_le X Z)) hpos, hgen⟩

/-! ### Flips -/

section Flip

open TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A point of coheight at most one does not lie in a closed set of codimension at least two. -/
private theorem notMem_of_coheight_le_one {T : Scheme.{u}} {Z : Closeds T}
    (h2 : 2 ≤ closedsCodimension Z) {x : T} (hx : Order.coheight x ≤ 1) : x ∉ Z := by
  intro hxZ
  have hsub : ((irreducibleSetEquivPoints (α := T)).symm x : Set T) ⊆ Z :=
    Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxZ)
  have := le_closedsCodimension_iff.mp h2 _ hsub
  rw [codimension_eq_coheight, Order.coheight_orderIso] at this
  exact absurd (this.trans hx) (by decide)

/-- A rational map represented by a partial isomorphism whose source contains the generic point
of a prime divisor `E` does not contract `E`. -/
private theorem not_isExceptional_of_mem_source {X X' : Scheme.{u}} (e : X.PartialIso X')
    (E : MMP.Mori.PrimeDivisor X) (hE : E.genericPoint ∈ e.source) :
    ¬ RationalMap.IsExceptional (X := X) e.toRationalMap E := by
  rw [RationalMap.isExceptional_iff, not_imp]
  refine ⟨RationalMap.definedAt_iff.mpr ⟨e.toPartialMap, hE, rfl⟩, fun h2 ↦ ?_⟩
  set p : X' := e.toPartialMap.hom ⟨E.genericPoint, hE⟩
  have hp : p ∈ (RationalMap.transform (X := X) e.toRationalMap E.idealSheaf.support : Set X') := by
    refine RationalMap.image_subset_transform e.toPartialMap rfl _ ⟨⟨E.genericPoint, hE⟩, ?_, rfl⟩
    change E.genericPoint ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  refine notMem_of_coheight_le_one h2 (x := p) ?_ hp
  let q : e.source.toScheme := ⟨E.genericPoint, hE⟩
  have h1 : Order.coheight p = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ (e.iso.hom ≫ e.target.ι).isOpenEmbedding
  have h2' : Order.coheight (e.source.ι q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ e.source.ι.isOpenEmbedding
  rw [h1, ← h2']
  exact (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E).le

/-- If `f⁺` is an isomorphism over `U`, two morphisms into `(f⁺)⁻¹(U)` which agree after
composing with `f⁺` are equal. -/
private theorem eq_of_comp_eq {T X' Y : Scheme.{u}} (fp : X' ⟶ Y) (U : Y.Opens)
    [IsIso (fp ∣_ U)] (a b : T ⟶ X') (ha : Set.range a ⊆ (fp ⁻¹ᵁ U : Set X'))
    (hb : Set.range b ⊆ (fp ⁻¹ᵁ U : Set X')) (h : a ≫ fp = b ≫ fp) : a = b := by
  have ha' : Set.range a ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  have hb' : Set.range b ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  rw [← IsOpenImmersion.lift_fac _ _ ha', ← IsOpenImmersion.lift_fac _ _ hb']
  congr 1
  rw [← cancel_mono (fp ∣_ U), ← cancel_mono U.ι, Category.assoc, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
    IsOpenImmersion.lift_fac, h]

/-- A morphism `a : T ⟶ X'` with `a ≫ f⁺ = c ≫ f` for some `c` landing in `f⁻¹(U)` lands in
`(f⁺)⁻¹(U)`. -/
private theorem range_subset_of_comp_eq {T X X' Y : Scheme.{u}} {f : X ⟶ Y} {fp : X' ⟶ Y}
    {U : Y.Opens} (a : T ⟶ X') (c : T ⟶ X) (hc : ∀ t, c t ∈ f ⁻¹ᵁ U) (h : a ≫ fp = c ≫ f) :
    Set.range a ⊆ (fp ⁻¹ᵁ U : Set X') := by
  rintro _ ⟨t, rfl⟩
  change fp (a t) ∈ U
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact hc t

/-- Let `f⁺` be an isomorphism over `U`. A partial map `p : X ⇀ X'` defined inside `f⁻¹(U)` with
`f⁺ ∘ p = f` represents every rational map `g` with `f⁺ ∘ g = f`. -/
private theorem toRationalMap_eq_of_comp_eq {X X' Y : Scheme.{u}} {f : X ⟶ Y} (fp : X' ⟶ Y)
    (U : Y.Opens) [IsIso (fp ∣_ U)] (p : X.PartialMap X') (hpU : p.domain ≤ f ⁻¹ᵁ U)
    (hp : p.hom ≫ fp = p.domain.ι ≫ f) (g : X.PartialMap X')
    (hg : g.toRationalMap.compHom fp = f.toPartialMap.toRationalMap) :
    p.toRationalMap = g.toRationalMap := by
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at hg
  obtain ⟨W, hWd, hWl, _, hWe⟩ := hg
  replace hWl : W ≤ g.domain := hWl
  have h2 : W ⊓ p.domain ≤ g.domain := inf_le_left.trans hWl
  have hc : ∀ t, (W ⊓ p.domain).ι t ∈ f ⁻¹ᵁ U := fun t ↦ hpU t.2.2
  have ha : (X.homOfLE (inf_le_right : W ⊓ p.domain ≤ _) ≫ p.hom) ≫ fp =
      (W ⊓ p.domain).ι ≫ f := by
    rw [Category.assoc, hp, Scheme.homOfLE_ι_assoc]
  have hb : (X.homOfLE h2 ≫ g.hom) ≫ fp = (W ⊓ p.domain).ι ≫ f := by
    have hWe' : X.homOfLE hWl ≫ g.hom ≫ fp = X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom ≫ f := hWe
    rw [Category.assoc, ← X.homOfLE_homOfLE (inf_le_left : W ⊓ p.domain ≤ W) hWl,
      Category.assoc, hWe', Scheme.topIso_hom, ← Category.assoc, ← Category.assoc,
      Scheme.homOfLE_homOfLE, Scheme.homOfLE_ι]
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  exact ⟨_, hWd.inter_of_isOpen_left p.dense_domain W.isOpen, inf_le_right, h2,
    eq_of_comp_eq fp U _ _ (range_subset_of_comp_eq _ _ hc ha)
      (range_subset_of_comp_eq _ _ hc hb) (ha.trans hb.symm)⟩

/-- A prime divisor `E` of a normal scheme `W` is exceptional for a morphism `g : W ⟶ T` to a
separated normal scheme exactly when `g(η_E)` has coheight at least two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight {W T : Scheme.{u}}
    [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (T ↘ ⊤_ Scheme)] (g : W ⟶ T) (E : MMP.Mori.PrimeDivisor W) :
    RationalMap.IsExceptional (X := W) g.toRationalMap E ↔
      2 ≤ Order.coheight (g E.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (g '' (E.idealSheaf.support : Set W)) =
      ⟨((IrreducibleCloseds.closureSingleton (g E.genericPoint) : IrreducibleCloseds T) : Set T),
        (IrreducibleCloseds.closureSingleton (g E.genericPoint)).isClosed⟩ := by
    ext1
    change closure (g '' E.support) = closure {g E.genericPoint}
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine le_antisymm ?_ (closure_mono ?_)
    · refine closure_minimal ?_ isClosed_closure
      refine (image_closure_subset_closure_image g.continuous).trans ?_
      rw [Set.image_singleton]
    · rw [Set.singleton_subset_iff]
      exact ⟨E.genericPoint, subset_closure rfl, rfl⟩
  rw [hcl, closedsCodimension_coe, codimension_eq_coheight,
    show IrreducibleCloseds.closureSingleton (g E.genericPoint) =
      (irreducibleSetEquivPoints (α := T)).symm (g E.genericPoint) from rfl,
    Order.coheight_orderIso]

/-- Let `D` be a divisor over an integral scheme `X` and `f : X ⟶ Y` dominant. The valuation of
`D`, read on `k(Y)` through `f`, dominates the local ring of `Y` at `f(x)`, where `x` is the
generic point of the center of `D`. -/
private theorem valuation_comap_dominates {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (D : DivisorOver k sX) :
    (∀ a : Y.presheaf.stalk (f (D.f D.E.genericPoint)),
      D.valuation.comap (functionFieldMap f) (algebraMap _ Y.functionField a) ≤ 1) ∧
    (∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (D.f D.E.genericPoint))),
      D.valuation.comap (functionFieldMap f) (algebraMap _ Y.functionField a) < 1) := by
  refine ⟨fun a ↦ ?_, fun a ha ↦ ?_⟩
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl _
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl _ ?_
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu ↦
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)

/-- Divisors `D` over `X` and `D'` over `X'` whose valuations agree on `k(Y)`, read through
dominant morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y` to a separated `Y`, have the same center
on `Y`. -/
private theorem map_genericPoint_eq_of_valuation_comap_eq {k : Type u} [Field k]
    {X X' Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [IsIntegral X] [IsIntegral X'] [IsIntegral Y]
    (f : X ⟶ Y) (f' : X' ⟶ Y) [IsDominant f] [IsDominant f'] (D : DivisorOver k sX)
    (D' : DivisorOver k sX')
    (h : D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap f')) :
    f (D.f D.E.genericPoint) = f' (D'.f D'.E.genericPoint) := by
  obtain ⟨h1, h2⟩ := valuation_comap_dominates f D
  obtain ⟨h1', h2'⟩ := valuation_comap_dominates f' D'
  rw [← h] at h1' h2'
  exact MMP.Positivity.DivisorOver.eq_of_dominates sY _ h1 h2 h1' h2'

/-- `Y` is separated over the terminal scheme when it is separated over `Spec k`. -/
private theorem isSeparated_terminal {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] : IsSeparated (Y ↘ ⊤_ Scheme) := by
  have : (Y ↘ ⊤_ Scheme) = sY ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
  rw [this]
  infer_instance

/-- A proper birational morphism `g : W ⟶ T` to a normal scheme whose exceptional set has
codimension at least two preserves the property "coheight at least two": `g(w)` has coheight at
least two if and only if `w` does. -/
private theorem two_le_coheight_map_iff {W T : Scheme.{u}} [IsIntegral W] [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (g : W ⟶ T) [IsDominant g] [IsProper g]
    (hg : Function.Bijective (functionFieldMap g))
    (h2 : 2 ≤ closedsCodimension (exceptionalSet g)) (w : W) :
    2 ≤ Order.coheight (g w) ↔ 2 ≤ Order.coheight w := by
  rw [← not_iff_not, not_le, not_le, ENat.lt_two_iff, ENat.lt_two_iff]
  refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
  · rwa [← MMP.Positivity.coheight_map_of_mem_biregularLocus g
      (MMP.Positivity.mem_biregularLocus_of_coheight_le_one g hg h2 hw)]
  · have hwE : w ∉ exceptionalSet g := fun hm ↦ absurd
      ((MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 hm).trans hw) (by decide)
    rwa [MMP.Positivity.coheight_map_of_mem_biregularLocus g (not_not.mp hwE)]

variable {k : Type u} [Field k] {X Y X' : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- The birational map `φ = (f⁺)⁻¹ ∘ f : X ⤏ X⁺` of a `(K + D)`-flip `f⁺ : X⁺ ⟶ Y` of a
`(K + D)`-flipping contraction `f : X ⟶ Y` is an isomorphism in codimension one. -/
@[mmp "lem_km3c_flip_isomorphism_in_codimension_one"]
public theorem IsFlipRationalMap.isIsomorphismInCodimOne {K : Divisor X} {D : QDivisor X}
    {f : X ⟶ Y} {fp : X' ⟶ Y} {φ : RationalMap X X'}
    (h : IsFlipRationalMap sX sY sX' K D f fp φ) : φ.IsIsomorphismInCodimOne := by
  obtain ⟨hflip, hcomp⟩ := h
  obtain ⟨hW, hbf, hbp, hcf, hcp, -⟩ :=
    MMP.Positivity.IsFlip.exists_isClosed_image_exceptionalSet hflip
  set U : Y.Opens := ⟨_, hW.isOpen_compl⟩
  haveI : IsIso (f ∣_ U) := hbf
  haveI : IsIso (fp ∣_ U) := hbp
  haveI : IsIntegral X := hflip.1.1.1.toIsIntegral
  haveI : IsIntegral X' := hflip.2.1.toIsIntegral
  have hA : ∀ x : X, Order.coheight x ≤ 1 → x ∈ f ⁻¹ᵁ U := fun x hx ↦
    notMem_of_coheight_le_one hcf hx
  have hB : ∀ x : X', Order.coheight x ≤ 1 → x ∈ fp ⁻¹ᵁ U := fun x hx ↦
    notMem_of_coheight_le_one hcp hx
  have hgen : ∀ (Z : Scheme.{u}) [IsIntegral Z], Order.coheight (genericPoint Z) ≤ 1 :=
    fun Z _ ↦ (Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z).trans_le
      zero_le_one
  let e : X.PartialIso X' :=
    ⟨f ⁻¹ᵁ U, (f ⁻¹ᵁ U).isOpen.dense ⟨_, hA _ (hgen X)⟩,
      fp ⁻¹ᵁ U, (fp ⁻¹ᵁ U).isOpen.dense ⟨_, hB _ (hgen X')⟩,
      asIso (f ∣_ U) ≪≫ (asIso (fp ∣_ U)).symm⟩
  have he_fac : e.toPartialMap.hom ≫ fp = (f ⁻¹ᵁ U).ι ≫ f := by
    change ((f ∣_ U) ≫ inv (fp ∣_ U)) ≫ (fp ⁻¹ᵁ U).ι ≫ fp = _
    rw [← morphismRestrict_ι, ← morphismRestrict_ι, Category.assoc, IsIso.inv_hom_id_assoc]
  have he : e.toRationalMap = φ := by
    obtain ⟨g, rfl⟩ := Quotient.exists_rep φ
    exact toRationalMap_eq_of_comp_eq fp U e.toPartialMap le_rfl he_fac g hcomp
  refine ⟨⟨e, he⟩, fun E ↦ he ▸ not_isExceptional_of_mem_source e E
    (hA _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E).le), fun ψ hψ E ↦ ?_⟩
  obtain rfl := (MMP.Positivity.IsBirational.existsUnique_isInverse ⟨e, he⟩).unique hψ ⟨e, he, rfl⟩
  exact not_isExceptional_of_mem_source e.symm E
    (hB _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E).le)

/-- Let `f⁺ : X⁺ ⟶ Y` be a `(K + D)`-flip of the `(K + D)`-flipping contraction `f : X ⟶ Y`,
and let `E` over `X` and `E'` over `X⁺` be divisors with the same valuation of `k(Y)`. Then `E'`
is exceptional over `X⁺` if and only if `E` is exceptional over `X`, and in that case `E` is
exceptional over `Y`, for the birational morphism `E.f ≫ f`. -/
@[mmp "lem_km3c_flip_exceptional_divisors_correspond"]
public theorem IsFlip.isExceptional_iff_and_isExceptional_comp {K : Divisor X}
    {D : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y} (h : IsFlip sX sY sX' K D f fp)
    (E : DivisorOver k sX) (E' : DivisorOver k sX')
    (hE :
      haveI : IsIntegral X := h.isFlippingContraction.isNormalVariety_source.1.toIsIntegral
      haveI : IsIntegral X' := h.isNormalVariety.1.toIsIntegral
      haveI : IsIntegral Y := h.isFlippingContraction.isNormalVariety_target.1.toIsIntegral
      haveI : IsDominant f := h.isFlippingContraction.isBirationalMorphism.isDominant
      haveI : IsDominant fp := h.isBirationalMorphism.isDominant
      E.valuation.comap (functionFieldMap f) = E'.valuation.comap (functionFieldMap fp)) :
    (E'.IsExceptional ↔ E.IsExceptional) ∧
      (E.IsExceptional → RationalMap.IsExceptional (X := E.Y) (E.f ≫ f).toRationalMap E.E) := by
  have hFC := h.isFlippingContraction
  have hXv := hFC.isNormalVariety_source
  have hYv := hFC.isNormalVariety_target
  have hX'v := h.isNormalVariety
  haveI : IsIntegral X := hXv.1.toIsIntegral
  haveI : IsIntegral X' := hX'v.1.toIsIntegral
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : IsDominant f := hFC.isBirationalMorphism.isDominant
  haveI : IsDominant fp := h.isBirationalMorphism.isDominant
  haveI : IsNormal Y := hYv.2
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsSeparated sY := hYv.1.toIsSeparated
  haveI : IsSeparated sX := hXv.1.toIsSeparated
  haveI : IsSeparated sX' := hX'v.1.toIsSeparated
  haveI := isSeparated_terminal sY
  haveI := isSeparated_terminal sX
  haveI := isSeparated_terminal sX'
  haveI := hFC.isProper
  haveI := h.isProper
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E'.isIntegral
  haveI := E'.isNormal
  haveI := E'.isLocallyNoetherian
  have hy : f (E.f E.E.genericPoint) = fp (E'.f E'.E.genericPoint) :=
    map_genericPoint_eq_of_valuation_comap_eq sY f fp E E' hE
  have hf := two_le_coheight_map_iff f hFC.isBirationalMorphism.functionFieldMap_bijective
    hFC.two_le_codimension
  have hfp := two_le_coheight_map_iff fp h.isBirationalMorphism.functionFieldMap_bijective
    h.two_le_codimension
  unfold DivisorOver.IsExceptional
  simp only [isExceptional_toRationalMap_iff_two_le_coheight, Scheme.Hom.comp_apply]
  exact ⟨by rw [← hf, ← hfp, hy], (hf _).2⟩

end Flip

end MMP.Mori
