module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.IndexOneCover
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Resolution.Blowup.CoherentIdealBlowup
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Resolution.Blowup.ProjectiveBirationalIsBlowup
public import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Resolution.StrongResolution.Functorial
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.Resolution.SNCHypersurfaceCentres
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
public import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
public import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

universe u

section

/-!
## Proof of the realisation of divisors over `S`

The proof follows Kollár–Mori. On an affine open `U₀ ⊆ S` meeting the center of `F` there is a
projective birational model `Bl_{J₀} U₀` on which `F` is a prime divisor; `Ĵ ⊆ 𝒪_X` is the ideal
of the closure of `V(J₀)` in `X`. A log resolution `f : Y ⟶ X` of `(X, S + B)` on which `Ĵ`, the
ideal of `S ∩ Supp B` and the ideal of `Sing X` become invertible has the strict transforms `S'`
of `S` and `f⁻¹_* B` disjoint, and `S' ⟶ S` factors through `Bl_{J₀} U₀` over `U₀`, so `F` is a
prime divisor `F'` of `S'`. The adjunction formula on `S'` computes `a(F, S, B|_S)` as
`∑ᵢ eᵢ mult_{F'}(Eᵢ|_{S'})`, with `eᵢ = a(Eᵢ, X, S + B)`, and the exceptional divisor `G` of the
blow-up of `Y` along `F'` has the same discrepancy over `(X, S + B)`.
-/

open CategoryTheory TopologicalSpace MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor
open scoped WithZero

namespace MMP.FourfoldProofs.Km5bDiscrepancyOverSRealisedOnXProof

/-! ### Exceptional divisors -/

/-- A divisor over a normal variety is exceptional if and only if its center has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- The generic point of an integral scheme has coheight zero. -/
private theorem coheight_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    Order.coheight (genericPoint X) = 0 :=
  Order.coheight_eq_zero.2 fun b hb => by
    rw [Scheme.le_iff_specializes] at hb ⊢
    exact genericPoint_specializes _

/-! ### Auxiliary facts on log resolutions -/

/-- The generic point of a prime divisor specializes to every point of its support. -/
private theorem genericPoint_specializes_of_mem_support {X : Scheme.{u}} (P : PrimeDivisor X)
    {x : X} (hx : x ∈ P.support) : P.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
  exact specializes_iff_mem_closure.2 hx

/-- A proper specialization of the generic point of a prime divisor has codimension at least
two. -/
private theorem two_le_coheight_of_specializes {X : Scheme.{u}} (P : PrimeDivisor X) {x : X}
    (hx : P.genericPoint ⤳ x) (hne : x ≠ P.genericPoint) : 2 ≤ Order.coheight x := by
  have hlt : x < P.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hx) fun h =>
    hne (inseparable_iff_specializes_and.2 ⟨Scheme.le_iff_specializes.1 h, hx⟩).eq
  have := Order.coheight_add_one_le hlt
  rwa [P.coheight_genericPoint, one_add_one_eq_two] at this

/-- A prime divisor in the support of `mapPrimeDivisors φ D` is `φ P` for a component `P` of
`D`. -/
private theorem exists_of_mem_support_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : PrimeDivisor X → Option (PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {Γ : PrimeDivisor Y}
    (h : Γ ∈ (DivisorWithCoeffs.mapPrimeDivisors φ D).support) :
    ∃ P ∈ D.support, φ P = some Γ := by
  classical
  by_contra hne
  push Not at hne
  apply Finsupp.mem_support_iff.1 h
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum,
    Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  have := hne P hP
  cases hφ : φ P with
  | none => simp
  | some Γ' =>
    have hΓ' : Γ' ≠ Γ := fun h => this (by rw [hφ, h])
    simp [Finsupp.single_apply, hΓ']

/-- The exceptional prime divisors of a log resolution form a finite set. -/
private theorem exists_finset_isExceptional {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)} {D : RDivisor X}
    {Y : Scheme.{u}} {f : Y ⟶ X} (hf : IsLogResolution sX D f) (hY : IsNormalVariety k (f ≫ sX)) :
    ∃ Ex : Finset (PrimeDivisor Y), ∀ E, E ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap E := by
  classical
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  have hcoh : ∀ s ∈ (exceptionalSet f : Set Y), Order.coheight s ≠ 0 := by
    intro s hs
    have hs' : s ∈ ((exceptionalSet f ⊔ D.supp.preimage f.continuous : Closeds Y) : Set Y) :=
      Or.inl hs
    rcases hf.isSNCSubset with h | ⟨t, ht, -⟩
    · rw [h] at hs'
      exact hs'.elim
    · rw [← ht] at hs'
      obtain ⟨E, -, hsE⟩ := Set.mem_iUnion₂.1 hs'
      have hle : s ≤ E.genericPoint :=
        Scheme.le_iff_specializes.2 (genericPoint_specializes_of_mem_support E hsE)
      have h1 := Order.coheight_anti hle
      rw [E.coheight_genericPoint] at h1
      intro h0
      rw [h0] at h1
      exact absurd h1 (by norm_num)
  have hfin := finite_setOf_genericPoint_mem (exceptionalSet f).isClosed hcoh
  refine ⟨hfin.toFinset.filter fun E => RationalMap.IsExceptional f.toRationalMap E, fun E => ?_⟩
  rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun h => h.2, fun h => ⟨MMP.Positivity.support_subset_exceptionalSet E h
    (MMP.Flips.primeDivisor_genericPoint_mem_support E), h⟩⟩

/-- The stalk ideal of an ideal sheaf at a point is the stalk of the ideal sheaf there. -/
private theorem stalkIdeal_eq_stalk {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    I.stalkIdeal x = AlgebraicGeometry.IdealSheafData.stalk I x :=
  le_antisymm
    (iSup_le fun U => le_iSup_of_le U.1 (le_iSup_of_le U.2 le_rfl))
    (iSup_le fun U => iSup_le fun hx => le_iSup_of_le ⟨U, hx⟩ le_rfl)

/-- In `Fin n` with `n ≤ 2`, two elements both different from a third are equal. -/
private theorem fin_eq_of_ne_of_ne {n : ℕ} (hn : n ≤ 2) {a b c : Fin n} (ha : a ≠ c)
    (hb : b ≠ c) : a = b := by
  rw [Ne, Fin.ext_iff] at ha hb
  ext
  omega

/-- If `F + E` is snc (over any base), then along every prime divisor `Q` of `F` whose generic
point lies on `E`, the local intersection length of `E` is one. -/
private theorem intersectionLength_eq_one {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (F E : PrimeDivisor Y) (hEF : E ≠ F)
    (hsnc : DivisorWithCoeffs.IsSNC f (Finsupp.single F (1 : ℤ) + Finsupp.single E (1 : ℤ)))
    (Q : PrimeDivisor F.idealSheaf.subscheme)
    (hyE : F.idealSheaf.subschemeι Q.genericPoint ∈ E.support) :
    E.intersectionLength F.idealSheaf.subschemeι Q = 1 := by
  classical
  set ι := F.idealSheaf.subschemeι with hι
  set η := Q.genericPoint with hη
  set y := ι η with hy
  set D : Divisor Y := Finsupp.single F (1 : ℤ) + Finsupp.single E (1 : ℤ) with hD
  have hFD : F ∈ D.support := by
    simp [hD, Finsupp.single_apply, hEF, hEF.symm]
  have hED : E ∈ D.support := by
    simp [hD, Finsupp.single_apply, hEF, hEF.symm]
  have hyF : y ∈ F.support := by
    change y ∈ (F.idealSheaf.support : Set Y)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨η, rfl⟩
  obtain ⟨n, z, j, hz, hj, hI⟩ := hsnc.2 y
  set φ := (ι.stalkMap η).hom with hφ
  have hφs : Function.Surjective φ := ι.stalkMap_surjective η
  have hstalk : ∀ E' (h : E' ∈ D.support ∧ y ∈ E'.support),
      E'.idealSheaf.stalkIdeal y = Ideal.span {z (j ⟨E', h⟩)} := by
    intro E' h
    rw [stalkIdeal_eq_stalk]
    exact hI ⟨E', h⟩
  have hker : RingHom.ker φ = Ideal.span {z (j ⟨F, hFD, hyF⟩)} :=
    (Scheme.IdealSheafData.ker_stalkMap_subschemeι F.idealSheaf η).trans
      (hstalk F ⟨hFD, hyF⟩)
  have hdimA : ringKrullDim (F.idealSheaf.subscheme.presheaf.stalk η) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hη,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    rfl
  have hmemB : ∀ i, z i ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := fun i =>
    hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hn : n ≤ 2 := by
    have h1 := Ideal.height_le_ringKrullDim_quotient_add_one
      (p := IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (hmemB (j ⟨F, hFD, hyF⟩))
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hz.2, ← hker,
      ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφs), hdimA,
      one_add_one_eq_two] at h1
    exact_mod_cast h1
  set i0 := j ⟨E, hED, hyE⟩
  set iF := j ⟨F, hFD, hyF⟩
  have hi : i0 ≠ iF := fun hjj => hEF (congrArg Subtype.val (hj hjj))
  have hmax : (E.idealSheaf.stalkIdeal (ι η)).map φ =
      IsLocalRing.maximalIdeal (F.idealSheaf.subscheme.presheaf.stalk η) := by
    rw [hstalk E ⟨hED, hyE⟩, Ideal.map_span, Set.image_singleton]
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff, ←
        IsLocalRing.map_maximalIdeal_of_surjective φ hφs]
      exact Ideal.mem_map_of_mem _ (hmemB i0)
    · rw [← IsLocalRing.map_maximalIdeal_of_surjective φ hφs, ← hz.1, Ideal.map_span,
        Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hiF : i = iF
      · have : z i ∈ RingHom.ker φ := hker ▸ hiF ▸ Ideal.mem_span_singleton_self _
        rw [RingHom.mem_ker.mp this]
        exact Ideal.zero_mem _
      · rw [fin_eq_of_ne_of_ne hn hiF hi]
        exact Ideal.mem_span_singleton_self _
  have h1 : Module.length (F.idealSheaf.subscheme.presheaf.stalk η)
      ((F.idealSheaf.subscheme.presheaf.stalk η) ⧸
        (E.idealSheaf.stalkIdeal (ι η)).map φ) = 1 := by
    rw [Module.length_eq_one_iff, hmax, isSimpleModule_iff_isCoatom]
    exact (IsLocalRing.maximalIdeal.isMaximal _).out
  unfold PrimeDivisor.intersectionLength
  rw [h1]
  rfl

/-- On an integral scheme, a point of coheight zero is the generic point. -/
private theorem eq_genericPoint_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X] {s : X}
    (h : Order.coheight s = 0) : s = genericPoint X := by
  have hmax := Order.coheight_eq_zero.1 h
  have h1 : s ≤ genericPoint X := by
    rw [Scheme.le_iff_specializes]; exact genericPoint_specializes s
  have h2 := hmax h1
  rw [Scheme.le_iff_specializes] at h1 h2
  exact (inseparable_iff_specializes_and.2 ⟨h1, h2⟩).eq.symm

open Classical in
/-- On a log resolution of `(X, S + B)`, the restriction of an exceptional prime divisor `E` to
the strict transform `S'` of `S` has coefficient one along a prime divisor `F'` of `S'` whose
generic point lies on `E`, and zero otherwise. -/
private theorem coeff_restrict_single_eq {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (S : PrimeDivisor X) {B : QDivisor X}
    {Y : Scheme.{u}} {f : Y ⟶ X}
    (hf : IsLogResolution sX
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single S 1) + B)) f)
    (hY : IsNormalVariety k (f ≫ sX))
    (S' : PrimeDivisor Y) (hS' : inverseTransformPrimeDivisor f S = some S')
    (hB : B.coeff S = 0)
    (E : PrimeDivisor Y) (hE : RationalMap.IsExceptional f.toRationalMap E)
    (F' : PrimeDivisor S'.idealSheaf.subscheme) :
    (DivisorWithCoeffs.restrict S'.idealSheaf.subschemeι
        (Finsupp.single E (1 : ℚ))).coeff F' =
      if S'.idealSheaf.subschemeι F'.genericPoint ∈ E.support then 1 else 0 := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  haveI : IsIntegral S'.idealSheaf.subscheme := S'.integral
  set ι := S'.idealSheaf.subschemeι with hι
  haveI : IsLocallyNoetherian S'.idealSheaf.subscheme := LocallyOfFiniteType.isLocallyNoetherian ι
  haveI : CompactSpace S'.idealSheaf.subscheme := ι.isClosedEmbedding.compactSpace
  haveI : AlgebraicGeometry.IsNoetherian S'.idealSheaf.subscheme := {}
  have hfS := MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hS'
  -- `S'` is not exceptional
  have hES : E ≠ S' := by
    rintro rfl
    have h2 := (isExceptional_iff_two_le_coheight hX
      (⟨Y, f, hY, hf.isBirationalMorphism, E⟩ : DivisorOver k sX)).mp hE
    change 2 ≤ Order.coheight (f E.genericPoint) at h2
    rw [hfS.1, S.coheight_genericPoint] at h2
    exact absurd h2 (by norm_num)
  -- `S'` and `E` are components of an snc divisor
  have hsnc : DivisorWithCoeffs.IsSNC (f ≫ sX)
      (Finsupp.single S' (1 : ℤ) + Finsupp.single E (1 : ℤ)) := by
    have hEx : E.genericPoint ∈ (exceptionalSet f : Set Y) :=
      MMP.Positivity.support_subset_exceptionalSet E hE
        (MMP.Flips.primeDivisor_genericPoint_mem_support E)
    set Dl : RDivisor X :=
      QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single S 1) + B) with hDl
    rcases hf.isSNCSubset with h | ⟨t, ht, htsnc⟩
    · have : E.genericPoint ∈ ((exceptionalSet f ⊔ Dl.supp.preimage f.continuous : Closeds Y) :
          Set Y) := Or.inl hEx
      rw [h] at this
      exact this.elim
    · have hmem : ∀ P : PrimeDivisor Y,
          P.genericPoint ∈ ((exceptionalSet f ⊔ Dl.supp.preimage f.continuous : Closeds Y) :
            Set Y) → P ∈ t := by
        intro P hP
        rw [← ht] at hP
        obtain ⟨P', hP', hPP'⟩ := Set.mem_iUnion₂.1 hP
        rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPP'] at hP'
      have hEt : E ∈ t := hmem E (Or.inl hEx)
      have hS't : S' ∈ t := by
        refine hmem S' (Or.inr ?_)
        change f S'.genericPoint ∈ Dl.supp
        rw [hfS.1, hDl, QDivisor.supp_toRDivisor, DivisorWithCoeffs.mem_supp_iff]
        refine ⟨S, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support S⟩
        rw [DivisorWithCoeffs.coeff_add, hB, add_zero, MMP.Threefold.Resolution.toQDivisor_single,
          DivisorWithCoeffs.coeff_single_self]
        norm_num
      refine htsnc.of_support_subset fun P hP => ?_
      have hP' := Finsupp.support_add hP
      rw [Finset.mem_union, Finsupp.support_single_ne_zero _ one_ne_zero,
        Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton,
        Finset.mem_singleton] at hP'
      have hPt : P ∈ t := by rcases hP' with rfl | rfl <;> assumption
      rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply,
        Finset.sum_eq_single_of_mem P hPt fun Q _ hQP => Finsupp.single_eq_of_ne hQP.symm,
        Finsupp.single_eq_same]
      exact one_ne_zero
  -- the restriction is defined
  have hfin : (Function.support (DivisorWithCoeffs.restrictCoeff ι
      (Finsupp.single E (1 : ℚ)))).Finite := by
    refine DivisorWithCoeffs.finite_support_restrictCoeff _ _ fun E' hE' s hs => ?_
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hE'
    subst hE'
    rw [eq_genericPoint_of_coheight_eq_zero hs]
    intro hmem
    exact hES (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hmem)
  rw [DivisorWithCoeffs.coeff_restrict ι hfin F', Finsupp.sum_single_index (by simp)]
  split_ifs with hyE
  · rw [intersectionLength_eq_one (f ≫ sX) S' E hES hsnc F' hyE]
    simp
  · rw [PrimeDivisor.intersectionLength_eq_zero_of_notMem ι E hyE]
    simp

/-- In `WithBot ℕ∞`, if `d + 1 = n` and `d + c = n + 1`, then `c = 2`. -/
private theorem eq_two_of_add_one_eq_of_add_eq {d : WithBot ℕ∞} {n : ℕ} {c : ℕ∞}
    (h1 : d + 1 = (n : WithBot ℕ∞)) (h2 : d + (c : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    c = 2 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h1
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => norm_cast at h1
    | coe m =>
      induction c using ENat.recTopCoe with
      | top => norm_cast at h2
      | coe c => norm_cast at h1 h2 ⊢; omega

/-- In `WithBot ℕ∞`, `e + 1 = n + 1` forces `e = n`. -/
private theorem eq_of_add_one_eq_add_one {e : WithBot ℕ∞} {n : ℕ}
    (h : e + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : e = (n : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => simp at h; exact absurd h WithBot.bot_ne_coe
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => norm_cast at h
    | coe m => norm_cast at h ⊢; omega

/-- A prime divisor `T ⊂ X` of a variety of dimension `n + 1` has dimension `n`. -/
private theorem topologicalKrullDim_eq_of_range_eq_support
    {k : Type u} [Field k] {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX]
    {n : ℕ} (hdim : topologicalKrullDim X = n + 1) (ι : T ⟶ X) [IsClosedImmersion ι]
    (P : PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X)) :
    topologicalKrullDim T = n := by
  have hPP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX P.genericPoint
  rw [P.coheight_genericPoint, hdim] at hPP
  have hT : topologicalKrullDim T = topologicalKrullDim (closure {P.genericPoint} : Set X) := by
    have e : (closure {P.genericPoint} : Set X) = Set.range ι.base := by
      rw [hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [e]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.toHomeomorph ι.isEmbedding).isHomeomorph)
  rw [hT, eq_of_add_one_eq_add_one
    (e := topologicalKrullDim (closure {P.genericPoint} : Set X)) (n := n)
    (by simpa using hPP)]

/-- The image in a variety `Y` of dimension `m + 1` of the generic point of a prime divisor of a
prime divisor `S'` of `Y` has codimension two. -/
private theorem coheight_subschemeι_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    {m : ℕ} (hdim : topologicalKrullDim Y = m + 1)
    (S' : PrimeDivisor Y) (F' : PrimeDivisor S'.idealSheaf.subscheme) :
    Order.coheight (S'.idealSheaf.subschemeι F'.genericPoint) = 2 := by
  haveI : IsIntegral S'.idealSheaf.subscheme := S'.integral
  set ι := S'.idealSheaf.subschemeι
  have hP : Set.range ι.base = (S'.support : Set Y) := Scheme.IdealSheafData.range_subschemeι _
  have hQ := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (ι ≫ sY) F'.genericPoint
  rw [F'.coheight_genericPoint] at hQ
  have hx := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (ι F'.genericPoint)
  have hcl : topologicalKrullDim (closure {ι F'.genericPoint} : Set Y) =
      topologicalKrullDim (closure {F'.genericPoint} : Set S'.idealSheaf.subscheme) := by
    have e : (closure {ι F'.genericPoint} : Set Y) = ι.base '' closure {F'.genericPoint} := by
      rw [← Set.image_singleton, ← ι.isClosedEmbedding.closure_image_eq]
    rw [e]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.homeomorphImage ι.isEmbedding _).isHomeomorph).symm
  rw [topologicalKrullDim_eq_of_range_eq_support sY hdim ι S' hP] at hQ
  rw [hcl, hdim] at hx
  exact eq_two_of_add_one_eq_of_add_eq (by simpa using hQ) hx

/-- The stalk of an ideal sheaf at a generization `y` of `x` is generated by the image of its
stalk at `x`. -/
private theorem stalk_map_stalkSpecializes {X : Scheme.{u}} (I : X.IdealSheafData) {x y : X}
    (h : y ⤳ x) :
    (IdealSheafData.stalk I x).map (X.presheaf.stalkSpecializes h).hom =
      IdealSheafData.stalk I y := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.isOpen hxU
  rw [IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ I y ⟨U, hU⟩ hyU, Ideal.map_map, ← CommRingCat.hom_comp,
    TopCat.Presheaf.germ_stalkSpecializes]

/-- If the stalk of `L` at `y` is contained in that of `K`, then a generization of `y` outside
the support of `L` lies outside the support of `K`. -/
private theorem notMem_support_of_stalk_le {Y : Scheme.{u}} (K L : Y.IdealSheafData) {η y : Y}
    (h : η ⤳ y) (hle : IdealSheafData.stalk L y ≤ IdealSheafData.stalk K y)
    (hL : η ∉ L.support) : η ∉ K.support := by
  have h1 := Ideal.map_mono (f := (Y.presheaf.stalkSpecializes h).hom) hle
  rw [stalk_map_stalkSpecializes, stalk_map_stalkSpecializes,
    (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).2 hL] at h1
  exact (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).1 (top_le_iff.1 h1)

/-- The pull-back of an effective Cartier divisor `J` along a morphism from an integral scheme
whose generic point avoids the support of `J` is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_comap_of_genericPoint_notMem {Y Z : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsIntegral Z] [IsLocallyNoetherian Z] (J : Y.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (g : Z ⟶ Y)
    (hη : g (genericPoint Z) ∉ J.support) :
    Stacks.Divisors.IsEffectiveCartierDivisor (J.comap g) := by
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun t _ => ?_
  obtain ⟨h, -, hgen⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor J hJ (g t)
  have hst : IdealSheafData.stalk (J.comap g) t = Ideal.span {(g.stalkMap t).hom h} := by
    rw [AlgebraicGeometry.stalk_comap, hgen, Ideal.map_span, Set.image_singleton]
  refine ⟨(g.stalkMap t).hom h, IsRegular.of_ne_zero ?_, hst⟩
  intro h0
  have hsp : genericPoint Z ⤳ t := genericPoint_specializes t
  have hη' : genericPoint Z ∉ (J.comap g).support := by
    intro hm
    have h' : genericPoint Z ∈ ((J.comap g).support : Set Z) := hm
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage] at h'
    exact hη h'
  rw [← Stacks.Divisors.stalk_eq_top_iff_notMem_support, ← stalk_map_stalkSpecializes _ hsp, hst,
    h0, Ideal.span_singleton_eq_bot.2 rfl, Ideal.map_bot] at hη'
  exact bot_ne_top hη'

/-! ### The divisor `G` -/

/-- A morphism is injective over its biregular locus. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {X Y : Scheme.{u}} {f : X ⟶ Y} {x y : X}
    (h : f x = f y) (hx : f x ∈ biregularLocus f) : x = y := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let px : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let py : (f ⁻¹ᵁ V).toScheme := ⟨y, show f y ∈ V by rwa [← h]⟩
  have hpx : V.ι ((f ∣_ V) px) = f x := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  have hpy : V.ι ((f ∣_ V) py) = f y := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  have h1 : (f ∣_ V) px = (f ∣_ V) py := V.ι.isOpenEmbedding.injective (by rw [hpx, hpy, h])
  exact congrArg Subtype.val ((f ∣_ V).isOpenEmbedding.injective h1)

/-- A prime divisor whose ideal at `η_Z` is generated by a member of a regular system of
parameters has multiplicity `1` along `Z`. -/
private theorem multiplicityAlong_eq_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Q : PrimeDivisor X) (Z : IrreducibleCloseds X) {m : ℕ}
    {z : Fin m → X.presheaf.stalk Z.isIrreducible.genericPoint}
    (hz : IsRegularSystemOfParameters z) (i : Fin m)
    (hQ : IdealSheafData.stalk Q.idealSheaf Z.isIrreducible.genericPoint = Ideal.span {z i}) :
    Q.multiplicityAlong Z = 1 := by
  have hmem : ∀ j, z j ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk Z.isIrreducible.genericPoint) :=
    fun j => hz.1 ▸ Ideal.subset_span ⟨j, rfl⟩
  have hli := linearIndependent_toCotangent_of_isRegularSystemOfParameters hz hmem
  have hsq :
      z i ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk Z.isIrreducible.genericPoint) ^ 2 :=
    fun h => hli.ne_zero i ((Ideal.toCotangent_eq_zero _ _).2 h)
  have hQ' : Q.idealSheaf.stalkIdeal Z.isIrreducible.genericPoint = Ideal.span {z i} := by
    rwa [stalkIdeal_eq_stalk]
  rw [PrimeDivisor.multiplicityAlong_eq_of_stalkIdeal_eq_span Q Z hQ']
  refine le_antisymm (iSup₂_le fun s hs => ?_) (le_iSup₂_of_le 1 (by simpa using hmem i) le_rfl)
  by_contra hlt
  push Not at hlt
  have : 2 ≤ s := by exact_mod_cast (ENat.add_one_le_iff (by simp)).2 hlt
  exact hsq (Ideal.pow_le_pow_right this hs)

/-- A prime divisor not passing through `η_Z` has multiplicity `0` along `Z`. -/
private theorem multiplicityAlong_eq_zero {X : Scheme.{u}} (Q : PrimeDivisor X)
    (Z : IrreducibleCloseds X) (h : Z.isIrreducible.genericPoint ∉ Q.support) :
    Q.multiplicityAlong Z = 0 := by
  unfold MMP.Mori.PrimeDivisor.multiplicityAlong
  rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ h]
  refine le_antisymm (iSup₂_le fun s hs => ?_) bot_le
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp
  · exact absurd (top_le_iff.1 (hs.trans (Ideal.pow_le_self hs0.ne')))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top

/-- A divisor `(W, g, F)` over `Y`, for a birational morphism `f : Y ⟶ X` of varieties, regarded
as the divisor `(W, f ∘ g, F)` over `X`. -/
private noncomputable def compDivisorOver {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (E : DivisorOver k (f ≫ sX)) : DivisorOver k sX :=
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI := E.isIntegral
  { Y := E.Y
    f := E.f ≫ f
    isNormalVariety := by rw [Category.assoc]; exact E.isNormalVariety
    isBirationalMorphism := IsPair.isBirationalMorphism_comp E.isBirationalMorphism hf
    E := E.E }

/-- The valuation of `(W, f ∘ g, F)` is that of `(W, g, F)`, read on `k(X)` through `f^*`. -/
private theorem valuation_compDivisorOver {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (E : DivisorOver k (f ≫ sX)) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hY hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have := E.isIntegral
  have := E.isDominant
  have := E.isNormal
  have := E.isLocallyNoetherian
  ext t
  change E.E.divisorialValuation (functionFieldMap (E.f ≫ f) t) =
    E.E.divisorialValuation (functionFieldMap E.f (functionFieldMap f t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The components of the snc divisor `Ex(f) ∪ f⁻¹(Supp D)` of a log resolution: a finite set of
prime divisors, which are exactly those with generic point in that set, whose reduced sum is
snc. -/
private theorem exists_finset_isSNC_of_isLogResolution {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {D : RDivisor X} {Y : Scheme.{u}} {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hf : IsLogResolution sX D f) :
    ∃ t : Finset (PrimeDivisor Y),
      (∀ P : PrimeDivisor Y,
        P.genericPoint ∈ (exceptionalSet f : Set Y) ∨ f P.genericPoint ∈ D.supp ↔ P ∈ t) ∧
      DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ P ∈ t, Finsupp.single P (1 : ℤ)) := by
  rcases hf.isSNCSubset with h | ⟨t, ht, htsnc⟩
  · refine ⟨∅, fun P => ?_, ?_⟩
    · simp only [Finset.notMem_empty, iff_false]
      intro hP
      have : P.genericPoint ∈
          ((exceptionalSet f ⊔ D.supp.preimage f.continuous : Closeds Y) : Set Y) := hP
      rw [h] at this
      exact this
    · rw [Finset.sum_empty]
      haveI := MMP.Resolution.Aux.smooth_of_isSmoothScheme' (f ≫ sX) hf.isSmoothScheme
      exact DivisorWithCoeffs.isSNC_zero _
  · refine ⟨t, fun P => ⟨fun hP => ?_, fun hP => ?_⟩, htsnc⟩
    · have : P.genericPoint ∈
          ((exceptionalSet f ⊔ D.supp.preimage f.continuous : Closeds Y) : Set Y) := hP
      rw [← ht] at this
      obtain ⟨P', hP', hPP'⟩ := Set.mem_iUnion₂.1 this
      rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPP'] at hP'
    · have : P.genericPoint ∈ ⋃ E ∈ t, (E.support : Set Y) :=
        Set.mem_iUnion₂.2 ⟨P, hP, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
      rw [ht] at this
      exact this

private theorem toQDivisor_single_one {X : Scheme.{u}} (S : PrimeDivisor X) :
    Divisor.toQDivisor (Finsupp.single S (1 : ℤ)) = Finsupp.single S (1 : ℚ) := by
  rw [MMP.Threefold.Resolution.toQDivisor_single]
  simp

/-- A prime divisor `Γ` lying biregularly over a prime divisor of `X`, and lying over `Supp S`
or `Supp B`, meets the strict transform `S'` of `S` only if `Γ = S'`. -/
private theorem eq_of_mem_support_of_mem_biregularLocus {X Y : Scheme.{u}} (f : Y ⟶ X)
    {S : PrimeDivisor X} {B : QDivisor X} {S' Γ : PrimeDivisor Y} {P : PrimeDivisor X} {y : Y}
    (hfS : f S'.genericPoint = S.genericPoint ∧ f S'.genericPoint ∈ biregularLocus f)
    (hdisj : ∀ Γ : PrimeDivisor Y, f Γ.genericPoint ∈ B.supp → f Γ.genericPoint ∉ S.support →
      Disjoint (S'.support : Set Y) Γ.support)
    (hP : f Γ.genericPoint = P.genericPoint) (hPV : f Γ.genericPoint ∈ biregularLocus f)
    (hΓ : Γ.genericPoint ∈ (exceptionalSet f : Set Y) ∨
      f Γ.genericPoint ∈ DivisorWithCoeffs.supp (Finsupp.single S 1 + B))
    (hyS : y ∈ S'.support) (hyΓ : y ∈ Γ.support) : Γ = S' := by
  rcases hΓ with hΓX | hΓD
  · exact (hΓX hPV).elim
  rw [hP, DivisorWithCoeffs.mem_supp_iff] at hΓD
  obtain ⟨Q, hQ, hPQ⟩ := hΓD
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPQ
  by_cases hQS : Q = S
  · subst hQS
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_of_mem_biregularLocus (hP.trans hfS.1.symm) (hP ▸ hPV))
  have hBQ : B.coeff Q ≠ 0 := by
    rwa [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_single_of_ne
      (Ne.symm hQS), zero_add] at hQ
  refine (Set.disjoint_left.1 (hdisj Γ ?_ ?_) hyS hyΓ).elim
  · rw [hP, DivisorWithCoeffs.mem_supp_iff]
    exact ⟨Q, hBQ, MMP.Flips.primeDivisor_genericPoint_mem_support Q⟩
  · rw [hP]
    intro hm
    exact hQS (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hm).symm

/-- A non-exceptional prime divisor `Γ` of `Y` over a pair `(X, Δ)` lies over a prime divisor `P`
of `X`, at a point of the biregular locus of `f`, with discrepancy `-Δ.coeff P`. -/
private theorem exists_primeDivisor_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hPW : IsPairWith sX n K Δ) {Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (hY : IsNormalVariety k (f ≫ sX)) (hfb : IsBirationalMorphism f)
    (Γ : PrimeDivisor Y) (hΓ : ¬ RationalMap.IsExceptional f.toRationalMap Γ) :
    ∃ P : PrimeDivisor X, f Γ.genericPoint = P.genericPoint ∧
      f Γ.genericPoint ∈ biregularLocus f ∧
      IsDiscrepancy sX n K Δ ⟨Y, f, hY, hfb, Γ⟩ (-Δ.coeff P) := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPW
    (⟨Y, f, hY, hfb, Γ⟩ : DivisorOver k sX) hΓ
  have hη : f Γ.genericPoint = P.genericPoint := by
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hfb, Γ⟩ : DivisorOver k sX), hc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine ⟨P, hη, ?_, hd⟩
  by_contra hV
  have h2 := (MMP.Flips.le_closedsCodimension_iff_le_coheight.1
    (two_le_closedsCodimension_compl_biregularLocus sX f (hY := hPW.1.1) (hX := hY.1) hfb)) _ hV
  rw [hη, P.coheight_genericPoint] at h2
  exact absurd h2 (by norm_num)

/-- If the strict transform `S'` of `S` lies over the biregular locus of `f`, a codimension-two
point of `S'` maps to a point of codimension at least two of `X`. -/
private theorem two_le_coheight_map_of_mem_support {X Y : Scheme.{u}} (f : Y ⟶ X)
    {S : PrimeDivisor X} {S' : PrimeDivisor Y}
    (hfS : f S'.genericPoint = S.genericPoint ∧ f S'.genericPoint ∈ biregularLocus f)
    {y : Y} (hyS : y ∈ S'.support) (hy : Order.coheight y = 2) : 2 ≤ Order.coheight (f y) := by
  refine two_le_coheight_of_specializes S
    (hfS.1 ▸ (genericPoint_specializes_of_mem_support S' hyS).map f.continuous) fun h => ?_
  have := eq_of_map_eq_of_mem_biregularLocus (h.trans hfS.1.symm) (h ▸ hfS.1 ▸ hfS.2)
  rw [this, S'.coheight_genericPoint] at hy
  exact absurd hy (by norm_num)

open Classical in
/-- **The divisor `G` over `X`.** On a log resolution `f : Y ⟶ X` of `(X, S + B)` such that the
strict transform `S'` of `S` meets no prime divisor lying over a point of `Supp B ∖ S`, and for
a point `y ∈ S'` of codimension two in `Y`, the exceptional divisor `G` of the blow-up of `Y`
along the closure of `y` is exceptional over `X`, has center the closure of `f(y)`, and
`a(G, X, S + B) = ∑_{y ∈ E} a(E, X, S + B)`, the sum over the `f`-exceptional prime divisors
`E` through `y`. -/
private theorem exists_divisorOver_isDiscrepancy {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : PrimeDivisor X) {B : QDivisor X} (hB : B.coeff S = 0)
    (hKSB : (Divisor.toQDivisor K + Finsupp.single S 1 + B).IsQCartier)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsLogResolution sX
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single S 1) + B)) f)
    (hY : IsNormalVariety k (f ≫ sX))
    (S' : PrimeDivisor Y) (hS' : inverseTransformPrimeDivisor f S = some S')
    (hdisj : ∀ Γ : PrimeDivisor Y, f Γ.genericPoint ∈ B.supp → f Γ.genericPoint ∉ S.support →
      Disjoint (S'.support : Set Y) Γ.support)
    (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ E, E ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap E)
    (e : PrimeDivisor Y → ℚ)
    (he : ∀ E ∈ Ex, IsDiscrepancy sX (n + 1) K
      (Divisor.toQDivisor (Finsupp.single S 1) + B)
      ⟨Y, f, hY, hf.isBirationalMorphism, E⟩ (e E))
    (y : Y) (hyS : y ∈ S'.support) (hy : Order.coheight y = 2) :
    ∃ G : DivisorOver k sX, G.IsExceptional ∧ (G.center : Set X) = closure {f y} ∧
      IsDiscrepancy sX (n + 1) K (Finsupp.single S 1 + B) G
        (∑ E ∈ Ex, if y ∈ E.support then e E else 0) := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  haveI : IsProper f := hf.isProper
  have hfb : IsBirationalMorphism f := hf.isBirationalMorphism
  have hsm : IsSmoothScheme (f ≫ sX) := hf.isSmoothScheme
  haveI : Smooth (f ≫ sX) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hsm
  have hS1 := toQDivisor_single_one S
  set Δ : QDivisor X := Finsupp.single S 1 + B with hΔ
  have hPW : IsPairWith sX (n + 1) K Δ := ⟨hX, hK, by rwa [hΔ, ← add_assoc]⟩
  obtain ⟨t, ht, htsnc⟩ := exists_finset_isSNC_of_isLogResolution hf
  rw [QDivisor.supp_toRDivisor, hS1] at ht
  choose a ha using fun Γ : PrimeDivisor Y =>
    MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hK ⟨Y, f, hY, hfb, Γ⟩
  have hfS := MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hS'
  have hnex : ∀ Γ : PrimeDivisor Y, ¬ RationalMap.IsExceptional f.toRationalMap Γ →
      ∃ P : PrimeDivisor X, f Γ.genericPoint = P.genericPoint ∧
        f Γ.genericPoint ∈ biregularLocus f ∧ a Γ = -Δ.coeff P := fun Γ hΓ => by
    obtain ⟨P, hη, hV, hd⟩ := exists_primeDivisor_of_not_isExceptional hPW f hY hfb Γ hΓ
    exact ⟨P, hη, hV, (ha Γ).eq hd⟩
  have hS'nex : ¬ RationalMap.IsExceptional f.toRationalMap S' := by
    intro hE
    have h2 := (isExceptional_iff_two_le_coheight hX
      (⟨Y, f, hY, hfb, S'⟩ : DivisorOver k sX)).mp hE
    change 2 ≤ Order.coheight (f S'.genericPoint) at h2
    rw [hfS.1, S.coheight_genericPoint] at h2
    exact absurd h2 (by norm_num)
  have hΔS : Δ.coeff S = 1 := by
    rw [hΔ, DivisorWithCoeffs.coeff_add, hB, add_zero, DivisorWithCoeffs.coeff_single_self]
  have haS' : a S' = -1 := by
    obtain ⟨P, hP, -, hPa⟩ := hnex S' hS'nex
    have : P = S := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP.symm.trans hfS.1)
    rw [hPa, this, hΔS]
  have hS't : S' ∈ t := by
    refine (ht S').1 (Or.inr ?_)
    rw [hfS.1, DivisorWithCoeffs.mem_supp_iff]
    exact ⟨S, by rw [hΔS]; norm_num, MMP.Flips.primeDivisor_genericPoint_mem_support S⟩
  have hExt : ∀ E ∈ Ex, E ∈ t := fun E hE => (ht E).1 (Or.inl
    (MMP.Positivity.support_subset_exceptionalSet E ((hEx E).1 hE)
      (MMP.Flips.primeDivisor_genericPoint_mem_support E)))
  -- the crepant boundary of `(X, S + B)` on `Y`
  set ΔY : QDivisor Y := ∑ Γ ∈ t, (-a Γ) • Finsupp.single Γ (1 : ℚ) with hΔY
  have hΔYc : ∀ Γ, ΔY.coeff Γ = if Γ ∈ t then -a Γ else 0 := by
    intro Γ
    rw [hΔY, ← DivisorWithCoeffs.coeffAddMonoidHom_apply, map_sum]
    simp only [DivisorWithCoeffs.coeffAddMonoidHom_apply, DivisorWithCoeffs.coeff_apply,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq']
  have hcrep : IsCrepantBoundary sX (n + 1) K Δ f hY hfb ΔY := by
    intro Γ
    rw [hΔYc]
    split_ifs with hΓ
    · rw [neg_neg]
      exact ha Γ
    · have hΓex : ¬ RationalMap.IsExceptional f.toRationalMap Γ := fun hE =>
        hΓ ((ht Γ).1 (Or.inl (MMP.Positivity.support_subset_exceptionalSet Γ hE
          (MMP.Flips.primeDivisor_genericPoint_mem_support Γ))))
      obtain ⟨P, hP, -, hPa⟩ := hnex Γ hΓex
      have h0 : Δ.coeff P = 0 := by
        by_contra h0
        refine hΓ ((ht Γ).1 (Or.inr ?_))
        rw [hP, DivisorWithCoeffs.mem_supp_iff]
        exact ⟨P, h0, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
      rw [neg_zero, ← neg_zero, ← h0, ← hPa]
      exact ha Γ
  -- the canonical divisor of `Y`
  have hdimY : topologicalKrullDim Y = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hK.topologicalKrullDim_eq]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hfb).symm
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm hdimY
  obtain ⟨-, hiff⟩ := IsPair.isDiscrepancy_iff_of_crepant hPW.isPair f hY hfb hK hKY
    (Or.inl hcrep)
  -- the blow-up of `Y` along the closure of `y`
  set W := IrreducibleCloseds.closureSingleton y with hWdef
  have hWy : W.isIrreducible.genericPoint = y :=
    AlgebraicGeometry.AlgebraicCycle.genericPoint_closureSingleton y
  have hWc : codimension W = 2 := by rw [MMP.Flips.codimension_closureSingleton, hy]
  have hreg : IsRegularLocalRing (Y.presheaf.stalk W.isIrreducible.genericPoint) :=
    isRegularLocalRing_stalk_of_smooth_over_field (f ≫ sX) _
  obtain ⟨⟨D, j, hjo, hj, hE⟩, -⟩ :=
    MMP.Flips.valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp (f ≫ sX) hY W
      (by rw [hWc]) hreg
  haveI := hjo
  obtain ⟨-, hDd⟩ := isDiscrepancy_blowUp (f ≫ sX) hY.1 hKY ΔY W (c := 2) (by rw [hWc]; rfl)
    le_rfl D j hj hE
  rw [hWy] at hE
  have hGd := (hiff D (compDivisorOver f hY hfb D)
    (valuation_compDivisorOver f hY hfb D) _).mp hDd
  have hfy := two_le_coheight_map_of_mem_support f hfS hyS hy
  refine ⟨compDivisorOver f hY hfb D, ?_, ?_, ?_⟩
  · rw [isExceptional_iff_two_le_coheight hX]
    change 2 ≤ Order.coheight ((D.f ≫ f) D.E.genericPoint)
    rw [Scheme.Hom.comp_apply, hE]
    exact hfy
  · rw [DivisorOver.center_eq_closure_genericPoint]
    change closure {(D.f ≫ f) D.E.genericPoint} = _
    rw [Scheme.Hom.comp_apply, hE]
  · convert hGd using 1
    have hmemt : ∀ Γ ∈ t, Γ ∈ (∑ P ∈ t, Finsupp.single P (1 : ℤ)).support := fun Γ hΓ => by
      rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply,
        Finset.sum_eq_single_of_mem Γ hΓ fun Q _ hQΓ => Finsupp.single_eq_of_ne hQΓ.symm,
        Finsupp.single_eq_same]
      exact one_ne_zero
    have hsum : (ΔY.sum fun Γ c => c * ((Γ.multiplicityAlong W).toNat : ℚ)) =
        ∑ Γ ∈ t, -a Γ * (if y ∈ Γ.support then 1 else 0) := by
      rw [hΔY, ← Finsupp.sum_finset_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
      refine Finset.sum_congr rfl fun Γ hΓ => ?_
      rw [Finsupp.smul_single, Finsupp.sum_single_index (zero_mul _), smul_eq_mul, mul_one]
      congr 1
      split_ifs with hyΓ
      · obtain ⟨m, z, j, hz, -, hI⟩ := htsnc.2 W.isIrreducible.genericPoint
        rw [multiplicityAlong_eq_one Γ W hz (j ⟨Γ, hmemt Γ hΓ, hWy ▸ hyΓ⟩)
          (hI ⟨Γ, hmemt Γ hΓ, hWy ▸ hyΓ⟩)]
        rfl
      · rw [multiplicityAlong_eq_zero Γ W (hWy ▸ hyΓ)]
        rfl
    -- the components of the snc divisor through `y`
    have hterm : ∀ Γ ∈ t, (if y ∈ Γ.support then a Γ else 0) =
        (if Γ = S' then a Γ else 0) +
          (if Γ ∈ Ex then (if y ∈ Γ.support then a Γ else 0) else 0) := by
      intro Γ hΓ
      by_cases hΓS : Γ = S'
      · subst hΓS
        have : Γ ∉ Ex := fun h => hS'nex ((hEx Γ).1 h)
        simp [hyS, this]
      by_cases hΓE : Γ ∈ Ex
      · simp [hΓS, hΓE]
      · simp only [hΓS, hΓE, if_false, zero_add]
        split_ifs with hyΓ
        · obtain ⟨P, hP, hPV, -⟩ := hnex Γ fun h => hΓE ((hEx Γ).2 h)
          exact (hΓS (eq_of_mem_support_of_mem_biregularLocus f hfS hdisj hP hPV
            ((ht Γ).2 hΓ) hyS hyΓ)).elim
        · rfl
    have hkey : (∑ Γ ∈ t, if y ∈ Γ.support then a Γ else 0) =
        -1 + ∑ E ∈ Ex, if y ∈ E.support then e E else 0 := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' t S' a,
        if_pos hS't, haS', ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 hExt]
      congr 1
      refine Finset.sum_congr rfl fun E hE => ?_
      have h' : IsDiscrepancy sX (n + 1) K Δ ⟨Y, f, hY, hfb, E⟩ (e E) := by
        simpa only [hS1] using he E hE
      have : a E = e E := (ha E).eq h'
      rw [this]
    rw [hsum]
    have h2 : (∑ Γ ∈ t, -a Γ * (if y ∈ Γ.support then (1 : ℚ) else 0)) =
        -∑ Γ ∈ t, if y ∈ Γ.support then a Γ else 0 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      split_ifs <;> ring
    rw [h2, hkey]
    push_cast
    ring

/-! ### The ideal `Ĵ` through which `F` is realised -/

/-- A valuation `ξ` of `k(Y)` restricting along a proper dominant `f : Y ⟶ X` to the valuation
of a divisor over `X` dominates the local ring of a point of `Y` (valuative criterion). -/
private theorem exists_dominates_of_comap_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] {f : Y ⟶ X} [IsDominant f]
    [IsProper f] (D : DivisorOver k sX) {ξ : Valuation Y.functionField ℤᵐ⁰}
    (hξ : ξ.comap (functionFieldMap f) = D.valuation) :
    ∃ x : Y, (∀ a : Y.presheaf.stalk x, ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
        ξ (algebraMap _ Y.functionField a) < 1 := by
  set z := D.f D.E.genericPoint
  have hw : ∀ b : X.presheaf.stalk z,
      ξ (functionFieldMap f (algebraMap _ X.functionField b)) =
        D.valuation (algebraMap _ X.functionField b) := fun b => by
    simpa only [Valuation.comap_apply] using
      congrArg (fun v => v (algebraMap _ X.functionField b)) hξ
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk z →+* R :=
    ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _)
  have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence f := by
    have h : @IsProper _ _ f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq f :=
    { R := R
      K := Y.functionField
      i₁ := Y.fromSpecStalk (genericPoint Y)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk f,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
      Y.fromSpecStalk (genericPoint Y) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint Y ⤳ x := (genericPoint_spec Y).specializes trivial
  let g := Scheme.stalkClosedPointTo l
  have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
      Y.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hga : ∀ a : Y.presheaf.stalk x,
      algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hg).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hga]
    exact (g.hom a).2
  · rw [hga]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))

/-- **Divisors over `X` lift to a proper birational model.** For a proper birational morphism
`f : Y ⟶ X` from a normal variety, every divisor `D` over `X` has the valuation of a divisor `E`
over `Y`, read on `k(X)` through `f^*`. -/
private theorem exists_divisorOver_comap_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    [IsProper f] (D : DivisorOver k sX) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    ∃ E : DivisorOver k (f ≫ sX), D.valuation = E.valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hbW := hf.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbW
  let ξ : Valuation Y.functionField ℤᵐ⁰ := D.valuation.comap (e.symm : Y.functionField →+* _)
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    change D.valuation (e.symm (functionFieldMap f t)) = D.valuation t
    have : e.symm (functionFieldMap f t) = t := e.symm_apply_apply t
    rw [this]
  obtain ⟨x, h1, h2⟩ := exists_dominates_of_comap_eq D hξ
  -- `ξ` is a divisor of `k(Y)`: `ord_E` on `D.Y`, along `k(Y) ≅ k(X) ≅ k(D.Y)`
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX f hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hs := congrArg (fun v => v s) hξ
    simp only [Valuation.comap_apply] at hs
    have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
    rw [h1, hs]
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX) hdiv x h1 h2
  refine ⟨D'.toDivisorOver, ?_⟩
  change D.valuation = D'.valuation.comap (functionFieldMap f)
  rw [hv, hξ]

/-- A morphism of integral schemes sending the generic point to the generic point is
dominant. -/
private theorem isDominant_of_map_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) : IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  have hc : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
  rw [← hc]
  exact closure_mono (by rintro _ rfl; exact ⟨_, h⟩)

/-- **Realising a divisor over `T` on a proper birational model `W`.** Let `F` be a divisor over
a normal variety `T`, `G₀` a divisor over `T` with the same valuation whose model maps only its
generic point to the generic point of `T`, and `g : W ⟶ T` a proper birational morphism from a
normal variety such that, on an open `V ⊆ W` containing every point of `W` over the center of
`F`, `g` factors through the model of `G₀`. Then `F` is a prime divisor of `W`. -/
private theorem exists_primeDivisor_valuation_eq_of_lift {k : Type u} [Field k]
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {sT : T ⟶ Spec (.of k)} (hT : IsNormalVariety k sT)
    (F G0 : DivisorOver k sT) (hG0 : G0.valuation = F.valuation)
    (hgen : ∀ z : G0.Y, G0.f z = genericPoint T →
      z = (haveI := G0.isIntegral; genericPoint G0.Y))
    {W : Scheme.{u}} (g : W ⟶ T) (hW : IsNormalVariety k (g ≫ sT))
    (hg : IsBirationalMorphism g) [IsProper g] (V : W.Opens) (ψ : V.toScheme ⟶ G0.Y)
    (hψ : ψ ≫ G0.f = V.ι ≫ g) (hV : ∀ w : W, g w = F.f F.E.genericPoint → w ∈ V) :
    ∃ F' : PrimeDivisor W, (⟨W, g, hW, hg, F'⟩ : DivisorOver k sT).valuation = F.valuation := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (g ≫ sT) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sT)
  haveI : IsDominant g := hg.isDominant
  haveI := G0.isIntegral
  haveI := G0.isNormal
  haveI := G0.isLocallyNoetherian
  haveI := G0.isDominant
  haveI : IsSeparated (G0.f ≫ sT) := G0.isNormalVariety.1.toIsSeparated
  -- the divisor `F` on `W`
  obtain ⟨Fh, hFh⟩ := exists_divisorOver_comap_eq hW hg F
  haveI := Fh.isIntegral
  haveI := Fh.isNormal
  haveI := Fh.isLocallyNoetherian
  haveI := Fh.isDominant
  set c := Fh.f Fh.E.genericPoint with hc
  have hgc : g c = F.f F.E.genericPoint := by
    have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hT.1
      (D := compDivisorOver g hW hg Fh) (D' := F) (by rw [valuation_compDivisorOver, ← hFh])
    exact this
  have hcV : c ∈ V := hV c hgc
  set c' : V.toScheme := ⟨c, hcV⟩ with hc'
  haveI : Nonempty V.toScheme := ⟨c'⟩
  haveI : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨c, hcV⟩)
  -- `ψ` is dominant
  have hψη : ψ (genericPoint V.toScheme) = genericPoint G0.Y := hgen _ (by
    rw [← Scheme.Hom.comp_apply, hψ, Scheme.Hom.comp_apply, map_genericPoint_of_isDominant V.ι,
      map_genericPoint_of_isDominant g])
  haveI : IsDominant ψ := isDominant_of_map_genericPoint ψ hψη
  have key : ∀ (m : V.toScheme ⟶ T) [IsDominant m], m = ψ ≫ G0.f → ∀ t,
      functionFieldMap m t = functionFieldMap ψ (functionFieldMap G0.f t) := by
    intro m _ hm t
    subst hm
    exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply ψ G0.f t).symm
  have hff : ∀ t, functionFieldMap ψ (functionFieldMap G0.f t) =
      functionFieldMap V.ι (functionFieldMap g t) := by
    intro t
    rw [← key (V.ι ≫ g) hψ.symm t,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hbG := G0.isBirationalMorphism.functionFieldMap_bijective
  have hbg := hg.functionFieldMap_bijective
  have hbV : Function.Bijective (functionFieldMap V.ι) :=
    functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨c', trivial⟩
  set w0 := G0.E.divisorialValuation with hw0def
  have hw0 : ∀ t, w0 (functionFieldMap G0.f t) = F.valuation t := fun t => by rw [← hG0]; rfl
  have hvW : ∀ t, Fh.valuation (functionFieldMap g t) = F.valuation t := fun t => by
    rw [hFh]; rfl
  -- the local homomorphism `𝒪_{G₀, ψ(c)} ⟶ 𝒪_{W, c}`
  haveI : IsIso (V.ι.stalkMap c') := inferInstance
  let φ : G0.Y.presheaf.stalk (ψ c') →+* W.presheaf.stalk c :=
    (inv (V.ι.stalkMap c')).hom.comp (ψ.stalkMap c').hom
  have hφ : ∀ a t, algebraMap _ G0.Y.functionField a = functionFieldMap G0.f t →
      algebraMap _ W.functionField (φ a) = functionFieldMap g t := by
    intro a t ha
    apply hbV.1
    have h1 : functionFieldMap V.ι (algebraMap _ W.functionField (φ a)) =
        algebraMap _ V.toScheme.functionField ((V.ι.stalkMap c').hom (φ a)) :=
      functionFieldMap_algebraMap_stalk V.ι c' (φ a)
    have h2 : (V.ι.stalkMap c').hom (φ a) = (ψ.stalkMap c').hom a := by
      change ((V.ι.stalkMap c').hom ((inv (V.ι.stalkMap c')).hom ((ψ.stalkMap c').hom a))) = _
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
    rw [h1, h2, ← functionFieldMap_algebraMap_stalk ψ c' a, ha, hff]
  -- `ψ(c)` is the generic point of the divisor of `G₀`
  have hdom : ∀ a : G0.Y.presheaf.stalk (ψ c'), w0 (algebraMap _ _ a) ≤ 1 ∧
      (a ∈ IsLocalRing.maximalIdeal _ → w0 (algebraMap _ _ a) < 1) := by
    intro a
    obtain ⟨t, ht⟩ := hbG.2 (algebraMap _ G0.Y.functionField a)
    have hb := hφ a t ht.symm
    rw [← ht, hw0, ← hvW, ← hb]
    refine ⟨MMP.Positivity.DivisorOver.valuation_algebraMap_le_one Fh c rfl (φ a), fun ha => ?_⟩
    refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one Fh c rfl (φ a) ?_
    haveI : IsLocalHom φ := by
      change IsLocalHom ((inv (V.ι.stalkMap c')).hom.comp (ψ.stalkMap c').hom)
      infer_instance
    exact map_nonunit φ a ha
  have hψc : ψ c' = G0.E.genericPoint := by
    refine MMP.Positivity.DivisorOver.eq_of_dominates (G0.f ≫ sT) w0 (fun a => (hdom a).1)
      (fun a ha => (hdom a).2 ha) (fun a => ?_) (fun a ha => ?_)
    · exact (PrimeDivisor.divisorialValuation_le_one_iff G0.E _).2 ⟨a, rfl⟩
    · exact (PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff G0.E a).2 ha
  -- `φ` is an isomorphism
  have hrange : ∀ z : G0.Y, z = G0.E.genericPoint → ∀ s, w0 s ≤ 1 →
      s ∈ (algebraMap (G0.Y.presheaf.stalk z) G0.Y.functionField).range := by
    rintro z rfl s hs
    exact (PrimeDivisor.divisorialValuation_le_one_iff G0.E s).1 hs
  have hφb : Function.Bijective φ := by
    refine ⟨fun a a' haa => ?_, fun b => ?_⟩
    · obtain ⟨t, ht⟩ := hbG.2 (algebraMap _ G0.Y.functionField a)
      obtain ⟨t', ht'⟩ := hbG.2 (algebraMap _ G0.Y.functionField a')
      have h1 := hφ a t ht.symm
      rw [haa, hφ a' t' ht'.symm] at h1
      obtain rfl : t = t' := hbg.1 h1.symm
      exact IsFractionRing.injective (G0.Y.presheaf.stalk (ψ c')) G0.Y.functionField
        (ht.symm.trans ht')
    · obtain ⟨t, ht⟩ := hbg.2 (algebraMap _ W.functionField b)
      have hle : w0 (functionFieldMap G0.f t) ≤ 1 := by
        rw [hw0, ← hvW, ht]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one Fh c rfl b
      obtain ⟨a, ha⟩ := hrange (ψ c') hψc _ hle
      refine ⟨a, IsFractionRing.injective (W.presheaf.stalk c) W.functionField ?_⟩
      rw [hφ a t ha, ht]
  have hcoh : Order.coheight c = 1 := by
    have h1 := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective φ hφb)
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hψc,
      G0.E.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne c hcoh, ?_⟩
  have hv := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hW Fh
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne c hcoh)
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne c hcoh).symm
  ext t
  rw [← hvW, hv]
  change _ = PrimeDivisor.divisorialValuation _
    (functionFieldMap (𝟙 W) (functionFieldMap g t))
  rw [functionFieldMap_id_apply]
  rfl

/-- An affine variety is quasi-projective: `𝒪_X` is ample relative to the quasi-affine structure
morphism. -/
private theorem isQuasiProjectiveVariety_of_isAffine {k : Type u} [Field k] {U : Scheme.{u}}
    [IsAffine U] (s : U ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k s] :
    IsQuasiProjectiveVariety k s := by
  rw [isQuasiProjectiveVariety_iff_isQuasiProjective,
    isQuasiProjective_iff_hProjectiveIsQuasiProjective]
  exact ⟨⟨inferInstance, inferInstance⟩, Stacks.Ample.unitModule U, inferInstance,
    Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule s _ (Iso.refl _)⟩

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- The pull-back of an effective Cartier divisor along an open immersion of integral schemes is
an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_comap_of_isOpenImmersion {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsIntegral X] (J : Y.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (j : X ⟶ Y) [IsOpenImmersion j] :
    Stacks.Divisors.IsEffectiveCartierDivisor (J.comap j) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian j
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun t _ => ?_
  obtain ⟨g, hg, hgen⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor J hJ (j t)
  refine ⟨(j.stalkMap t).hom g, IsRegular.of_ne_zero ?_, by
    rw [AlgebraicGeometry.stalk_comap, hgen, Ideal.map_span, Set.image_singleton]⟩
  haveI : IsIso (j.stalkMap t) := @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ _ ‹_› t
  have hinj : Function.Injective (j.stalkMap t).hom :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap t)).1
  intro h0
  have : g = 0 := hinj (by rw [h0, map_zero])
  exact hg.ne_zero this

/-- **Realising a divisor over `T` on the models of `T`.** Let `T ⊆ X` be a normal closed
subvariety, image of a prime divisor `P` of `X`, with a canonical divisor, and `F` a divisor over
`T` whose center is not all of `T`. There is an ideal sheaf `J ⊆ 𝒪_X` whose support has
codimension at least two in `X` such that `F` is a prime divisor of every proper birational
model `W ⟶ T` from a normal variety on which `J` pulls back to an effective Cartier divisor. -/
private theorem exists_idealSheaf_realising {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of k)}
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (ι : T ⟶ X)
    [IsClosedImmersion ι] (hT : IsNormalVariety k (ι ≫ sX)) (P : PrimeDivisor X)
    (hP : Set.range ι = (P.support : Set X))
    {n : ℕ} {KS : Divisor T} (hKS : KS.IsCanonicalDivisor (ι ≫ sX) n)
    (F : DivisorOver k (ι ≫ sX)) (hFη : F.f F.E.genericPoint ≠ genericPoint T) :
    ∃ J : X.IdealSheafData, (∀ x ∈ J.support, 2 ≤ Order.coheight x) ∧
      ∀ (W : Scheme.{u}) (g : W ⟶ T) (hW : IsNormalVariety k (g ≫ ι ≫ sX))
        (hg : IsBirationalMorphism g), IsProper g →
        Stacks.Divisors.IsEffectiveCartierDivisor (J.comap (g ≫ ι)) →
        ∃ F' : PrimeDivisor W,
          (⟨W, g, hW, hg, F'⟩ : DivisorOver k (ι ≫ sX)).valuation = F.valuation := by
  haveI : AlgebraicGeometry.IsVariety k (ι ≫ sX) := hT.1
  set x0 := F.f F.E.genericPoint with hx0
  -- an affine open `U₀ ⊆ T` through the center of `F`
  obtain ⟨_, ⟨V, hVa, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (ι x0)) isOpen_univ
  set U0 : T.Opens := ι ⁻¹ᵁ V with hU0
  have hx0U : x0 ∈ U0 := hxV
  haveI : IsAffine U0 := (hVa.preimage ι : IsAffineOpen U0)
  haveI : Nonempty U0 := ⟨⟨x0, hx0U⟩⟩
  haveI : IsDominant U0.ι := Opens.isDominant_ι (U0.isOpen.dense ⟨x0, hx0U⟩)
  have hU0v : IsNormalVariety k (U0.ι ≫ ι ≫ sX) := isNormalVariety_ι hT U0
  haveI : AlgebraicGeometry.IsVariety k (U0.ι ≫ ι ≫ sX) := hU0v.1
  haveI : IsQuasiProjectiveVariety k (U0.ι ≫ ι ≫ sX) := isQuasiProjectiveVariety_of_isAffine _
  have hU0b : IsBirationalMorphism U0.ι := by
    haveI : IsOpenImmersion ((⊤ : U0.toScheme.Opens).ι ≫ U0.ι) := inferInstance
    exact isBirationalMorphism_of_isOpenImmersion U0.ι ⊤ (by simp)
  -- `F` restricted to `U₀`
  have hPW0 : IsPairWith (ι ≫ sX) n KS (-Divisor.toQDivisor KS) :=
    ⟨hT, hKS, by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero⟩
  have hFc : ((F.center : Set T) ∩ U0).Nonempty :=
    ⟨x0, by rw [F.center_eq_closure_genericPoint]; exact subset_closure rfl, hx0U⟩
  obtain ⟨hY0, hf0, E0, -, hv0, -⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPW0 F U0 hFc
  set F0 : DivisorOver k (U0.ι ≫ ι ≫ sX) := ⟨_, F.f ∣_ U0, hY0, hf0, E0⟩ with hF0
  haveI := F0.isIntegral
  haveI := F0.isNormal
  haveI := F0.isLocallyNoetherian
  haveI := F0.isDominant
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (U0.ι ≫ ι ≫ sX) F0.valuation := by
    refine ⟨F0.Y, F0.f ≫ U0.ι ≫ ι ≫ sX, F0.isNormalVariety, F0.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra (U0.ι ≫ ι ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (F0.f ≫ U0.ι ≫ ι ≫ sX)
    refine ⟨MMP.Mori.functionFieldAlgEquiv (U0.ι ≫ ι ≫ sX) F0.f
      F0.isBirationalMorphism.functionFieldMap_bijective, ?_⟩
    ext t
    rfl
  -- a projective model of `U₀` on which `F` is a prime divisor, and its blow-up presentation
  obtain ⟨D0, hD0p, hD0v, -⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates
    (U0.ι ≫ ι ≫ sX) hdiv (F0.f F0.E.genericPoint)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one F0 _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one F0 _ rfl)
  haveI := D0.toDivisorOver.isIntegral
  haveI := D0.toDivisorOver.isDominant
  obtain ⟨J0, hJ0, hJ0ft, e, he⟩ := MMP.exists_blowUp_iso_of_isProjective_of_isBirational
    (U0.ι ≫ ι ≫ sX) D0.f hD0p
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D0.isBirationalMorphism)
  obtain ⟨-, -, hisoU, -, hlift, -⟩ :=
    MMP.Blowup.isBirational_blowUpToBase_and_exists_iso_blowUp (U0.ι ≫ ι ≫ sX) J0 hJ0 hJ0ft
  -- the ideals `J' ⊆ 𝒪_T` and `J ⊆ 𝒪_X`
  set J' : T.IdealSheafData := (J0.subschemeι ≫ U0.ι).ker with hJ'
  have hJ'U : J'.comap U0.ι = J0 := AlgebraicGeometry.ker_comap_eq_of_isOpenImmersion U0 J0
  set J : X.IdealSheafData := (J'.subschemeι ≫ ι).ker with hJdef
  have hJT : J.comap ι = J' := by
    rw [hJdef, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have h : Limits.pullback.fst ι (J'.subschemeι ≫ ι) =
        Limits.pullback.snd ι (J'.subschemeι ≫ ι) ≫ J'.subschemeι := by
      rw [← cancel_mono ι, Category.assoc, Limits.pullback.condition]
    rw [h, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
  -- the generic point of `U₀` is not in `V(J₀)`
  have hηJ0 : genericPoint U0.toScheme ∉ J0.support := by
    intro h
    refine hJ0 (Scheme.IdealSheafData.support_eq_top_iff.1 ?_)
    refine top_le_iff.1 fun z _ => ?_
    have hz : genericPoint U0.toScheme ⤳ z := genericPoint_specializes z
    exact hz.mem_closed J0.support.isClosed h
  refine ⟨J, ?_, ?_⟩
  · -- the support of `J` lies in `P` and misses its generic point
    intro x hx
    have h1 : (J.support : Set X) = closure (Set.range (J'.subschemeι ≫ ι)) :=
      Scheme.Hom.support_ker _
    have hxr : x ∈ Set.range ι := by
      have hx' : x ∈ closure (Set.range (J'.subschemeι ≫ ι)) := h1 ▸ hx
      refine closure_minimal ?_ ι.isClosedEmbedding.isClosed_range hx'
      rintro _ ⟨z, rfl⟩
      exact ⟨J'.subschemeι z, rfl⟩
    obtain ⟨t, rfl⟩ := hxr
    have hPsp : ∀ t' : T, P.genericPoint ⤳ ι t' := fun t' =>
      genericPoint_specializes_of_mem_support P (hP ▸ ⟨t', rfl⟩ : ι t' ∈ (P.support : Set X))
    have hgP : ι (genericPoint T) = P.genericPoint := by
      obtain ⟨t0, ht0⟩ : P.genericPoint ∈ Set.range ι := by
        rw [hP]; exact MMP.Flips.primeDivisor_genericPoint_mem_support P
      have h3 : ι (genericPoint T) ⤳ P.genericPoint := by
        rw [← ht0]; exact (genericPoint_specializes t0).map ι.continuous
      exact (inseparable_iff_specializes_and.2 ⟨h3, hPsp _⟩).eq
    have ht : t ≠ genericPoint T := by
      rintro rfl
      have h2 : genericPoint T ∈ ((J.comap ι).support : Set T) := by
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage]
        exact hx
      rw [hJT] at h2
      have h4 : genericPoint U0.toScheme ∈ ((J'.comap U0.ι).support : Set _) := by
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
          map_genericPoint_of_isDominant]
        exact h2
      rw [hJ'U] at h4
      exact hηJ0 h4
    exact two_le_coheight_of_specializes P (hPsp t)
      fun h => ht (ι.isClosedEmbedding.injective (h.trans hgP.symm))
  · intro W g hW hg hgp hJW
    haveI := hgp
    haveI : IsIntegral W := hW.1.toIsIntegral
    haveI : LocallyOfFiniteType (g ≫ ι ≫ sX) := hW.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ ι ≫ sX)
    rw [Scheme.IdealSheafData.comap_comp, hJT] at hJW
    set Vg : W.Opens := g ⁻¹ᵁ U0 with hVg
    haveI : IsDominant g := hg.isDominant
    haveI : Nonempty Vg := ⟨⟨genericPoint W, show g (genericPoint W) ∈ U0 by
      rw [map_genericPoint_of_isDominant]
      exact ((genericPoint_spec T).mem_open_set_iff U0.isOpen).2 ⟨x0, trivial, hx0U⟩⟩⟩
    have hJ0V : Stacks.Divisors.IsEffectiveCartierDivisor (J0.comap (g ∣_ U0)) := by
      rw [← hJ'U, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι,
        Scheme.IdealSheafData.comap_comp]
      exact isEffectiveCartierDivisor_comap_of_isOpenImmersion _ hJW Vg.ι
    obtain ⟨φ, hφ, -⟩ := hlift (g ∣_ U0) hJ0V
    have hψ0 : (φ ≫ e.inv) ≫ D0.f = g ∣_ U0 := by
      rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, hφ]
    set G0 : DivisorOver k (ι ≫ sX) := compDivisorOver U0.ι hU0v hU0b D0.toDivisorOver with hG0d
    have hG0 : G0.valuation = F.valuation := by
      rw [hG0d, valuation_compDivisorOver, hv0]
      exact congrArg (Valuation.comap (functionFieldMap U0.ι)) hD0v
    have hgen' : ∀ z : D0.Y, U0.ι (D0.f z) = genericPoint T → z = genericPoint D0.Y := by
      intro z hz2
      have hz' : D0.f z = genericPoint U0.toScheme := by
        apply U0.ι.isOpenEmbedding.injective
        rw [hz2, map_genericPoint_of_isDominant U0.ι]
      have hbir : genericPoint U0.toScheme ∈ biregularLocus (blowUpToBase J0) :=
        le_biregularLocus hisoU hηJ0
      have h7 : blowUpToBase J0 (e.hom z) = genericPoint U0.toScheme := by
        rw [← Scheme.Hom.comp_apply, he, hz']
      have h8 : blowUpToBase J0 (e.hom (genericPoint D0.Y)) = genericPoint U0.toScheme := by
        rw [← Scheme.Hom.comp_apply, he, map_genericPoint_of_isDominant D0.f]
      have h9 := eq_of_map_eq_of_mem_biregularLocus (h7.trans h8.symm) (h7 ▸ hbir)
      exact e.hom.isOpenEmbedding.injective h9
    have hgen : ∀ z : G0.Y, G0.f z = genericPoint T →
        z = (haveI := G0.isIntegral; genericPoint G0.Y) := fun z hz => hgen' z hz
    refine exists_primeDivisor_valuation_eq_of_lift hT F G0 hG0 hgen g hW hg Vg (φ ≫ e.inv)
      ?_ fun w hw => ?_
    · change (φ ≫ e.inv) ≫ D0.f ≫ U0.ι = Vg.ι ≫ g
      rw [← Category.assoc, hψ0, morphismRestrict_ι]
    · change g w ∈ U0
      rw [hw]
      exact hx0U

/-! ### A log resolution principalizing `Ĵ` -/

/-- A variety is a disjoint union of varieties, with one component. -/
private theorem isDisjointUnionOfVarieties_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX) :
    MMP.Resolution.IsDisjointUnionOfVarieties sX := by
  haveI := hX
  haveI : IsIntegral X := hX.toIsIntegral
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro C hC C' hC' hne
  rw [irreducibleComponents_eq_singleton] at hC hC'
  exact absurd (hC.trans hC'.symm) hne

/-- If the end result of a blow-up sequence of a variety is nonempty, it is a variety. -/
private theorem isVariety_toBase {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : MMP.Resolution.ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)),
      AlgebraicGeometry.IsVariety k sX → Nonempty B.target →
        AlgebraicGeometry.IsVariety k (B.toBase ≫ sX)
  | X, .nil _, sX, hX, _ => by
    change AlgebraicGeometry.IsVariety k (𝟙 X ≫ sX)
    rwa [Category.id_comp]
  | X, .cons Z B, sX, hX, hne => by
    haveI := hX
    have hZ : Z ≠ ⊥ := by
      rintro rfl
      haveI := AlgebraicGeometry.isEmpty_blowUp_bot X
      obtain ⟨y⟩ := hne
      exact isEmptyElim (B.toBase y)
    have h := (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      sX Z hZ).1
    have := isVariety_toBase B _ h hne
    change AlgebraicGeometry.IsVariety k ((B.toBase ≫ blowUpToBase Z) ≫ sX)
    rwa [Category.assoc]

/-- A morphism which is an isomorphism over a nonempty open has points over it. -/
private theorem nonempty_preimage_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  exact ⟨(inv (g ∣_ V) ⟨x, hx⟩).1, (inv (g ∣_ V) ⟨x, hx⟩).2⟩

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : IsBirationalMorphism g := by
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    (nonempty_preimage_of_isIso_restrict g V hV) hV le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- A composite of isomorphisms over `V` and over its inverse image is an isomorphism over `V`. -/
private theorem isIso_restrict_comp {X Y W : Scheme.{u}} (h : W ⟶ Y) (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] [IsIso (h ∣_ g ⁻¹ᵁ V)] : IsIso ((h ≫ g) ∣_ V) := by
  rw [morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›

/-- An open of `X` which is smooth over `k` lies in the smooth locus. -/
private theorem le_smoothLocus_of_isSmoothScheme {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {U : X.Opens}
    (hU : IsSmoothScheme (U.ι ≫ sX)) : U ≤ smoothLocus sX := by
  have : LocallyOfFinitePresentation (U.ι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sX)).mpr inferInstance
  exact le_smoothLocus _ ((isSmoothScheme_iff _).1 hU)

/-- An open in the smooth locus is smooth over `k`. -/
private theorem isSmoothScheme_of_le_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : U ≤ smoothLocus sX) :
    IsSmoothScheme (U.ι ≫ sX) := by
  refine top_le_iff.1 fun x' _ => ?_
  obtain ⟨V, hxV, hV⟩ := mem_smoothLocus_iff.1 (hU x'.2)
  refine mem_smoothLocus_iff.2 ⟨U.ι ⁻¹ᵁ V, hxV, ?_⟩
  haveI := hV
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι U.ι (le_refl (U.ι ⁻¹ᵁ V)), Category.assoc]
  infer_instance

/-- A point of the support of an ideal sheaf with principal stalks which has no proper
generization in the support has coheight at most one. -/
private theorem coheight_le_one_of_principal {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) (hI : ∀ y, ∃ h, IdealSheafData.stalk I y = Ideal.span {h})
    {η : Y} (hη : η ∈ I.support) (hmax : ∀ η' ∈ I.support, η' ⤳ η → η ⤳ η') :
    Order.coheight η ≤ 1 := by
  obtain ⟨h, hh⟩ := hI η
  have hmin : IsLocalRing.maximalIdeal _ ∈ (Ideal.span {h}).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, fun P hP _ => ?_⟩
    · rw [← hh]
      exact IsLocalRing.le_maximalIdeal
        ((Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).not.2 (not_not.2 hη))
    · obtain ⟨hPp, hPh⟩ := hP
      let p : PrimeSpectrum (Y.presheaf.stalk η) := ⟨P, hPp⟩
      have hp1 : Y.fromSpecStalk η p ∈ I.support := by
        change p ∈ Y.fromSpecStalk η ⁻¹' (I.support : Set Y)
        rw [MMP.Resolution.preimage_fromSpecStalk_support, hh]
        exact (PrimeSpectrum.mem_zeroLocus _ _).2 fun x hx => hPh hx
      have hp2 := MMP.Resolution.fromSpecStalk_specializes_self η p
      have heq : Y.fromSpecStalk η p = η := (hp2.antisymm (hmax _ hp1 hp2)).eq
      have hpc : p = IsLocalRing.closedPoint _ := (Y.fromSpecStalk η).isEmbedding.injective
        (heq.trans Scheme.fromSpecStalk_closedPoint.symm)
      change IsLocalRing.maximalIdeal _ ≤ p.asIdeal
      rw [hpc]
      exact le_rfl
  haveI : (Ideal.span {h}).IsPrincipal := ⟨⟨h, rfl⟩⟩
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing _ hmin
  have h2 : (Order.coheight η : WithBot ℕ∞) ≤ 1 := by
    rw [← ringKrullDim_stalk_eq_coheight, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast h1
  exact_mod_cast h2

/-- In a Noetherian space every point of a closed set specializes from a maximal point of it. -/
private theorem exists_maximal_generization {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y]
    [QuasiSober Y] (S : Closeds Y) {y : Y} (hy : y ∈ S) :
    ∃ η ∈ S, η ⤳ y ∧ ∀ η' ∈ S, η' ⤳ η → η ⤳ η' := by
  obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf S.isClosed
  obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.1 (hcov hy)
  have hWc : IsClosed W := MMP.Resolution.Aux.isClosed_of_mem_componentsOf S.isClosed hW
  have hgen := hW.1.1.isGenericPoint_genericPoint_closure
  rw [hWc.closure_eq] at hgen
  refine ⟨hW.1.1.genericPoint, hW.1.2 hgen.mem, hgen.specializes hyW, fun η' hη' hsp => ?_⟩
  have h1 : W ⊆ closure {η'} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
      isClosed_closure
  have h2 := hW.2 ⟨isIrreducible_singleton.closure, closure_minimal
    (Set.singleton_subset_iff.2 hη') S.isClosed⟩ h1
  rw [specializes_iff_mem_closure, hgen.def]
  exact h2 (subset_closure rfl)

/-- The stalks of an effective Cartier divisor are principal. -/
private theorem stalk_principal_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    (I : Y.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    ∀ y, ∃ h, IdealSheafData.stalk I y = Ideal.span {h} := fun y =>
  (AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor I hI y).imp
    fun _ => And.right

/-- **A resolution principalizing an ideal of codimension two.** Let `X` be a normal variety in
characteristic zero and `I ⊆ 𝒪_X` an ideal whose support has codimension at least two and
contains the singular locus. The strong resolution of the blow-up of `I` is a resolution
`p : X₀ ⟶ X` on which `I 𝒪_{X₀}` is an effective Cartier divisor, and its exceptional set is
`p⁻¹(V(I))`. -/
private theorem exists_resolution_principalizing {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (I : X.IdealSheafData)
    (hI : ∀ x ∈ I.support, 2 ≤ Order.coheight x)
    (hsing : (singularLocus sX : Set X) ⊆ I.support) :
    ∃ (X0 : Scheme.{u}) (p0 : X0 ⟶ X), MMP.Resolution.IsResolutionOfVariety sX p0 ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap p0) ∧
      (exceptionalSet p0 : Set X0) = p0 ⁻¹' (I.support : Set X) := by
  haveI hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := {}
  have hηI : genericPoint X ∉ I.support := fun h => by
    have := hI _ h
    rw [coheight_genericPoint] at this
    exact absurd this (by norm_num)
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    exact hηI (by simp; exact Set.mem_univ _)
  obtain ⟨hBv, hπp, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sX I hI0
  haveI := hBv
  haveI : IsIntegral (blowUp I) := hBv.toIsIntegral
  haveI : LocallyOfFiniteType (blowUpToBase I ≫ sX) := hBv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (blowUp I) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I ≫ sX)
  haveI : QuasiCompact (blowUpToBase I ≫ sX) := hBv.toQuasiCompact
  haveI : CompactSpace (blowUp I) :=
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase I ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian (blowUp I) := {}
  haveI hπi : IsIso (blowUpToBase I ∣_ I.support.compl) :=
    isIso_blowUpToBase_restrict_compl_support I
  -- the strong resolution of the blow-up
  obtain ⟨BR, hBR, -⟩ := MMP.Resolution.exists_strongResolution_blowupSequenceFunctor.{u}
  have hDU := isDisjointUnionOfVarieties_of_isVariety (blowUpToBase I ≫ sX) hBv
  obtain ⟨hsm₁, hiso₁, -⟩ := hBR (blowUpToBase I ≫ sX) hDU
  set B₁ := BR (blowUpToBase I ≫ sX) hDU with hB₁
  haveI := hiso₁
  set W : X.Opens := I.support.compl with hW
  have hWne : (W : Set X).Nonempty := ⟨genericPoint X, hηI⟩
  -- the blow-up is smooth over `W`
  have hWsm : W ≤ smoothLocus sX := fun x hx => by
    by_contra h
    exact hx (hsing h)
  have hπW : blowUpToBase I ⁻¹ᵁ W ≤ smoothLocus (blowUpToBase I ≫ sX) := by
    apply le_smoothLocus_of_isSmoothScheme
    have hWs : IsSmoothScheme (W.ι ≫ sX) := isSmoothScheme_of_le_smoothLocus sX hWsm
    haveI : Smooth (W.ι ≫ sX) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hWs
    have : LocallyOfFinitePresentation ((blowUpToBase I ⁻¹ᵁ W).ι ≫ blowUpToBase I ≫ sX) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
    refine (isSmoothScheme_iff _).2 ?_
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance
  haveI : IsIso (B₁.toBase ∣_ blowUpToBase I ⁻¹ᵁ W) :=
    MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le B₁.toBase hπW
  haveI hp0W : IsIso ((B₁.toBase ≫ blowUpToBase I) ∣_ W) :=
    isIso_restrict_comp B₁.toBase (blowUpToBase I) W
  set p0 := B₁.toBase ≫ blowUpToBase I with hp0
  -- `X₀` is a smooth variety
  have hX0ne : Nonempty B₁.target :=
    let ⟨y, _⟩ := nonempty_preimage_of_isIso_restrict p0 W hWne; ⟨y⟩
  have hX0v : AlgebraicGeometry.IsVariety k (p0 ≫ sX) := by
    rw [hp0, Category.assoc]; exact isVariety_toBase B₁ _ hBv hX0ne
  haveI := hX0v
  haveI : IsIntegral B₁.target := hX0v.toIsIntegral
  haveI : LocallyOfFiniteType (p0 ≫ sX) := hX0v.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian B₁.target := LocallyOfFiniteType.isLocallyNoetherian (p0 ≫ sX)
  haveI : QuasiCompact (p0 ≫ sX) := hX0v.toQuasiCompact
  haveI : CompactSpace B₁.target := QuasiCompact.compactSpace_of_compactSpace (p0 ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian B₁.target := {}
  have hp0b : IsBirationalMorphism p0 := isBirationalMorphism_of_isIso_restrict p0 W hWne
  haveI : IsDominant p0 := hp0b.isDominant
  have hp0p : IsProjective p0 :=
    (MMP.Resolution.ClosedBlowupSequence.isProjective_toBase B₁).comp hπp
  -- `I 𝒪_{X₀}` is an effective Cartier divisor
  have hL : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap p0) := by
    rw [hp0, Scheme.IdealSheafData.comap_comp]
    refine isEffectiveCartierDivisor_comap_of_genericPoint_notMem _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) B₁.toBase ?_
    intro h
    have h' : B₁.toBase (genericPoint B₁.target) ∈
        ((I.comap (blowUpToBase I)).support : Set (blowUp I)) := h
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, ← hp0, map_genericPoint_of_isDominant] at h'
    exact hηI h'
  -- the exceptional set
  have hWV : W ≤ biregularLocus p0 := le_biregularLocus hp0W
  have hEx : (exceptionalSet p0 : Set B₁.target) = p0 ⁻¹' (I.support : Set X) := by
    apply Set.Subset.antisymm
    · intro y hy
      by_contra hyI
      exact hy (hWV hyI)
    · intro y hy hyV
      have hyL : y ∈ (I.comap p0).support := by
        change y ∈ ((I.comap p0).support : Set B₁.target)
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
        exact hy
      obtain ⟨η, hηL, hηy, hηmax⟩ := exists_maximal_generization (I.comap p0).support hyL
      have h1 := coheight_le_one_of_principal (I.comap p0)
        (stalk_principal_of_isEffectiveCartierDivisor _ hL) hηL hηmax
      have hηV : p0 η ∈ biregularLocus p0 :=
        (hηy.map p0.continuous).mem_open (biregularLocus p0).isOpen hyV
      have h2 := MMP.Positivity.coheight_map_of_mem_biregularLocus p0 hηV
      have hηI' : p0 η ∈ I.support := by
        have : η ∈ ((I.comap p0).support : Set B₁.target) := hηL
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at this
        exact this
      have h3 := hI _ hηI'
      rw [h2] at h3
      exact absurd (h3.trans h1) (by norm_num)
  refine ⟨B₁.target, p0, ⟨hXv, hX0v, hp0p, hp0b, ?_⟩, hL, hEx⟩
  rw [hp0, Category.assoc]
  exact hsm₁

/-- If `a ≫ b` is an isomorphism, `a` is dominant, the source of `b` is reduced and `b` is
separated, then `b` is an isomorphism. -/
private theorem isIso_of_isIso_comp {A B V : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ V) [IsIso (a ≫ b)]
    [IsDominant a] [IsReduced B] [IsSeparated b] : IsIso b := by
  refine ⟨⟨inv (a ≫ b) ≫ a, ?_, by simp⟩⟩
  refine ext_of_isDominant_of_isSeparated b ?_ a ?_
  · simp
  · rw [← Category.assoc, IsIso.hom_inv_id_assoc, Category.comp_id]

/-- If `h ≫ g` is an isomorphism over `V`, with `h` dominant, `X'` reduced and `g` separated,
then `g` is an isomorphism over `V` and `h` over `g⁻¹(V)`. -/
private theorem isBiregular_of_isBiregular_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] {V : X.Opens}
    (hV : IsBiregular (h ≫ g) V) : IsBiregular g V ∧ IsBiregular h (g ⁻¹ᵁ V) := by
  unfold IsBiregular at hV ⊢
  rw [morphismRestrict_comp] at hV
  have : IsDominant (h ∣_ g ⁻¹ᵁ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant h› _
  have : IsSeparated (g ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› _
  have := @isIso_of_isIso_comp _ _ _ (h ∣_ g ⁻¹ᵁ V) (g ∣_ V) hV _ _ _
  exact ⟨this, @IsIso.of_isIso_comp_right _ _ _ _ _ _ (g ∣_ V) this hV⟩

/-- The exceptional set of `h ≫ g` is `Ex(h) ∪ h⁻¹(Ex(g))`. -/
private theorem exceptionalSet_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] [UniversallyClosed g] :
    exceptionalSet (h ≫ g) = exceptionalSet h ⊔ (exceptionalSet g).preimage h.continuous := by
  apply SetLike.coe_injective
  ext y
  change y ∈ exceptionalSet (h ≫ g) ↔ y ∈ exceptionalSet h ∨ h y ∈ exceptionalSet g
  simp only [mem_exceptionalSet]
  refine ⟨fun hy => ?_, fun hy hmem => ?_⟩
  · by_contra hne
    push Not at hne
    obtain ⟨hyh, hyg⟩ := hne
    apply hy
    have hcl : IsClosed (g '' (biregularLocus h : Set X')ᶜ) :=
      g.isClosedMap _ (biregularLocus h).isOpen.isClosed_compl
    let W : X.Opens := biregularLocus g ⊓ ⟨_, hcl.isOpen_compl⟩
    have hWg : IsBiregular g W :=
      isBiregular_iff_le_biregularLocus.mpr inf_le_left
    have hWh : IsBiregular h (g ⁻¹ᵁ W) :=
      isBiregular_iff_le_biregularLocus.mpr fun x hx => by_contra fun hxU => hx.2 ⟨x, hxU, rfl⟩
    have hiso : IsBiregular (h ≫ g) W := @isIso_restrict_comp _ _ _ h g W hWg hWh
    refine le_biregularLocus hiso ⟨hyg, ?_⟩
    rintro ⟨x, hx, hxy⟩
    have hxy' : g x = g (h y) := hxy.trans (Scheme.Hom.comp_apply h g y)
    exact hx (eq_of_map_eq_of_mem_biregularLocus hxy' (hxy' ▸ hyg) ▸ hyh)
  · have hb := isBiregular_of_isBiregular_comp h g (isBiregular_biregularLocus (h ≫ g))
    rcases hy with hy | hy
    · exact hy (le_biregularLocus hb.2 hmem)
    · exact hy (le_biregularLocus hb.1 hmem)

open MMP.Resolution in
/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

open MMP.Resolution in
/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

open MMP.Resolution in
/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rw [hPs]
        exact hxW
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-- The support of an ideal sheaf with principal stalks on an integral locally Noetherian scheme
which misses the generic point is of pure codimension one. -/
private theorem isPureCodimOne_support_of_principal {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [NoetherianSpace Y] (I : Y.IdealSheafData)
    (hI : ∀ y, ∃ h, IdealSheafData.stalk I y = Ideal.span {h})
    (hgen : genericPoint Y ∉ I.support) : IsPureCodimOne I.support := by
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := by rw [hWη]; exact subset_closure rfl
  have hηI : e W ∈ I.support := hW.1 hηW
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  have hle := coheight_le_one_of_principal I hI hηI fun η' hη' hsp => by
    let W' : IrreducibleCloseds Y :=
      ⟨closure {η'}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hWW' : W ≤ W' := by
      change (W : Set Y) ⊆ closure {η'}
      rw [hWη]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
        isClosed_closure
    have h2 := hW.2 (y := W') (closure_minimal (Set.singleton_subset_iff.2 hη') I.support.isClosed)
      hWW'
    rw [specializes_iff_mem_closure, ← hWη]
    exact h2 (subset_closure rfl)
  have hne : Order.coheight (e W) ≠ 0 := by
    intro h0
    have : e W = genericPoint Y := eq_genericPoint_of_coheight_eq_zero h0
    exact hgen (this ▸ hηI)
  exact le_antisymm hle (ENat.one_le_iff_ne_zero.2 hne)

/-- A union of two closed subsets of pure codimension one is of pure codimension one. -/
private theorem isPureCodimOne_sup {T : Type*} [TopologicalSpace T] {A B : Closeds T}
    (hA : IsPureCodimOne A) (hB : IsPureCodimOne B) : IsPureCodimOne (A ⊔ B) := by
  intro W hW
  have hWsub : (W : Set T) ⊆ (A : Set T) ∪ B := hW.1
  classical
  have key : (W : Set T) ⊆ A ∨ (W : Set T) ⊆ B := by
    obtain ⟨z, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible
      {(A : Set T), (B : Set T)} (by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact A.isClosed
        · exact B.isClosed) (by
        intro x hx
        rcases hWsub hx with h | h
        · exact ⟨A, by simp, h⟩
        · exact ⟨B, by simp, h⟩)
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Or.inl hWz
    · exact Or.inr hWz
  rcases key with h | h
  · exact hA W ⟨h, fun W' hW' hle => hW.2 (hW'.trans Set.subset_union_left) hle⟩
  · exact hB W ⟨h, fun W' hW' hle => hW.2 (hW'.trans Set.subset_union_right) hle⟩

/-- The stalk of a sum of ideal sheaves is the sum of the stalks. -/
private theorem stalk_sup {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I ⊔ J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ J x ⟨U, hU⟩ hxU, ← Ideal.map_sup]
  rfl

/-- In a local ring, if `a + b` is generated by a non-zero-divisor `m`, then `a = (m)` or
`b = (m)`. -/
private theorem eq_span_or_eq_span_of_sup_eq_span {R : Type*} [CommRing R] [IsLocalRing R]
    {a b : Ideal R} {m : R} (hm : IsRegular m) (h : a ⊔ b = Ideal.span {m}) :
    a = Ideal.span {m} ∨ b = Ideal.span {m} := by
  have hma : m ∈ a ⊔ b := h ▸ Ideal.mem_span_singleton_self m
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hma
  have hx' : x ∈ Ideal.span {m} := h ▸ Ideal.mem_sup_left hx
  have hy' : y ∈ Ideal.span {m} := h ▸ Ideal.mem_sup_right hy
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hx'
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hy'
  have hrt : r + t = 1 := by
    apply hm.2
    change (r + t) * m = 1 * m
    rw [add_mul, hr, ht, one_mul, hxy]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hrt with hu | hu
  · left
    refine le_antisymm (h ▸ le_sup_left) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨u, hu⟩ := hu
    have : m = ↑u⁻¹ * x := by rw [← hr, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact a.mul_mem_left _ hx
  · right
    refine le_antisymm (h ▸ le_sup_right) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨u, hu⟩ := hu
    have : m = ↑u⁻¹ * y := by rw [← ht, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact b.mul_mem_left _ hy

/-- A point of the singular locus of a normal variety has codimension at least two. -/
private theorem two_le_coheight_of_mem_singularLocus {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {x : X}
    (hxs : x ∈ (singularLocus sX : Set X)) : 2 ≤ Order.coheight x := by
  haveI hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := {}
  have h0 : Order.coheight x ≠ 0 := fun h => by
    have := eq_genericPoint_of_coheight_eq_zero h
    exact hxs (this ▸ MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus')
  have h1 : Order.coheight x ≠ 1 := fun h => by
    have := MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hX
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h)
    have hg : MMP.Mori.PrimeDivisor.genericPoint
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h) = x :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h
    exact hxs (hg ▸ this)
  generalize Order.coheight x = c at h0 h1 ⊢
  induction c using ENat.recTopCoe with
  | top => exact le_top
  | coe c =>
    norm_cast at h0 h1 ⊢
    omega

/-- Every point of the support of an effective Cartier divisor without generic point lies on a
prime divisor whose generic point is in that support. -/
theorem exists_primeDivisor_genericPoint_mem_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [NoetherianSpace Y] (L : Y.IdealSheafData)
    (hL : Stacks.Divisors.IsEffectiveCartierDivisor L)
    (h0 : ∀ s ∈ L.support, Order.coheight s ≠ 0) {x : Y} (hx : x ∈ L.support) :
    ∃ P : PrimeDivisor Y, P.genericPoint ∈ L.support ∧ x ∈ P.support := by
  obtain ⟨η, hηL, hηx, hηmax⟩ := exists_maximal_generization L.support hx
  have hcoh : Order.coheight η = 1 := le_antisymm
    (coheight_le_one_of_principal L (stalk_principal_of_isEffectiveCartierDivisor _ hL) hηL hηmax)
    (ENat.one_le_iff_ne_zero.2 (h0 η hηL))
  have hg : MMP.Mori.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hcoh) = η :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne η hcoh
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hcoh, by rw [hg]; exact hηL, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  change x ∈ closure {(MMP.Mori.PrimeDivisor.genericPoint
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hcoh))}
  rw [hg]
  exact specializes_iff_mem_closure.1 hηx

/-- A prime divisor through a point of the biregular locus of `p` lifts to a prime divisor
through any preimage of that point. -/
theorem exists_primeDivisor_map_genericPoint_eq_of_mem_support {X₀ X : Scheme.{u}}
    {p : X₀ ⟶ X} {x : X₀} (hxV : p x ∈ biregularLocus p) {Q : PrimeDivisor X}
    (hxQ : p x ∈ Q.support) :
    ∃ Q' : PrimeDivisor X₀, p Q'.genericPoint = Q.genericPoint ∧ x ∈ Q'.support := by
  have hQsp := genericPoint_specializes_of_mem_support Q hxQ
  have hηQ : Q.genericPoint ∈ biregularLocus p := hQsp.mem_open (biregularLocus p).isOpen hxV
  obtain ⟨Q', -, hQ'⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := p) Q hηQ
  refine ⟨Q', hQ', ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine specializes_iff_mem_closure.1 ?_
  set V := biregularLocus p
  haveI : IsIso (p ∣_ V) := isBiregular_biregularLocus p
  let a : (p ⁻¹ᵁ V).toScheme := ⟨Q'.genericPoint, show p Q'.genericPoint ∈ V from hQ' ▸ hηQ⟩
  let b : (p ⁻¹ᵁ V).toScheme := ⟨x, hxV⟩
  have hab : (p ∣_ V) a ⤳ (p ∣_ V) b := by
    rw [← V.ι.isOpenEmbedding.isInducing.specializes_iff, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    change p Q'.genericPoint ⤳ p x
    rw [hQ']
    exact hQsp
  exact (p ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.2
    ((p ∣_ V).isOpenEmbedding.isInducing.specializes_iff.1 hab)

/-- If the pull-back of `I_S + I_B` is an effective Cartier divisor, then a prime divisor `S'`
over the generic point of `S` meets no prime divisor lying over a point of `Supp B ∖ S`. -/
private theorem disjoint_support_of_isEffectiveCartierDivisor_comap_sup {X Y : Scheme.{u}}
    (f : Y ⟶ X) {S : PrimeDivisor X} {B : QDivisor X} {S' Γ : PrimeDivisor Y}
    (hMf : Stacks.Divisors.IsEffectiveCartierDivisor
      ((S.idealSheaf ⊔ Scheme.IdealSheafData.vanishingIdeal B.supp).comap f))
    (hfS' : f S'.genericPoint = S.genericPoint) (hSB : S.genericPoint ∉ (B.supp : Set X))
    (hΓB : f Γ.genericPoint ∈ B.supp) (hΓS : f Γ.genericPoint ∉ S.support) :
    Disjoint (S'.support : Set Y) Γ.support := by
  set IB : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal B.supp with hIB
  refine Set.disjoint_left.2 fun y hyS hyΓ => ?_
  obtain ⟨m, hm, hgen⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hMf y
  rw [Scheme.IdealSheafData.comap_sup, stalk_sup] at hgen
  have hsuppc : ∀ (K : X.IdealSheafData) (z : Y),
      z ∈ ((K.comap f).support : Set Y) ↔ f z ∈ (K.support : Set X) := fun K z => by
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage]
  have hIBs : (IB.support : Set X) = B.supp := by
    rw [hIB, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hS'S : S'.genericPoint ∈ (S.idealSheaf.comap f).support := by
    change S'.genericPoint ∈ ((S.idealSheaf.comap f).support : Set Y)
    rw [hsuppc, hfS']
    exact MMP.Flips.primeDivisor_genericPoint_mem_support S
  have hS'B : S'.genericPoint ∉ (IB.comap f).support := by
    change S'.genericPoint ∉ ((IB.comap f).support : Set Y)
    rw [hsuppc, hfS', hIBs]
    exact hSB
  have hΓS' : Γ.genericPoint ∉ (S.idealSheaf.comap f).support := by
    change Γ.genericPoint ∉ ((S.idealSheaf.comap f).support : Set Y)
    rw [hsuppc]
    exact hΓS
  have hΓB' : Γ.genericPoint ∈ (IB.comap f).support := by
    change Γ.genericPoint ∈ ((IB.comap f).support : Set Y)
    rw [hsuppc, hIBs]
    exact hΓB
  rcases eq_span_or_eq_span_of_sup_eq_span hm hgen with ha | hb
  · exact notMem_support_of_stalk_le _ _ (genericPoint_specializes_of_mem_support S' hyS)
      (le_sup_right.trans (hgen.trans ha.symm).le) hS'B hS'S
  · exact notMem_support_of_stalk_le _ _ (genericPoint_specializes_of_mem_support Γ hyΓ)
      (le_sup_left.trans (hgen.trans hb.symm).le) hΓS' hΓB'

/-- **A log resolution of `(X, S + B)` principalizing an ideal.** Let `X` be a normal variety in
characteristic zero, `S` a prime divisor, `B` a `ℚ`-divisor without component `S` and `J` an
ideal sheaf whose support has codimension at least two. There is a log resolution
`f : Y ⟶ X` of `(X, S + B)` such that the strict transform `S'` of `S` meets no prime divisor
lying over a point of `Supp B ∖ S`, and `J 𝒪_Y` is an effective Cartier divisor. -/
private theorem exists_isLogResolution_disjoint_isEffectiveCartierDivisor {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (S : PrimeDivisor X) {B : QDivisor X} (hB : B.coeff S = 0)
    (J : X.IdealSheafData) (hJ : ∀ x ∈ J.support, 2 ≤ Order.coheight x) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsLogResolution sX
        (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single S 1) + B)) f ∧
      IsNormalVariety k (f ≫ sX) ∧
      ∃ S' : PrimeDivisor Y, inverseTransformPrimeDivisor f S = some S' ∧
        (∀ Γ : PrimeDivisor Y, f Γ.genericPoint ∈ B.supp → f Γ.genericPoint ∉ S.support →
          Disjoint (S'.support : Set Y) Γ.support) ∧
        Stacks.Divisors.IsEffectiveCartierDivisor (J.comap f) := by
  classical
  haveI hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := {}
  have hS1 := toQDivisor_single_one S
  set Δ : QDivisor X := Finsupp.single S 1 + B with hΔ
  set IB : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal B.supp with hIB
  set ISg : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (singularLocus sX) with hISg
  set I : X.IdealSheafData := J * (S.idealSheaf ⊔ IB) * ISg with hIdef
  have hSB : S.genericPoint ∉ (B.supp : Set X) := by
    intro h
    obtain ⟨P, hP, hSP⟩ := DivisorWithCoeffs.mem_supp_iff.1 h
    rw [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hSP] at hP
    exact hP hB
  have hmemI : ∀ x, x ∈ (I.support : Set X) ↔ (x ∈ (J.support : Set X) ∨
      (x ∈ (S.support : Set X) ∧ x ∈ (B.supp : Set X))) ∨ x ∈ (singularLocus sX : Set X) := by
    intro x
    simp only [hIdef, Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_sup, hIB,
      hISg, Closeds.coe_sup, Closeds.coe_inf, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Set.mem_union, Set.mem_inter_iff]
  have hI2 : ∀ x ∈ I.support, 2 ≤ Order.coheight x := by
    intro x hx
    rcases (hmemI x).1 hx with (hxJ | ⟨hxS, hxB⟩) | hxs
    · exact hJ x hxJ
    · exact two_le_coheight_of_specializes S (genericPoint_specializes_of_mem_support S hxS)
        fun h => hSB (h ▸ hxB)
    · exact two_le_coheight_of_mem_singularLocus hX hxs
  have hsing : (singularLocus sX : Set X) ⊆ I.support := fun x hx => (hmemI x).2 (Or.inr hx)
  obtain ⟨X0, p0, hres, hL, hEx0⟩ := exists_resolution_principalizing hX I hI2 hsing
  -- the smooth model `X₀`
  have hX0v : AlgebraicGeometry.IsVariety k (p0 ≫ sX) := hres.isVariety_source
  haveI := hX0v
  haveI : IsIntegral X0 := hX0v.toIsIntegral
  haveI : LocallyOfFiniteType (p0 ≫ sX) := hX0v.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X0 := LocallyOfFiniteType.isLocallyNoetherian (p0 ≫ sX)
  haveI : QuasiCompact (p0 ≫ sX) := hX0v.toQuasiCompact
  haveI : CompactSpace X0 := QuasiCompact.compactSpace_of_compactSpace (p0 ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian X0 := {}
  have hX0n : IsNormal X0 :=
    isNormal_of_isRegular X0
      (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hres.isSmoothScheme)
  haveI := hX0n
  have hX0 : IsNormalVariety k (p0 ≫ sX) := ⟨hX0v, hX0n⟩
  haveI : IsProper p0 := hres.isProjective.isProper
  have hp0b := hres.isBirationalMorphism
  haveI : IsDominant p0 := hp0b.isDominant
  -- the prime divisors of `X₀` over `V(I) ∪ Supp Δ`
  set C : Set X0 := p0 ⁻¹' ((I.support : Set X) ∪ (Δ.supp : Set X)) with hC
  have hCc : IsClosed C := (I.support.isClosed.union Δ.supp.isClosed).preimage p0.continuous
  have hηX : genericPoint X ∉ (I.support : Set X) ∪ (Δ.supp : Set X) := by
    rintro (h | h)
    · have := hI2 _ h
      rw [coheight_genericPoint] at this
      exact absurd this (by norm_num)
    · obtain ⟨P, -, hP⟩ := DivisorWithCoeffs.mem_supp_iff.1 h
      exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support P hP
  have hCcoh : ∀ s ∈ C, Order.coheight s ≠ 0 := by
    intro s hs h0
    rw [eq_genericPoint_of_coheight_eq_zero h0] at hs
    exact hηX (by rw [← map_genericPoint_of_isDominant p0]; exact hs)
  have hfinD := finite_setOf_genericPoint_mem hCc hCcoh
  set D0 := hfinD.toFinset with hD0
  have hmemD0 : ∀ P : PrimeDivisor X0, P ∈ D0 ↔ P.genericPoint ∈ C := fun P => by
    rw [hD0, Set.Finite.mem_toFinset]; rfl
  have hcov : ∀ x ∈ C, ∃ P ∈ D0, x ∈ P.support := by
    intro x hx
    by_cases hxI : p0 x ∈ (I.support : Set X)
    · have hxL : x ∈ (I.comap p0).support := by
        change x ∈ ((I.comap p0).support : Set X0)
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
        exact hxI
      have hLC : ∀ s ∈ (I.comap p0).support, s ∈ C := fun s hs => by
        have : s ∈ ((I.comap p0).support : Set X0) := hs
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at this
        exact Or.inl this
      obtain ⟨P, hP, hxP⟩ := exists_primeDivisor_genericPoint_mem_of_isEffectiveCartierDivisor
        _ hL (fun s hs => hCcoh s (hLC s hs)) hxL
      exact ⟨P, (hmemD0 P).2 (hLC _ hP), hxP⟩
    · have hxD : p0 x ∈ (Δ.supp : Set X) := hx.resolve_left hxI
      obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.1 hxD
      have hxV : p0 x ∈ biregularLocus p0 := by
        by_contra h
        have : x ∈ (exceptionalSet p0 : Set X0) := h
        rw [hEx0] at this
        exact hxI this
      obtain ⟨Q', hQ', hxQ'⟩ := exists_primeDivisor_map_genericPoint_eq_of_mem_support hxV hxQ
      refine ⟨Q', ?_, hxQ'⟩
      rw [hmemD0, hC, Set.mem_preimage, hQ']
      exact Or.inr (DivisorWithCoeffs.mem_supp_iff.2
        ⟨Q, hQ, MMP.Flips.primeDivisor_genericPoint_mem_support Q⟩)
  have hsuppD0 : ∀ P ∈ D0, (P.support : Set X0) ⊆ C := by
    intro P hP x hx
    rw [hmemD0] at hP
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    exact closure_minimal (Set.singleton_subset_iff.2 hP) hCc hx
  -- the snc-preserving log resolution of `(X₀, D₀)`
  obtain ⟨Y, f1, hres1, hpure1, hsnc1, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset (p0 ≫ sX) hX0 D0
  set f := f1 ≫ p0 with hfdef
  have hYv : AlgebraicGeometry.IsVariety k (f ≫ sX) := by
    rw [hfdef, Category.assoc]; exact hres1.isVariety_source
  haveI := hYv
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hYv.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  haveI : IsProper f1 := hres1.isProjective.isProper
  have hf1b := hres1.isBirationalMorphism
  haveI : IsDominant f1 := hf1b.isDominant
  have hfb : IsBirationalMorphism f := IsPair.isBirationalMorphism_comp hf1b hp0b
  haveI : IsProper f := by rw [hfdef]; infer_instance
  haveI : IsDominant f := hfb.isDominant
  have hsmY : IsSmoothScheme (f ≫ sX) := by
    rw [hfdef, Category.assoc]; exact hres1.isSmoothScheme
  have hYn : IsNormal Y :=
    isNormal_of_isRegular Y (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsmY)
  have hY : IsNormalVariety k (f ≫ sX) := ⟨hYv, hYn⟩
  -- `I 𝒪_Y` and the exceptional set of `f`
  have hgenI : genericPoint Y ∉ (I.comap f).support := by
    intro h
    have h' : genericPoint Y ∈ ((I.comap f).support : Set Y) := h
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      map_genericPoint_of_isDominant] at h'
    exact hηX (Or.inl h')
  have hLf : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) := by
    rw [hfdef, Scheme.IdealSheafData.comap_comp]
    refine isEffectiveCartierDivisor_comap_of_genericPoint_notMem _ hL f1 ?_
    intro h
    have h' : f1 (genericPoint Y) ∈ ((I.comap p0).support : Set X0) := h
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      map_genericPoint_of_isDominant, map_genericPoint_of_isDominant] at h'
    exact hηX (Or.inl h')
  have hExf : (exceptionalSet f : Set Y) =
      (exceptionalSet f1 : Set Y) ∪ f1 ⁻¹' (exceptionalSet p0 : Set X0) := by
    rw [hfdef, exceptionalSet_comp]
    rfl
  have hExfC : exceptionalSet f = exceptionalSet f1 ⊔ (I.comap f).support := by
    apply SetLike.coe_injective
    rw [hExf, Closeds.coe_sup, hEx0, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
    rfl
  have hpure : IsPureCodimOne (exceptionalSet f) := by
    rw [hExfC]
    exact isPureCodimOne_sup hpure1 (isPureCodimOne_support_of_principal _
      (stalk_principal_of_isEffectiveCartierDivisor _ hLf) hgenI)
  -- simple normal crossings
  have hSig : ((exceptionalSet f ⊔ (QDivisor.toRDivisor (Divisor.toQDivisor
      (Finsupp.single S 1) + B)).supp.preimage f.continuous : Closeds Y) : Set Y) =
      (exceptionalSet f1 : Set Y) ∪ f1 ⁻¹' D0.sup fun E => (E.idealSheaf.support : Set X0) := by
    rw [Closeds.coe_sup, Closeds.coe_preimage, QDivisor.supp_toRDivisor, hS1, hExf, hEx0,
      Finset.sup_set_eq_biUnion]
    ext y
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · obtain ⟨P, hP, hyP⟩ := hcov (f1 y) (Or.inl h)
        exact Or.inr ⟨P, hP, hyP⟩
      · obtain ⟨P, hP, hyP⟩ := hcov (f1 y) (Or.inr h)
        exact Or.inr ⟨P, hP, hyP⟩
    · rintro (h | ⟨P, hP, hyP⟩)
      · exact Or.inl (Or.inl h)
      · exact (hsuppD0 P hP hyP).imp_left Or.inr
  have hlog : IsLogResolution sX
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single S 1) + B)) f := by
    refine ⟨⟨inferInstance, hfb, hsmY⟩, hpure, isSNCSubset_of_isSNCClosedSubset (f ≫ sX) ?_⟩
    rwa [hSig, hfdef, Category.assoc]
  -- the strict transform of `S`
  have hbir := two_le_closedsCodimension_compl_biregularLocus sX f (hY := hX.1) (hX := hYv) hfb
  have hηS : S.genericPoint ∈ biregularLocus f := by
    by_contra h
    have h2 := (MMP.Flips.le_closedsCodimension_iff_le_coheight.1 hbir) _ h
    rw [S.coheight_genericPoint] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨S', hS', hfS'⟩ :=
    MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := f) S hηS
  -- `J 𝒪_Y` and `(I_S + I_B) 𝒪_Y` are effective Cartier divisors
  have hprod := hLf
  rw [hIdef, AlgebraicGeometry.comap_mul, AlgebraicGeometry.comap_mul] at hprod
  have hprod' := AlgebraicGeometry.isEffectiveCartierDivisor_left_of_mul _ _ hprod
  have hJf := AlgebraicGeometry.isEffectiveCartierDivisor_left_of_mul _ _ hprod'
  have hMf := AlgebraicGeometry.isEffectiveCartierDivisor_right_of_mul _ _ hprod'
  refine ⟨Y, f, hlog, hY, S', hS', fun Γ hΓB hΓS => ?_, hJf⟩
  exact disjoint_support_of_isEffectiveCartierDivisor_comap_sup f hMf hfS' hSB hΓB hΓS

/-! ### The main theorem -/

/-- **Divisors over `S` are realised over `X`** (Kollár–Mori, proof of 5.46). -/
theorem solution.{v} {k : Type v} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{v}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : PrimeDivisor X) (hS : IsNormalVariety k (S.idealSheaf.subschemeι ≫ sX))
    (hSC : ∀ x ∈ S.support, Order.coheight x = 2 →
      MMP.Flips.IsCartierAt (Finsupp.single S 1) x)
    {B : QDivisor X} (hB : B.coeff S = 0)
    (hKSB : (Divisor.toQDivisor K + Finsupp.single S 1 + B).IsQCartier) :
    haveI := hS.1.toIsIntegral
    haveI := hS.2
    haveI := hS.1.toLocallyOfFiniteType
    haveI := LocallyOfFiniteType.isLocallyNoetherian (S.idealSheaf.subschemeι ≫ sX)
    ∀ {KS : Divisor S.idealSheaf.subscheme},
      KS.IsCanonicalDivisor (S.idealSheaf.subschemeι ≫ sX) n →
      ∀ F : DivisorOver k (S.idealSheaf.subschemeι ≫ sX), F.IsExceptionalOrPrimeDivisor →
      ∃ G : DivisorOver k sX, G.IsExceptional ∧
        (G.center : Set X) = S.idealSheaf.subschemeι '' (F.center : Set S.idealSheaf.subscheme) ∧
        ∀ a : ℚ, IsDiscrepancy sX (n + 1) K (Finsupp.single S 1 + B) G a ↔
          IsDiscrepancy (S.idealSheaf.subschemeι ≫ sX) n KS (B.restrictPrimeDivisor S) F a := by
  intro KS hKS F hF
  classical
  haveI : IsIntegral S.idealSheaf.subscheme := hS.1.toIsIntegral
  haveI : IsNormal S.idealSheaf.subscheme := hS.2
  haveI : LocallyOfFiniteType (S.idealSheaf.subschemeι ≫ sX) := hS.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian S.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (S.idealSheaf.subschemeι ≫ sX)
  haveI : QuasiCompact (S.idealSheaf.subschemeι ≫ sX) := hS.1.toQuasiCompact
  haveI : CompactSpace S.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (S.idealSheaf.subschemeι ≫ sX)
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hS1 := toQDivisor_single_one S
  -- the center of `F` is not the generic point of `S`
  have hFη : F.f F.E.genericPoint ≠ genericPoint S.idealSheaf.subscheme := by
    intro h
    have h0 : Order.coheight (F.f F.E.genericPoint) = 0 := by
      rw [h]; exact coheight_genericPoint _
    rcases hF with hE | ⟨hT, P, rfl⟩
    · have := (isExceptional_iff_two_le_coheight hS F).mp hE
      rw [h0] at this
      exact absurd this (by norm_num)
    · change Order.coheight P.genericPoint = 0 at h0
      rw [P.coheight_genericPoint] at h0
      exact absurd h0 (by norm_num)
  obtain ⟨J, hJ, hreal⟩ := exists_idealSheaf_realising S.idealSheaf.subschemeι hS S
    (Scheme.IdealSheafData.range_subschemeι _) hKS F hFη
  obtain ⟨Y, f, hf, hY, S', hS', hdisjP, hJY⟩ :=
    exists_isLogResolution_disjoint_isEffectiveCartierDivisor hX S hB J hJ
  have hdisj : Disjoint (S'.support : Set Y) ((inverseTransformDivisor f B).supp : Set Y) := by
    rw [DivisorWithCoeffs.coe_supp, Set.disjoint_iUnion₂_right]
    intro Γ hΓ
    obtain ⟨P, hP, hPΓ⟩ := exists_of_mem_support_mapPrimeDivisors hΓ
    have h1 := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hPΓ).1
    refine hdisjP Γ ?_ ?_
    · rw [h1, DivisorWithCoeffs.mem_supp_iff]
      exact ⟨P, Finsupp.mem_support_iff.1 hP, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    · rw [h1]
      intro hm
      have := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hm
      subst this
      exact Finsupp.mem_support_iff.1 hP hB
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  set T' := S'.idealSheaf.subscheme with hT'def
  set ι' := S'.idealSheaf.subschemeι with hι'def
  haveI : IsIntegral T' := S'.integral
  obtain ⟨Ex, hEx⟩ := exists_finset_isExceptional hf hY
  have hPX : IsPair sX (Divisor.toQDivisor (Finsupp.single S 1) + B) :=
    ⟨hX, n + 1, K, hK, by rwa [hS1, ← add_assoc]⟩
  choose e he using fun E : PrimeDivisor Y =>
    MMP.Positivity.IsPair.exists_isDiscrepancy hPX hK ⟨Y, f, hY, hf.isBirationalMorphism, E⟩
  have hdim : topologicalKrullDim X = (n : WithBot ℕ∞) + 1 := by
    rw [hK.topologicalKrullDim_eq]; rfl
  have hrange : Set.range S.idealSheaf.subschemeι = (S.support : Set X) :=
    Scheme.IdealSheafData.range_subschemeι _
  have hrange' : Set.range ι' = (S'.support : Set Y) :=
    Scheme.IdealSheafData.range_subschemeι _
  obtain ⟨⟨fS, hfS⟩, H⟩ := isCrepantBoundary_restrict_of_isLogResolution sX hX hdim
    S.idealSheaf.subschemeι S hrange
    (fun x h2 hx => hSC x hx h2) B hB K hK (by rwa [hS1]) f hf hY S' hS' hdisj ι'
    hrange' Ex hEx e (fun E _ => he E)
  obtain ⟨hprop, hsmT', hT', hfSb, hcrep⟩ := H fS hfS
  have hJT' :
      Stacks.Divisors.IsEffectiveCartierDivisor (J.comap (fS ≫ S.idealSheaf.subschemeι)) := by
    rw [hfS, Scheme.IdealSheafData.comap_comp]
    haveI : IsLocallyNoetherian T' := LocallyOfFiniteType.isLocallyNoetherian ι'
    refine isEffectiveCartierDivisor_comap_of_genericPoint_notMem _ hJY ι' ?_
    intro hmem
    have hmem' : S'.genericPoint ∈ ((J.comap f).support : Set Y) := hmem
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hS').1] at hmem'
    have := hJ _ hmem'
    rw [S.coheight_genericPoint] at this
    exact absurd this (by norm_num)
  obtain ⟨F', hF'⟩ := hreal T' fS hT' hfSb hprop hJT'
  set Θ : QDivisor T' := -∑ E ∈ Ex, e E • DivisorWithCoeffs.restrict ι'
    (Finsupp.single E (1 : ℚ)) with hΘ
  have hd'' := hcrep KS hKS F'
  set y : Y := ι' F'.genericPoint with hy
  have hyS : y ∈ (S'.support : Set Y) := hrange' ▸ ⟨_, rfl⟩
  have hsmY : IsSmoothScheme (f ≫ sX) := hf.isSmoothScheme
  have hdimY : topologicalKrullDim Y = (n : WithBot ℕ∞) + 1 := by
    haveI := hX.1
    haveI := hY.1
    rw [← hdim]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      hf.isBirationalMorphism).symm
  have hy2 : Order.coheight y = 2 := coheight_subschemeι_genericPoint (f ≫ sX) hdimY S' F'
  obtain ⟨G, hGex, hGc, hGd⟩ := exists_divisorOver_isDiscrepancy hX hK S hB hKSB f hf hY S' hS'
    hdisjP Ex hEx e (fun E _ => he E) y hyS hy2
  have ha0 : -Θ.coeff F' = ∑ E ∈ Ex, if y ∈ E.support then e E else 0 := by
    rw [hΘ, DivisorWithCoeffs.coeff_neg, neg_neg, ← DivisorWithCoeffs.coeffAddMonoidHom_apply,
      map_sum]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [DivisorWithCoeffs.coeffAddMonoidHom_apply, DivisorWithCoeffs.coeff_smul,
      coeff_restrict_single_eq hX S hf hY S' hS' hB E ((hEx E).1 hE) F']
    split_ifs <;> simp
  rw [ha0] at hd''
  set a0 : ℚ := ∑ E ∈ Ex, if y ∈ E.support then e E else 0 with ha0def
  -- the discrepancy of `F` is `a0`
  have hPW : IsPairWith (S.idealSheaf.subschemeι ≫ sX) n KS (B.restrictPrimeDivisor S) := by
    obtain ⟨hT, -, m, hm, hmC, -⟩ := hd''
    exact ⟨hT, hKS, ⟨m, by exact_mod_cast hm.ne', hmC⟩⟩
  have hFa : ∀ a : ℚ,
      IsDiscrepancy (S.idealSheaf.subschemeι ≫ sX) n KS (B.restrictPrimeDivisor S) F a ↔
        a = a0 := by
    refine fun a => ⟨fun ha =>
      (MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPW hF' hd'' ha).symm, ?_⟩
    rintro rfl
    obtain ⟨a1, ha1⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hKS F
    have := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPW hF' hd'' ha1
    rwa [← this] at ha1
  refine ⟨G, hGex, ?_, fun a => ?_⟩
  · -- centers
    have hx0 := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hS.1 hF'
    have hfy : f y = S.idealSheaf.subschemeι (fS F'.genericPoint) := by
      rw [hy, ← Scheme.Hom.comp_apply, ← hfS, Scheme.Hom.comp_apply]
    rw [hGc, F.center_eq_closure_genericPoint, ← hx0, hfy, ← Set.image_singleton,
      S.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq]
  · rw [hFa]
    exact ⟨fun ha => (hGd.eq ha).symm, fun ha => ha ▸ hGd⟩

end MMP.FourfoldProofs.Km5bDiscrepancyOverSRealisedOnXProof

end

section

/-!
# Divisors over a divisor `S ⊆ X` are realised by exceptional divisors over `X`

Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero,
`S ⊆ X` a normal prime divisor which is Cartier at every codimension-two point of `X` lying on
`S`, and `B` a `ℚ`-divisor on `X` of which `S` is not a component, such that `K_X + S + B` is
`ℚ`-Cartier. Then every divisor `F` over `S` which is exceptional over `S` or a prime divisor of
`S` is realised over `X`: there is an exceptional divisor `G` over `X` whose center on `X` is
the center of `F` on `S`, and `a(G, X, S + B) = a(F, S, B|_S)`.

This is the step of the proof of Kollár–Mori 5.46 which compares discrepancies over `S` with
discrepancies over `X`.

## Main results

* `MMP.Mori.exists_isExceptional_isDiscrepancy_iff_restrictPrimeDivisor`: the realisation of a
  divisor over `S` by an exceptional divisor over `X`.

## Implementation notes

The scheme `S` is the closed subscheme `S.idealSheaf.subscheme` cut out by the prime divisor,
a variety over `k` through `S.idealSheaf.subschemeι ≫ s_X`, and `B|_S` is
`MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor`. "Cartier in codimension two" is read as
`MMP.Flips.IsCartierAt S x` at every point `x ∈ S` of coheight two in `X`. The dimensions are
`n + 1` for `X` and `n` for `S`, with canonical divisors `K` and `K_S`.

The discrepancy is a predicate `MMP.Mori.IsDiscrepancy` on a rational number, so the equality
`a(G, X, S + B) = a(F, S, B|_S)` is stated as: a rational `a` is the discrepancy of `G` over
`(X, S + B)` exactly when it is the discrepancy of `F` over `(S, B|_S)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.46, 5.47
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **Divisors over `S` are realised over `X`** (Kollár–Mori, proof of 5.46). Let `X` be a normal
variety with canonical divisor `K` of dimension `n + 1`, `S` a normal prime divisor of `X`, with
canonical divisor `K_S` of dimension `n`, which is Cartier at every point of `S` of codimension
two in `X`, and `B` a `ℚ`-divisor without component `S` such that `K + S + B` is `ℚ`-Cartier.
For every divisor `F` over `S` which is exceptional over `S` or a prime divisor of `S` there is an
exceptional divisor `G` over `X` with `center_X G = center_S F` and
`a(G, X, S + B) = a(F, S, B|_S)`. -/
@[mmp "lem_km5b_discrepancy_over_s_realised_on_x"]
public theorem exists_isExceptional_isDiscrepancy_iff_restrictPrimeDivisor
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : PrimeDivisor X) (hS : IsNormalVariety k (S.idealSheaf.subschemeι ≫ sX))
    (hSC : ∀ x ∈ S.support, Order.coheight x = 2 →
      MMP.Flips.IsCartierAt (Finsupp.single S 1) x)
    {B : QDivisor X} (hB : B.coeff S = 0)
    (hKSB : (Divisor.toQDivisor K + Finsupp.single S 1 + B).IsQCartier) :
    haveI := hS.1.toIsIntegral
    haveI := hS.2
    haveI := hS.1.toLocallyOfFiniteType
    haveI := LocallyOfFiniteType.isLocallyNoetherian (S.idealSheaf.subschemeι ≫ sX)
    ∀ {KS : Divisor S.idealSheaf.subscheme},
      KS.IsCanonicalDivisor (S.idealSheaf.subschemeι ≫ sX) n →
      ∀ F : DivisorOver k (S.idealSheaf.subschemeι ≫ sX), F.IsExceptionalOrPrimeDivisor →
      ∃ G : DivisorOver k sX, G.IsExceptional ∧
        (G.center : Set X) = S.idealSheaf.subschemeι '' (F.center : Set S.idealSheaf.subscheme) ∧
        ∀ a : ℚ, IsDiscrepancy sX (n + 1) K (Finsupp.single S 1 + B) G a ↔
          IsDiscrepancy (S.idealSheaf.subschemeι ≫ sX) n KS (B.restrictPrimeDivisor S) F a :=
  MMP.FourfoldProofs.Km5bDiscrepancyOverSRealisedOnXProof.solution hX hK S hS hSC hB hKSB

end MMP.Mori

end
