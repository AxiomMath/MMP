module
public import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ResidueFunctionIntegral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZeroSplitting

/-!
# The ample model of a birational contraction is birational over the base

Let `(X, B)` be a projective lc fourfold pair over `ℂ` with rational boundary, `D = K_X + B`,
`f : X ⟶ Z` a birational contraction onto a normal projective variety with `-D` `f`-ample, and
`(M, B_M, q, V, B_V)` an ample-model datum for `f`, with `π_M : M ⟶ Z` and `p : V ⟶ Z`. Then
`p` is projective and birational.

Write `V ≅ Proj_Z 𝒜` over `Z` for `𝒜 = ⨁_n π_* 𝒪_M(nD)`, `D = k(K_M + B_M)`, with `q` the
morphism induced by `𝒜`. Over an affine open `U ⊆ Z` the graded ring `𝒜(U)` embeds in
`𝒦_M(π⁻¹U)[T]`, so `Proj_Z 𝒜` and `V` are reduced. A nonzero homogeneous section
`a ∈ 𝒜_n(U)` generates `𝒪_M(nD)` off the support of `div(a) + nD`, so its generating locus
`M_a` is nonempty, the ring map `𝒜(U)_(a) → 𝒪_M(M_a)` describing `q` on `M_a` is injective,
and `q` is dominant. Since `f` and the birational map `φ : X ⤏ M` over `Z` are birational,
`π_M` restricts to an open immersion on a nonempty open `W ⊆ M`. The inverse of `π_M|_W`
composed with `q` is a section of `p` over the image `O ⊆ Z`; since `V` is reduced, `p` is
separated and `q(W)` is dense, this section is inverse to `p⁻¹(O) ⟶ O`. Hence `p` is
birational. That `p` is projective is the projectivity of the relative `Proj` of the section
algebra of the relatively free Cartier divisor `D` along the projective `π_M`: its pieces are
coherent (Stacks 02O5), it is of finite type over the base (the section ring is integral over
finitely many degree-one generators, by the valuative criterion, and `𝒪_Z(U)` is Nagata), and
a twisting sheaf `𝒪(d)` is relatively ample (Stacks 0B45).

## Main results

* `MMP.Fourfold.IsAmpleModelDatum.isProjectiveMorphism_and_isBirationalMorphism`: the structure
  morphism `V ⟶ Z` of an ample-model datum is projective and birational.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.Fourfold

open MMP.Mori

universe u

/-! ### The relative `Proj` of a divisorial section algebra

The graded ring `⨁_n 𝒜_n(U)` embeds in `𝒦_M(π⁻¹U)[T]` by `a ↦ a Tⁿ`, so it is reduced and so is
its relative `Proj`. A nonzero homogeneous section `a` generates `𝒪_M(nD)` off the support of
`div(a) + nD`, so its generating locus is nonempty; the ring map `𝒜(U)_(a) → 𝒪_M(M_a)` of the
induced morphism is then injective, and the induced morphism is dominant. -/

section SectionAlgebra

variable {M Z : Scheme.{u}} [IsLocallyNoetherian M] [IsNormal M] {π : M ⟶ Z} {D : Divisor M}
  (A : DivisorialSectionAlgebra π D)

private theorem sectionEquiv_heq {i j : ℤ} (h : i = j) (hi : 0 ≤ i) (hj : 0 ≤ j) (U : Z.Opens)
    (a : (A.algebra.piece i).val.obj (op U)) (b : (A.algebra.piece j).val.obj (op U))
    (hab : HEq a b) :
    (A.sectionEquiv i hi U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) =
      (A.sectionEquiv j hj U b : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) := by
  subst h
  cases hab
  rfl

/-- The degree-`n` piece of the section ring, embedded as monomials in `𝒦[T]`. -/
private noncomputable def pieceHom (U : Z.Opens) (n : ℕ) :
    A.situation.sectionPieces U n →+
      Polynomial ((rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) :=
  (Polynomial.monomial n).toAddMonoidHom.comp
    ((((n : ℤ) • D).divisorialSubmodule (π ⁻¹ᵁ U)).subtype.toAddMonoidHom.comp
      (A.sectionEquiv n (Int.natCast_nonneg n) U).toAddMonoidHom)

private theorem pieceHom_apply (U : Z.Opens) (n : ℕ) (a : A.situation.sectionPieces U n) :
    pieceHom A U n a = Polynomial.monomial n
      (A.sectionEquiv n (Int.natCast_nonneg n) U a :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) := rfl

private noncomputable def toPoly (U : Z.Opens) :
    A.situation.sectionRing U →+*
      Polynomial ((rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) :=
  DirectSum.toSemiring (pieceHom A U) (by
      rw [pieceHom_apply]
      change Polynomial.monomial 0 ((A.sectionEquiv 0 le_rfl U
        (GradedMonoid.GOne.one : A.situation.sectionPieces U 0) :
          (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))) = 1
      rw [A.situation.sectionRingStructure.one_homogeneous U, A.sectionEquiv_one]
      simp)
    (fun {i j} a b => by
      rw [pieceHom_apply, pieceHom_apply, pieceHom_apply, Polynomial.monomial_mul_monomial]
      congr 1
      rw [← A.sectionEquiv_mul i j (Int.natCast_nonneg i) (Int.natCast_nonneg j) U a b]
      exact sectionEquiv_heq A (by push_cast; rfl) _ _ U _ _
        (A.situation.sectionRingStructure.mul_homogeneous U i j a b))

private theorem coeff_toPoly (U : Z.Opens) (n : ℕ) (x : A.situation.sectionRing U) :
    (toPoly A U x).coeff n = (A.sectionEquiv n (Int.natCast_nonneg n) U (x n) :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) := by
  have : (Polynomial.lcoeff _ n).toAddMonoidHom.comp (toPoly A U).toAddMonoidHom =
      ((((n : ℤ) • D).divisorialSubmodule (π ⁻¹ᵁ U)).subtype.toAddMonoidHom.comp
        (A.sectionEquiv n (Int.natCast_nonneg n) U).toAddMonoidHom).comp
        (DirectSum.component ℤ ℕ (A.situation.sectionPieces U) n).toAddMonoidHom := by
    refine DirectSum.addHom_ext fun i a => ?_
    simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
      LinearMap.toAddMonoidHom_coe, Polynomial.lcoeff_apply, toPoly,
      DirectSum.toSemiring_of, pieceHom_apply, Polynomial.coeff_monomial]
    by_cases h : i = n
    · subst h
      simp only [ite_true]
      erw [DirectSum.component.of]
      simp
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      erw [DirectSum.component.of, dite_eq_right_of_eq_false (eq_false h)]
      simp
  exact congrArg (fun F => F x) this

private theorem injective_toPoly (U : Z.Opens) : Function.Injective (toPoly A U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  ext n
  have := coeff_toPoly A U n x
  rw [hx, Polynomial.coeff_zero] at this
  simpa using (Subtype.ext this.symm : A.sectionEquiv n (Int.natCast_nonneg n) U (x n) = 0)

private theorem isReduced_sectionRing (U : Z.Opens) :
    _root_.IsReduced (A.situation.sectionRing U) := by
  have : _root_.IsReduced ((rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) :=
    (inferInstance : _root_.IsReduced (∀ Y : {Y : irreducibleComponents M //
      componentGenericPoint M Y ∈ π ⁻¹ᵁ U}, M.presheaf.stalk (componentGenericPoint M Y.1)))
  have : _root_.IsReduced (Polynomial ((rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))) :=
    ⟨fun p hp => Polynomial.ext fun i => by
      simpa using (Polynomial.isNilpotent_iff.mp hp i).eq_zero⟩
  exact isReduced_of_injective (toPoly A U) (injective_toPoly A U)

/-- `Proj` of a reduced graded ring is reduced. -/
private theorem isReduced_proj {σ R : Type*} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [_root_.IsReduced R] : IsReduced (Proj 𝒜) := by
  suffices h : ∀ x : AlgebraicGeometry.Proj 𝒜,
      _root_.IsReduced ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) from
    @isReduced_of_isReduced_stalk _ h
  intro x
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have : _root_.IsReduced (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
    isReduced_of_injective
      (algebraMap (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)
        (Localization.AtPrime x.asHomogeneousIdeal.toIdeal))
      (HomogeneousLocalization.val_injective _)
  exact isReduced_of_injective (Proj.stalkIso' 𝒜 x) (Proj.stalkIso' 𝒜 x).injective

private theorem isReduced_model : IsReduced A.model := by
  suffices h : ∀ x : A.model, _root_.IsReduced (A.model.presheaf.stalk x) from
    @isReduced_of_isReduced_stalk _ h
  intro x
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (show A.toBase x ∈ (⊤ : Z.Opens) from trivial)
  have hx : x ∈ (A.situation.relativeProjChart ⟨W, hW⟩).opensRange :=
    (Stacks.RelativeProj.Situation.mem_opensRange_relativeProjChart _ _ x).mpr hxW
  obtain ⟨y, rfl⟩ := hx
  have : _root_.IsReduced (A.situation.sectionRing W) := isReduced_sectionRing A W
  have : IsReduced (AlgebraicGeometry.Proj (A.situation.sectionRingGrading W)) := isReduced_proj _
  have : IsIso ((A.situation.relativeProjChart ⟨W, hW⟩).stalkMap y) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp
      (Stacks.RelativeProj.Situation.isOpenImmersion_relativeProjChart _ _)).2 y
  exact isReduced_of_injective _
    (ConcreteCategory.bijective_of_isIso
      ((A.situation.relativeProjChart ⟨W, hW⟩).stalkMap y)).1

omit [IsLocallyNoetherian M] [IsNormal M] in
private theorem rationalFunctions_map_injective [IrreducibleSpace M] {U V : M.Opens} (h : V ≤ U)
    (hV : (V : Set M).Nonempty) :
    Function.Injective ((rationalFunctionsPresheaf M).map (homOfLE h).op) := by
  intro s s' hss
  funext Y
  have hY : componentGenericPoint M Y.1 ∈ V := by
    rw [genericPoint_mem_iff]
    have : Y.1.1 = Set.univ := (irreducibleComponents_eq_singleton (X := M)).le Y.1.2
    rwa [this, Set.inter_univ]
  exact congrFun hss ⟨Y.1, hY⟩

private theorem injective_of_factors [IrreducibleSpace M] (U : Z.affineOpens) (n : ℕ)
    (a : (A.algebra.piece (n : ℤ)).val.obj (op U.1))
    (hne : ((A.generatingLocus (Int.natCast_nonneg n) a : M.Opens) : Set M).Nonempty)
    (ψ : HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1)
        (DirectSum.of (A.situation.sectionPieces U.1) n a) →+*
        Γ(M, A.generatingLocus (Int.natCast_nonneg n) a))
    (heq : ∀ (m : ℕ) (t : (A.algebra.piece ((m • n : ℕ) : ℤ)).val.obj (op U.1)),
          (toRationalFunctionsPresheaf M).app (op (A.generatingLocus (Int.natCast_nonneg n) a))
              (ψ (HomogeneousLocalization.Away.mk (A.situation.sectionRingGrading U.1) ⟨a, rfl⟩ m
                (DirectSum.of (A.situation.sectionPieces U.1) (m • n) t) ⟨t, rfl⟩)) *
              (rationalFunctionsPresheaf M).map
                (homOfLE (A.generatingLocus_le _ a)).op
                (A.sectionEquiv n (Int.natCast_nonneg n) U.1 a :
                  (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U.1))) ^ m =
            (rationalFunctionsPresheaf M).map (homOfLE (A.generatingLocus_le _ a)).op
              (A.sectionEquiv _ (Int.natCast_nonneg _) U.1 t :
                (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U.1)))) :
    Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (A.situation.sectionRingGrading U.1)
    (show DirectSum.of (A.situation.sectionPieces U.1) n a ∈ A.situation.sectionRingGrading U.1 n
      from ⟨a, rfl⟩) x
  obtain ⟨t, rfl⟩ := hy
  have h := heq m t
  rw [hx, map_zero, zero_mul] at h
  have h0 := rationalFunctions_map_injective (A.generatingLocus_le _ a) hne
    (h.symm.trans (map_zero _).symm)
  have ht : t = 0 := by
    simpa using (Subtype.ext h0 : A.sectionEquiv _ (Int.natCast_nonneg _) U.1 t = 0)
  subst ht
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk, Localization.mk_zero]

omit [IsLocallyNoetherian M] [IsNormal M] in
private theorem coeff_eq_zero_of_nonempty_inter {E0 : Divisor M} {E : MMP.Mori.PrimeDivisor M}
    {s : Set M} (hs : s ⊆ (E0.supp : Set M)ᶜ) (hE : (E.support ∩ s).Nonempty) :
    E0.coeff E = 0 := by
  by_contra hne
  obtain ⟨x, hxE, hxs⟩ := hE
  exact hs hxs (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hxE⟩)

private theorem generatingLocus_nonempty [IsIntegral M] [CompactSpace M] {i : ℤ} (hi : 0 ≤ i)
    {U : Z.Opens}
    (a : (A.algebra.piece i).val.obj (op U)) (ha : a ≠ 0) :
    ((A.generatingLocus hi a : M.Opens) : Set M).Nonempty := by
  classical
  set φ : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)) := (A.sectionEquiv i hi U a :
    (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
  have hφ : φ ≠ 0 := fun h => ha (by simpa using (Subtype.ext h : A.sectionEquiv i hi U a = 0))
  have hall : ∀ Y Y' : irreducibleComponents M, Y = Y' := fun Y Y' =>
    Subtype.ext (((irreducibleComponents_eq_singleton (X := M)).le Y.2).trans
      ((irreducibleComponents_eq_singleton (X := M)).le Y'.2).symm)
  obtain ⟨⟨Y0, hY0⟩⟩ : Nonempty {Y : irreducibleComponents M //
      componentGenericPoint M Y ∈ π ⁻¹ᵁ U} := by
    by_contra h
    exact hφ (funext fun Y => absurd ⟨Y⟩ h)
  have hmem : ∀ Y : irreducibleComponents M, componentGenericPoint M Y ∈ π ⁻¹ᵁ U := fun Y =>
    (hall Y Y0) ▸ hY0
  let val : RationalFunctions M := fun Y => φ ⟨Y, hmem Y⟩
  have hval : IsUnit val := Pi.isUnit_iff.mpr fun Y => by
    let := (RationalFunctions.isField_stalk M Y).toField
    refine isUnit_iff_ne_zero.mpr fun h0 => hφ (funext fun Y' => ?_)
    obtain rfl : Y'.1 = Y := hall _ _
    exact h0
  let u : (RationalFunctions M)ˣ := hval.unit
  let E0 : Divisor M := MMP.Mori.principalDivisor u + i • D
  let W' : M.Opens := π ⁻¹ᵁ U ⊓ ⟨(E0.supp : Set M)ᶜ, E0.isClosed_supp.isOpen_compl⟩
  have hW' : componentGenericPoint M Y0 ∈ W' := by
    refine ⟨hY0, fun h => ?_⟩
    obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    exact MMP.Flips.componentGenericPoint_notMem_support Y0 E hE
  refine ⟨_, (le_sSup ?_ : W' ≤ A.generatingLocus hi a) hW'⟩
  refine ⟨inf_le_left, fun Y => ((u⁻¹ : (RationalFunctions M)ˣ) : RationalFunctions M) Y.1, ?_, ?_⟩
  · intro E hE
    right
    have hE0 : E0.coeff E = 0 := coeff_eq_zero_of_nonempty_inter (fun _ h => h.2) hE
    have hcoeff : E.ord u + i * D.coeff E = 0 := by
      simpa [E0, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul] using hE0
    change WithZero.exp _ ≤ E.valuation (((u⁻¹ : (RationalFunctions M)ˣ) :
      RationalFunctions M) E.component)
    rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv]
    apply le_of_eq
    congr 1
    simp only [DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_smul, neg_neg, smul_eq_mul]
    linarith
  · funext Y
    change (u : RationalFunctions M) Y.1 * _ = 1
    rw [← Pi.mul_apply, Units.mul_inv, Pi.one_apply]

private theorem mem_range_awayι {σ R : Type*} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : R} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m)
    {y : AlgebraicGeometry.Proj 𝒜} (hy : y ∈ Proj.basicOpen 𝒜 f) :
    y ∈ Set.range (Proj.awayι 𝒜 f hf hm) := by
  rwa [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]

private theorem exists_pos_decompose_notMem {σ R : Type*} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜] (y : ProjectiveSpectrum 𝒜) :
    ∃ (r : R) (i : ℕ), 0 < i ∧ (DirectSum.decompose 𝒜 r i : R) ∉ y.asHomogeneousIdeal := by
  classical
  obtain ⟨r, hr, hry⟩ := SetLike.not_le_iff_exists.mp y.not_irrelevant_le
  obtain ⟨i, hi⟩ : ∃ i, (DirectSum.decompose 𝒜 r i : R) ∉ y.asHomogeneousIdeal := not_forall.mp
    fun H => hry (DirectSum.sum_support_decompose 𝒜 r ▸ Ideal.sum_mem _ fun j _ => H j)
  exact ⟨r, i, Nat.pos_of_ne_zero fun h => hi (by
    subst h
    exact (show (DirectSum.decompose 𝒜 r 0 : R) = 0 from hr) ▸ zero_mem _), hi⟩

private theorem isDominant_of_isInducedMorphism [IsIntegral M] [CompactSpace M] {q : M ⟶ A.model}
    (hq : A.IsInducedMorphism q)
    (hne : ∀ (U : Z.affineOpens) (n : ℕ) (_ : 0 < n)
      (a : (A.algebra.piece (n : ℤ)).val.obj (op U.1)), a ≠ 0 →
        ((A.generatingLocus (Int.natCast_nonneg n) a : M.Opens) : Set M).Nonempty) :
    IsDominant q := by
  classical
  rw [isDominant_iff]
  refine dense_iff_inter_open.mpr fun O hO ⟨x, hx⟩ => ?_
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (show A.toBase x ∈ (⊤ : Z.Opens) from trivial)
  let U : Z.affineOpens := ⟨W, hW⟩
  obtain ⟨y, rfl⟩ :=
    (Stacks.RelativeProj.Situation.mem_opensRange_relativeProjChart A.situation U x).mpr hxW
  obtain ⟨r, i, hi0, hi⟩ := exists_pos_decompose_notMem _ y
  obtain ⟨a, ha⟩ := (DirectSum.decompose (A.situation.sectionRingGrading W) r i).2
  have hya : y ∈ Proj.basicOpen _ (DirectSum.of (A.situation.sectionPieces W) i a) := by
    rwa [Proj.mem_basicOpen, ha]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Proj.mem_basicOpen, map_zero] at hya
    exact hya (zero_mem _)
  obtain ⟨z, rfl⟩ : y ∈ Set.range (Proj.awayι (A.situation.sectionRingGrading U.1)
      (DirectSum.of (A.situation.sectionPieces U.1) i a) ⟨a, rfl⟩ hi0) :=
    mem_range_awayι _ _ hi0 hya
  have hL := hne U i hi0 a ha0
  set L := A.generatingLocus (Int.natCast_nonneg i) a
  obtain ⟨ψ, hfac, heq⟩ := hq.factors U i hi0 a
  have hinj := injective_of_factors A U i a hL ψ heq
  have : Nonempty L := hL.to_subtype
  have : IsDomain (HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1)
      (DirectSum.of (A.situation.sectionPieces U.1) i a)) := hinj.isDomain ψ
  have : IsDominant (Spec.map (CommRingCat.ofHom ψ)) :=
    isDominant_Spec_map_of_injective _ hinj
  have : IsNoetherian M := {}
  have : CompactSpace L :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsDominant L.toSpecΓ := by
    unfold Scheme.Opens.toSpecΓ
    infer_instance
  let c := Proj.awayι (A.situation.sectionRingGrading U.1)
      (DirectSum.of (A.situation.sectionPieces U.1) i a) ⟨a, rfl⟩ hi0 ≫
    A.situation.relativeProjChart U
  obtain ⟨_, hw, ⟨m, rfl⟩⟩ :=
    (L.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).denseRange.inter_open_nonempty _
      (hO.preimage c.continuous) ⟨z, hx⟩
  refine ⟨q (L.ι m), ?_, L.ι m, rfl⟩
  have := congrArg (fun h : L.toScheme ⟶ A.model => h m) hfac
  change (L.ι ≫ q) m ∈ O
  rwa [this]

end SectionAlgebra

/-- Precomposing an H-projective morphism with an isomorphism keeps it H-projective. -/
private theorem isProjectiveMorphism_iso_comp {V V' Z : Scheme.{u}} (e : V ≅ V') {g : V' ⟶ Z}
    (hg : IsProjectiveMorphism g) : IsProjectiveMorphism (e.hom ≫ g) := by
  obtain ⟨n, i, hi, rfl⟩ := hg
  exact ⟨n, e.hom ≫ i, inferInstance, by simp⟩

/-! ### The homogeneous pieces are the direct images `π_* 𝒪_M(nD)`

The identifications `𝒜_n(U) ≃ H⁰(π⁻¹U, 𝒪_M(nD))` commute with restriction and are
`𝒪_Z(U)`-linear, so they assemble into an isomorphism of `𝒪_Z`-modules
`𝒜_n ≅ π_* 𝒪_M(nD)`. For `D` Cartier, `𝒪_M(nD)` is invertible, hence coherent on the locally
Noetherian `M`, and for `π` proper over a locally Noetherian base its direct image is coherent
(Stacks 02O5); so every homogeneous piece is of finite type. -/

section Pieces

variable {M Z : Scheme.{u}} [IsLocallyNoetherian M] [IsNormal M] {π : M ⟶ Z} {D : Divisor M}
  (A : DivisorialSectionAlgebra π D)

/-- The morphism `𝒜_n ⟶ π_* 𝒪_M(nD)` given by the identifications of sections. -/
private noncomputable def pieceHomPushforward (n : ℤ) (hn : 0 ≤ n) :
    A.algebra.piece n ⟶ (Scheme.Modules.pushforward π).obj (n • D).divisorialSheaf :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (A.sectionEquiv n hn U.unop).toAddMonoidHom
      naturality U V i := by
        ext a
        exact A.sectionEquiv_restrict n hn i.unop.le a }
    (fun U r a => A.sectionEquiv_smul n hn U.unop r a)⟩

/-- The morphism `π_* 𝒪_M(nD) ⟶ 𝒜_n` given by the inverse identifications of sections. -/
private noncomputable def pushforwardHomPiece (n : ℤ) (hn : 0 ≤ n) :
    (Scheme.Modules.pushforward π).obj (n • D).divisorialSheaf ⟶ A.algebra.piece n :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (A.sectionEquiv n hn U.unop).symm.toAddMonoidHom
      naturality U V i := by
        ext a
        refine (AddEquiv.symm_apply_eq _).mpr ?_
        have := A.sectionEquiv_restrict n hn i.unop.le ((A.sectionEquiv n hn U.unop).symm a)
        erw [this, AddEquiv.apply_symm_apply]
        rfl }
    (fun U r a => by
      refine (AddEquiv.symm_apply_eq _).mpr ?_
      have := A.sectionEquiv_smul n hn U.unop r ((A.sectionEquiv n hn U.unop).symm a)
      erw [this, AddEquiv.apply_symm_apply]
      rfl)⟩

/-- **The homogeneous piece `𝒜_n` is `π_* 𝒪_M(nD)`** as an `𝒪_Z`-module, for `n ≥ 0`. -/
private noncomputable def pieceIsoPushforward (n : ℤ) (hn : 0 ≤ n) :
    A.algebra.piece n ≅ (Scheme.Modules.pushforward π).obj (n • D).divisorialSheaf where
  hom := pieceHomPushforward A n hn
  inv := pushforwardHomPiece A n hn
  hom_inv_id := by
    ext U a
    exact (A.sectionEquiv n hn U.unop).symm_apply_apply a
  inv_hom_id := by
    ext U a
    exact (A.sectionEquiv n hn U.unop).apply_symm_apply a

/-- **Every homogeneous piece of the section algebra of a Cartier divisor along a proper
morphism to a locally Noetherian scheme is of finite type** (Stacks 02O5). -/
private theorem isFiniteType_piece [CompactSpace M] [IsLocallyNoetherian Z] (hπ : IsProper π)
    (hDC : D.IsCartier) (n : ℤ) (hn : 0 ≤ n) :
    SheafOfModules.IsFiniteType (A.algebra.piece n) := by
  have := (hDC.zsmul n).isInvertibleModule_divisorialSheaf
  have : (n • D).divisorialSheaf.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible M _
  have : ((Scheme.Modules.pushforward π).obj (n • D).divisorialSheaf).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward π _
  exact SheafOfModules.IsFiniteType.of_iso SheafOfModules.IsCoherent.isFiniteType
    (pieceIsoPushforward A n hn).symm

/-- **The relative `Proj` of the section algebra is proper over the base** once the section
algebra is of finite type over `𝒪_Z` (Stacks 0800, with `𝒜_0 = π_* 𝒪_M` of finite type by
`isFiniteType_piece`). -/
private theorem isProper_toBase [CompactSpace M] [IsLocallyNoetherian Z] (hπ : IsProper π)
    (hDC : D.IsCartier) (hb : A.situation.IsFiniteTypeOverBase) : IsProper A.toBase :=
  Stacks.RelativeProj.Situation.isProper_relativeProjToBase_of_pieceZero_of_isFiniteTypeOverBase
    (isFiniteType_piece A hπ hDC 0 le_rfl) hb

end Pieces

/-! ### H-projectivity over a projective variety -/

/-- A projective variety over `ℂ` is locally Noetherian. -/
private theorem isLocallyNoetherian_of_isProjectiveVariety {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) : IsLocallyNoetherian Z := by
  have := hZ.toIsVariety
  exact LocallyOfFiniteType.isLocallyNoetherian sZ

/-- A projective variety over `ℂ` carries an ample invertible module (Stacks 0B45 over the
affine base `Spec ℂ`, clause (2) ⟹ clause (5)). -/
private theorem exists_isAmple_of_isProjectiveVariety {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) :
    ∃ (L : Z.Modules) (hL : Stacks.Ample.IsInvertibleModule Z L),
      letI : Stacks.Ample.IsInvertibleModule Z L := hL
      Stacks.Ample.IsAmple Z L := by
  have h := (isProjective_tfae_seven_of_exists_isAmple sZ
    ⟨Stacks.Ample.unitModule _, inferInstance,
      Stacks.Ample.isAmple_unitModule_of_isAffine _⟩).out 2 5
  exact (h.mp hZ.isProjective).2

/-- **A proper morphism to a projective variety carrying a relatively ample invertible module is
H-projective** (Stacks 0B45, clause (6) ⟹ clause (2), the base carrying an ample module by
`exists_isAmple_of_isProjectiveVariety`). -/
private theorem isProjectiveMorphism_of_isRelativelyAmple {V Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (p : V ⟶ Z) (hp : IsProper p)
    (hL : ∃ (L : V.Modules) (hL : Stacks.Ample.IsInvertibleModule V L),
      letI : Stacks.Ample.IsInvertibleModule V L := hL
      Stacks.RelativeAmple.IsRelativelyAmple p L) :
    IsProjectiveMorphism p := by
  have h := (isProjective_tfae_seven_of_exists_isAmple p
    (exists_isAmple_of_isProjectiveVariety hZ)).out 6 2
  exact h.mp ⟨hp, hL⟩

/-! ### Finite generation of the section algebra -/

/-- Linear independence over `F` of elements algebraic over `F` persists over the subalgebra
generated by an algebraically independent family. -/
private theorem linearIndependent_adjoin_of_algebraicIndependent {F L : Type*} [Field F] [Field L]
    [Algebra F L] {σ : Type*} {b : σ → L} (hb : AlgebraicIndependent (algebraicClosure F L) b)
    {ι : Type*} [Finite ι] {v : ι → algebraicClosure F L} (hv : LinearIndependent F v) :
    LinearIndependent (Algebra.adjoin F (Set.range b)) (fun i => (v i : L)) := by
  classical
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpoly : ∀ i, ∃ P : MvPolynomial σ F, MvPolynomial.aeval b P = (g i : L) := fun i =>
    (Algebra.adjoin_range_eq_range_aeval F b).le (g i).2
  choose P hP using hpoly
  let Q : MvPolynomial σ (algebraicClosure F L) :=
    ∑ i, MvPolynomial.C (v i) * MvPolynomial.map (algebraMap F (algebraicClosure F L)) (P i)
  have hQ : MvPolynomial.aeval b Q = 0 := by
    simp only [Q, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap]
    rw [← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP i, mul_comm]
    rfl
  have hQ0 : Q = 0 := hb.eq_zero_of_aeval_eq_zero Q hQ
  have hcoeff : ∀ α i, (P i).coeff α = 0 := by
    intro α
    have h := congrArg (fun p => p.coeff α) hQ0
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    refine (Fintype.linearIndependent_iff.mp hv) (fun i => (P i).coeff α) ?_
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, mul_comm]
  intro i
  apply Subtype.ext
  rw [← hP i]
  have : P i = 0 := MvPolynomial.ext _ _ fun α => by rw [hcoeff α i, MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [this, map_zero]
  rfl

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- The algebraic closure of `F` in a field extension essentially of finite type is finite. -/
private theorem finiteDimensional_algebraicClosure {F L : Type*} [Field F] [Field L] [Algebra F L]
    [Algebra.EssFiniteType F L] : FiniteDimensional F (algebraicClosure F L) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis (K := F) (L := L)
  have hb : AlgebraicIndependent (algebraicClosure F L) ((↑) : s → L) :=
    hs.1.extendScalars (algebraicClosure F L)
  set L0 := IntermediateField.adjoin F (Set.range ((↑) : s → L))
  have : Algebra.IsAlgebraic L0 L := hs.isAlgebraic_field
  have : Algebra.EssFiniteType L0 L := Algebra.EssFiniteType.of_comp F L0 L
  have : Module.Finite L0 L := Algebra.finite_of_essFiniteType_of_isAlgebraic
  refine Module.rank_lt_aleph0_iff.mp <|
    lt_of_le_of_lt (_root_.rank_le (n := Module.finrank L0 L) fun t ht => ?_)
    (Cardinal.natCast_lt_aleph0)
  have h1 := linearIndependent_adjoin_of_algebraicIndependent hb ht
  have h2 : LinearIndependent L0 (fun i : t => ((i : algebraicClosure F L) : L)) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin F (Set.range ((↑) : s → L))) L0).mp h1
  simpa using h2.fintype_card_le_finrank

private theorem finiteType_of_isIntegral_adjoin {R S L : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Field L] [Algebra R L] (hR : IsNagataRing R) [Algebra.EssFiniteType R L]
    (Ψ : S →ₐ[R] L) (hΨ : Function.Injective Ψ) (g : Finset S)
    (hint : ∀ s : S, _root_.IsIntegral (Algebra.adjoin R (g : Set S)) s) :
    Algebra.FiniteType R S := by
  classical
  set C := Algebra.adjoin R (g : Set S)
  have hCft : Algebra.FiniteType R C := Algebra.FiniteType.adjoin_of_finite g.finite_toSet
  have hCN : IsNagataRing C := IsNagataRing.of_finiteType hR
  have : IsDomain S := hΨ.isDomain Ψ.toRingHom
  let : Algebra C L := (Ψ.toRingHom.comp (algebraMap C S)).toAlgebra
  have hinj : Function.Injective (algebraMap C L) := hΨ.comp Subtype.val_injective
  have : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).mpr hinj
  let : Algebra (FractionRing C) L := FractionRing.liftAlgebra C L
  have : IsScalarTower C (FractionRing C) L := FractionRing.isScalarTower_liftAlgebra C L
  have : IsScalarTower R (FractionRing C) L := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [IsScalarTower.algebraMap_apply R C (FractionRing C),
      ← IsScalarTower.algebraMap_apply C (FractionRing C) L]
    change _ = Ψ (algebraMap C S (algebraMap R C r))
    rw [← IsScalarTower.algebraMap_apply R C S, Ψ.commutes]
  have : Algebra.EssFiniteType (FractionRing C) L := Algebra.EssFiniteType.of_comp R _ L
  have : FiniteDimensional (FractionRing C) (algebraicClosure (FractionRing C) L) :=
    finiteDimensional_algebraicClosure
  have hfin := module_finite_integralClosure_of_isNagataRing (A := C) (FractionRing C)
    (algebraicClosure (FractionRing C) L) hCN
  set E := algebraicClosure (FractionRing C) L
  have hmemE : ∀ s : S, Ψ s ∈ E := fun s => by
    rw [mem_algebraicClosure_iff]
    have h1 : _root_.IsIntegral C (Ψ s) := by
      let ΨC : S →ₐ[C] L := { Ψ.toRingHom with commutes' := fun _ => rfl }
      exact (hint s).map ΨC
    exact (h1.tower_top (A := FractionRing C)).isAlgebraic
  have hintE : ∀ s : S, IsIntegral C (⟨Ψ s, hmemE s⟩ : E) := fun s => by
    let ΨC : S →ₐ[C] E :=
      { toFun := fun s => ⟨Ψ s, hmemE s⟩
        map_one' := Subtype.ext (map_one Ψ)
        map_mul' := fun a b => Subtype.ext (map_mul Ψ a b)
        map_zero' := Subtype.ext (map_zero Ψ)
        map_add' := fun a b => Subtype.ext (map_add Ψ a b)
        commutes' := fun _ => rfl }
    exact (hint s).map ΨC
  let f : S →ₗ[C] integralClosure C E :=
    { toFun := fun s => ⟨⟨Ψ s, hmemE s⟩, hintE s⟩
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by
        ext
        change Ψ (c • a) = (algebraMap C L c) * Ψ a
        rw [Algebra.smul_def, map_mul]
        rfl }
  have hf : Function.Injective f := fun a b h => hΨ (by
    simpa [f] using congrArg (fun z : integralClosure C E => ((z : E) : L)) h)
  have : Module.Finite C S := Module.Finite.of_injective f hf
  exact Algebra.FiniteType.trans hCft (Module.Finite.finiteType (R := C) S)

private theorem fromSpecResidueField_comp_eq {M Z : Scheme} (π : M ⟶ Z) {U : Z.Opens}
    (hU : IsAffineOpen U) (y : M) (hy : y ∈ π ⁻¹ᵁ U) :
    M.fromSpecResidueField y ≫ π = Spec.map (π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy ≫
      M.residue y) ≫ hU.fromSpec := by
  rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← hU.fromSpecStalk_eq_fromSpecStalk (x := π y) hy]
  dsimp only [IsAffineOpen.fromSpecStalk]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg (· ≫ M.residue y) (Scheme.Hom.germ_stalkMap π U y hy)

private theorem exists_center_of_valuationSubring {M Z : Scheme} (π : M ⟶ Z) [UniversallyClosed π]
    {U : Z.Opens} (hU : IsAffineOpen U) (y : M) (hy : y ∈ π ⁻¹ᵁ U)
    (V : ValuationSubring (M.residueField y))
    (hV : ∀ r : Γ(Z, U), M.residue y (M.presheaf.germ (π ⁻¹ᵁ U) y hy (π.app U r)) ∈ V) :
    ∃ (x : M) (h : y ⤳ x), x ∈ π ⁻¹ᵁ U ∧
      ∀ t : M.presheaf.stalk x, M.residue y (M.presheaf.stalkSpecializes h t) ∈ V := by
  let K := M.residueField y
  let ρ : Γ(Z, U) ⟶ K := π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy ≫ M.residue y
  let φV : Γ(Z, U) ⟶ CommRingCat.of V :=
    CommRingCat.ofHom (ρ.hom.codRestrict V.toSubring hV)
  have hφ : φV ≫ CommRingCat.ofHom (algebraMap V K) = ρ := by
    ext; rfl
  have w : M.fromSpecResidueField y ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ (Spec.map φV ≫ hU.fromSpec) := by
    rw [fromSpecResidueField_comp_eq π hU y hy, ← Spec.map_comp_assoc, hφ]
  have H : ValuativeCriterion.Existence π :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed π) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) π).1
  obtain ⟨l, hl₁, hl₂⟩ :=
    (H (ValuativeCommSq.mk (R := V) (K := K) (M.fromSpecResidueField y)
      (Spec.map φV ≫ hU.fromSpec) ⟨w⟩)).exists_lift
  dsimp only at hl₁ hl₂
  let x := l (IsLocalRing.closedPoint V)
  have hyx : y ⤳ x := by
    simp_rw [x, ← Scheme.fromSpecResidueField_apply y (IsLocalRing.closedPoint K), ← hl₁]
    exact (IsLocalRing.specializes_closedPoint _).map l.continuous
  have hxU : x ∈ π ⁻¹ᵁ U := by
    have h2 := congrArg (fun h : Spec (CommRingCat.of V) ⟶ Z => h (IsLocalRing.closedPoint V)) hl₂
    change (l ≫ π) (IsLocalRing.closedPoint V) ∈ U
    rw [h2, ← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨x, hyx, hxU, fun t => ?_⟩
  let ψ : M.presheaf.stalk x ⟶ CommRingCat.of V := Scheme.stalkClosedPointTo l
  have hl : Spec.map ψ ≫ M.fromSpecStalk x = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  have heq : ψ ≫ CommRingCat.ofHom (algebraMap V K) =
      M.presheaf.stalkSpecializes hyx ≫ M.residue y := by
    apply Spec.map_injective
    apply (cancel_mono (M.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, hl, hl₁, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  have hval : algebraMap V K (ψ t) = M.residue y (M.presheaf.stalkSpecializes hyx t) :=
    congrArg (fun g => g.hom t) heq
  rw [← hval]
  exact (ψ t).2

private theorem exists_pow_smul_eq_restrict {X : Scheme.{0}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (g : Γ(X, U)) (σ : Γ(F, X.basicOpen g)) :
    ∃ (m : ℕ) (a : Γ(F, U)), F.presheaf.map (homOfLE (X.basicOpen_le g)).op a =
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) ^ m • σ := by
  let _ : Module Γ(X, U) Γ(F, X.basicOpen g) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) :=
    ⟨fun r s m => by
      change ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom r • s) • m = _
      rw [smul_assoc]; rfl⟩
  let ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, X.basicOpen g) :=
    { toFun := fun a => F.presheaf.map (homOfLE (X.basicOpen_le g)).op a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => (Scheme.Modules.map_smul F (homOfLE (X.basicOpen_le g)) r a) }
  have hloc := isLocalizedModule_restrict_basicOpen F hU g ρ (fun _ => rfl)
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, h⟩ := hloc.surj σ
  refine ⟨m, a, ?_⟩
  change ρ a = _
  rw [← h]
  change (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ m) • σ = _
  rw [map_pow]

section Generation

variable {M Z : Scheme.{0}} [IsLocallyNoetherian M] [IsNormal M] {π : M ⟶ Z} {D : Divisor M}
  (A : DivisorialSectionAlgebra π D)

private theorem exists_stalk_mul_pow_eq {U : Z.Opens} (a : (A.algebra.piece (1 : ℤ)).val.obj (op U))
    {x : M} (hx : x ∈ A.generatingLocus zero_le_one a) {Y : irreducibleComponents M}
    (hxY : x ∈ Y.1) (hY : componentGenericPoint M Y ∈ π ⁻¹ᵁ U) (n : ℕ)
    (t : (A.algebra.piece (n : ℤ)).val.obj (op U)) :
    ∃ r : M.presheaf.stalk x, (stalkToRationalFunctions M hxY).hom r *
        ((A.sectionEquiv 1 zero_le_one U a :
          (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y, hY⟩) ^ n =
      (A.sectionEquiv n (Int.natCast_nonneg n) U t :
          (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y, hY⟩ := by
  obtain ⟨W, ⟨hWU, b, hb, hab⟩, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
  set tK := (A.sectionEquiv n (Int.natCast_nonneg n) U t :
          (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
  let φ : (rationalFunctionsPresheaf M).obj (op W) :=
    (rationalFunctionsPresheaf M).map (homOfLE hWU).op tK * b ^ n
  have hφ : (0 : Divisor M).IsDivisorialSection W φ := by
    intro E hE
    have h1 := (A.sectionEquiv n (Int.natCast_nonneg n) U t).2 E
      (hE.mono (Set.inter_subset_inter_right _ hWU))
    have h2 := (hb E hE).pow n
    convert h1.mul h2 using 1
    · simp [DivisorWithCoeffs.coeff_smul]
    · rfl
  have hYW : componentGenericPoint M Y ∈ W := (genericPoint_mem_iff Y W).mpr ⟨x, hxW, hxY⟩
  obtain ⟨r, hr⟩ := hφ.exists_stalk_eq hxW hxY
  refine ⟨r, ?_⟩
  rw [hr]
  change tK ⟨Y, _⟩ * b ⟨Y, hYW⟩ ^ n * _ = tK ⟨Y, hY⟩
  have hab'' : (A.sectionEquiv 1 zero_le_one U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y, hY⟩ * b ⟨Y, hYW⟩ = 1 :=
    congrFun hab ⟨Y, hYW⟩
  calc tK ⟨Y, _⟩ * b ⟨Y, hYW⟩ ^ n * _ = tK ⟨Y, hY⟩ * ((A.sectionEquiv 1 zero_le_one U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y, hY⟩ * b ⟨Y, hYW⟩) ^ n := by ring
    _ = tK ⟨Y, hY⟩ := by rw [hab'', one_pow, mul_one]

private theorem mem_generatingLocus_of_restrict_eq_smul [IsIntegral M] [CompactSpace M]
    {U V : Z.Opens} (hVU : V ≤ U) (a : (A.algebra.piece (1 : ℤ)).val.obj (op U))
    (ψ : (RationalFunctions M)ˣ) {x : M}
    (hB : ∀ E : MMP.Mori.PrimeDivisor M, x ∈ E.support → D.coeff E + E.ord ψ = 0)
    {u : Γ(M, π ⁻¹ᵁ V)} (hu : IsUnit u) {ψK : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ V))}
    (hψK : ∀ Y, ψK Y = (ψ : RationalFunctions M) Y.1)
    (hkey : (rationalFunctionsPresheaf M).map (homOfLE (π.preimage_mono hVU)).op
      (A.sectionEquiv 1 zero_le_one U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) =
      u • ψK)
    (hx : x ∈ π ⁻¹ᵁ V) : x ∈ A.generatingLocus zero_le_one a := by
  classical
  obtain ⟨w, huw⟩ := hu.exists_right_inv
  let E0 : Divisor M := principalDivisor ψ + (1 : ℤ) • D
  have hE0 : ∀ E, E0.coeff E = E.ord ψ + D.coeff E := fun E => by
    simp [E0, DivisorWithCoeffs.coeff_add]
  let W : M.Opens := π ⁻¹ᵁ V ⊓ ⟨(E0.supp : Set M)ᶜ, E0.isClosed_supp.isOpen_compl⟩
  have hWV : W ≤ π ⁻¹ᵁ V := inf_le_left
  have hWU : W ≤ π ⁻¹ᵁ U := hWV.trans (π.preimage_mono hVU)
  have hxW : x ∈ W := ⟨hx, fun h => by
    obtain ⟨E, hne, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    exact hne ((hE0 E).trans ((add_comm _ _).trans (hB E hxE)))⟩
  let β : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ V)) :=
    fun Y => M.presheaf.germ (π ⁻¹ᵁ V) _ Y.2 w * ((ψ⁻¹ : (RationalFunctions M)ˣ) :
      RationalFunctions M) Y.1
  let b := (rationalFunctionsPresheaf M).map (homOfLE hWV).op β
  have hb : b ∈ (-((1 : ℤ) • D)).divisorialSubmodule W := by
    intro E hE
    have hcoeff := (hE0 E).symm.trans (coeff_eq_zero_of_nonempty_inter (fun _ h => h.2) hE)
    have h1 := Divisor.isDivisorialSection_algebraMap (D := 0) le_rfl w E
      (hE.mono (Set.inter_subset_inter_right _ hWV))
    have h2 : E.OrdGE (D.coeff E) (((ψ⁻¹ : (RationalFunctions M)ˣ) : RationalFunctions M)
        E.component) := by
      refine Or.inr ?_
      rw [E.valuation_component, WithZero.exp_le_exp, PrimeDivisor.ord_inv]
      linarith
    convert h1.mul h2 using 1
    · simp
    · rfl
  refine (le_sSup ⟨hWU, b, hb, ?_⟩ : W ≤ A.generatingLocus zero_le_one a) hxW
  funext Y
  have hY : componentGenericPoint M Y.1 ∈ π ⁻¹ᵁ V := hWV Y.2
  have hk := congrFun hkey ⟨Y.1, hY⟩
  change (A.sectionEquiv 1 zero_le_one U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
      ⟨Y.1, _⟩ * (M.presheaf.germ (π ⁻¹ᵁ V) _ hY w * ((ψ⁻¹ : (RationalFunctions M)ˣ) :
      RationalFunctions M) Y.1) = 1
  rw [MMP.Mori.rationalFunctions_smul_apply, hψK] at hk
  have hk' : (A.sectionEquiv 1 zero_le_one U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y.1, hWU Y.2⟩ =
      M.presheaf.germ (π ⁻¹ᵁ V) _ hY u * (ψ : RationalFunctions M) Y.1 := hk
  rw [hk', mul_mul_mul_comm, ← map_mul, huw, map_one, one_mul, ← Pi.mul_apply, Units.mul_inv,
    Pi.one_apply]

private theorem exists_mem_generatingLocus [IsIntegral M] [CompactSpace M] (hDC : D.IsCartier)
    (hfree : IsRelativelyFreeDivisor π D) {U : Z.Opens} (hU : IsAffineOpen U) {x : M}
    (hx : x ∈ π ⁻¹ᵁ U) :
    ∃ a : (A.algebra.piece (1 : ℤ)).val.obj (op U), x ∈ A.generatingLocus zero_le_one a := by
  classical
  obtain ⟨U', hxU', ψ, hA, hB⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree π hDC hfree x
  obtain ⟨g, hgle, hxg⟩ := hU.exists_basicOpen_le (V := U ⊓ U') ⟨π x, hx, hxU'⟩ hx
  set Dg := Z.basicOpen g
  have hDgU : Dg ≤ U := Z.basicOpen_le g
  let ψK : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ Dg)) :=
    fun Y => (ψ : RationalFunctions M) Y.1
  have hψK : ψK ∈ ((1 : ℤ) • D).divisorialSubmodule (π ⁻¹ᵁ Dg) := by
    intro E hE
    refine Or.inr ?_
    change WithZero.exp _ ≤ E.valuation ((ψ : RationalFunctions M) E.component)
    rw [E.valuation_component, WithZero.exp_le_exp]
    have := hA E (hE.mono (Set.inter_subset_inter_right _
      (π.preimage_mono (hgle.trans inf_le_right))))
    simp only [one_smul]
    linarith
  let σ := (A.sectionEquiv 1 zero_le_one Dg).symm ⟨ψK, hψK⟩
  have := A.isQuasicoherent 1
  obtain ⟨m, a, ha⟩ := exists_pow_smul_eq_restrict (A.algebra.piece (1 : ℤ)) hU g σ
  have hres := A.sectionEquiv_restrict 1 zero_le_one hDgU a
  set gD := Z.presheaf.map (homOfLE (Z.basicOpen_le g)).op g
  have hkey : (rationalFunctionsPresheaf M).map (homOfLE (π.preimage_mono hDgU)).op
      (A.sectionEquiv 1 zero_le_one U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) =
      π.app Dg (gD ^ m) • ψK := by
    have h1 := congrArg (fun z => (A.sectionEquiv 1 zero_le_one Dg z :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ Dg)))) ha
    simp only at h1
    calc _ = ((A.sectionEquiv 1 zero_le_one Dg
            ((A.algebra.piece 1).val.map (homOfLE hDgU).op a) :
            (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ Dg)))) := by rw [hres]; rfl
      _ = _ := h1
      _ = ((π.app Dg (gD ^ m) • A.sectionEquiv 1 zero_le_one Dg σ :
            ((1 : ℤ) • D).divisorialSubmodule (π ⁻¹ᵁ Dg)) :
            (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ Dg))) :=
              congrArg Subtype.val (A.sectionEquiv_smul 1 zero_le_one Dg (gD ^ m) σ)
      _ = _ := by simp only [σ, AddEquiv.apply_symm_apply]; rfl
  have hu : IsUnit (π.app Dg (gD ^ m)) := by
    rw [map_pow]
    exact ((RingedSpace.isUnit_res_basicOpen Z.toRingedSpace g).map (π.app Dg).hom).pow m
  exact ⟨a, mem_generatingLocus_of_restrict_eq_smul A hDgU a ψ hB hu (fun _ => rfl) hkey hxg⟩

private theorem exists_finset_generatingLocus_cover [IsIntegral M] [CompactSpace M]
    (hDC : D.IsCartier) (hfree : IsRelativelyFreeDivisor π D) {U : Z.Opens}
    (hU : IsAffineOpen U) :
    ∃ (T : Finset (π ⁻¹ᵁ U : M.Opens))
      (a : (π ⁻¹ᵁ U : M.Opens) → (A.algebra.piece (1 : ℤ)).val.obj (op U)),
      ∀ x ∈ π ⁻¹ᵁ U, ∃ y ∈ T, x ∈ A.generatingLocus zero_le_one (a y) := by
  choose a ha using fun x : (π ⁻¹ᵁ U : M.Opens) => exists_mem_generatingLocus A hDC hfree hU x.2
  have : IsNoetherian M := {}
  obtain ⟨T, hT⟩ := (TopologicalSpace.NoetherianSpace.isCompact
    ((π ⁻¹ᵁ U : M.Opens) : Set M)).elim_finite_subcover _
    (fun x => (A.generatingLocus zero_le_one (a x)).isOpen)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ha ⟨x, hx⟩⟩)
  exact ⟨T, a, fun x hx => (Set.mem_iUnion₂.mp (hT hx)).imp fun _ ⟨hy, hxy⟩ => ⟨hy, hxy⟩⟩

private theorem sectionEquiv_apply_ne_zero_of_mem_generatingLocus {U : Z.Opens}
    {Y0 : irreducibleComponents M} (hY0 : ∀ x : M, x ∈ Y0.1)
    (hη : componentGenericPoint M Y0 ∈ π ⁻¹ᵁ U) {a : (A.algebra.piece (1 : ℤ)).val.obj (op U)}
    {x : M} (hx : x ∈ A.generatingLocus zero_le_one a) :
    (A.sectionEquiv 1 zero_le_one U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y0, hη⟩ ≠ 0 := by
  intro h0
  obtain ⟨W, ⟨hWU, b, hb, hab⟩, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
  have hYW : componentGenericPoint M Y0 ∈ W := (genericPoint_mem_iff Y0 W).mpr ⟨x, hxW, hY0 x⟩
  have h1 : (A.sectionEquiv 1 zero_le_one U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y0, hη⟩ * b ⟨Y0, hYW⟩ = 1 :=
    congrFun hab ⟨Y0, hYW⟩
  exact zero_ne_one (by rwa [h0, zero_mul] at h1)

end Generation

/-- The residue field at a point over an affine open `U` of the base of a morphism locally of
finite type is essentially of finite type over `Γ(Z, U)`. -/
private theorem essFiniteType_residueField_of_mem {M Z : Scheme.{0}} (π : M ⟶ Z)
    [LocallyOfFiniteType π] {U : Z.Opens} (hU : IsAffineOpen U) (y : M) (hy : y ∈ π ⁻¹ᵁ U) :
    letI : Algebra Γ(Z, U) (M.residueField y) :=
      (π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy ≫ M.residue y).hom.toAlgebra
    Algebra.EssFiniteType Γ(Z, U) (M.residueField y) := by
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := M) (x := y)
    (U := π ⁻¹ᵁ U) hy
  have e : V ≤ π ⁻¹ᵁ U := hVU
  let : Algebra Γ(Z, U) Γ(M, V) := (π.appLE U V e).hom.toAlgebra
  let : Algebra Γ(Z, U) (M.presheaf.stalk y) :=
    (π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy).hom.toAlgebra
  let : Algebra Γ(M, V) (M.presheaf.stalk y) := (M.presheaf.germ V y hyV).hom.toAlgebra
  let : Algebra Γ(Z, U) (M.residueField y) :=
    (π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy ≫ M.residue y).hom.toAlgebra
  let : Algebra (M.presheaf.stalk y) (M.residueField y) := (M.residue y).hom.toAlgebra
  have : IsScalarTower Γ(Z, U) Γ(M, V) (M.presheaf.stalk y) := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a ↦ ?_)
    change M.presheaf.germ (π ⁻¹ᵁ U) y hy (π.app U a) =
      M.presheaf.germ V y hyV (π.appLE U V e a)
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, M.presheaf.germ_res_apply]
  have : IsScalarTower Γ(Z, U) (M.presheaf.stalk y) (M.residueField y) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ ↦ rfl)
  have hft : Algebra.FiniteType Γ(Z, U) Γ(M, V) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π ‹_› ⟨U, hU⟩ ⟨V, hV⟩ e
  have : IsLocalization (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
      (M.presheaf.stalk y) := hV.isLocalization_stalk ⟨y, hyV⟩
  have : Algebra.EssFiniteType Γ(M, V) (M.presheaf.stalk y) :=
    Algebra.EssFiniteType.of_isLocalization _ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
  have : Algebra.EssFiniteType Γ(Z, U) (M.presheaf.stalk y) :=
    Algebra.EssFiniteType.comp Γ(Z, U) Γ(M, V) (M.presheaf.stalk y)
  exact Algebra.EssFiniteType.of_surjective
    (IsScalarTower.toAlgHom Γ(Z, U) (M.presheaf.stalk y) (M.residueField y))
    (M.residue_surjective y)

/-- The sections of a variety over `ℂ` over an affine open form a Nagata ring. -/
private theorem isNagataRing_of_isVariety {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {U : Z.Opens} (hU : IsAffineOpen U) :
    IsNagataRing Γ(Z, U) := by
  have := hZ.toIsVariety
  let : Algebra ℂ Γ(Z, U) := ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sZ.appLE ⊤ U (by simp)).hom.toAlgebra
  have : Algebra.FiniteType ℂ Γ(Z, U) := by
    change RingHom.FiniteType ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sZ.appLE ⊤ U (by simp)).hom
    rw [CommRingCat.hom_comp]
    exact (HasRingHomProperty.appLE @LocallyOfFiniteType sZ inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _).comp (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.surjective)
  exact IsNagataRing.of_finiteType (A := ℂ) IsNagataRing.of_field

/-- Over an open of the base with empty preimage, the section ring is trivial. -/
theorem DivisorialSectionAlgebra.subsingleton_sectionRing_of_not_nonempty {M Z : Scheme.{0}}
    [IsLocallyNoetherian M] [IsNormal M]
    {π : M ⟶ Z} {D : Divisor M} (A : DivisorialSectionAlgebra π D) {U : Z.Opens}
    (hne : ¬((π ⁻¹ᵁ U : M.Opens) : Set M).Nonempty) :
    Subsingleton (A.situation.sectionRing U) := by
  have hpiece : ∀ n (s : A.situation.sectionPieces U n), s = 0 := fun n s =>
    (A.sectionEquiv n (Int.natCast_nonneg n) U).injective (by
      rw [map_zero]
      exact Subtype.ext (funext fun Y => (hne ⟨_, Y.2⟩).elim))
  exact ⟨fun x y => DFinsupp.ext fun n => (hpiece n _).trans (hpiece n _).symm⟩

private theorem injective_residue_componentGenericPoint {M : Scheme.{u}} [IsReduced M]
    (Y : irreducibleComponents M) :
    Function.Injective (M.residue (componentGenericPoint M Y)).hom := by
  let := (RationalFunctions.isField_stalk M Y).toField
  exact (M.residue _).hom.injective

/-- In a valuation ring, `c eᵢⁿ Xⁿ` lies in it if `c` and a maximal-valuation `e i₀ X` do. -/
theorem algebraMap_mul_pow_mul_pow_mem {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring L) {ι : Type*} {T : Finset ι} {e : ι → K} {X : L} (hX : X ≠ 0)
    {i₀ : ι} (he₀ : e i₀ ≠ 0)
    (hmax : ∀ y ∈ T, e y ≠ 0 →
      V.valuation (algebraMap K L (e y) * X) ≤ V.valuation (algebraMap K L (e i₀) * X))
    (h₀ : algebraMap K L (e i₀) * X ∈ V) {c : K} (hc : algebraMap K L c ∈ V) {i : ι}
    (hi : i ∈ T) (n : ℕ) : algebraMap K L (c * e i ^ n) * X ^ n ∈ V := by
  have hr : algebraMap K L (e i / e i₀) ∈ V := by
    by_cases hei : e i = 0
    · simp [hei]
    have hden : V.valuation (algebraMap K L (e i₀) * X) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (mul_ne_zero ((map_ne_zero _).mpr he₀) hX)
    rw [map_div₀, ← mul_div_mul_right _ _ hX, ← ValuationSubring.valuation_le_one_iff, map_div₀]
    exact (div_le_one₀ (zero_lt_iff.mpr hden)).mpr (hmax i hi hei)
  have hdec : algebraMap K L (c * e i ^ n) * X ^ n =
      algebraMap K L c * (algebraMap K L (e i / e i₀)) ^ n * (algebraMap K L (e i₀) * X) ^ n := by
    rw [mul_assoc (algebraMap K L _), ← mul_pow, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ he₀,
      mul_pow, map_mul, map_pow, mul_assoc]
  rw [hdec]
  exact mul_mem (mul_mem hc (pow_mem hr n)) (pow_mem h₀ n)

section SectionRingEmbedding

variable {M Z : Scheme.{0}} [IsLocallyNoetherian M] [IsNormal M] {π : M ⟶ Z} {D : Divisor M}
  (A : DivisorialSectionAlgebra π D) {U : Z.Opens} {Y0 : irreducibleComponents M}
  (hη : componentGenericPoint M Y0 ∈ π ⁻¹ᵁ U)

private noncomputable def evalResidue :
    (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)) →+*
      M.residueField (componentGenericPoint M Y0) :=
  (M.residue _).hom.comp (Pi.evalRingHom (fun Y : {Y : irreducibleComponents M //
    componentGenericPoint M Y ∈ π ⁻¹ᵁ U} => M.presheaf.stalk (componentGenericPoint M Y.1))
    ⟨Y0, hη⟩)

private noncomputable def sectionRingEmbedding : A.situation.sectionRing U →+*
    FractionRing (Polynomial (M.residueField (componentGenericPoint M Y0))) :=
  (algebraMap _ _).comp ((Polynomial.mapRingHom (evalResidue hη)).comp (toPoly A U))

private theorem injective_sectionRingEmbedding [IsIntegral M] :
    Function.Injective (sectionRingEmbedding A hη) := by
  have hevK : Function.Injective (evalResidue hη) := by
    intro c d h
    funext Y
    obtain rfl : Y = ⟨Y0, hη⟩ := Subtype.ext (Subtype.ext
      (((irreducibleComponents_eq_singleton (X := M)).le Y.1.2).trans
        ((irreducibleComponents_eq_singleton (X := M)).le Y0.2).symm))
    exact injective_residue_componentGenericPoint Y0 h
  exact (IsFractionRing.injective _ _).comp
    ((Polynomial.map_injective _ hevK).comp (injective_toPoly A U))

private theorem sectionRingEmbedding_of (n : ℕ) (s : A.situation.sectionPieces U n) :
    sectionRingEmbedding A hη (DirectSum.of (A.situation.sectionPieces U) n s) =
      algebraMap (M.residueField (componentGenericPoint M Y0))
        (FractionRing (Polynomial (M.residueField (componentGenericPoint M Y0))))
        (evalResidue hη (A.sectionEquiv n (Int.natCast_nonneg n) U s :
          (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))) *
      algebraMap (Polynomial (M.residueField (componentGenericPoint M Y0)))
        (FractionRing (Polynomial (M.residueField (componentGenericPoint M Y0))))
        Polynomial.X ^ n := by
  change algebraMap _ _ (Polynomial.map (evalResidue hη) (toPoly A U (DirectSum.of _ n s))) = _
  rw [show toPoly A U (DirectSum.of _ n s) = pieceHom A U n s from
    DirectSum.toSemiring_of _ _ _ _ _, pieceHom_apply, Polynomial.map_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    IsScalarTower.algebraMap_apply (M.residueField (componentGenericPoint M Y0))
      (Polynomial (M.residueField (componentGenericPoint M Y0)))
      (FractionRing (Polynomial (M.residueField (componentGenericPoint M Y0))))]
  rfl

private theorem sectionRingEmbedding_baseMap (r : _) :
    sectionRingEmbedding A hη (A.situation.sectionRingBaseMap U r) =
      algebraMap _ _ ((π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) _ hη ≫ M.residue _).hom r) := by
  change sectionRingEmbedding A hη ((A.situation.sectionRingStructure).baseMap U r) = _
  rw [(A.situation.sectionRingStructure).baseMap_apply U r, sectionRingEmbedding_of, pow_zero,
    mul_one]
  congr 1
  change M.residue _ ((A.sectionEquiv 0 le_rfl U (r • A.algebra.one.eval (op U)) :
    (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y0, hη⟩) = _
  rw [A.sectionEquiv_smul 0 le_rfl U r (A.algebra.one.eval (op U))]
  change M.residue _ ((π.app U r • (A.sectionEquiv 0 le_rfl U (A.algebra.one.eval (op U)) :
    (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))) ⟨Y0, hη⟩) = _
  rw [MMP.Mori.rationalFunctions_smul_apply, A.sectionEquiv_one U]
  exact congrArg (M.residue _).hom (mul_one _)

include hη in
private theorem isIntegral_of_generatingLocus_cover [IsIntegral M] [UniversallyClosed π]
    (hU : IsAffineOpen U) (hY0 : ∀ x : M, x ∈ Y0.1) {x0 : M} (hx0 : x0 ∈ π ⁻¹ᵁ U) {ι : Type*}
    {T : Finset ι} {a : ι → (A.algebra.piece (1 : ℤ)).val.obj (op U)}
    (hcov : ∀ x ∈ π ⁻¹ᵁ U, ∃ y ∈ T, x ∈ A.generatingLocus zero_le_one (a y))
    [Algebra Γ(Z, U) (A.situation.sectionRing U)]
    (hbase : algebraMap Γ(Z, U) _ = A.situation.sectionRingBaseMap U)
    {g : Set (A.situation.sectionRing U)}
    (hg : ∀ y ∈ T, DirectSum.of (A.situation.sectionPieces U) 1 (a y) ∈ g)
    (n : ℕ) (s : A.situation.sectionPieces U n) :
    _root_.IsIntegral (Algebra.adjoin Γ(Z, U) g)
      (DirectSum.of (A.situation.sectionPieces U) n s) := by
  classical
  set C := Algebra.adjoin Γ(Z, U) g
  let K := M.residueField (componentGenericPoint M Y0)
  let L := FractionRing (Polynomial K)
  let Ψ0 := sectionRingEmbedding A hη
  let : Algebra C L := (Ψ0.comp (algebraMap C (A.situation.sectionRing U))).toAlgebra
  let ΨC : A.situation.sectionRing U →ₐ[C] L := { Ψ0 with commutes' := fun _ => rfl }
  let Xb := algebraMap (Polynomial K) L Polynomial.X
  have hXb : Xb ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) L)).mpr Polynomial.X_ne_zero
  let e : ι → K := fun y => evalResidue hη (A.sectionEquiv 1 zero_le_one U (a y) :
    (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
  have hΨa : ∀ y, Ψ0 (DirectSum.of (A.situation.sectionPieces U) 1 (a y)) =
      algebraMap K L (e y) * Xb := fun y =>
    (sectionRingEmbedding_of A hη 1 (a y)).trans (by rw [pow_one]; rfl)
  rw [← isIntegral_algHom_iff ΨC (injective_sectionRingEmbedding A hη)]
  refine AlgebraicGeometry.isIntegralElem_of_forall_valuationSubring (algebraMap C L)
    fun V hV => ?_
  have hVC : ∀ c : C, Ψ0 c ∈ V := fun c => hV ⟨c, rfl⟩
  have hVR : ∀ r, algebraMap K L ((π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) _ hη ≫
      M.residue _).hom r) ∈ V := fun r => by
    have h := hVC (algebraMap Γ(Z, U) C r)
    change Ψ0 (algebraMap Γ(Z, U) _ r) ∈ V at h
    rw [hbase] at h
    exact (congrArg (· ∈ V) (sectionRingEmbedding_baseMap A hη r)).mp h
  obtain ⟨y1, hy1T, hy1⟩ := hcov x0 hx0
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (T.filter fun y => e y ≠ 0)
    (fun y => V.valuation (algebraMap K L (e y) * Xb))
    ⟨y1, Finset.mem_filter.mpr ⟨hy1T, fun he => sectionEquiv_apply_ne_zero_of_mem_generatingLocus
      A hY0 hη hy1 (injective_residue_componentGenericPoint Y0 (he.trans (map_zero _).symm))⟩⟩
  obtain ⟨hi0T, he0⟩ := Finset.mem_filter.mp hi0
  have h0 : algebraMap K L (e i0) * Xb ∈ V :=
    hΨa i0 ▸ hVC ⟨_, Algebra.subset_adjoin (hg i0 hi0T)⟩
  obtain ⟨x, hηx, hxU, hstalk⟩ := exists_center_of_valuationSubring π hU _ hη
    (V.comap (algebraMap K L)) hVR
  obtain ⟨i, hiT, hxi⟩ := hcov x hxU
  obtain ⟨r, hr⟩ := exists_stalk_mul_pow_eq A (a i) hxi (hY0 x) hη n s
  have hs : evalResidue hη (A.sectionEquiv n (Int.natCast_nonneg n) U s :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) =
      M.residue _ ((stalkToRationalFunctions M (hY0 x)).hom r) * e i ^ n := by
    change M.residue _ ((A.sectionEquiv n (Int.natCast_nonneg n) U s :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y0, hη⟩) = _
    rw [← hr, map_mul, map_pow]
    rfl
  change Ψ0 (DirectSum.of (A.situation.sectionPieces U) n s) ∈ V
  rw [sectionRingEmbedding_of, hs]
  exact algebraMap_mul_pow_mul_pow_mem V hXb he0
    (fun y hy hey => hmax y (Finset.mem_filter.mpr ⟨hy, hey⟩)) h0 (hstalk r) hiT n

end SectionRingEmbedding

/-- **Over an affine open of the base, the section ring of a relatively free Cartier divisor
along a proper morphism is a finitely generated algebra.** -/
private theorem finiteType_sectionRingBaseMap {M Z : Scheme.{0}} [IsIntegral M] [CompactSpace M]
    [IsLocallyNoetherian M] [IsNormal M] {π : M ⟶ Z} (hπ : IsProper π) {D : Divisor M}
    (hDC : D.IsCartier) (hfree : IsRelativelyFreeDivisor π D) (A : DivisorialSectionAlgebra π D)
    {U : Z.Opens} (hU : IsAffineOpen U) (hR : IsNagataRing Γ(Z, U)) :
    (show Γ(Z, U) →+* A.situation.sectionRing U from
      A.situation.sectionRingBaseMap U).FiniteType := by
  classical
  rcases ((π ⁻¹ᵁ U : M.Opens) : Set M).eq_empty_or_nonempty with hne | ⟨x0, hx0⟩
  · have := A.subsingleton_sectionRing_of_not_nonempty (Set.not_nonempty_iff_eq_empty.mpr hne)
    exact RingHom.FiniteType.of_surjective _ fun s => ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨Y0, -⟩ := MMP.Mori.exists_mem_irreducibleComponents x0
  have hY0 : ∀ x : M, x ∈ Y0.1 := fun x => by
    rw [(irreducibleComponents_eq_singleton (X := M)).le Y0.2]; trivial
  have hη : componentGenericPoint M Y0 ∈ π ⁻¹ᵁ U :=
    (genericPoint_mem_iff Y0 _).mpr ⟨x0, hx0, hY0 x0⟩
  obtain ⟨T, a, hcov⟩ := exists_finset_generatingLocus_cover A hDC hfree hU
  let g : Finset (A.situation.sectionRing U) :=
    T.image (fun y => DirectSum.of (A.situation.sectionPieces U) 1 (a y))
  let K := M.residueField (componentGenericPoint M Y0)
  let L := FractionRing (Polynomial K)
  let : Algebra Γ(Z, U) (A.situation.sectionRing U) := (A.situation.sectionRingBaseMap U).toAlgebra
  let : Algebra Γ(Z, U) K := (π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) _ hη ≫ M.residue _).hom.toAlgebra
  have : Algebra.EssFiniteType Γ(Z, U) K := essFiniteType_residueField_of_mem π hU _ hη
  have : Algebra.EssFiniteType (Polynomial K) L :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial K))
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.comp K (Polynomial K) L
  have : Algebra.EssFiniteType Γ(Z, U) L := Algebra.EssFiniteType.comp Γ(Z, U) K L
  let Ψ : A.situation.sectionRing U →ₐ[Γ(Z, U)] L :=
    { sectionRingEmbedding A hη with
      commutes' := fun r => (sectionRingEmbedding_baseMap A hη r).trans
        (IsScalarTower.algebraMap_apply Γ(Z, U) K L r).symm }
  refine finiteType_of_isIntegral_adjoin hR Ψ (injective_sectionRingEmbedding A hη) g fun s => ?_
  induction s using DirectSum.induction_on with
  | zero => exact isIntegral_zero
  | of n s =>
    refine isIntegral_of_generatingLocus_cover A hη hU hY0 hx0 hcov ?_ ?_ n s
    · rfl
    · exact fun y hy => Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy)
  | add x y hx hy => exact hx.add hy

/-- **The section algebra of a relatively free Cartier divisor along a projective morphism is of
finite type over the base.** -/
private theorem isFiniteTypeOverBase_situation {M Z : Scheme.{0}} [IsIntegral M] [CompactSpace M]
    [IsLocallyNoetherian M] [IsNormal M] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {π : M ⟶ Z} (hπ : IsProjectiveMorphism π)
    {D : Divisor M} (hDC : D.IsCartier) (hfree : IsRelativelyFreeDivisor π D)
    (A : DivisorialSectionAlgebra π D) : A.situation.IsFiniteTypeOverBase := fun _ hU =>
  finiteType_sectionRingBaseMap (isProper_of_isProjectiveMorphism π hπ) hDC hfree A hU
    (isNagataRing_of_isVariety hZ hU)

section RelativeAmpleTwist

open TopologicalSpace AlgebraicGeometry.ProjectiveSpectrum.Proj

section Absolute

universe w

variable {A : Type w} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- On a quasi-compact `Proj 𝒜` some positive degree has its standard opens covering. -/
private theorem exists_pos_degreeOpen_eq_top_of_compactSpace
    [CompactSpace (AlgebraicGeometry.Proj 𝒜)] :
    ∃ d : ℕ, 0 < d ∧ AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤ := by
  have hcompact : IsCompact ((⊤ : (AlgebraicGeometry.Proj 𝒜).Opens) :
      Set (AlgebraicGeometry.Proj 𝒜)) := by
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  obtain ⟨d, hd, s, hs, hcover⟩ :=
    AlgebraicGeometry.Proj.exists_common_degree_finite_basicOpen_cover 𝒜 ⊤ hcompact
  refine ⟨d, hd, top_le_iff.mp fun x _ => ?_⟩
  have hx : x ∈ ⨆ f ∈ s, AlgebraicGeometry.Proj.basicOpen 𝒜 f ⊓
      (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens) := hcover ▸ trivial
  obtain ⟨f, hf⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨hfs, hxf⟩ := TopologicalSpace.Opens.mem_iSup.mp hf
  exact AlgebraicGeometry.Proj.basicOpen_le_degreeOpen 𝒜 (hs f hfs)
    (TopologicalSpace.Opens.mem_inf.mp hxf).1

/-- The covering condition passes to positive multiples of the degree. -/
private theorem degreeOpen_eq_top_of_dvd {d d' : ℕ} (hdvd : d ∣ d') (hd' : 0 < d')
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    AlgebraicGeometry.Proj.degreeOpen 𝒜 d' = ⊤ :=
  top_le_iff.mp (htop ▸ AlgebraicGeometry.Proj.degreeOpen_le_of_dvd 𝒜 hdvd hd')

private theorem ratioLocus_eq_top_of_degreeOpen_eq_top {d : ℕ}
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒜 d = ⊤ :=
  top_le_iff.mp (htop ▸
    Stacks.AlgebraicGeometry.ProjDegreeOpenSections.degreeOpen_le_ratioLocus 𝒜 d)

/-- `𝒪(d)` is invertible when the degree-`d` standard opens cover `Proj 𝒜`. -/
private theorem isInvertibleModule_twistingSheaf_of_degreeOpen {d : ℕ}
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.isInvertibleModule_of_forall_exists_restrict_isoUnit
    _
    fun x => Stacks.AlgebraicGeometry.TwistMapsInvertible.exists_mem_restrict_isoUnit_twistingSheaf
      𝒜 (d := d) (n := 1) (c := (d : ℤ)) (one_mul _)
      ((ratioLocus_eq_top_of_degreeOpen_eq_top 𝒜 htop).ge (TopologicalSpace.Opens.mem_top x))

private theorem isInvertible_twistingSheaf_of_degreeOpen {d : ℕ}
    (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj 𝒜).toRingedSpace.presheaf
      (structureSheafRing (AlgebraicGeometry.Proj 𝒜).toRingedSpace).property
      (twistingSheaf 𝒜 (d : ℤ)) := by
  have h :=
    Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_ratioLocus_eq_top
    𝒜 (ratioLocus_eq_top_of_degreeOpen_eq_top 𝒜 htop) 1
  rwa [mul_one] at h

private theorem mem_nonvanishingLocus_degreeSection_iff_of_eq {d k : ℕ} (hk : k = 1 * d)
    (f : 𝒜 k) {x : ProjectiveSpectrum.top 𝒜}
    (hx : x ∈ Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible 𝒜 d) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus
        (X := (AlgebraicGeometry.Proj 𝒜).toRingedSpace) (twistingSheaf 𝒜 (k : ℤ))
        (Stacks.SheafOfModules.sectionsOfTop _ (degreeSection 𝒜 k f)) ↔
      x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) := by
  subst hk
  exact Stacks.AlgebraicGeometry.ProjInvertibleLocus.mem_nonvanishingLocus_degreeSection_iff
    𝒜 d 1 f hx

/-- `𝒪(d)` is ample on a quasi-compact `Proj 𝒜` when `d > 0` and the degree-`d` standard opens
cover. -/
private theorem isAmple_twistingSheaf_of_degreeOpen [CompactSpace (AlgebraicGeometry.Proj 𝒜)]
    {d : ℕ} (hd : 0 < d) (htop : AlgebraicGeometry.Proj.degreeOpen 𝒜 d = ⊤) :
    letI := isInvertibleModule_twistingSheaf_of_degreeOpen 𝒜 htop
    Stacks.Ample.IsAmple (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 (d : ℤ)) := by
  let _ := isInvertibleModule_twistingSheaf_of_degreeOpen 𝒜 htop
  refine (Stacks.AmpleBridge.isAmple_iff_isAmple _
    (Stacks.ProjTwistSection.twistingModule 𝒜 (d : ℤ))).mpr ?_
  let _ := isInvertible_twistingSheaf_of_degreeOpen 𝒜 htop
  let _ : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj 𝒜).toRingedSpace.presheaf
      (structureSheafRing (AlgebraicGeometry.Proj 𝒜).toRingedSpace).property
      (twistingSheaf 𝒜 (d : ℤ)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr inferInstance
  refine AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_exists_affine_nonvanishingOpen
    _ _ inferInstance fun x => ?_
  obtain ⟨g, hxg⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (htop ▸ TopologicalSpace.Opens.mem_top x :
      x ∈ AlgebraicGeometry.Proj.degreeOpen 𝒜 d)
  have key : Stacks.SheafOfModules.nonvanishingOpen
        (X := (AlgebraicGeometry.Proj 𝒜).toRingedSpace)
        (twistingSheaf 𝒜 (d : ℤ)) (Stacks.ProjTwistSection.homogeneousSection 𝒜 (g : A) g.2)
      = AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) := by
    ext y
    exact mem_nonvanishingLocus_degreeSection_iff_of_eq 𝒜 (one_mul d).symm g
      (Stacks.AlgebraicGeometry.ProjDegreeOpenSections.degreeOpen_le_whereInvertible 𝒜 d
        (htop ▸ TopologicalSpace.Opens.mem_top y))
  exact ⟨Stacks.ProjTwistSection.homogeneousSection 𝒜 (g : A) g.2, key.ge hxg,
    Eq.mp (congrArg (IsAffineOpen (X := AlgebraicGeometry.Proj 𝒜)) key).symm
      (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (g : A) g.2 hd)⟩

end Absolute

section Relative

open Stacks.RelativeProj Stacks.RelativeProj.Situation

/-- Each chart of a relative `Proj` of a finite type algebra is quasi-compact. -/
private theorem compactSpace_proj_sectionRingGrading (s : Stacks.RelativeProj.Situation.{0})
    (h₀ : SheafOfModules.IsFiniteType (s.algebra.piece 0)) (hb : s.IsFiniteTypeOverBase)
    (W : s.base.affineOpens) :
    CompactSpace (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)) := by
  have hdz := ((isFiniteType_and_isFiniteTypeOverDegreeZero_iff (s := s)).mpr ⟨h₀, hb⟩).2
  have := hdz W.1 W.2
  exact (quasiCompact_iff_compactSpace (AlgebraicGeometry.Proj.toSpecZero _)).mp inferInstance

/-- Over a quasi-compact base there are a finite cover by affine opens and a common positive
degree whose standard opens cover every chart of the cover. -/
private theorem exists_finset_affineOpens_degreeOpen_eq_top
    (s : Stacks.RelativeProj.Situation.{0}) [CompactSpace s.base]
    (hc : ∀ W : s.base.affineOpens,
      CompactSpace (AlgebraicGeometry.Proj (s.sectionRingGrading W.1))) :
    ∃ d : ℕ, 0 < d ∧ ∃ ι : Finset s.base.affineOpens, (∀ x : s.base, ∃ W ∈ ι, x ∈ W.1) ∧
      ∀ W ∈ ι, AlgebraicGeometry.Proj.degreeOpen (s.sectionRingGrading W.1) d = ⊤ := by
  classical
  obtain ⟨ι, hι⟩ := isCompact_univ.elim_finite_subcover
    (fun W : s.base.affineOpens => ((W.1 : s.base.Opens) : Set s.base))
    (fun W => W.1.isOpen) (fun x _ => by
      obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
        (X := s.base) (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  choose e he htop using fun W : s.base.affineOpens =>
    have := hc W; exists_pos_degreeOpen_eq_top_of_compactSpace (s.sectionRingGrading W.1)
  refine ⟨∏ W ∈ ι, e W, Finset.prod_pos fun W _ => he W, ι, fun x => ?_, fun W hW => ?_⟩
  · exact (Set.mem_iUnion₂.mp (hι (Set.mem_univ x))).imp fun _ ⟨hW, hxW⟩ => ⟨hW, hxW⟩
  · exact degreeOpen_eq_top_of_dvd _ (Finset.dvd_prod_of_mem e hW)
      (Finset.prod_pos fun W _ => he W) (htop W)

/-- The twisting sheaf `𝒪(d)` of a relative `Proj` is invertible when the degree-`d` standard
opens cover the charts of an affine cover of the base. -/
private theorem isInvertibleModule_twistSheaf_of_cover (s : Stacks.RelativeProj.Situation.{0})
    {d : ℕ} {ι : Finset s.base.affineOpens} (hcov : ∀ x : s.base, ∃ W ∈ ι, x ∈ W.1)
    (htop : ∀ W ∈ ι, AlgebraicGeometry.Proj.degreeOpen (s.sectionRingGrading W.1) d = ⊤) :
    Stacks.Ample.IsInvertibleModule s.relativeProj (twistSheaf s (d : ℤ)) := by
  open Stacks.AlgebraicGeometry.TwistMapsInvertible in
  refine isInvertibleModule_of_forall_exists_isoUnit_openImmersion _ fun x => ?_
  obtain ⟨W, hWι, hxW⟩ := hcov ((relativeProjToBase s).base x)
  have hmem : x ∈ (relativeProjChart s W).opensRange := by
    rwa [← relativeProjToBase_preimage_eq_opensRange s W]
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨U, hyU, ⟨eU⟩⟩ :=
    Stacks.AlgebraicGeometry.TwistMapsInvertible.exists_mem_restrict_isoUnit_twistingSheaf
      (s.sectionRingGrading W.1) (d := d) (n := 1) (c := (d : ℤ)) (one_mul _)
      ((ratioLocus_eq_top_of_degreeOpen_eq_top _ (htop W hWι)).ge
        (TopologicalSpace.Opens.mem_top y))
  refine ⟨U.toScheme, U.ι ≫ relativeProjChart s W, inferInstance, ⟨⟨y, hyU⟩, hy⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorComp U.ι (relativeProjChart s W)).app
      (twistSheaf s (d : ℤ)) ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (twistSheafChartIso s (d : ℤ) W) ≪≫ eU

/-- **The relative `Proj` of a finite type quasi-coherent graded algebra over a quasi-compact
base carries a relatively ample invertible module.** -/
private theorem exists_isRelativelyAmple_relativeProjToBase (s : Stacks.RelativeProj.Situation.{0})
    [CompactSpace s.base] (h₀ : SheafOfModules.IsFiniteType (s.algebra.piece 0))
    (hb : s.IsFiniteTypeOverBase) :
    ∃ (L : s.relativeProj.Modules) (hL : Stacks.Ample.IsInvertibleModule s.relativeProj L),
      letI : Stacks.Ample.IsInvertibleModule s.relativeProj L := hL
      Stacks.RelativeAmple.IsRelativelyAmple s.relativeProjToBase L := by
  have hc := compactSpace_proj_sectionRingGrading s h₀ hb
  obtain ⟨d, hd, ι, hcov, htop⟩ := exists_finset_affineOpens_degreeOpen_eq_top s hc
  have hL := isInvertibleModule_twistSheaf_of_cover s hcov htop
  refine ⟨twistSheaf s (d : ℤ), hL, ?_⟩
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple _ _
    (quasiCompact_relativeProjToBase s hc) fun x => ?_
  obtain ⟨W, hWι, hxW⟩ := hcov x
  refine ⟨W.1, W.2, hxW, ?_⟩
  set c := relativeProjChart s W with hc'
  set V := relativeProjToBase s ⁻¹ᵁ W.1
  have hrange : Set.range c.base = Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι, hc']
    exact congrArg (fun U : s.relativeProj.Opens => (U : Set s.relativeProj))
      (relativeProjToBase_preimage_eq_opensRange s W).symm
  set φ := IsOpenImmersion.isoOfRangeEq c V.ι hrange
  have hfac : φ.hom ≫ V.ι = c := IsOpenImmersion.isoOfRangeEq_hom_fac c V.ι hrange
  have hfac' : φ.inv ≫ c = V.ι := (Iso.inv_comp_eq φ).mpr hfac.symm
  have := hc W
  have hinvC := isInvertibleModule_twistingSheaf_of_degreeOpen _ (htop W hWι)
  have hinvP : Stacks.Ample.IsInvertibleModule V.toScheme
      ((Scheme.Modules.pullback φ.inv).obj
        (twistingSheaf (s.sectionRingGrading W.1) (d : ℤ))) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback φ.inv.toLRSHom.toShHom _
  have hinvQ : Stacks.Ample.IsInvertibleModule V.toScheme
      ((Scheme.Modules.pullback V.ι).obj (twistSheaf s (d : ℤ))) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback V.ι.toLRSHom.toShHom _
  have hA := Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion φ.inv
    (twistingSheaf (s.sectionRingGrading W.1) (d : ℤ))
    (isAmple_twistingSheaf_of_degreeOpen _ hd (htop W hWι))
  have e₁ : (Scheme.Modules.pullback c).obj (twistSheaf s (d : ℤ)) ≅
      twistingSheaf (s.sectionRingGrading W.1) (d : ℤ) :=
    ((Scheme.Modules.restrictFunctorIsoPullback c).app (twistSheaf s (d : ℤ))).symm ≪≫
      twistSheafChartIso s (d : ℤ) W
  have e := (Scheme.Modules.pullback φ.inv).mapIso e₁.symm ≪≫
    (Scheme.Modules.pullbackComp φ.inv c).app (twistSheaf s (d : ℤ)) ≪≫
    (Scheme.Modules.pullbackCongr hfac').app (twistSheaf s (d : ℤ))
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp hA

end Relative

end RelativeAmpleTwist

/-- **The relative `Proj` of the section algebra of a relatively free Cartier divisor along a
projective morphism to a projective variety is H-projective.** -/
private theorem isProjectiveMorphism_toBase {M Z : Scheme.{0}} [IsIntegral M] [CompactSpace M]
    [IsLocallyNoetherian M] [IsNormal M] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {π : M ⟶ Z} (hπ : IsProjectiveMorphism π)
    {D : Divisor M} (hDC : D.IsCartier) (hfree : IsRelativelyFreeDivisor π D)
    (A : DivisorialSectionAlgebra π D) : IsProjectiveMorphism A.toBase := by
  have := isLocallyNoetherian_of_isProjectiveVariety hZ
  have hπ' : IsProper π := isProper_of_isProjectiveMorphism π hπ
  have : CompactSpace Z := by
    have := hZ.toIsVariety
    have : IsProper sZ := isProper_of_isProjectiveMorphism sZ hZ.isProjective
    exact (quasiCompact_iff_compactSpace sZ).mp inferInstance
  have hb := isFiniteTypeOverBase_situation hZ hπ hDC hfree A
  exact isProjectiveMorphism_of_isRelativelyAmple hZ A.toBase
    (isProper_toBase A hπ' hDC hb)
    (exists_isRelativelyAmple_relativeProjToBase A.situation
      (isFiniteType_piece A hπ' hDC 0 le_rfl) hb)

/-- A morphism which is an open immersion on a dense open, with dense image, is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {V Z : Scheme.{u}} (p : V ⟶ Z)
    (W : V.Opens) (hW : Dense (W : Set V)) [IsOpenImmersion (W.ι ≫ p)]
    (hW' : Dense (Set.range (W.ι ≫ p))) : IsBirationalMorphism p := by
  refine ⟨⟨W, hW, (W.ι ≫ p).opensRange,
    by rwa [Scheme.Hom.coe_opensRange], (W.ι ≫ p).isoOpensRange⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨W, hW, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, Scheme.Hom.isoOpensRange_hom_ι]
  rw [Scheme.topIso_hom]
  change V.homOfLE (le_refl W) ≫ W.ι ≫ p = V.homOfLE (le_top : W ≤ ⊤) ≫ (⊤ : V.Opens).ι ≫ p
  rw [Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]

/-- If `u ≫ p` is an open immersion for a dominant `u : U ⟶ V` into a reduced scheme and `p` is
separated, then `p` is an isomorphism over the image `O` of `u ≫ p`. -/
private theorem isIso_morphismRestrict {U V Z : Scheme.{u}} [IsReduced V] (p : V ⟶ Z)
    [IsSeparated p] (u : U ⟶ V) [IsOpenImmersion (u ≫ p)] [IsDominant u] :
    IsIso (p ∣_ (u ≫ p).opensRange) := by
  set O := (u ≫ p).opensRange
  let σ := (u ≫ p).isoOpensRange
  have hu : Set.range u ⊆ Set.range (p ⁻¹ᵁ O).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  let u' : U ⟶ p ⁻¹ᵁ O := IsOpenImmersion.lift (p ⁻¹ᵁ O).ι u hu
  have hu' : u' ≫ (p ⁻¹ᵁ O).ι = u := IsOpenImmersion.lift_fac _ _ _
  have h1 : u' ≫ p ∣_ O = σ.hom := by
    rw [← cancel_mono O.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hu']
    exact (Scheme.Hom.isoOpensRange_hom_ι _).symm
  have : IsDominant u' := by
    have : IsDominant (u' ≫ (p ⁻¹ᵁ O).ι) := by rw [hu']; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion u' (p ⁻¹ᵁ O).ι
  let s' := σ.inv ≫ u'
  have h2 : s' ≫ p ∣_ O = 𝟙 _ := by simp [s', h1]
  refine ⟨s', ?_, h2⟩
  refine ext_of_isDominant_of_isSeparated (p ∣_ O)
    (by rw [Category.assoc, h2, Category.comp_id, Category.id_comp]) u' ?_
  simp [s', reassoc_of% h1]

/-- If `u ≫ p` is an open immersion for a dominant `u : U ⟶ V` from a nonempty scheme into a
reduced scheme, `p` is separated and `Z` is irreducible, then `p` is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {U V Z : Scheme.{u}} [Nonempty U]
    [IsReduced V] [IrreducibleSpace Z] (p : V ⟶ Z) [IsSeparated p] (u : U ⟶ V)
    [IsOpenImmersion (u ≫ p)] [IsDominant u] : IsBirationalMorphism p := by
  have := isIso_morphismRestrict p u
  have hsub : Set.range u ⊆ (p ⁻¹ᵁ (u ≫ p).opensRange : Set V) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  have : IsOpenImmersion ((p ⁻¹ᵁ (u ≫ p).opensRange).ι ≫ p) := by
    rw [← morphismRestrict_ι]; infer_instance
  refine isBirationalMorphism_of_isOpenImmersion p _ (u.denseRange.mono hsub) ?_
  obtain ⟨t⟩ := ‹Nonempty U›
  refine ((u ≫ p).isOpenEmbedding.isOpenMap.isOpen_range.dense ⟨_, t, rfl⟩).mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨⟨u t, hsub ⟨t, rfl⟩⟩, rfl⟩

/-- If `f : X ⟶ Z` is birational and `φ : X ⤏ M` is a birational map with `π ∘ φ = f`, then some
nonempty open subscheme of `M` maps to `Z` by an open immersion. -/
private theorem exists_isOpenImmersion_comp {X M Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Z} (hf : IsBirationalMorphism f) {φ : X.RationalMap M}
    (hφ : RationalMap.IsBirational φ) {π : M ⟶ Z} (hover : φ.compHom π = f.toRationalMap) :
    ∃ (T : Scheme.{u}) (g : T ⟶ M), Nonempty T ∧ IsOpenImmersion g ∧
      IsOpenImmersion (g ≫ π) := by
  have : Nonempty X := IrreducibleSpace.toNonempty
  obtain ⟨W₁, hW₁, hW₁f⟩ := hf.exists_isOpenImmersion
  obtain ⟨eφ, rfl⟩ := hφ
  rw [Scheme.PartialIso.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at hover
  obtain ⟨W, hW, hWe, _, hWf⟩ := hover
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.compHom_hom,
    Scheme.PartialIso.toPartialMap_hom, Scheme.Hom.toPartialMap_hom] at hWf
  have hne : ((W ⊓ W₁ : X.Opens) : Set X).Nonempty := by
    simpa [Set.inter_comm] using hW.inter_open_nonempty _ W₁.isOpen hW₁
  have hWe' : W ≤ eφ.source := hWe
  refine ⟨(W ⊓ W₁ : X.Opens), X.homOfLE (inf_le_left.trans hWe') ≫ eφ.iso.hom ≫ eφ.target.ι,
    ⟨⟨_, hne.some_mem⟩⟩, inferInstance, ?_⟩
  have : (X.homOfLE (inf_le_left.trans hWe') ≫ eφ.iso.hom ≫ eφ.target.ι) ≫ π =
      X.homOfLE (inf_le_right : W ⊓ W₁ ≤ W₁) ≫ W₁.ι ≫ f := by
    calc _ = X.homOfLE (inf_le_left : W ⊓ W₁ ≤ W) ≫ X.homOfLE hWe' ≫
          (eφ.iso.hom ≫ eφ.target.ι) ≫ π := by
            simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
      _ = X.homOfLE (inf_le_left : W ⊓ W₁ ≤ W) ≫ X.homOfLE (le_top : W ≤ ⊤) ≫
          X.topIso.hom ≫ f := by
            rw [← Category.assoc (X.homOfLE hWe')]; exact congrArg (X.homOfLE _ ≫ ·) hWf
      _ = _ := by
            rw [Scheme.topIso_hom, Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_ι_assoc,
              Scheme.homOfLE_ι_assoc]
  rw [this]
  infer_instance

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {X Z M V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]

/-- The structure morphism `p : V ⟶ Z` of an ample-model datum `(M, B_M, q, V, B_V)` of a
birational contraction `f : X ⟶ Z` is projective and birational. -/
@[mmp "lem_oai4_c3_ample_model_birational"]
public theorem IsAmpleModelDatum.isProjectiveMorphism_and_isBirationalMorphism
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV) :
    IsProjectiveMorphism p ∧ IsBirationalMorphism p := by
  obtain ⟨k, hk, D, hD, hDC, hfree, A, e, he, hind⟩ := h.isRelativeAmpleModel
  have hproj : IsProjectiveMorphism p := by
    rw [← he]
    exact isProjectiveMorphism_iso_comp e
      (isProjectiveMorphism_toBase h.isProjectiveVariety_target
        h.isGoodLogMinimalModel.isProjectiveMorphism_model hDC hfree A)
  refine ⟨hproj, ?_⟩
  have hqp : q ≫ p = πM := by
    have := hind.comp_toBase
    rwa [Category.assoc, he] at this
  have : IsReduced A.model := isReduced_model A
  have : IsReduced V := isReduced_of_isOpenImmersion e.hom
  have : IsDominant (q ≫ e.hom) := isDominant_of_isInducedMorphism A hind
    fun _ _ _ a ha => generatingLocus_nonempty A _ a ha
  have : IsDominant q := by
    have : IsDominant ((q ≫ e.hom) ≫ e.inv) := inferInstance
    simpa using this
  have : IsProper p := isProper_of_isProjectiveMorphism p hproj
  have : IrreducibleSpace Z :=
    Function.Surjective.irreducibleSpace f.continuous h.isContraction.surjective
  obtain ⟨T, g, ⟨t⟩, hg, hgπ⟩ := exists_isOpenImmersion_comp h.isBirationalMorphism
    h.isGoodLogMinimalModel.isBirational h.isGoodLogMinimalModel.isOver
  have : Nonempty T := ⟨t⟩
  have : IsOpenImmersion ((g ≫ q) ≫ p) := by simpa [hqp] using hgπ
  have : IsDominant g := ⟨g.isOpenEmbedding.isOpenMap.isOpen_range.dense ⟨g t, t, rfl⟩⟩
  exact isBirationalMorphism_of_isOpenImmersion_comp p (g ≫ q)

end

end MMP.Fourfold

end
