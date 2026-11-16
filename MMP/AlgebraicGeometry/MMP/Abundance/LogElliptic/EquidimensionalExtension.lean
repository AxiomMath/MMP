module
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries

/-!
# The extended fibration is a log elliptic fiber space

Let `(X, Δ_X)` satisfy the assumptions of FA 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`),
with `f_U : U ⟶ Z` a log elliptic fiber space on a nonempty open `U ⊆ X` as in (15.4.3), and
suppose that no prime divisor of `X` is `(K_X + Δ_X)`-trivially connected. Let `f : X ⟶ Z̄` be
an extension of `f_U` as produced by
`MMP.Flips.exists_extension_of_forall_not_isTriviallyConnected`: `Z̄` is a normal projective
surface containing a nonempty open `Z₀ ⊆ Z`, `f_* 𝒪_X = 𝒪_{Z̄}`, all fibres of `f` are connected
of pure dimension one, and `f = f_U` on `f_U⁻¹(Z₀)`. Then `f : (X, Δ_X) ⟶ Z̄` is itself a log
elliptic fiber space: its generic fiber is that of `f_U`, an irreducible curve on which
`K_X + Δ_X` has degree zero.

The proof: since `f_U⁻¹(Z₀) ⟶ Z₀` is proper, the image of `f_U⁻¹(Z₀)` in `f⁻¹(Z₀)` is open and
closed, so `f⁻¹(Z₀) = f_U⁻¹(Z₀)`. Hence the generic fibre of `f` is that of `f_U`, and the degree
of `K_X + Δ_X` on it is the degree of `K_U + Δ_X|_U` on the generic fibre of `f_U`, which is zero.

## Main results

* `MMP.Flips.isLogEllipticFiberSpace_of_forall_not_isTriviallyConnected`: `f` is a log elliptic
  fiber space.

## Implementation notes

As for `MMP.Flips.exists_extension_of_forall_not_isTriviallyConnected`, the source's `ℂ` is
replaced by an algebraically closed field `k` of characteristic zero, the inclusion `Z₀ ⊆ Z̄` is
an open immersion `j : Z₀ ⟶ Z̄` over `k`, and `f = f_U` on `f_U⁻¹(Z₀)` is an equality of
morphisms `f_U⁻¹(Z₀) ⟶ Z̄`. The data of the conclusion of that theorem are taken as hypotheses.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.13
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Flips

open MMP.Mori

/-- The residue degree of a composite is that of the second map when the first induces an
isomorphism of residue fields. -/
private theorem residueDegree_comp_of_isIso_left {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) [IsIso (f.residueFieldMap x)] :
    (f ≫ g).residueDegree x = g.residueDegree (f x) := by
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  letI := (g.residueFieldMap (f x)).hom.toAlgebra
  refine (Algebra.finrank_eq_of_equiv_equiv (R₀ := Z.residueField (g (f x)))
    (S₀ := Y.residueField (f x)) (R₁ := Z.residueField (g (f x))) (S₁ := X.residueField x)
    (RingEquiv.refl _) (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv ?_).symm
  ext a
  change ((f ≫ g).residueFieldMap x) a = f.residueFieldMap x (g.residueFieldMap (f x) a)
  rw [Scheme.residueFieldMap_comp]
  rfl

/-- The residue degree of a composite is that of the first map when the second induces an
isomorphism of residue fields. -/
private theorem residueDegree_comp_of_isIso_right {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) [IsIso (g.residueFieldMap (f x))] :
    (f ≫ g).residueDegree x = f.residueDegree x := by
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (R₀ := Z.residueField (g (f x)))
    (S₀ := X.residueField x) (R₁ := Y.residueField (f x)) (S₁ := X.residueField x)
    (asIso (g.residueFieldMap (f x))).commRingCatIsoToRingEquiv (RingEquiv.refl _) ?_
  ext a
  change f.residueFieldMap x (g.residueFieldMap (f x) a) = ((f ≫ g).residueFieldMap x) a
  rw [Scheme.residueFieldMap_comp]
  rfl

/-- A morphism to an integral scheme all of whose maps on sections are isomorphisms is
dominant: over an open set missing its image, the sections upstairs vanish. -/
private theorem isDominant_of_forall_isIso_app {V W : Scheme.{u}} (g : V ⟶ W) [IsIntegral W]
    (hg : ∀ U : W.Opens, IsIso (g.app U)) : IsDominant g := by
  constructor
  by_contra hd
  rw [DenseRange, dense_iff_closure_eq] at hd
  let U' : W.Opens := ⟨(closure (Set.range g))ᶜ, isClosed_closure.isOpen_compl⟩
  have hbot : g ⁻¹ᵁ U' = ⊥ := by
    ext x
    exact iff_of_false (fun hx => hx (subset_closure ⟨x, rfl⟩)) id
  have : Nonempty U' := (Set.nonempty_compl.mpr hd).to_subtype
  have : Subsingleton Γ(V, g ⁻¹ᵁ U') := by rw [hbot]; infer_instance
  exact not_subsingleton Γ(W, U')
    (asIso (g.app U')).commRingCatIsoToRingEquiv.injective.subsingleton

/-- A proper morphism to an integral scheme all of whose maps on sections are isomorphisms is
surjective. -/
private theorem surjective_of_forall_isIso_app {V W : Scheme.{u}} (g : V ⟶ W) [IsIntegral W]
    [IsProper g] (hg : ∀ U : W.Opens, IsIso (g.app U)) : Function.Surjective g :=
  have := isDominant_of_forall_isIso_app g hg
  g.surjective

/-- If `a ≫ f = g ≫ j` with `a` and `j` open immersions, then `f` and `g` have the same residue
degree at corresponding points. -/
private theorem residueDegree_eq_of_comp_eq {W X Y Z : Scheme.{u}} (a : W ⟶ X)
    [IsOpenImmersion a] (f : X ⟶ Y) (g : W ⟶ Z) (j : Z ⟶ Y) [IsOpenImmersion j]
    (h : a ≫ f = g ≫ j) (w : W) : f.residueDegree (a w) = g.residueDegree w := by
  rw [← residueDegree_comp_of_isIso_left a f w, h, residueDegree_comp_of_isIso_right]

/-- Let `a : W ⟶ X` be an open immersion of a nonempty scheme into an integral one, and suppose
`a ≫ f = g ≫ j` with `f` separated, `g` proper and `j` an open immersion. Then
`f⁻¹(j(Z)) ⊆ a(W)`: the factorisation of `a` through `f⁻¹(j(Z))` is an open immersion and proper,
so its image is clopen in the irreducible scheme `f⁻¹(j(Z))`, hence everything. -/
private theorem preimage_range_subset_range_of_comp_eq {W X Y Z : Scheme.{u}} [IsIntegral X]
    [Nonempty W] (a : W ⟶ X) [IsOpenImmersion a] (f : X ⟶ Y) [IsSeparated f] (g : W ⟶ Z)
    [IsProper g] (j : Z ⟶ Y) [IsOpenImmersion j] (h : a ≫ f = g ≫ j) :
    f ⁻¹' Set.range j ⊆ Set.range a := by
  let V := f ⁻¹ᵁ j.opensRange
  have ha : Set.range a ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (a ≫ f) w ∈ j.opensRange
    rw [h]
    exact ⟨_, rfl⟩
  let a' := IsOpenImmersion.lift V.ι a ha
  have ha' : a' ≫ V.ι = a := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (a' ≫ V.ι) := by rw [ha']; infer_instance
  haveI : IsOpenImmersion a' := IsOpenImmersion.of_comp a' V.ι
  have hcomp : a' ≫ (f ∣_ j.opensRange) = g ≫ j.isoOpensRange.hom := by
    rw [← cancel_mono j.opensRange.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.isoOpensRange_hom_ι]
    rw [← Category.assoc, ha', h]
  haveI : IsProper (a' ≫ (f ∣_ j.opensRange)) := by rw [hcomp]; infer_instance
  haveI : IsProper a' := IsProper.of_comp a' (f ∣_ j.opensRange)
  haveI : Nonempty V := ⟨a' (Classical.arbitrary W)⟩
  have huniv : Set.range a' = Set.univ :=
    IsClopen.eq_univ ⟨a'.isClosedMap.isClosed_range, a'.isOpenEmbedding.isOpen_range⟩
      (Set.range_nonempty _)
  intro y hy
  obtain ⟨w, hw⟩ := huniv.ge (Set.mem_univ (⟨y, hy⟩ : V))
  exact ⟨w, by rw [← ha', Scheme.Hom.comp_apply, hw]; rfl⟩

section Restrict

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (U : X.Opens)

/-- At the generic point of a prime divisor `E`, the stalk of the ideal of `E` is the maximal
ideal of the local ring. -/
private theorem stalkIdeal_idealSheaf_eq_maximalIdeal (E : Mori.PrimeDivisor X) {y : X}
    (hy : y = E.genericPoint) :
    E.idealSheaf.stalkIdeal y = IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  subst hy
  rw [← MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf]
  have := Stacks.Chow.stalkIdeal_vanishingIdeal_closure_fromSpecStalk E.genericPoint
    (IsLocalRing.closedPoint _)
  rwa [Scheme.fromSpecStalk_closedPoint] at this

open Classical in
/-- Along an open immersion, the local intersection length of a prime divisor `E` of `X` along a
prime divisor `P` of `U` is `1` if `E` is the closure of `P` and `0` otherwise. -/
private theorem intersectionLength_ι (E : Mori.PrimeDivisor X) (P : Mori.PrimeDivisor U) :
    E.intersectionLength U.ι P =
      if E = OpenWeilRestriction.primeDivisorMap U.ι P then 1 else 0 := by
  split_ifs with hE
  · have hy : U.ι P.genericPoint = E.genericPoint := by
      rw [hE]
      exact (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm
    have hiso : IsIso (U.ι.stalkMap P.genericPoint) :=
      inferInstanceAs <| IsIso (U.ι.toLRSHom.stalkMap P.genericPoint)
    rw [PrimeDivisor.intersectionLength, stalkIdeal_idealSheaf_eq_maximalIdeal E hy,
      IsLocalRing.map_maximalIdeal_of_surjective _
        (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap P.genericPoint)).2]
    have : IsSimpleModule (U.toScheme.presheaf.stalk P.genericPoint)
        (U.toScheme.presheaf.stalk P.genericPoint ⧸
          IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk P.genericPoint)) :=
      isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal _).out
    rw [Module.length_eq_one]
    rfl
  · refine PrimeDivisor.intersectionLength_eq_zero_of_notMem U.ι E fun hmem => hE ?_
    have hco : Order.coheight (U.ι P.genericPoint) = 1 := by
      rw [← OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P]
      exact Mori.PrimeDivisor.coheight_genericPoint _
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((PrimeDivisor.eq_genericPoint_of_mem_support E hmem hco).symm.trans
        (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm)

/-- Along an open immersion `U ⟶ X`, the restriction of a divisor (`DivisorWithCoeffs.restrict`)
is its restriction by coefficients (`DivisorWithCoeffs.restrictOpen`). -/
private theorem restrict_ι_eq_restrictOpen {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : D.restrict U.ι = D.restrictOpen U := by
  classical
  have hc : ∀ P, DivisorWithCoeffs.restrictCoeff U.ι D P =
      D.coeff (OpenWeilRestriction.primeDivisorMap U.ι P) := by
    intro P
    simp only [DivisorWithCoeffs.restrictCoeff, intersectionLength_ι, ite_smul, one_smul,
      zero_smul, Finsupp.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h).symm
  have hfin : (Function.support (DivisorWithCoeffs.restrictCoeff U.ι D)).Finite := by
    refine (D.support.finite_toSet.preimage
      (OpenWeilRestriction.primeDivisorMap_injective U.ι).injOn).subset fun P hP => ?_
    rw [Function.mem_support, hc] at hP
    exact Finsupp.mem_support_iff.mpr hP
  ext P
  change (D.restrict U.ι).coeff P = (D.restrictOpen U).coeff P
  rw [DivisorWithCoeffs.coeff_restrict U.ι hfin, DivisorWithCoeffs.coeff_restrictOpen]
  exact hc P

/-- If `f : X ⟶ Ȳ` agrees with `f_U : U ⟶ Z` over an open `Z₀ ⊆ Z` embedded in `Ȳ` by `j`, and
`f⁻¹(j(Z₀)) ⊆ f_U⁻¹(Z₀)`, then `f_U` and `f` have the same generic fibre point degrees along
corresponding prime divisors. -/
private theorem genericFiberPointDegree_eq_primeDivisorMap {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (fU : U.toScheme ⟶ Z) (Z₀ : Z.Opens) (j : Z₀.toScheme ⟶ Y)
    [IsOpenImmersion j] (f : X ⟶ Y) (hfj : (fU ⁻¹ᵁ Z₀).ι ≫ U.ι ≫ f = (fU ∣_ Z₀) ≫ j)
    (hηZ : genericPoint Z ∈ Z₀) (key : f ⁻¹' Set.range j ⊆ Set.range ((fU ⁻¹ᵁ Z₀).ι ≫ U.ι))
    (P : Mori.PrimeDivisor U) : genericFiberPointDegree fU P =
      genericFiberPointDegree f (OpenWeilRestriction.primeDivisorMap U.ι P) := by
  classical
  haveI : Nonempty Z₀.toScheme := ⟨⟨_, hηZ⟩⟩
  let W := fU ⁻¹ᵁ Z₀
  let a : W.toScheme ⟶ X := W.ι ≫ U.ι
  let g : W.toScheme ⟶ Z₀.toScheme := fU ∣_ Z₀
  have hag : a ≫ f = g ≫ j := by simpa [a, g] using hfj
  have hηZ₀ : Z₀.ι (genericPoint Z₀) = genericPoint Z := genericPoint_eq_of_isOpenImmersion _
  have hηj : j (genericPoint Z₀) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hpd : ∀ x : U, (if fU x = genericPoint Z then fU.residueDegree x else 0) =
      (if f (U.ι x) = genericPoint Y then f.residueDegree (U.ι x) else 0) := by
    intro x
    by_cases hx : fU x ∈ Z₀
    · let w : W.toScheme := ⟨x, hx⟩
      have hfx : f (U.ι x) = j (g w) := congrArg (fun φ : W.toScheme ⟶ Y => φ w) hag
      have hgx : Z₀.ι (g w) = fU x := morphismRestrict_base_coe fU Z₀ w
      have hiff : fU x = genericPoint Z ↔ f (U.ι x) = genericPoint Y := by
        rw [hfx, ← hηj, ← hgx, ← hηZ₀, Z₀.ι.isOpenEmbedding.injective.eq_iff,
          j.isOpenEmbedding.injective.eq_iff]
      have hdeg : f.residueDegree (U.ι x) = fU.residueDegree x :=
        (residueDegree_eq_of_comp_eq a f g j hag w).trans
          (residueDegree_eq_of_comp_eq W.ι fU g Z₀.ι (morphismRestrict_ι fU Z₀).symm w).symm
      simp only [hiff, hdeg]
    · have h1 : fU x ≠ genericPoint Z := fun he => hx (he ▸ hηZ)
      have h2 : f (U.ι x) ≠ genericPoint Y := fun he => by
        obtain ⟨w, hw⟩ := key ⟨_, hηj.trans he.symm⟩
        exact hx (U.ι.isOpenEmbedding.injective hw ▸ w.2)
      rw [if_neg h1, if_neg h2]
  have := hpd P.genericPoint
  rwa [← OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P] at this

/-- If `f_U : U ⟶ Z` and `f : X ⟶ Y` have the same generic fibre point degrees along
corresponding prime divisors, and every prime divisor of `X` of nonzero generic fibre point degree
meets `U`, then the degree of `D` on the generic fibre of `f` is that of `D|_U` on the generic
fibre of `f_U`. -/
private theorem genericFiberDegree_restrictOpen {Y Z : Scheme.{u}} [IrreducibleSpace Y]
    [IrreducibleSpace Z] (fU : U.toScheme ⟶ Z) (f : X ⟶ Y) (D : QDivisor X)
    (hgp : ∀ P : Mori.PrimeDivisor U, genericFiberPointDegree fU P =
      genericFiberPointDegree f (OpenWeilRestriction.primeDivisorMap U.ι P))
    (hrange : ∀ E : Mori.PrimeDivisor X, genericFiberPointDegree f E ≠ 0 →
      E ∈ Set.range (OpenWeilRestriction.primeDivisorMap U.ι)) :
    genericFiberDegree fU (D.restrictOpen U) = genericFiberDegree f D := by
  rw [genericFiberDegree, genericFiberDegree]
  refine Finset.sum_bij_ne_zero (fun P _ _ => OpenWeilRestriction.primeDivisorMap U.ι P)
    ?_ ?_ ?_ ?_
  · intro P hP _
    rwa [Finsupp.mem_support_iff] at hP ⊢
  · exact fun P₁ _ _ P₂ _ _ he => OpenWeilRestriction.primeDivisorMap_injective U.ι he
  · intro E hE hne
    obtain ⟨P, rfl⟩ := hrange E fun h0 => hne (by simp [h0])
    rw [Finsupp.mem_support_iff] at hE
    exact ⟨P, Finsupp.mem_support_iff.mpr hE, by rwa [← hgp] at hne, rfl⟩
  · intro P _ _
    rw [hgp]
    rfl

end Restrict

/-- The fibre over the generic point of a surjective morphism of integral schemes is
irreducible. -/
private theorem isIrreducible_preimage_genericPoint_of_surjective {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : Function.Surjective f) :
    IsIrreducible (f.base ⁻¹' {genericPoint Y}) := by
  have hcl : closure (f.base ⁻¹' {genericPoint Y}) = closure {genericPoint X} := by
    refine le_antisymm ?_ (closure_mono (Set.singleton_subset_iff.mpr
      (genericPoint_map_of_surjective f hf)))
    rw [(genericPoint_spec X).def]
    exact Set.subset_univ _
  exact isIrreducible_iff_closure.mp (hcl ▸ isIrreducible_singleton.closure)

/-- **The extended fibration is a log elliptic fiber space** (FA 15.13). In the situation of
`MMP.Flips.exists_extension_of_forall_not_isTriviallyConnected`, let `Z̄` be a normal projective
surface over `k`, `j : Z₀ ⟶ Z̄` an open immersion over `k` of a nonempty open `Z₀ ⊆ Z`, and
`f : X ⟶ Z̄` a morphism over `k` with `f_* 𝒪_X = 𝒪_{Z̄}` (`MMP.Flips.IsContraction`), all of
whose fibres are connected of pure dimension one, such that `f = f_U` on `f_U⁻¹(Z₀)`. Then
`f : (X, Δ_X) ⟶ Z̄` is a log elliptic fiber space (`MMP.Flips.IsLogEllipticFiberSpace`). -/
@[mmp "lem_fa15_equidimensional_fibration_is_log_elliptic"]
public theorem isLogEllipticFiberSpace_of_forall_not_isTriviallyConnected
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3 (DivisorWithCoeffs.restrict U.ι K)
      (DivisorWithCoeffs.restrict U.ι Δ) fU)
    (hD : ∀ D : Mori.PrimeDivisor X, ¬ IsTriviallyConnected k sX 3 K Δ (Finsupp.single D 1))
    {Zbar : Scheme.{u}} (sZbar : Zbar ⟶ Spec (.of k)) (Z₀ : Z.Opens)
    (j : Z₀.toScheme ⟶ Zbar) (f : X ⟶ Zbar)
    (hZbar : IsNormalVariety k sZbar) (hZbarp : Mori.IsProjectiveVariety k sZbar)
    (hZbard : topologicalKrullDim Zbar = 2) (hZ₀ : (Z₀ : Set Z).Nonempty) [IsOpenImmersion j]
    (hjs : j ≫ sZbar = Z₀.ι ≫ sZ) (hf : IsContraction k sZbar sX f)
    (hconn : ∀ z : Zbar, _root_.IsConnected (f.base ⁻¹' {z}))
    (hdim : ∀ z : Zbar, ∀ Y ∈ irreducibleComponents (f.base ⁻¹' {z}), topologicalKrullDim Y = 1)
    (hfj : (fU ⁻¹ᵁ Z₀).ι ≫ U.ι ≫ f = (fU ∣_ Z₀) ≫ j) :
    IsLogEllipticFiberSpace k sX sZbar 3 K Δ f := by
  haveI := hf.isVariety_target.toIsIntegral
  haveI := hfU.isContraction.isVariety_target.toIsIntegral
  haveI := hf.isProper
  haveI := hfU.isContraction.isProper
  have hsurj : Function.Surjective f := surjective_of_forall_isIso_app f hf.isIso_app
  obtain ⟨x₀, hx₀⟩ := surjective_of_forall_isIso_app fU hfU.isContraction.isIso_app (genericPoint Z)
  have hηZ : genericPoint Z ∈ Z₀ :=
    ((genericPoint_spec Z).mem_open_set_iff Z₀.isOpen).mpr (by simpa using hZ₀)
  let W := fU ⁻¹ᵁ Z₀
  let a : W.toScheme ⟶ X := W.ι ≫ U.ι
  let g : W.toScheme ⟶ Z₀.toScheme := fU ∣_ Z₀
  have hag : a ≫ f = g ≫ j := by simpa [a, g] using hfj
  haveI : Nonempty W.toScheme := ⟨⟨x₀, show fU x₀ ∈ Z₀ from hx₀ ▸ hηZ⟩⟩
  haveI : Nonempty Z₀.toScheme := ⟨⟨_, hηZ⟩⟩
  have key := preimage_range_subset_range_of_comp_eq a f g j hag
  have hrange : ∀ E : Mori.PrimeDivisor X, genericFiberPointDegree f E ≠ 0 →
      E ∈ Set.range (OpenWeilRestriction.primeDivisorMap U.ι) := fun E hpd0 => by
    have hfE : f E.genericPoint = genericPoint Zbar := by
      by_contra hc
      exact hpd0 (by simp [genericFiberPointDegree, hc])
    obtain ⟨w, hw⟩ := key ⟨_, (genericPoint_eq_of_isOpenImmersion j).trans hfE.symm⟩
    exact (OpenWeilRestriction.mem_range_primeDivisorMap_iff U.ι E).mpr ⟨W.ι w, hw⟩
  refine ⟨h.isKawamataLogTerminal.1, h.isKawamataLogTerminal.2.1, h.isQCartier, hf,
    isIrreducible_preimage_genericPoint_of_surjective f hsurj, ?_, ?_⟩
  · rw [← (f.fiberHomeo (genericPoint Zbar)).isHomeomorph.topologicalKrullDim_eq]
    have := hf.isVariety_target.toLocallyOfFiniteType
    have := hf.isVariety_target.toQuasiCompact
    have : CompactSpace Zbar := QuasiCompact.compactSpace_of_compactSpace sZbar
    exact topologicalKrullDim_genericFiber_eq_one sX sZbar f hf.comp_eq hsurj
      (by rw [h.dim_eq, hZbard]; rfl)
  · have hLU : Divisor.toQDivisor (DivisorWithCoeffs.restrict U.ι K) +
        DivisorWithCoeffs.restrict U.ι Δ = (Divisor.toQDivisor K + Δ).restrictOpen U := by
      rw [restrict_ι_eq_restrictOpen, restrict_ι_eq_restrictOpen]
      ext P
      rfl
    rw [← hfU.genericFiberDegree_eq_zero, hLU, genericFiberDegree_restrictOpen U fU f _
      (genericFiberPointDegree_eq_primeDivisorMap U fU Z₀ j f hfj hηZ key) hrange]

end MMP.Flips
