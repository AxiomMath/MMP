module

public import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
public import MMP.AlgebraicGeometry.Cohomology.LongExactDimensionBounds

/-!
# Exceptional cycles on the resolution of a surface germ

Let `f : Y ⟶ X` be a resolution of a normal surface germ `(X, P)` over an algebraically closed
field `k` of arbitrary characteristic, and let `Z = ∑ nᵢ Eᵢ` be a nonzero effective cycle on the
exceptional curves of `f`, viewed as the closed subscheme of `Y` with ideal sheaf
`𝒪_Y(-Z) = ∏ I_{Eᵢ}^{nᵢ}`. Then `Z` is proper over `k` and
`χ(Z, 𝒪_Z) = -½ (Z² + K_Y · Z)`,
where the intersection numbers are the algebraic degrees of `𝒪_Y(Z)` and `𝒪_Y(K_Y)` on the
(possibly nonreduced) scheme `Z`. As a consequence, if `χ(𝒪_{Z'}) > 0` for every nonzero
effective cycle `Z' ≤ Z`, then `H¹(Z, 𝒪_Z) = 0`.

The cycle formula is proved by induction on the cycle. For `Z = W + E`, with `E` a prime
divisor, the divisors are effective Cartier on the smooth surface `Y` and there is a short exact
sequence `0 ⟶ 𝒪_E(-W) ⟶ 𝒪_Z ⟶ 𝒪_W ⟶ 0`; additivity of the Euler characteristic gives
`χ(𝒪_Z) = χ(𝒪_W) - (W · E) + χ(𝒪_E)`, the same sequence twisted by an invertible sheaf shows that
the degree on `Z` is the sum of the degrees on `W` and on `E`, and adjunction
`(K_Y + E) · E = -2 χ(𝒪_E)` with the symmetry of the intersection numbers of two curves finishes
the induction step.

For the vanishing, positivity of `χ(𝒪_{Eᵢ}) = 1 - h¹(𝒪_{Eᵢ})` makes every component of genus
zero. Take a minimal cycle `Z'' ≤ Z` with `H¹(𝒪_{Z''}) ≠ 0`. For each component `E` of `Z''`
the sequence of `E ⊆ Z''` gives `H¹(𝒪_E(-(Z'' - E))) ≠ 0`, so `(Z'' - E) · E ≥ 2` since on a
curve of genus zero an invertible sheaf of degree at least `-1` has no `H¹` ([Stacks, Tag 0B90]).
Summing gives `Z''² + K_Y · Z'' ≥ 0`, that is `χ(𝒪_{Z''}) ≤ 0` by the cycle formula.

## Main results

* `MMP.Flips.IsGermResolution.eulerCharacteristic_divisorIdeal_eq`: the formula
  `χ(𝒪_Z) = -½ (Z² + K_Y · Z)`.
* `MMP.Flips.IsGermResolution.subsingleton_cohomologyOverField_one_divisorIdeal`: if
  `χ(𝒪_{Z'}) > 0` for every nonzero effective `Z' ≤ Z`, then `H¹(Z, 𝒪_Z) = 0`.

## Implementation notes

Cycles are handled as multisets of prime divisors, the cycle `∑_{E ∈ m} E` having ideal
`∏_{E ∈ m} I_E`. In place of the explicit Čech computation of `H¹(ℙ¹, 𝒪(d))`, the vanishing for
`d ≥ -1` is taken from the large-degree vanishing theorem on a proper curve, applied to a curve of
genus zero.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.4, 3.4.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

section Cycles

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- The tensor product of two modules on a scheme, as a module. -/
local notation3 (prettyPrint := false) "tens" X:max F:max G:max =>
  ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(X : Scheme).toRingedSpace.presheaf, (X : Scheme).toRingedSpace.IsSheaf⟩).obj F).obj G

/-! ### The ideal of a cycle given by a multiset of prime divisors -/

/-- The ideal sheaf `∏_{E ∈ m} I_E` of the cycle `∑_{E ∈ m} E`. -/
private def cycleIdeal (m : Multiset (MMP.Mori.PrimeDivisor Y)) : Y.IdealSheafData :=
  (m.map fun E => E.idealSheaf).prod

/-- The divisor `∑_{E ∈ m} E`. -/
private def cycleDivisor (m : Multiset (MMP.Mori.PrimeDivisor Y)) : Divisor Y :=
  (m.map fun E => Finsupp.single E (1 : ℤ)).sum

private theorem cycleIdeal_zero : cycleIdeal (0 : Multiset (MMP.Mori.PrimeDivisor Y)) = ⊤ := by
  simp [cycleIdeal, Scheme.IdealSheafData.one_eq_top]

private theorem cycleIdeal_cons (E : MMP.Mori.PrimeDivisor Y)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    cycleIdeal (E ::ₘ m) = E.idealSheaf * cycleIdeal m := by
  simp [cycleIdeal]

private theorem cycleDivisor_cons (E : MMP.Mori.PrimeDivisor Y)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    cycleDivisor (E ::ₘ m) = Finsupp.single E 1 + cycleDivisor m := by
  simp [cycleDivisor]

private theorem cycleIdeal_cons' (E : MMP.Mori.PrimeDivisor Y)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    cycleIdeal (E ::ₘ m) = cycleIdeal m * E.idealSheaf := by
  rw [cycleIdeal_cons, mul_comm]

private theorem cycleDivisor_apply (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (C : MMP.Mori.PrimeDivisor Y) [DecidableEq (MMP.Mori.PrimeDivisor Y)] :
    cycleDivisor m C = m.count C := by
  induction m using Multiset.induction_on with
  | empty => simp [cycleDivisor]
  | cons E m ih =>
    rw [cycleDivisor_cons, Finsupp.add_apply, ih, Finsupp.single_apply, Multiset.count_cons]
    by_cases h : E = C
    · subst h
      simp [add_comm]
    · simp [h, Ne.symm h]

private theorem mem_support_cycleIdeal (m : Multiset (MMP.Mori.PrimeDivisor Y)) (x : Y) :
    x ∈ (cycleIdeal m).support ↔ ∃ E ∈ m, x ∈ E.idealSheaf.support := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [cycleIdeal_zero, Scheme.IdealSheafData.support_top, Multiset.notMem_zero,
      false_and, exists_false, iff_false]
    exact id
  | cons E m ih =>
    rw [cycleIdeal_cons, Scheme.IdealSheafData.support_mul, ← SetLike.mem_coe,
      TopologicalSpace.Closeds.coe_sup, Set.mem_union, SetLike.mem_coe, SetLike.mem_coe, ih]
    simp

private theorem isEffectiveCartierDivisor_cycleIdeal [IsLocallyNoetherian Y] [IsNormal Y]
    {s : Y ⟶ Spec (.of k)} (hsm : IsSmoothScheme s) (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (cycleIdeal m) := by
  induction m using Multiset.induction_on with
  | empty =>
    rw [cycleIdeal_zero]
    exact Stacks.Divisors.isEffectiveCartierDivisor_top
  | cons E m ih =>
    rw [cycleIdeal_cons]
    exact isEffectiveCartierDivisor_mul _ _
      (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm E) ih

/-! ### Dimension and properness -/

private theorem topologicalKrullDim_cycleIdeal_le (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (hm : ∀ E ∈ m, topologicalKrullDim E.idealSheaf.subscheme ≤ 1) :
    topologicalKrullDim (cycleIdeal m).subscheme ≤ 1 := by
  classical
  rw [topologicalKrullDim_subscheme]
  have : ((cycleIdeal m).support : Set Y) =
      ⋃ E ∈ m.toFinset, ((E.idealSheaf.support : TopologicalSpace.Closeds Y) : Set Y) := by
    ext x
    simp only [Set.mem_iUnion, Multiset.mem_toFinset, exists_prop]
    exact mem_support_cycleIdeal m x
  rw [this]
  exact topologicalKrullDim_biUnion_le _ (fun E => E.idealSheaf.support.isClosed)
    fun E hE => by
      rw [← topologicalKrullDim_subscheme]
      exact hm E (Multiset.mem_toFinset.mp hE)

private theorem surjective_inclusion_le_radical (J : Y.IdealSheafData) :
    Surjective (Scheme.IdealSheafData.inclusion J.le_radical) := by
  refine ⟨fun z => ?_⟩
  have hz : J.subschemeι z ∈ (J.radical.support : Set Y) := by
    rw [Scheme.IdealSheafData.support_radical, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  rw [← Scheme.IdealSheafData.range_subschemeι] at hz
  obtain ⟨r, hr⟩ := hz
  refine ⟨r, J.subschemeι.isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι, hr]

/-- **A closed subscheme of the resolution lying over `P` is proper over `k`.** Its reduction
maps to the closed point `P` and is reduced, so it factors through `Spec κ(P)`, which is finite
over `k`; the subscheme itself is universally closed because its reduction surjects onto it. -/
private theorem isProper_of_support_subset {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {f : Y ⟶ X} (hf : IsGermResolution sX P f) (J : Y.IdealSheafData)
    (hJ : (J.support : Set Y) ⊆ f.base ⁻¹' {P}) :
    IsProper (J.subschemeι ≫ f ≫ sX) := by
  have : IsProper f := hf.isSmoothResolution.isProper
  have hX := hf.isSurfaceGerm.1.1
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsClosedImmersion (X.fromSpecResidueField P) :=
    isClosed_singleton_iff_isClosedImmersion.mp hf.isSurfaceGerm.2.2.1
  set R := J.radical with hR
  have hJR : J ≤ R := J.le_radical
  have : IsReduced R.subscheme := by
    rw [hR, ← Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  set h := R.subschemeι ≫ f with hh
  have H : (X.fromSpecResidueField P).ker ≤ h.ker := by
    have h1 : h.ker = Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure
          (h.base '' (⊤ : TopologicalSpace.Closeds R.subscheme))) := by
      rw [← Scheme.IdealSheafData.map_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_top,
        Scheme.nilradical_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [h1, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      TopologicalSpace.Closeds.closure_le]
    rintro _ ⟨z, -, rfl⟩
    refine (X.fromSpecResidueField P).range_subset_ker_support ?_
    rw [Scheme.range_fromSpecResidueField]
    have hz : R.subschemeι z ∈ (J.support : Set Y) := by
      rw [← Scheme.IdealSheafData.support_radical, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    exact hJ hz
  let l := IsClosedImmersion.lift (X.fromSpecResidueField P) h H
  have hl : l ≫ X.fromSpecResidueField P = h := IsClosedImmersion.lift_fac _ _ H
  have : IsProper (l ≫ X.fromSpecResidueField P) := by
    rw [hl]
    infer_instance
  have : IsProper l := IsProper.of_comp l (X.fromSpecResidueField P)
  have : IsFinite (X.fromSpecResidueField P ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have hRp : IsProper (R.subschemeι ≫ f ≫ sX) := by
    rw [← Category.assoc, ← hh, ← hl, Category.assoc]
    infer_instance
  have : IsSeparated sX := hX.toIsSeparated
  have := surjective_inclusion_le_radical J
  have : UniversallyClosed (Scheme.IdealSheafData.inclusion hJR ≫ J.subschemeι ≫ f ≫ sX) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    infer_instance
  have : UniversallyClosed (J.subschemeι ≫ f ≫ sX) :=
    UniversallyClosed.of_comp_surjective (Scheme.IdealSheafData.inclusion hJR) _
  exact ⟨⟩

/-! ### Intersection numbers with the curves of a cycle -/

section Intersection

variable (s : Y ⟶ Spec (.of k)) [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

open Classical in
/-- The intersection number `(D · E)` of a `ℚ`-divisor with a prime divisor, when defined. -/
private def ixn (D : QDivisor Y) (E : MMP.Mori.PrimeDivisor Y) : ℚ :=
  if h : ∃ x, IsIntersectionNumber s D E.idealSheaf x then h.choose else 0

variable {s}

private theorem isIntersectionNumber_ixn (hsm : IsSmoothScheme s) {E : MMP.Mori.PrimeDivisor Y}
    (hEp : IsProper (E.idealSheaf.subschemeι ≫ s))
    (hEd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) (D : QDivisor Y) :
    IsIntersectionNumber s D E.idealSheaf (ixn s D E) := by
  have h : ∃ x, IsIntersectionNumber s D E.idealSheaf x :=
    ⟨_, hEp, hEd, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D, rfl⟩
  rw [ixn, dif_pos h]
  exact h.choose_spec

private theorem ixn_eq_of_isIntersectionNumber {D : QDivisor Y} {E : MMP.Mori.PrimeDivisor Y}
    {x : ℚ} (h : IsIntersectionNumber s D E.idealSheaf x) : ixn s D E = x := by
  have h' : ∃ x, IsIntersectionNumber s D E.idealSheaf x := ⟨x, h⟩
  rw [ixn, dif_pos h']
  exact h'.choose_spec.unique h

private theorem ixn_add (hsm : IsSmoothScheme s) {E : MMP.Mori.PrimeDivisor Y}
    (hEp : IsProper (E.idealSheaf.subschemeι ≫ s))
    (hEd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) (D D' : QDivisor Y) :
    ixn s (D + D') E = ixn s D E + ixn s D' E :=
  ixn_eq_of_isIntersectionNumber (isIntersectionNumber_add
    (isIntersectionNumber_ixn hsm hEp hEd D) (isIntersectionNumber_ixn hsm hEp hEd D'))

/-- The intersection number of `∑_{F ∈ m} F + D` with `E` is `∑_{F ∈ m} (F · E) + (D · E)`. -/
private theorem ixn_cycleDivisor_add (hsm : IsSmoothScheme s) {E : MMP.Mori.PrimeDivisor Y}
    (hEp : IsProper (E.idealSheaf.subschemeι ≫ s))
    (hEd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (D : QDivisor Y) :
    ixn s (Divisor.toQDivisor (cycleDivisor m) + D) E =
      (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum + ixn s D E := by
  induction m using Multiset.induction_on with
  | empty => simp [cycleDivisor]
  | cons F m ih =>
    rw [cycleDivisor_cons, map_add, add_assoc, ixn_add hsm hEp hEd, ih, Multiset.map_cons,
      Multiset.sum_cons, add_assoc]

/-- **Symmetry of the intersection numbers of two curves on a smooth surface.** -/
private theorem ixn_single_comm (hY : MMP.Mori.IsVariety k s) (hsm : IsSmoothScheme s)
    (hd : topologicalKrullDim Y = 2) {E F : MMP.Mori.PrimeDivisor Y}
    (hE : IsProper (E.idealSheaf.subschemeι ≫ s)) (hF : IsProper (F.idealSheaf.subschemeι ≫ s)) :
    ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E =
      ixn s (Divisor.toQDivisor (Finsupp.single E 1)) F := by
  by_cases hEF : E = F
  · subst hEF; rfl
  obtain ⟨-, h1, -⟩ :=
    MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne s hY hsm hd hEF hE
  obtain ⟨-, h2, -⟩ :=
    MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne s hY hsm hd
      (Ne.symm hEF) hF
  rw [MMP.Threefold.Resolution.toQDivisor_single, MMP.Threefold.Resolution.toQDivisor_single]
  push_cast
  rw [ixn_eq_of_isIntersectionNumber h1, ixn_eq_of_isIntersectionNumber h2, Set.inter_comm]
  congr 1
  funext z
  rw [MMP.Mori.localIntersectionNumber, MMP.Mori.localIntersectionNumber, sup_comm]

/-- The reduced subscheme on the support of the divisor `E` of a prime divisor is `E`. -/
private theorem suppIdeal_single_one (E : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.suppIdeal (Finsupp.single E (1 : ℤ) : Divisor Y) = E.idealSheaf := by
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf E, DivisorWithCoeffs.suppIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E, DivisorWithCoeffs.coe_supp,
    Finsupp.support_single_ne_zero _ one_ne_zero]
  simp

/-- **Adjunction on an integral curve of a smooth surface**: `((K + E) · E) = -2 χ(E, 𝒪_E)`. -/
private theorem ixn_canonical_add_single [IsAlgClosed k] (hY : MMP.Mori.IsVariety k s)
    (hsm : IsSmoothScheme s) (hd : topologicalKrullDim Y = 2) {K : Divisor Y}
    (hK : K.IsCanonicalDivisor s 2) (E : MMP.Mori.PrimeDivisor Y)
    [hE : IsProper (E.idealSheaf.subschemeι ≫ s)] :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (E.idealSheaf.subschemeι ≫ s)
    ixn s (Divisor.toQDivisor (K + Finsupp.single E 1)) E =
      -2 * eulerCharacteristic k (E.idealSheaf.subschemeι ≫ s)
        (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) := by
  have hI := suppIdeal_single_one E
  have hC : ∀ F ∈ (Finsupp.single E (1 : ℤ) : Divisor Y).support,
      (Finsupp.single E (1 : ℤ) : Divisor Y) F = 1 := by
    intro F hF
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hF
    rw [hF, Finsupp.single_eq_same]
  have hpr' : IsProper ((DivisorWithCoeffs.suppIdeal
      (Finsupp.single E (1 : ℤ) : Divisor Y)).subschemeι ≫ s) := by
    rwa [hI]
  have h := MMP.Threefold.isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic
    hY hsm hd hK _ hC hpr'
  revert h hpr'
  generalize DivisorWithCoeffs.suppIdeal (Finsupp.single E (1 : ℤ) : Divisor Y) = I at hI ⊢
  subst hI
  intro _ h
  exact ixn_eq_of_isIntersectionNumber h

end Intersection

/-! ### Short exact sequences supported on a proper closed subscheme -/

section Sequence

variable {s : Y ⟶ Spec (.of k)}

private theorem isProper_of_le {J I : Y.IdealSheafData} (h : J ≤ I)
    [IsProper (J.subschemeι ≫ s)] : IsProper (I.subschemeι ≫ s) := by
  rw [← Scheme.IdealSheafData.inclusion_subschemeι h, Category.assoc]
  infer_instance

private theorem eulerCharacteristic_congr_hom {X : Scheme.{u}} {g g' : X ⟶ Spec (.of k)}
    (h : g = g') (hg : IsProper g) (hg' : IsProper g') (F : X.Modules) (hF : F.IsCoherent) :
    @eulerCharacteristic k _ _ g hg F hF = @eulerCharacteristic k _ _ g' hg' F hF := by
  subst h; rfl

/-- **A short exact sequence of `𝒪_Y`-modules pushed forward from closed subschemes of `J`
descends to `J`**: the direct image along the closed immersion `J ⟶ Y` is fully faithful and
exact. -/
private theorem exists_shortExact_inclusion (J : Y.IdealSheafData) {J₁ J₂ J₃ : Y.IdealSheafData}
    (h₁ : J ≤ J₁) (h₂ : J ≤ J₂) (h₃ : J ≤ J₃)
    {G₁ : J₁.subscheme.Modules} {G₂ : J₂.subscheme.Modules} {G₃ : J₃.subscheme.Modules}
    {T : ShortComplex Y.Modules} (hT : T.ShortExact)
    (e₁ : T.X₁ ≅ (Scheme.Modules.pushforward J₁.subschemeι).obj G₁)
    (e₂ : T.X₂ ≅ (Scheme.Modules.pushforward J₂.subschemeι).obj G₂)
    (e₃ : T.X₃ ≅ (Scheme.Modules.pushforward J₃.subschemeι).obj G₃) :
    ∃ (v : (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h₁)).obj G₁ ⟶
        (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h₂)).obj G₂)
      (w : (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h₂)).obj G₂ ⟶
        (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h₃)).obj G₃)
      (hvw : v ≫ w = 0), (ShortComplex.mk v w hvw).ShortExact := by
  have iso : ∀ {I : Y.IdealSheafData} (h : J ≤ I) (G : I.subscheme.Modules),
      (Scheme.Modules.pushforward J.subschemeι).obj
          ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h)).obj G) ≅
        (Scheme.Modules.pushforward I.subschemeι).obj G := fun h G =>
    (Scheme.Modules.pushforwardComp (Scheme.IdealSheafData.inclusion h) J.subschemeι).app G ≪≫
      (Scheme.Modules.pushforwardCongr (Scheme.IdealSheafData.inclusion_subschemeι h)).app G
  have u₁ := e₁ ≪≫ (iso h₁ G₁).symm
  have u₂ := e₂ ≪≫ (iso h₂ G₂).symm
  have u₃ := e₃ ≪≫ (iso h₃ G₃).symm
  have hff := Stacks.ClosedImmersion.fullyFaithfulPushforward J.subschemeι
  have : (Scheme.Modules.pushforward J.subschemeι).Faithful := hff.faithful
  set v := hff.preimage (u₁.inv ≫ T.f ≫ u₂.hom)
  set w := hff.preimage (u₂.inv ≫ T.g ≫ u₃.hom)
  have hmapv : (Scheme.Modules.pushforward J.subschemeι).map v = u₁.inv ≫ T.f ≫ u₂.hom :=
    hff.map_preimage _
  have hmapw : (Scheme.Modules.pushforward J.subschemeι).map w = u₂.inv ≫ T.g ≫ u₃.hom :=
    hff.map_preimage _
  have hvw : v ≫ w = 0 := by
    apply hff.map_injective
    rw [Functor.map_comp, Functor.map_zero, hmapv, hmapw]
    simp
  refine ⟨v, w, hvw, ?_⟩
  refine ShortComplex.shortExact_of_shortExact_map (Scheme.Modules.pushforward J.subschemeι) ?_
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk u₁ u₂ u₃ ?_ ?_) hT
  · change u₁.hom ≫ (Scheme.Modules.pushforward J.subschemeι).map v = T.f ≫ u₂.hom
    rw [hmapv]
    simp
  · change u₂.hom ≫ (Scheme.Modules.pushforward J.subschemeι).map w = T.g ≫ u₃.hom
    rw [hmapw]
    simp

/-- The Euler characteristic on `J` of a module pushed forward from a closed subscheme `I ⊆ J`
is its Euler characteristic on `I`. -/
private theorem eulerCharacteristic_pushforward_inclusion {J I : Y.IdealSheafData} (h : J ≤ I)
    [hJ : IsProper (J.subschemeι ≫ s)] (G : I.subscheme.Modules) [hG : G.IsCoherent]
    (hc : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h)).obj G).IsCoherent)
    (hI : IsProper (I.subschemeι ≫ s)) :
    @eulerCharacteristic k _ _ (J.subschemeι ≫ s) hJ _ hc =
      @eulerCharacteristic k _ _ (I.subschemeι ≫ s) hI G hG := by
  have : IsProper (Scheme.IdealSheafData.inclusion h ≫ J.subschemeι ≫ s) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]; exact hI
  rw [eulerCharacteristic_pushforward_of_isClosedImmersion k _ _ G hG hc]
  exact eulerCharacteristic_congr_hom
    (by rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]) _ _ G hG

/-- The Euler characteristic on `J` of `L|_J ⊗ G` for a module `G` pushed forward from a closed
subscheme `I ⊆ J` is the Euler characteristic of `G ⊗ L|_I` on `I` (the projection formula). -/
private theorem eulerCharacteristic_tensor_pushforward_inclusion {J I : Y.IdealSheafData}
    (h : J ≤ I) [hJ : IsProper (J.subschemeι ≫ s)] (G : I.subscheme.Modules) [hG : G.IsCoherent]
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hc₁ : (tens J.subscheme ((Scheme.Modules.pullback J.subschemeι).obj L)
      ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h)).obj G)).IsCoherent)
    (hI : IsProper (I.subschemeι ≫ s))
    (hc₂ : (tens I.subscheme G ((Scheme.Modules.pullback I.subschemeι).obj L)).IsCoherent) :
    @eulerCharacteristic k _ _ (J.subschemeι ≫ s) hJ _ hc₁ =
      @eulerCharacteristic k _ _ (I.subschemeι ≫ s) hI _ hc₂ := by
  set i := Scheme.IdealSheafData.inclusion h
  have : IsLocallyNoetherian J.subscheme :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k
      (J.subschemeι ≫ s)
  have hiJ : IsProper (i ≫ J.subschemeι ≫ s) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]; exact hI
  have : SheafOfModules.IsInvertible J.subscheme.presheaf J.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback J.subschemeι).obj L) :=
    MMP.Mori.isInvertible_pullback_obj J.subschemeι L
  have hV : ((Scheme.Modules.pullback J.subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (J.subschemeι ≫ s) _ 1
  have : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback J.subschemeι).obj L)) :=
    MMP.Mori.isInvertible_pullback_obj i _
  have hV' : ((Scheme.Modules.pullback i).obj
      ((Scheme.Modules.pullback J.subschemeι).obj L)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (i ≫ J.subschemeι ≫ s) _ 1
  have hpush : ((Scheme.Modules.pushforward i).obj G).IsCoherent := inferInstance
  have : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback I.subschemeι).obj L) :=
    MMP.Mori.isInvertible_pullback_obj I.subschemeι L
  have hL' : ((Scheme.Modules.pullback I.subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (I.subschemeι ≫ s) _ 1
  have e : (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback J.subschemeι).obj L) ≅
      (Scheme.Modules.pullback I.subschemeι).obj L :=
    (Scheme.Modules.pullbackComp i J.subschemeι).app L ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.IdealSheafData.inclusion_subschemeι h)).app L
  have h1 := eulerCharacteristic_tensorSheaf_comm k (J.subschemeι ≫ s)
    ((Scheme.Modules.pullback J.subschemeι).obj L) ((Scheme.Modules.pushforward i).obj G)
    (hF := hV) (hG := hpush)
  have h2 := eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion k i
    (J.subschemeι ≫ s) G ((Scheme.Modules.pullback J.subschemeι).obj L) hG hV hpush hV'
  have h3 := @eulerCharacteristic_eq_of_iso k _ _ (i ≫ J.subschemeι ≫ s) hiJ _ _
    (@SheafOfModules.tensorSheaf_isCoherent I.subscheme.toRingedSpace G _ hG hV')
    (@SheafOfModules.tensorSheaf_isCoherent I.subscheme.toRingedSpace G _ hG hL')
    (((Stacks.SheafOfModules.Tensor.sheafTensor _).obj G).mapIso e)
  refine h1.trans (h2.trans (h3.trans ?_))
  exact eulerCharacteristic_congr_hom
    (by rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]) _ _ _ _

/-- The restriction `𝒪_Y(-W)|_I` of the ideal sheaf of an effective Cartier divisor to a closed
subscheme is invertible. -/
private theorem isInvertible_pullback_negativeTwist (W I : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor W] :
    SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) :=
  Stacks.Models.isInvertible_restrict I _ (Stacks.Divisors.isTensorInvertible_negativeTwist W)

/-- The short exact sequence `0 ⟶ 𝒪_Y(-W)|_I ⟶ 𝒪_{W+I} ⟶ 𝒪_W ⟶ 0` of [Stacks, Tag 0C4T],
descended to the closed subscheme `W + I`. -/
private theorem exists_shortExact_mul (W I : Y.IdealSheafData)
    [hW : Stacks.Divisors.IsEffectiveCartierDivisor W]
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I] :
    ∃ (v : (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
          (Scheme.IdealSheafData.mul_le_right W I))).obj
          ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) ⟶
        (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion (le_refl (W * I)))).obj
          (SheafOfModules.unit (W * I).subscheme.ringCatSheaf))
      (w : (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion (le_refl (W * I)))).obj
          (SheafOfModules.unit (W * I).subscheme.ringCatSheaf) ⟶
        (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
          (Scheme.IdealSheafData.mul_le_left W I))).obj
          (SheafOfModules.unit W.subscheme.ringCatSheaf))
      (hvw : v ≫ w = 0), (ShortComplex.mk v w hvw).ShortExact := by
  obtain ⟨f, zero, hex⟩ := Stacks.Divisors.addEffectiveCartierDivisor_shortExact W (W * I) I hW
    (Scheme.IdealSheafData.mul_le_left W I) rfl
  exact exists_shortExact_inclusion (W * I) _ _ _ hex (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- **`χ(𝒪_{W+I}) = χ(𝒪_W) + χ(𝒪_Y(-W)|_I)`** for effective Cartier divisors `W`, `I` whose
sum is proper over `k`: additivity of the Euler characteristic on `W + I` along the sequence
`0 ⟶ 𝒪_Y(-W)|_I ⟶ 𝒪_{W+I} ⟶ 𝒪_W ⟶ 0`. -/
private theorem eulerCharacteristic_unit_mul (W I : Y.IdealSheafData)
    [hW : Stacks.Divisors.IsEffectiveCartierDivisor W]
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]
    [hWI : IsProper ((W * I).subschemeι ≫ s)] :
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left W I)
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_right W I)
    haveI := isInvertible_pullback_negativeTwist W I
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (I.subschemeι ≫ s)
      ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) 1
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((W * I).subschemeι ≫ s)
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (W.subschemeι ≫ s)
    eulerCharacteristic k ((W * I).subschemeι ≫ s)
        (SheafOfModules.unit (W * I).subscheme.ringCatSheaf) =
      eulerCharacteristic k (W.subschemeι ≫ s) (SheafOfModules.unit W.subscheme.ringCatSheaf) +
        eulerCharacteristic k (I.subschemeι ≫ s)
          ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) := by
  haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left W I)
  haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_right W I)
  haveI := isInvertible_pullback_negativeTwist W I
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
    (I.subschemeι ≫ s)
    ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) 1
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k ((W * I).subschemeι ≫ s)
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (W.subschemeι ≫ s)
  haveI : IsLocallyNoetherian (W * I).subscheme :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k
      ((W * I).subschemeι ≫ s)
  obtain ⟨v, w, hvw, hS⟩ := exists_shortExact_mul W I
  have key := eulerCharacteristic_add_of_shortExact k ((W * I).subschemeι ≫ s) hS
  have e₁ := eulerCharacteristic_pushforward_inclusion (s := s)
    (Scheme.IdealSheafData.mul_le_right W I)
    ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W))
    inferInstance inferInstance
  have e₂ := eulerCharacteristic_pushforward_inclusion (s := s) (le_refl (W * I))
    (SheafOfModules.unit (W * I).subscheme.ringCatSheaf) inferInstance inferInstance
  have e₃ := eulerCharacteristic_pushforward_inclusion (s := s)
    (Scheme.IdealSheafData.mul_le_left W I) (SheafOfModules.unit W.subscheme.ringCatSheaf)
    inferInstance inferInstance
  refine e₂.symm.trans (key.trans ?_)
  rw [add_comm]
  exact congrArg₂ (· + ·) e₃ e₁

/-- **The degree on `W + I` is the sum of the degrees on `W` and on `I`**, for effective Cartier
divisors `W`, `I` whose sum is a proper curve over `k`: the sequence
`0 ⟶ 𝒪_Y(-W)|_I ⟶ 𝒪_{W+I} ⟶ 𝒪_W ⟶ 0` twisted by an invertible sheaf `L`, against the untwisted
one, with the additivity of the degree on `I`. -/
private theorem degreeOn_mul (W I : Y.IdealSheafData)
    [hW : Stacks.Divisors.IsEffectiveCartierDivisor W]
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]
    [hWI : IsProper ((W * I).subschemeι ≫ s)] (hd : topologicalKrullDim (W * I).subscheme ≤ 1)
    (hdW : topologicalKrullDim W.subscheme ≤ 1) (hdI : topologicalKrullDim I.subscheme ≤ 1)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left W I)
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_right W I)
    MMP.Mori.degreeOn k s (W * I).subschemeι hd L =
      MMP.Mori.degreeOn k s W.subschemeι hdW L + MMP.Mori.degreeOn k s I.subschemeι hdI L := by
  haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left W I)
  haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_right W I)
  haveI := isInvertible_pullback_negativeTwist W I
  haveI : IsLocallyNoetherian (W * I).subscheme :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k
      ((W * I).subschemeι ≫ s)
  haveI : SheafOfModules.IsInvertible (W * I).subscheme.presheaf
      (W * I).subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback (W * I).subschemeι).obj L) :=
    MMP.Mori.isInvertible_pullback_obj _ L
  haveI : SheafOfModules.IsInvertible W.subscheme.presheaf W.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback W.subschemeι).obj L) := MMP.Mori.isInvertible_pullback_obj _ L
  haveI : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback I.subschemeι).obj L) := MMP.Mori.isInvertible_pullback_obj _ L
  have hN : ((Scheme.Modules.pullback I.subschemeι).obj
      (Stacks.Divisors.negativeTwist W)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (I.subschemeι ≫ s) _ 1
  have hLJ : ((Scheme.Modules.pullback (W * I).subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      ((W * I).subschemeι ≫ s) _ 1
  have hLW : ((Scheme.Modules.pullback W.subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (W.subschemeι ≫ s) _ 1
  have hLI : ((Scheme.Modules.pullback I.subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (I.subschemeι ≫ s) _ 1
  have hOJ := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    ((W * I).subschemeι ≫ s)
  have hOW := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (W.subschemeι ≫ s)
  have hOI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (I.subschemeι ≫ s)
  haveI : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      (tens I.subscheme ((Scheme.Modules.pullback I.subschemeι).obj
        (Stacks.Divisors.negativeTwist W)) ((Scheme.Modules.pullback I.subschemeι).obj L)) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible I.subscheme.presheaf
      I.subscheme.ringCatSheaf.2 _ _
  have hNL := @SheafOfModules.tensorSheaf_isCoherent I.subscheme.toRingedSpace _ _ hN hLI
  obtain ⟨v, w, hvw, hS⟩ := exists_shortExact_mul W I
  have hp₁ : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (Scheme.IdealSheafData.mul_le_right W I))).obj ((Scheme.Modules.pullback I.subschemeι).obj
        (Stacks.Divisors.negativeTwist W))).IsCoherent :=
    @isCoherent_pushforward_of_isClosedImmersion _ _ _ _ _ _ hN
  have hp₂ : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (le_refl (W * I)))).obj (SheafOfModules.unit (W * I).subscheme.ringCatSheaf)).IsCoherent :=
    @isCoherent_pushforward_of_isClosedImmersion _ _ _ _ _ _ hOJ
  have hp₃ : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (Scheme.IdealSheafData.mul_le_left W I))).obj
        (SheafOfModules.unit W.subscheme.ringCatSheaf)).IsCoherent :=
    @isCoherent_pushforward_of_isClosedImmersion _ _ _ _ _ _ hOW
  have key := eulerCharacteristic_tensorSheaf_add_of_shortExact_of_isProper k
    ((W * I).subschemeι ≫ s) ((Scheme.Modules.pullback (W * I).subschemeι).obj L) 1 _ hS
    hp₁ hp₂ hp₃
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₁)
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₂)
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₃)
  have t₁ := @eulerCharacteristic_tensor_pushforward_inclusion k _ Y s (W * I) I
    (Scheme.IdealSheafData.mul_le_right W I) _ _ hN L _
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₁) inferInstance hNL
  have t₂ := @eulerCharacteristic_tensor_pushforward_inclusion k _ Y s (W * I) (W * I)
    (le_refl (W * I)) _ _ hOJ L _
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₂) inferInstance
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hOJ hLJ)
  have t₃ := @eulerCharacteristic_tensor_pushforward_inclusion k _ Y s (W * I) W
    (Scheme.IdealSheafData.mul_le_left W I) _ _ hOW L _
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₃) inferInstance
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hOW hLW)
  have u₂ := eulerCharacteristic_unit_tensorSheaf k ((W * I).subschemeι ≫ s) _ hLJ hOJ
  have u₃ := eulerCharacteristic_unit_tensorSheaf k (W.subschemeι ≫ s) _ hLW hOW
  have hA := u₂.symm.trans (t₂.symm.trans (key.trans (congrArg₂ (· + ·) t₁ (t₃.trans u₃))))
  have hB := eulerCharacteristic_unit_mul (s := s) W I
  have hC := invertibleCurveDegree_tensorSheaf_eq_add k (I.subschemeι ≫ s) hdI
    ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W))
    ((Scheme.Modules.pullback I.subschemeι).obj L)
  have c₁ := @invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (I.subschemeι ≫ s) _ hdI _
    _ hNL hOI
  have c₂ := @invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (I.subschemeι ≫ s) _ hdI _
    _ hN hOI
  have c₃ := @invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (I.subschemeι ≫ s) _ hdI _
    _ hLI hOI
  have g₁ := (MMP.Mori.degreeOn_eq_invertibleCurveDegree k s (W * I).subschemeι hd L).trans
    (@invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ ((W * I).subschemeι ≫ s) _ hd _
      _ hLJ hOJ)
  have g₂ := (MMP.Mori.degreeOn_eq_invertibleCurveDegree k s W.subschemeι hdW L).trans
    (@invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (W.subschemeι ≫ s) _ hdW _
      _ hLW hOW)
  have g₃ := (MMP.Mori.degreeOn_eq_invertibleCurveDegree k s I.subschemeι hdI L).trans
    (@invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (I.subschemeι ≫ s) _ hdI _
      _ hLI hOI)
  rw [g₁, g₂, g₃]
  rw [c₁, c₂, c₃] at hC
  linarith

end Sequence

/-! ### Degrees of the invertible sheaves of divisors -/

section Degree

variable {s : Y ⟶ Spec (.of k)} {C : Scheme.{u}} (i : C ⟶ Y) [IsProper (i ≫ s)]
  (hdim : topologicalKrullDim C ≤ 1)

private theorem isInvertible_invertibleSheaf' (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (Stacks.Divisors.invertibleSheaf' D) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.Divisors.isTensorInvertible_invertibleSheaf D)

private theorem isInvertible_negativeTwist' (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (Stacks.Divisors.negativeTwist' D) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.Divisors.isTensorInvertible_negativeTwist D)

/-- The structure sheaf has degree zero. -/
private theorem degreeOn_unit
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (SheafOfModules.unit Y.ringCatSheaf)] :
    MMP.Mori.degreeOn k s i hdim (SheafOfModules.unit Y.ringCatSheaf) = 0 := by
  haveI := MMP.Mori.isInvertible_pullback_obj i (SheafOfModules.unit Y.ringCatSheaf)
  exact (MMP.Mori.degreeOn_eq_invertibleCurveDegree k s i hdim _).trans
    (invertibleCurveDegree_eq_zero_of_iso_unit k (i ≫ s) hdim _
      (Scheme.Modules.pullbackUnitIso i))

/-- `deg 𝒪_Y(-D) = -deg 𝒪_Y(D)` for an effective Cartier divisor `D`: the evaluation pairing
trivialises `𝒪_Y(D) ⊗ 𝒪_Y(-D)`. -/
private theorem degreeOn_negativeTwist' (D : Y.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    haveI := isInvertible_negativeTwist' D
    haveI := isInvertible_invertibleSheaf' D
    MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.negativeTwist' D) =
      -MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' D) := by
  haveI := isInvertible_negativeTwist' D
  haveI := isInvertible_invertibleSheaf' D
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (tens Y (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.negativeTwist' D)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
      (Stacks.Models.isTensorInvertible_invertibleSheafTensorNegativeTwist D hD)
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (SheafOfModules.unit Y.ringCatSheaf) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
      (Stacks.Models.isTensorInvertible_unit Y)
  have h1 := MMP.Mori.degreeOn_tensorSheaf k s i hdim (Stacks.Divisors.invertibleSheaf' D)
    (Stacks.Divisors.negativeTwist' D)
  have h0 := (MMP.Mori.degreeOn_eq_of_iso k s i hdim
    (Stacks.Models.invertibleSheafTensorNegativeTwistIsoUnit D hD)).trans (degreeOn_unit i hdim)
  omega

private theorem degreeOn_invertibleSheaf'_congr {D D' : Y.IdealSheafData} (h : D = D')
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Divisors.IsEffectiveCartierDivisor D'] :
    haveI := isInvertible_invertibleSheaf' D
    haveI := isInvertible_invertibleSheaf' D'
    MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' D) =
      MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' D') := by
  subst h; rfl

/-- **The degree of `𝒪_Y(∑_{F ∈ m} F)` is `∑_{F ∈ m} deg 𝒪_Y(F)`** on a smooth `Y`. -/
private theorem degreeOn_invertibleSheaf'_cycleIdeal [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme s) (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
    haveI := isInvertible_invertibleSheaf' (cycleIdeal m)
    MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' (cycleIdeal m)) =
      (m.map fun F =>
        haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme
          hsm F
        haveI := isInvertible_invertibleSheaf' F.idealSheaf
        MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' F.idealSheaf)).sum := by
  induction m using Multiset.induction_on with
  | empty =>
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm (0 : Multiset (MMP.Mori.PrimeDivisor Y))
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (⊤ : Y.IdealSheafData) :=
      Stacks.Divisors.isEffectiveCartierDivisor_top
    haveI := isInvertible_invertibleSheaf' (⊤ : Y.IdealSheafData)
    haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (SheafOfModules.unit Y.ringCatSheaf) :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
        (Stacks.Models.isTensorInvertible_unit Y)
    refine (degreeOn_invertibleSheaf'_congr i hdim cycleIdeal_zero).trans
      ((MMP.Mori.degreeOn_eq_of_iso k s i hdim (L' := SheafOfModules.unit Y.ringCatSheaf)
        Stacks.Divisors.invertibleSheafTopIsoUnit).trans ?_)
    rw [degreeOn_unit i hdim]
    simp
  | cons F m ih =>
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm (F ::ₘ m)
    haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm F
    haveI := isInvertible_invertibleSheaf' (F.idealSheaf * cycleIdeal m)
    haveI := isInvertible_invertibleSheaf' F.idealSheaf
    haveI := isInvertible_invertibleSheaf' (cycleIdeal m)
    haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (Stacks.Divisors.sumSheaf F.idealSheaf (cycleIdeal m)) :=
      Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible Y.presheaf Y.ringCatSheaf.2 _ _
    rw [degreeOn_invertibleSheaf'_congr i hdim (cycleIdeal_cons F m),
      ← MMP.Mori.degreeOn_eq_of_iso k s i hdim
        (Stacks.Divisors.invertibleSheafSumIso F.idealSheaf (cycleIdeal m)),
      Multiset.map_cons, Multiset.sum_cons, ← ih]
    exact MMP.Mori.degreeOn_tensorSheaf k s i hdim _ _

end Degree

/-! ### Intersection numbers as degrees -/

section Curves

variable {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

/-- For a divisor `D` on a smooth `Y` and a closed subscheme `J` which is a proper curve,
`(D · J) = deg_J 𝒪_Y(D)`. -/
private theorem isIntersectionNumber_degreeOn (hsm : IsSmoothScheme s) {J : Y.IdealSheafData}
    [hp : IsProper (J.subschemeι ≫ s)] (hd : topologicalKrullDim J.subscheme ≤ 1)
    (D : Divisor Y) :
    IsIntersectionNumber s (Divisor.toQDivisor D) J
      (D.degreeOn k s J.subschemeι hd (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D)) :=
  ⟨hp, hd, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _,
    QDivisor.intersectionNumber_toQDivisor k s _ hd D _ _⟩

/-- `(F · E) = deg_E 𝒪_Y(F)` for prime divisors `E`, `F` on a smooth `Y`, with the invertible
sheaf of the effective Cartier divisor `F`. -/
private theorem ixn_single_eq_degreeOn (hsm : IsSmoothScheme s) {E : MMP.Mori.PrimeDivisor Y}
    (F : MMP.Mori.PrimeDivisor Y) [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) :
    haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm F
    haveI := isInvertible_invertibleSheaf' F.idealSheaf
    ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E =
      MMP.Mori.degreeOn k s E.idealSheaf.subschemeι hd
        (Stacks.Divisors.invertibleSheaf' F.idealSheaf) := by
  haveI hF := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm F
  haveI := isInvertible_invertibleSheaf' F.idealSheaf
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have hc := MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm F
  obtain ⟨b⟩ :=
    MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' F hF hc
  haveI := hc.isInvertibleModule_divisorialSheaf
  rw [ixn_eq_of_isIntersectionNumber (isIntersectionNumber_degreeOn hsm hd _)]
  congr 1
  exact MMP.Mori.degreeOn_eq_of_iso k s _ hd b

/-- **`χ(𝒪_Y(-W)|_E) = χ(𝒪_E) - (W · E)`** for `W = ∑_{F ∈ m} F` and a prime divisor `E` which
is a proper curve. -/
private theorem eulerCharacteristic_negativeTwist_cycleIdeal (hsm : IsSmoothScheme s)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (E : MMP.Mori.PrimeDivisor Y)
    [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) :
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
    haveI := isInvertible_pullback_negativeTwist (cycleIdeal m) E.idealSheaf
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (E.idealSheaf.subschemeι ≫ s)
      ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
        (Stacks.Divisors.negativeTwist (cycleIdeal m))) 1
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (E.idealSheaf.subschemeι ≫ s)
    (eulerCharacteristic k (E.idealSheaf.subschemeι ≫ s)
        ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
          (Stacks.Divisors.negativeTwist (cycleIdeal m))) : ℚ) =
      eulerCharacteristic k (E.idealSheaf.subschemeι ≫ s)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) -
        (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
  haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
  haveI := isInvertible_pullback_negativeTwist (cycleIdeal m) E.idealSheaf
  haveI hN := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
    (E.idealSheaf.subschemeι ≫ s)
    ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
      (Stacks.Divisors.negativeTwist (cycleIdeal m))) 1
  haveI hO := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (E.idealSheaf.subschemeι ≫ s)
  haveI := isInvertible_negativeTwist' (cycleIdeal m)
  have h1 := ((MMP.Mori.degreeOn_eq_invertibleCurveDegree k s E.idealSheaf.subschemeι hd
    (Stacks.Divisors.negativeTwist' (cycleIdeal m))).trans
    (@invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (E.idealSheaf.subschemeι ≫ s) _ hd
      _ _ hN hO)).symm
  rw [degreeOn_negativeTwist', degreeOn_invertibleSheaf'_cycleIdeal _ hd hsm m] at h1
  have h2 : (((m.map fun F =>
        haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme
          hsm F
        haveI := isInvertible_invertibleSheaf' F.idealSheaf
        MMP.Mori.degreeOn k s E.idealSheaf.subschemeι hd
          (Stacks.Divisors.invertibleSheaf' F.idealSheaf)).sum : ℤ) : ℚ) =
      (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
    rw [Int.cast_multiset_sum, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun F _ => (ixn_single_eq_degreeOn hsm F hd).symm)
  have h3 := congrArg (Int.cast : ℤ → ℚ) h1
  rw [Int.cast_sub, Int.cast_neg, h2] at h3
  linarith

/-- **The induction step for `χ`**: for `W = ∑_{F ∈ m} F` and a prime divisor `E` which is a
proper curve, `χ(𝒪_{W+E}) = χ(𝒪_W) + χ(𝒪_E) - ∑_{F ∈ m} (F · E)`. -/
private theorem eulerCharacteristic_cycleIdeal_mul (hsm : IsSmoothScheme s)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (E : MMP.Mori.PrimeDivisor Y)
    [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1)
    [IsProper ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s)] :
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left (cycleIdeal m) E.idealSheaf)
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s)
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((cycleIdeal m).subschemeι ≫ s)
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (E.idealSheaf.subschemeι ≫ s)
    (eulerCharacteristic k ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s)
        (SheafOfModules.unit (cycleIdeal m * E.idealSheaf).subscheme.ringCatSheaf) : ℚ) =
      eulerCharacteristic k ((cycleIdeal m).subschemeι ≫ s)
          (SheafOfModules.unit (cycleIdeal m).subscheme.ringCatSheaf) +
        eulerCharacteristic k (E.idealSheaf.subschemeι ≫ s)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) -
        (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
  haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
  haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm E
  have h := congrArg (Int.cast : ℤ → ℚ)
    (eulerCharacteristic_unit_mul (s := s) (cycleIdeal m) E.idealSheaf)
  push_cast at h
  rw [h, eulerCharacteristic_negativeTwist_cycleIdeal hsm m E hd]
  ring

end Curves

/-! ### The induction on the cycle -/

section Induction

variable [IsAlgClosed k] {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- **The cycle formula, by induction on the cycle.** For a nonzero cycle `Z = ∑_{E ∈ m} E` of
proper curves on a smooth surface whose subcycles are proper over `k`, the intersection number
of a divisor `D` with `Z` is `∑_{E ∈ m} (D · E)`, and `χ(𝒪_Z) = -½ ∑_{E ∈ m} ((Z + K) · E)`. -/
private theorem isIntersectionNumber_and_eulerCharacteristic_cycleIdeal
    (hY : MMP.Mori.IsVariety k s) (hsm : IsSmoothScheme s) (hd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor s 2)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (hm0 : m ≠ 0)
    (hmE : ∀ E ∈ m, IsProper (E.idealSheaf.subschemeι ≫ s) ∧
      topologicalKrullDim E.idealSheaf.subscheme ≤ 1)
    (hprop : ∀ m' ≤ m, IsProper ((cycleIdeal m').subschemeι ≫ s)) :
    (∀ D : Divisor Y, IsIntersectionNumber s (Divisor.toQDivisor D) (cycleIdeal m)
      (m.map fun F => ixn s (Divisor.toQDivisor D) F).sum) ∧
    ∀ hp : IsProper ((cycleIdeal m).subschemeι ≫ s),
      haveI := hp
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        ((cycleIdeal m).subschemeι ≫ s)
      (eulerCharacteristic k ((cycleIdeal m).subschemeι ≫ s)
        (SheafOfModules.unit (cycleIdeal m).subscheme.ringCatSheaf) : ℚ) =
        -(m.map fun F => ixn s (Divisor.toQDivisor (cycleDivisor m + K)) F).sum / 2 := by
  induction m using Multiset.induction_on with
  | empty => exact absurd rfl hm0
  | cons E m ih =>
    obtain ⟨hEp, hEd⟩ := hmE E (Multiset.mem_cons_self E m)
    haveI := hEp
    by_cases hm : m = 0
    · subst hm
      have hI : cycleIdeal (E ::ₘ 0) = E.idealSheaf := by
        rw [cycleIdeal_cons', cycleIdeal_zero, ← Scheme.IdealSheafData.one_eq_top, one_mul]
      rw [hI]
      refine ⟨fun D => ?_, fun hp => ?_⟩
      · simpa using isIntersectionNumber_ixn hsm hEp hEd (Divisor.toQDivisor D)
      · have h := ixn_canonical_add_single (s := s) hY hsm hd hK E
        have hc : cycleDivisor (E ::ₘ 0) + K = K + Finsupp.single E 1 := by
          rw [cycleDivisor_cons]
          simp [cycleDivisor, add_comm]
        simp only [Multiset.map_cons, Multiset.map_zero, Multiset.sum_cons, Multiset.sum_zero,
          add_zero, hc, h]
        ring
    · have hle : m ≤ E ::ₘ m := Multiset.le_cons_self m E
      have hmE' : ∀ F ∈ m, IsProper (F.idealSheaf.subschemeι ≫ s) ∧
          topologicalKrullDim F.idealSheaf.subscheme ≤ 1 :=
        fun F hF => hmE F (Multiset.mem_cons_of_mem hF)
      obtain ⟨ihc, ihd⟩ := ih hm hmE' fun m' hm' => hprop m' (hm'.trans hle)
      haveI hW := isEffectiveCartierDivisor_cycleIdeal hsm m
      haveI hIE :=
        MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm E
      haveI hpJ : IsProper ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s) := by
        rw [← cycleIdeal_cons']
        exact hprop _ le_rfl
      haveI hpW : IsProper ((cycleIdeal m).subschemeι ≫ s) := hprop m hle
      have hdW : topologicalKrullDim (cycleIdeal m).subscheme ≤ 1 :=
        topologicalKrullDim_cycleIdeal_le m fun F hF => (hmE' F hF).2
      have hdJ : topologicalKrullDim (cycleIdeal m * E.idealSheaf).subscheme ≤ 1 := by
        rw [← cycleIdeal_cons']
        exact topologicalKrullDim_cycleIdeal_le _ fun F hF => (hmE F hF).2
      rw [cycleIdeal_cons']
      refine ⟨fun D => ?_, fun hp => ?_⟩
      · haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
        have hcD := MMP.Fourfold.isCartier_of_isSmoothScheme hsm D
        haveI := hcD.isInvertibleModule_divisorialSheaf
        have h1 := isIntersectionNumber_degreeOn hsm hdJ D
        have h2 : D.degreeOn k s (cycleIdeal m * E.idealSheaf).subschemeι hdJ hcD =
            D.degreeOn k s (cycleIdeal m).subschemeι hdW hcD +
              D.degreeOn k s E.idealSheaf.subschemeι hEd hcD :=
          degreeOn_mul (s := s) (cycleIdeal m) E.idealSheaf hdJ hdW hEd D.divisorialSheaf
        have eW := (ihc D).unique (isIntersectionNumber_degreeOn hsm hdW D)
        have eE := ixn_eq_of_isIntersectionNumber (isIntersectionNumber_degreeOn hsm hEd D)
        convert h1 using 1
        rw [Multiset.map_cons, Multiset.sum_cons, eW, eE, h2]
        push_cast
        ring
      · have hstep := eulerCharacteristic_cycleIdeal_mul hsm m E hEd
        have hih := ihd hpW
        have hadj := ixn_canonical_add_single (s := s) hY hsm hd hK E
        have hlin : ∀ F ∈ E ::ₘ m, ixn s (Divisor.toQDivisor (cycleDivisor (E ::ₘ m) + K)) F =
            ixn s (Divisor.toQDivisor (Finsupp.single E 1)) F +
              ixn s (Divisor.toQDivisor (cycleDivisor m + K)) F := by
          intro F hF
          rw [cycleDivisor_cons, add_assoc, map_add, ixn_add hsm (hmE F hF).1 (hmE F hF).2]
        have hsum : (m.map fun F =>
              ixn s (Divisor.toQDivisor (cycleDivisor (E ::ₘ m) + K)) F).sum =
            (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum +
              (m.map fun F => ixn s (Divisor.toQDivisor (cycleDivisor m + K)) F).sum := by
          rw [← Multiset.sum_map_add]
          congr 1
          refine Multiset.map_congr rfl fun F hF => ?_
          rw [hlin F (Multiset.mem_cons_of_mem hF),
            ixn_single_comm hY hsm hd hEp (hmE' F hF).1]
        have hE : ixn s (Divisor.toQDivisor (cycleDivisor (E ::ₘ m) + K)) E =
            ixn s (Divisor.toQDivisor (Finsupp.single E 1)) E +
              (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum +
                ixn s (Divisor.toQDivisor K) E := by
          rw [hlin E (Multiset.mem_cons_self E m), map_add,
            ixn_cycleDivisor_add hsm hEp hEd m (Divisor.toQDivisor K)]
          ring
        rw [map_add, ixn_add hsm hEp hEd] at hadj
        rw [Multiset.map_cons, Multiset.sum_cons, hE, hsum]
        linarith

/-- **A component of genus zero meeting the rest of the cycle twice is not `K + Z`-negative.**
For a component `F` of `Z = ∑_{G ∈ m} G` with `χ(𝒪_F) = 1` and `((Z - F) · F) ≥ 2`, adjunction
`((K + F) · F) = -2` gives `((Z + K) · F) ≥ 0`. -/
private theorem ixn_cycleDivisor_add_canonical_nonneg [DecidableEq (MMP.Mori.PrimeDivisor Y)]
    (hY : MMP.Mori.IsVariety k s)
    (hsm : IsSmoothScheme s) (hd : topologicalKrullDim Y = 2) {K : Divisor Y}
    (hK : K.IsCanonicalDivisor s 2) {m : Multiset (MMP.Mori.PrimeDivisor Y)}
    {F : MMP.Mori.PrimeDivisor Y} (hF : F ∈ m) [hFp : IsProper (F.idealSheaf.subschemeι ≫ s)]
    (hFd : topologicalKrullDim F.idealSheaf.subscheme ≤ 1)
    (hχ : @eulerCharacteristic k _ _ (F.idealSheaf.subschemeι ≫ s) hFp
      (SheafOfModules.unit F.idealSheaf.subscheme.ringCatSheaf)
      (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        (F.idealSheaf.subschemeι ≫ s)) = 1)
    (h2 : 2 ≤ ((m.erase F).map fun G => ixn s (Divisor.toQDivisor (Finsupp.single G 1)) F).sum) :
    0 ≤ ixn s (Divisor.toQDivisor (cycleDivisor m + K)) F := by
  have hadj := ixn_canonical_add_single (s := s) hY hsm hd hK F
  rw [hχ, map_add, ixn_add hsm hFp hFd] at hadj
  rw [map_add, ixn_cycleDivisor_add hsm hFp hFd m (Divisor.toQDivisor K),
    ← Multiset.cons_erase hF, Multiset.map_cons, Multiset.sum_cons]
  push_cast at hadj
  linarith

end Induction

/-! ### First cohomology on the components and on the cycles -/

section Cohomology

/-- On a proper scheme of dimension at most one over `k`, `χ(ℱ) = h⁰(ℱ) - h¹(ℱ)`. -/
private theorem eulerCharacteristic_eq_finrank_sub {C : Scheme.{u}} (g : C ⟶ Spec (.of k))
    [IsProper g] (hdim : topologicalKrullDim C ≤ 1) (F : C.Modules) [F.IsCoherent] :
    eulerCharacteristic k g F = (Module.finrank k (cohomologyOverField k g F 0) : ℤ) -
      (Module.finrank k (cohomologyOverField k g F 1) : ℤ) := by
  rw [eulerCharacteristic_eq_finsum]
  have hz : ∀ n : ℕ, 2 ≤ n → Module.finrank k (cohomologyOverField k g F n) = 0 := fun n hn =>
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_of_topologicalKrullDim_le k g F (d := 1) (i := n) hdim hn)
    Module.finrank_zero_of_subsingleton
  rw [finsum_eq_sum_of_support_subset
    (f := fun m : ℕ => (-1 : ℤ) ^ m * (Module.finrank k (cohomologyOverField k g F m) : ℤ))
    (s := Finset.range 2) fun m hm => ?_]
  · rw [Finset.sum_range_succ, Finset.sum_range_one]; ring
  · by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    simp [hz m hn] at hm

/-- On an integral proper curve over an algebraically closed field, `χ(𝒪) = 1 - h¹(𝒪)`: the
global functions are the constants. -/
private theorem eulerCharacteristic_unit_eq_one_sub [IsAlgClosed k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g
    eulerCharacteristic k g (SheafOfModules.unit C.ringCatSheaf) =
      1 - (Module.finrank k
        (cohomologyOverField k g (SheafOfModules.unit C.ringCatSheaf) 1) : ℤ) := by
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g
  have h0 : Module.finrank k (cohomologyOverField k g (SheafOfModules.unit C.ringCatSheaf) 0) = 1 :=
    (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k g).trans
      (finrank_globalSections_eq_one k g)
  refine (eulerCharacteristic_eq_finrank_sub g hdim _).trans ?_
  omega

/-- **On a curve of genus zero, an invertible sheaf with `H¹ ≠ 0` has degree at most `-2`**:
by [Stacks, Tag 0B90], `H¹(ℒ) = 0` as soon as `deg ℒ ≥ 2g - 1 = -1`. -/
private theorem invertibleCurveDegree_le_neg_two [IsAlgClosed k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] [AlgebraicGeometry.IsCurve k g]
    (hg : Module.finrank k (cohomologyOverField k g (SheafOfModules.unit C.ringCatSheaf) 1) = 0)
    (hdim : topologicalKrullDim C ≤ 1) (L : C.Modules)
    [hL : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L]
    (h : ¬ IsZero (cohomologyOverField k g L 1)) : invertibleCurveDegree k g hdim L ≤ -2 := by
  by_contra hlt
  apply h
  refine
    isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree k g L hL ?_
  have hgen : genus g = 0 := by
    rw [genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField k g 1).toLinearEquiv.finrank_eq, hg]
  rw [hgen]
  push_cast
  have : invertibleCurveDegree k g (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le L =
      invertibleCurveDegree k g hdim L := rfl
  omega

variable {s : Y ⟶ Spec (.of k)}

/-- The cohomology on `J` of a module pushed forward from a closed subscheme `I ⊆ J` is its
cohomology on `I`. -/
private theorem finrank_cohomologyOverField_pushforward_inclusion {J I : Y.IdealSheafData}
    (h : J ≤ I) (G : I.subscheme.Modules) (n : ℕ) :
    Module.finrank k (cohomologyOverField k (J.subschemeι ≫ s)
        ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h)).obj G) n) =
      Module.finrank k (cohomologyOverField k (I.subschemeι ≫ s) G n) := by
  rw [← (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k (Scheme.IdealSheafData.inclusion h)
    (J.subschemeι ≫ s) G n).toLinearEquiv.finrank_eq, ← Category.assoc,
    Scheme.IdealSheafData.inclusion_subschemeι]

/-- **`h¹(𝒪_{W+I}) ≤ h¹(𝒪_Y(-W)|_I) + h¹(𝒪_W)`** for effective Cartier divisors `W`, `I` whose
sum is proper over `k`, from the sequence `0 ⟶ 𝒪_Y(-W)|_I ⟶ 𝒪_{W+I} ⟶ 𝒪_W ⟶ 0`. -/
private theorem finrank_cohomologyOverField_one_unit_mul_le (W I : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor W] [Stacks.Divisors.IsEffectiveCartierDivisor I]
    [IsProper ((W * I).subschemeι ≫ s)] :
    Module.finrank k (cohomologyOverField k ((W * I).subschemeι ≫ s)
        (SheafOfModules.unit (W * I).subscheme.ringCatSheaf) 1) ≤
      Module.finrank k (cohomologyOverField k (I.subschemeι ≫ s)
          ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) 1) +
        Module.finrank k (cohomologyOverField k (W.subschemeι ≫ s)
          (SheafOfModules.unit W.subscheme.ringCatSheaf) 1) := by
  haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left W I)
  haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_right W I)
  haveI := isInvertible_pullback_negativeTwist W I
  haveI hN := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
    (I.subschemeι ≫ s)
    ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) 1
  haveI hOW := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (W.subschemeι ≫ s)
  haveI : IsLocallyNoetherian (W * I).subscheme :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k
      ((W * I).subschemeι ≫ s)
  obtain ⟨v, w, hvw, hS⟩ := exists_shortExact_mul W I
  haveI : FiniteDimensional k (cohomologyOverField k ((W * I).subschemeι ≫ s)
      ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
        (Scheme.IdealSheafData.mul_le_right W I))).obj
        ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W))) 1) :=
    @finiteDimensional_cohomologyOverField_of_isProper k _ _ _ _ _
      (@isCoherent_pushforward_of_isClosedImmersion _ _ _ _ _ _ hN) 1
  haveI : FiniteDimensional k (cohomologyOverField k ((W * I).subschemeι ≫ s)
      ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
        (Scheme.IdealSheafData.mul_le_left W I))).obj
        (SheafOfModules.unit W.subscheme.ringCatSheaf)) 1) :=
    @finiteDimensional_cohomologyOverField_of_isProper k _ _ _ _ _
      (@isCoherent_pushforward_of_isClosedImmersion _ _ _ _ _ _ hOW) 1
  have h := (MMP.Resolution.Bridges.finrank_cohomologyOverField_two_le k
    ((W * I).subschemeι ≫ s) hS 1).2
  have e₁ := finrank_cohomologyOverField_pushforward_inclusion (k := k) (s := s)
    (Scheme.IdealSheafData.mul_le_right W I)
    ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) 1
  have e₂ := finrank_cohomologyOverField_pushforward_inclusion (k := k) (s := s) (le_refl (W * I))
    (SheafOfModules.unit (W * I).subscheme.ringCatSheaf) 1
  have e₃ := finrank_cohomologyOverField_pushforward_inclusion (k := k) (s := s)
    (Scheme.IdealSheafData.mul_le_left W I) (SheafOfModules.unit W.subscheme.ringCatSheaf) 1
  dsimp only at h
  omega

variable [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

/-- `deg_E 𝒪_Y(-W) = -∑_{F ∈ m} (F · E)` for `W = ∑_{F ∈ m} F` and a prime divisor `E` which is
a proper curve on a smooth `Y`. -/
private theorem degreeOn_negativeTwist'_cycleIdeal (hsm : IsSmoothScheme s)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (E : MMP.Mori.PrimeDivisor Y)
    [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) :
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
    haveI := isInvertible_negativeTwist' (cycleIdeal m)
    (MMP.Mori.degreeOn k s E.idealSheaf.subschemeι hd
        (Stacks.Divisors.negativeTwist' (cycleIdeal m)) : ℚ) =
      -(m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
  haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
  haveI := isInvertible_negativeTwist' (cycleIdeal m)
  rw [degreeOn_negativeTwist', degreeOn_invertibleSheaf'_cycleIdeal _ hd hsm m, Int.cast_neg,
    Int.cast_multiset_sum, Multiset.map_map]
  exact congrArg _ (congrArg _ (Multiset.map_congr rfl fun F _ =>
    (ixn_single_eq_degreeOn hsm F hd).symm))

/-- **The minimality step.** Let `W = ∑_{F ∈ m} F` be a cycle with `H¹(𝒪_W) = 0` and `E` a prime
divisor which is a proper curve of genus zero. If `H¹(𝒪_{W+E}) ≠ 0` then `(W · E) ≥ 2`: by the
sequence `0 ⟶ 𝒪_Y(-W)|_E ⟶ 𝒪_{W+E} ⟶ 𝒪_W ⟶ 0` the sheaf `𝒪_Y(-W)|_E` has `H¹ ≠ 0`, so its
degree `-(W · E)` is at most `-2`. -/
private theorem two_le_sum_ixn_of_finrank_cohomologyOverField_one_ne_zero [IsAlgClosed k]
    (hsm : IsSmoothScheme s) (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (E : MMP.Mori.PrimeDivisor Y) [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme = 1)
    (hgE : Module.finrank k (cohomologyOverField k (E.idealSheaf.subschemeι ≫ s)
      (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) 1) = 0)
    [IsProper ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s)]
    (hW : Module.finrank k (cohomologyOverField k ((cycleIdeal m).subschemeι ≫ s)
      (SheafOfModules.unit (cycleIdeal m).subscheme.ringCatSheaf) 1) = 0)
    (hne : Module.finrank k (cohomologyOverField k ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s)
      (SheafOfModules.unit (cycleIdeal m * E.idealSheaf).subscheme.ringCatSheaf) 1) ≠ 0) :
    2 ≤ (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
  haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
  haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm E
  haveI := isInvertible_pullback_negativeTwist (cycleIdeal m) E.idealSheaf
  haveI := isInvertible_negativeTwist' (cycleIdeal m)
  haveI : IsIntegral E.idealSheaf.subscheme := E.integral
  haveI : AlgebraicGeometry.IsCurve k (E.idealSheaf.subschemeι ≫ s) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := hd }
  have hb := finrank_cohomologyOverField_one_unit_mul_le (k := k) (s := s)
    (cycleIdeal m) E.idealSheaf
  rw [hW, add_zero] at hb
  have hdeg := invertibleCurveDegree_le_neg_two (E.idealSheaf.subschemeι ≫ s) hgE hd.le
    ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
      (Stacks.Divisors.negativeTwist (cycleIdeal m))) fun hz => by
      have := ModuleCat.subsingleton_of_isZero hz
      rw [Module.finrank_zero_of_subsingleton (R := k) (M := cohomologyOverField k
        (E.idealSheaf.subschemeι ≫ s) ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
          (Stacks.Divisors.negativeTwist (cycleIdeal m))) 1)] at hb
      omega
  have e := degreeOn_negativeTwist'_cycleIdeal hsm m E hd.le
  rw [MMP.Mori.degreeOn_eq_invertibleCurveDegree k s E.idealSheaf.subschemeι hd.le
    (Stacks.Divisors.negativeTwist' (cycleIdeal m))] at e
  have : (invertibleCurveDegree k (E.idealSheaf.subschemeι ≫ s) hd.le
      ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
        (Stacks.Divisors.negativeTwist (cycleIdeal m))) : ℚ) ≤ -2 := by exact_mod_cast hdeg
  linarith

end Cohomology

/-- The ideal `∏ I_C^{n_C}` of the divisor `∑_{F ∈ m} F` is `∏_{F ∈ m} I_F`. -/
private theorem divisorIdeal_cycleDivisor [DecidableEq (MMP.Mori.PrimeDivisor Y)]
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    MMP.Resolution.divisorIdeal (fun C => (cycleDivisor m C).toNat) = cycleIdeal m := by
  rw [cycleIdeal, Finset.prod_multiset_map_count, MMP.Resolution.divisorIdeal]
  refine (finprod_eq_prod_of_mulSupport_subset _ fun C hC => ?_).trans
    (Finset.prod_congr rfl fun C _ => by rw [cycleDivisor_apply, Int.toNat_natCast])
  rw [Finset.mem_coe, Multiset.mem_toFinset, ← Multiset.count_pos]
  by_contra h0
  exact hC (by simp only [cycleDivisor_apply, Int.toNat_natCast, Nat.eq_zero_of_not_pos h0,
    pow_zero])

private theorem cycleIdeal_singleton (E : MMP.Mori.PrimeDivisor Y) :
    cycleIdeal ({E} : Multiset (MMP.Mori.PrimeDivisor Y)) = E.idealSheaf := by
  simp [cycleIdeal]

/-- An effective divisor is the cycle `∑_{E ∈ m} E` of a multiset `m` of its components. -/
private theorem exists_eq_cycleDivisor {Z : Divisor Y} (hZ : 0 ≤ Z) (hZ0 : Z ≠ 0) :
    ∃ m : Multiset (MMP.Mori.PrimeDivisor Y),
      Z = cycleDivisor m ∧ m ≠ 0 ∧ ∀ E ∈ m, E ∈ Z.support := by
  classical
  set m := Finsupp.toMultiset (Finsupp.mapRange Int.toNat Int.toNat_zero Z)
  have hcount : ∀ C, m.count C = (Z C).toNat := fun C => by
    rw [Finsupp.count_toMultiset, Finsupp.mapRange_apply]
  have hZm : Z = cycleDivisor m :=
    Finsupp.ext fun C => by rw [cycleDivisor_apply, hcount, Int.toNat_of_nonneg (hZ C)]
  refine ⟨m, hZm, fun h0 => hZ0 (by rw [hZm, h0]; rfl), fun E hE => ?_⟩
  rw [Finsupp.mem_toMultiset, Finsupp.mem_support_iff, Finsupp.mapRange_apply] at hE
  exact Finsupp.mem_support_iff.2 fun h => hE (by simp [h])

/-- A cycle of exceptional curves of a germ resolution is proper over `k`. -/
private theorem isProper_cycleIdeal {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {f : Y ⟶ X} (hf : IsGermResolution sX P f) {m : Multiset (MMP.Mori.PrimeDivisor Y)}
    (hm : ∀ E ∈ m, IsGermExceptionalCurve f P E) :
    IsProper ((cycleIdeal m).subschemeι ≫ f ≫ sX) :=
  isProper_of_support_subset hf _ fun x hx => by
    obtain ⟨E, hE, hxE⟩ := (mem_support_cycleIdeal m x).1 hx
    exact (hm E hE).1.prop.2 hxE

end Cycles

/-- **Euler characteristic of an exceptional cycle.** Let `f : Y ⟶ X` resolve a normal surface
germ `(X, P)` over an algebraically closed field `k`, let `K` be a canonical divisor of `Y` and
`Z = ∑ nᵢ Eᵢ` a nonzero effective divisor supported on the exceptional curves of `f`. Then the
closed subscheme of `Y` with ideal `∏ I_{Eᵢ}^{nᵢ}` is proper over `k`, the intersection numbers
`(Z · Z) = a` and `(K · Z) = b` are defined, and `χ(Z, 𝒪_Z) = -(a + b) / 2`. -/
@[mmp "lem_mmp_foundation_exceptional_cycle_euler_characteristic"]
public theorem IsGermResolution.eulerCharacteristic_divisorIdeal_eq {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hf : IsGermResolution sX P f) {K : Divisor Y} (hK : K.IsCanonicalDivisor (f ≫ sX) 2)
    {Z : Divisor Y} (hZ : 0 ≤ Z) (hZ0 : Z ≠ 0)
    (hZE : ∀ C ∈ Z.support, IsGermExceptionalCurve f P C) :
    ∃ _ : IsProper ((MMP.Resolution.divisorIdeal fun C => (Z C).toNat).subschemeι ≫ f ≫ sX),
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        ((MMP.Resolution.divisorIdeal fun C => (Z C).toNat).subschemeι ≫ f ≫ sX)
      ∃ a b : ℚ,
        IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor Z)
          (MMP.Resolution.divisorIdeal fun C => (Z C).toNat) a ∧
        IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor K)
          (MMP.Resolution.divisorIdeal fun C => (Z C).toNat) b ∧
        (eulerCharacteristic k
          ((MMP.Resolution.divisorIdeal fun C => (Z C).toNat).subschemeι ≫ f ≫ sX)
          (SheafOfModules.unit
            (MMP.Resolution.divisorIdeal fun C => (Z C).toNat).subscheme.ringCatSheaf) : ℚ) =
          -(a + b) / 2 := by
  classical
  obtain ⟨m, hZm, hm0, hmem⟩ := exists_eq_cycleDivisor hZ hZ0
  have hexc : ∀ E ∈ m, IsGermExceptionalCurve f P E := fun E hE => hZE E (hmem E hE)
  have hmE : ∀ E ∈ m, IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX) ∧
      topologicalKrullDim E.idealSheaf.subscheme ≤ 1 := fun E hE => by
    obtain ⟨h1, h2⟩ := (hexc E hE).isProper sX hf
    exact ⟨h2, h1.2.le⟩
  have hprop : ∀ m' ≤ m, IsProper ((cycleIdeal m').subschemeι ≫ f ≫ sX) := fun m' hm' =>
    isProper_cycleIdeal hf fun E hE => hexc E (Multiset.mem_of_le hm' hE)
  have hsm := hf.isSmoothResolution.isSmoothScheme
  obtain ⟨hc, hχ⟩ := isIntersectionNumber_and_eulerCharacteristic_cycleIdeal (s := f ≫ sX)
    hf.isVariety hsm hf.topologicalKrullDim_eq hK m hm0 hmE hprop
  have hdiv : MMP.Resolution.divisorIdeal (fun C => (Z C).toNat) = cycleIdeal m := by
    rw [hZm]; exact divisorIdeal_cycleDivisor m
  rw [hdiv]
  refine ⟨hprop m le_rfl, (m.map fun F => ixn (f ≫ sX) (Divisor.toQDivisor Z) F).sum,
    (m.map fun F => ixn (f ≫ sX) (Divisor.toQDivisor K) F).sum, hc Z, hc K, ?_⟩
  rw [hχ (hprop m le_rfl), ← hZm, ← Multiset.sum_map_add]
  congr 3
  exact Multiset.map_congr rfl fun F hF => by
    rw [map_add, ixn_add hsm (hmE F hF).1 (hmE F hF).2]

/-- **Positive exceptional Euler characteristics kill `H¹`.** Let `f : Y ⟶ X` resolve a normal
surface germ `(X, P)` over an algebraically closed field `k`, and let `Z = ∑ nᵢ Eᵢ` be a nonzero
effective divisor supported on the exceptional curves of `f`. If `χ(Z', 𝒪_{Z'}) > 0` for every
nonzero effective divisor `Z' ≤ Z`, then `H¹(Z, 𝒪_Z) = 0`, where the scheme `Z` is the closed
subscheme of `Y` with ideal `∏ I_{Eᵢ}^{nᵢ}`. -/
@[mmp "lem_mmp_foundation_positive_cycles_hone_vanish"]
public theorem IsGermResolution.subsingleton_cohomologyOverField_one_divisorIdeal {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X}
    (hf : IsGermResolution sX P f) {Z : Divisor Y} (hZ : 0 ≤ Z) (hZ0 : Z ≠ 0)
    (hZE : ∀ C ∈ Z.support, IsGermExceptionalCurve f P C)
    (hχ : ∀ Z' : Divisor Y, 0 ≤ Z' → Z' ≤ Z → Z' ≠ 0 →
      ∀ _ : IsProper ((MMP.Resolution.divisorIdeal fun C => (Z' C).toNat).subschemeι ≫ f ≫ sX),
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          ((MMP.Resolution.divisorIdeal fun C => (Z' C).toNat).subschemeι ≫ f ≫ sX)
        0 < eulerCharacteristic k
          ((MMP.Resolution.divisorIdeal fun C => (Z' C).toNat).subschemeι ≫ f ≫ sX)
          (SheafOfModules.unit
            (MMP.Resolution.divisorIdeal fun C => (Z' C).toNat).subscheme.ringCatSheaf)) :
    Subsingleton (cohomologyOverField k
      ((MMP.Resolution.divisorIdeal fun C => (Z C).toNat).subschemeι ≫ f ≫ sX)
      (SheafOfModules.unit
        (MMP.Resolution.divisorIdeal fun C => (Z C).toNat).subscheme.ringCatSheaf) 1) := by
  classical
  haveI : QuasiCompact (f ≫ sX) := hf.quasiCompact_comp
  haveI : IsNormal Y := hf.isSmoothResolution.isNormal
  have hY : MMP.Mori.IsVariety k (f ≫ sX) := hf.isVariety
  haveI : MMP.Mori.IsVariety k (f ≫ sX) := hY
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have hsm := hf.isSmoothResolution.isSmoothScheme
  have hd := hf.topologicalKrullDim_eq
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm
    (n := 2) hd
  obtain ⟨m, hZm, hm0, hmem⟩ := exists_eq_cycleDivisor hZ hZ0
  have hexc : ∀ E ∈ m, IsGermExceptionalCurve f P E := fun E hE => hZE E (hmem E hE)
  have hmE : ∀ E ∈ m, IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX) ∧
      topologicalKrullDim E.idealSheaf.subscheme ≤ 1 := fun E hE => by
    obtain ⟨h1, h2⟩ := (hexc E hE).isProper sX hf
    exact ⟨h2, h1.2.le⟩
  have hprop : ∀ m' ≤ m, IsProper ((cycleIdeal m').subschemeι ≫ f ≫ sX) := fun m' hm' =>
    isProper_cycleIdeal hf fun E hE => hexc E (Multiset.mem_of_le hm' hE)
  -- the positivity hypothesis for subcycles given as multisets
  have hχm : ∀ m' ≤ m, m' ≠ 0 → ∀ hp : IsProper ((cycleIdeal m').subschemeι ≫ f ≫ sX),
      haveI := hp
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        ((cycleIdeal m').subschemeι ≫ f ≫ sX)
      0 < eulerCharacteristic k ((cycleIdeal m').subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit (cycleIdeal m').subscheme.ringCatSheaf) := by
    intro m' hm' hm0'
    have h := hχ (cycleDivisor m') (fun C => by rw [cycleDivisor_apply]; positivity)
      (fun C => by
        rw [hZm, cycleDivisor_apply, cycleDivisor_apply]
        exact_mod_cast Multiset.count_le_of_le C hm')
      (fun h0 => hm0' (Multiset.ext.2 fun C => by
        have := DFunLike.congr_fun h0 C
        rw [cycleDivisor_apply] at this
        simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_eq_zero] at this
        rw [this, Multiset.count_zero]))
    rw [divisorIdeal_cycleDivisor] at h
    exact h
  -- the components: `h¹(𝒪_E) = 0` and `χ(𝒪_E) = 1`
  have hcomp : ∀ E ∈ m,
      Module.finrank k (cohomologyOverField k (E.idealSheaf.subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) 1) = 0 ∧
      ∀ hp : IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX),
        haveI := hp
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          (E.idealSheaf.subschemeι ≫ f ≫ sX)
        eulerCharacteristic k (E.idealSheaf.subschemeι ≫ f ≫ sX)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) = 1 := by
    intro E hE
    obtain ⟨hEp, hEd⟩ := hmE E hE
    haveI := hEp
    haveI : IsIntegral E.idealSheaf.subscheme := E.integral
    have h1 := hχm {E} (Multiset.singleton_le.2 hE) (Multiset.singleton_ne_zero E)
    rw [cycleIdeal_singleton] at h1
    have h2 := h1 hEp
    have h3 := eulerCharacteristic_unit_eq_one_sub (E.idealSheaf.subschemeι ≫ f ≫ sX) hEd
    refine ⟨by omega, fun _ => by omega⟩
  -- the minimal bad cycle, by strong induction on the size of the cycle
  have key : ∀ n : ℕ, ∀ m' : Multiset (MMP.Mori.PrimeDivisor Y), m' ≤ m →
      Multiset.card m' = n → m' ≠ 0 →
      Module.finrank k (cohomologyOverField k ((cycleIdeal m').subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit (cycleIdeal m').subscheme.ringCatSheaf) 1) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro m' hm' hcard hm0'
    by_contra hne
    have hmE' : ∀ E ∈ m', IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX) ∧
        topologicalKrullDim E.idealSheaf.subscheme ≤ 1 :=
      fun E hE => hmE E (Multiset.mem_of_le hm' hE)
    -- each component `E` of `m'` meets the rest of `m'` with multiplicity at least two
    have hge : ∀ E ∈ m',
        2 ≤ ((m'.erase E).map fun F =>
          ixn (f ≫ sX) (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
      intro E hE
      have hEm : E ∈ m := Multiset.mem_of_le hm' hE
      obtain ⟨hEp, hEd⟩ := hmE E hEm
      haveI := hEp
      have hm'eq : m' = E ::ₘ m'.erase E := (Multiset.cons_erase hE).symm
      by_cases hW : m'.erase E = 0
      · exfalso
        apply hne
        rw [hm'eq, hW, Multiset.cons_zero, cycleIdeal_singleton]
        exact (hcomp E hEm).1
      · have hWcard : Multiset.card (m'.erase E) < n := by
          rw [← hcard, Multiset.card_erase_of_mem hE]
          exact Nat.pred_lt (Multiset.card_pos.2 hm0').ne'
        haveI : IsProper ((cycleIdeal (m'.erase E) * E.idealSheaf).subschemeι ≫ f ≫ sX) := by
          rw [← cycleIdeal_cons', ← hm'eq]; exact hprop m' hm'
        refine two_le_sum_ixn_of_finrank_cohomologyOverField_one_ne_zero hsm _ E
          ((hexc E hEm).isProper sX hf).1.2 (hcomp E hEm).1
          (ih _ hWcard _ ((Multiset.erase_le E m').trans hm') rfl hW) ?_
        rwa [← cycleIdeal_cons', ← hm'eq]
    -- the Euler characteristic of `m'` is then nonpositive
    have hprop' : ∀ m'' ≤ m', IsProper ((cycleIdeal m'').subschemeι ≫ f ≫ sX) :=
      fun m'' h => hprop m'' (h.trans hm')
    obtain ⟨-, hχf⟩ := isIntersectionNumber_and_eulerCharacteristic_cycleIdeal (s := f ≫ sX)
      hY hsm hd hK m' hm0' hmE' hprop'
    have hpos := hχm m' hm' hm0' (hprop m' hm')
    have hfor := hχf (hprop m' hm')
    have hterm : ∀ F ∈ m', 0 ≤ ixn (f ≫ sX) (Divisor.toQDivisor (cycleDivisor m' + K)) F := by
      intro F hF
      have hFm : F ∈ m := Multiset.mem_of_le hm' hF
      obtain ⟨hFp, hFd⟩ := hmE F hFm
      exact ixn_cycleDivisor_add_canonical_nonneg hY hsm hd hK hF hFd ((hcomp F hFm).2 hFp)
        (hge F hF)
    have hsum := Multiset.sum_nonneg (s := m'.map fun F =>
      ixn (f ≫ sX) (Divisor.toQDivisor (cycleDivisor m' + K)) F) (by
        intro x hx
        obtain ⟨F, hF, rfl⟩ := Multiset.mem_map.1 hx
        exact hterm F hF)
    haveI := hprop m' hm'
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((cycleIdeal m').subschemeι ≫ f ≫ sX)
    have hq : (0 : ℚ) < (eulerCharacteristic k ((cycleIdeal m').subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit (cycleIdeal m').subscheme.ringCatSheaf) : ℚ) := by
      exact_mod_cast hpos
    rw [hfor] at hq
    linarith
  have hdiv : MMP.Resolution.divisorIdeal (fun C => (Z C).toNat) = cycleIdeal m := by
    rw [hZm]; exact divisorIdeal_cycleDivisor m
  rw [hdiv]
  haveI := hprop m le_rfl
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    ((cycleIdeal m).subschemeι ≫ f ≫ sX)
  haveI := finiteDimensional_cohomologyOverField_of_isProper k ((cycleIdeal m).subschemeι ≫ f ≫ sX)
    (SheafOfModules.unit (cycleIdeal m).subscheme.ringCatSheaf) 1
  exact Module.finrank_zero_iff.1 (key _ m le_rfl rfl hm0)

end MMP.Flips
