module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.NonvanishingNumericallyTrivial
public import MMP.AlgebraicGeometry.MMP.BasepointFree.NonvanishingAdaptedResolution
public import MMP.AlgebraicGeometry.MMP.BasepointFree.NonvanishingTieBreaker
public import MMP.AlgebraicGeometry.MMP.BasepointFree.NonvanishingTieBreakerRestriction
public import MMP.AlgebraicGeometry.MMP.BasepointFree.NonvanishingRestriction
public import MMP.AlgebraicGeometry.MMP.BasepointFree.AdaptedResolution

@[expose] public section

section

/-!
# The non-vanishing theorem

The proof of Kollár–Mori 3.4 by induction on the dimension: the reduction to smooth data, the
numerically trivial case, and otherwise restriction to the tie-breaking divisor of an adapted
resolution, on which the induction hypothesis applies.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.5
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3aNonvanishingProof

section Relation

variable {k : Type} [Field k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
  [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {F : MMP.Mori.PrimeDivisor Y} [IsLocallyNoetherian F.idealSheaf.subscheme]
  [IsNormal F.idealSheaf.subscheme] [CompactSpace F.idealSheaf.subscheme]

/-- `𝒪_F(E') ≅ ι^* 𝒪_Y(E)` is additive in `(E, E')`, for the inclusion `ι` of a smooth prime
divisor `F` of a smooth scheme. -/
private theorem nonempty_divisorialSheaf_add_iso (hY : IsSmoothScheme sY)
    (hF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ sY)) {a b : Divisor Y}
    {a' b' : Divisor F.idealSheaf.subscheme}
    (ha : Nonempty (a'.divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj a.divisorialSheaf))
    (hb : Nonempty (b'.divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj b.divisorialSheaf)) :
    Nonempty ((a' + b').divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj (a + b).divisorialSheaf) := by
  obtain ⟨ea⟩ := ha
  obtain ⟨eb⟩ := hb
  have hc : ∀ D : Divisor Y, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hY
  have hc' : ∀ D : Divisor F.idealSheaf.subscheme, D.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hF
  exact ⟨((hc' a').divisorialSheafTensorIso (hc' b')).symm ≪≫ MonoidalCategory.tensorIso ea eb ≪≫
    (Stacks.RelativeVeryAmple.pullbackTensorModulesIso F.idealSheaf.subschemeι _ _).symm ≪≫
    (Scheme.Modules.pullback F.idealSheaf.subschemeι).mapIso
      ((hc a).divisorialSheafTensorIso (hc b))⟩

/-- `𝒪_F(E') ≅ ι^* 𝒪_Y(E)` passes to positive multiples. -/
private theorem nonempty_divisorialSheaf_nsmul_iso (hY : IsSmoothScheme sY)
    (hF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ sY)) {a : Divisor Y}
    {a' : Divisor F.idealSheaf.subscheme}
    (ha : Nonempty (a'.divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj a.divisorialSheaf))
    {j : ℕ} (hj : 0 < j) :
    Nonempty (((j : ℤ) • a').divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj ((j : ℤ) • a).divisorialSheaf) := by
  induction j, Nat.one_le_iff_ne_zero.mpr hj.ne' using Nat.le_induction with
  | base => simpa using ha
  | succ j hj ih =>
    simpa [add_smul] using nonempty_divisorialSheaf_add_iso hY hF (ih (by omega)) ha

/-- On a smooth variety `Z`, the pull-back of an invertible sheaf along any morphism `u` is
`𝒪_Z(B)` for a divisor `B` of `Z`. -/
private theorem exists_nonempty_divisorialSheaf_iso_pullback {Z W : Scheme.{0}}
    [IsLocallyNoetherian Z] [IsNormal Z] (g : Z ⟶ Spec (.of k)) [IsSmoothVariety k g]
    (u : Z ⟶ W) (L : W.Modules) [Stacks.Ample.IsInvertibleModule W L] :
    ∃ B : Divisor Z, Nonempty (B.divisorialSheaf ≅ (Scheme.Modules.pullback u).obj L) := by
  haveI : Stacks.Ample.IsInvertibleModule Z ((Scheme.Modules.pullback u).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback u L
  exact (Divisor.cartier_weil_dictionary_of_isSmoothVariety k g).2.2.2.2.1 _ inferInstance

/-- A nonzero global section of `𝒪_Z(E)` makes `H⁰(Z, M)` nonzero for every `M ≅ 𝒪_Z(E)`. -/
private theorem nontrivial_cohomologyOverField_zero_of_iso {Z : Scheme.{0}}
    [IsLocallyNoetherian Z] [IsNormal Z] (g : Z ⟶ Spec (.of k)) {E : Divisor Z} {M : Z.Modules}
    (e : E.divisorialSheaf ≅ M) (σ : E.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    Nontrivial (cohomologyOverField k g M 0) := by
  haveI : Nontrivial (E.divisorialSubmodule ⊤) := ⟨⟨σ, 0, hσ⟩⟩
  let ev := SheafOfModules.evaluation Z.ringCatSheaf (Opposite.op ⊤)
  haveI : Nontrivial (ev.obj E.divisorialSheaf) :=
    inferInstanceAs (Nontrivial (E.divisorialSubmodule ⊤))
  haveI hM : Nontrivial (ev.obj M) := (ev.mapIso e).toLinearEquiv.symm.toEquiv.nontrivial
  haveI : Nontrivial ((restrictScalarsOverBase k g).obj (ev.obj M)) := hM
  exact (cohomologyOverFieldZeroLinearIso k g M).toLinearEquiv.toEquiv.nontrivial

/-- Round-up commutes with restriction to a smooth prime divisor `F` of a smooth variety, at the
level of sheaves: if `F` is not a component of the `ℚ`-divisor `A` and `F + A` is snc, then
`𝒪_F(⌈A|_F⌉) ≅ ι^* 𝒪_Y(⌈A⌉)`. -/
private theorem nonempty_divisorialSheaf_roundUp_restrictPrimeDivisor_iso {Z : Scheme.{0}}
    [IsLocallyNoetherian Z] [IsNormal Z] (g : Z ⟶ Spec (.of k)) [IsSmoothVariety k g]
    (P : MMP.Mori.PrimeDivisor Z) [Smooth (P.idealSheaf.subschemeι ≫ g)]
    [IsLocallyNoetherian P.idealSheaf.subscheme] [IsNormal P.idealSheaf.subscheme]
    (A : DivisorWithCoeffs ℚ Z) (hAP : A.coeff P = 0)
    (hsnc : DivisorWithCoeffs.IsSNC g (Finsupp.single P (1 : ℚ) + A)) :
    Nonempty ((A.restrictPrimeDivisor P).roundUp.divisorialSheaf ≅
      (Scheme.Modules.pullback P.idealSheaf.subschemeι).obj A.roundUp.divisorialSheaf) := by
  have hround := DivisorWithCoeffs.restrictPrimeDivisor_roundUp g inferInstance
    ((isSmoothScheme_iff _).mpr inferInstance) P ((isSmoothScheme_iff _).mpr inferInstance) 0
    Divisor.isCartier_zero
    (by simpa using (show ¬ ((P.support : Set Z) ⊆ ∅) from
      fun h => h (MMP.Flips.primeDivisor_genericPoint_mem_support _))) A hAP hsnc
  simp only [map_zero, zero_add] at hround
  obtain ⟨-, eA, -⟩ := Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety k g P
    A.roundUp (by rw [DivisorWithCoeffs.coeff_roundUp, hAP, Int.ceil_zero])
  rwa [hround] at eA

end Relation

section TieBreaker

variable {Y : Scheme.{0}} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}

/-- Each `F_j` lies in the support of the reduced divisor `∑_j F_j`. -/
private theorem mem_support_sum_single_one (hF : Function.Injective F) (j : Fin s) :
    F j ∈ (∑ i, Finsupp.single (F i) (1 : ℤ)).support := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply, hF.eq_iff]

/-- The test boundary `∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j` does not contain `F_{j'}`. -/
private theorem coeff_tieBreakerBoundary_self (hF : Function.Injective F) {r a p : Fin s → ℚ}
    {j' : Fin s} {c : ℚ} : (tieBreakerBoundary F r a p j' c).coeff (F j') = 0 := by
  classical
  rw [tieBreakerBoundary, DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finsupp.single_apply, if_neg]
  exact fun h' => (Finset.mem_erase.mp hj).1 (hF h')

/-- `F_{j'} + ∑_{j ≠ j'} (…) F_j` is supported on the components of `∑_j F_j`. -/
private theorem support_single_add_tieBreakerBoundary_subset (hF : Function.Injective F)
    {r a p : Fin s → ℚ} {j' : Fin s} {c : ℚ} :
    (Finsupp.single (F j') (1 : ℚ) + tieBreakerBoundary F r a p j' c).support ⊆
      (∑ i, Finsupp.single (F i) (1 : ℤ)).support := by
  classical
  intro P hP
  rcases Finset.mem_union.mp (Finsupp.support_add hP) with h1 | h2
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h1)]
    exact mem_support_sum_single_one hF j'
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum h2)
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hj)]
    exact mem_support_sum_single_one hF j

end TieBreaker

/-- A prime divisor of an `n`-dimensional variety has dimension `n - 1`. -/
private theorem exists_topologicalKrullDim_subscheme_eq {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] [IsLocallyNoetherian Y]
    (P : MMP.Mori.PrimeDivisor Y) {n : ℕ} (hdim : topologicalKrullDim Y = n) :
    ∃ d : ℕ, topologicalKrullDim P.idealSheaf.subscheme = d ∧ d + 1 = n := by
  haveI : IsIntegral P.idealSheaf.subscheme := P.integral
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY P.genericPoint
  rw [P.coheight_genericPoint, hdim, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    ← MMP.Mori.topologicalKrullDim_subscheme_eq] at h
  have hne : topologicalKrullDim P.idealSheaf.subscheme ≠ ⊥ := by
    rw [ne_eq, topologicalKrullDim_eq_bot_iff_isEmpty, not_isEmpty_iff]
    infer_instance
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← he] at h ⊢
  have h' : e + 1 = n := by exact_mod_cast h
  lift e to ℕ using fun ht => by simp [ht] at h'
  exact ⟨e, rfl, by exact_mod_cast h'⟩

/-- A divisor on a variety of dimension `0` is numerically trivial: there are no curves. -/
private theorem isNumericallyTrivial_of_topologicalKrullDim_eq_zero {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {D : Divisor X} (hD : D.IsCartier)
    (hdim : topologicalKrullDim X = 0) :
    (Divisor.toQDivisor D).IsNumericallyTrivial k sX := by
  refine ⟨QDivisor.isQCartier_toQDivisor hD, QDivisor.isQCartier_zero,
    fun C i _ _ _ hC => absurd ?_ (by simp : ¬ (1 : WithBot ℕ∞) ≤ 0)⟩
  rw [← hC, ← hdim]
  exact i.isClosedEmbedding.isInducing.topologicalKrullDim_le

/-- The non-vanishing statement in dimension `n`. -/
private def NonvanishingIn (k : Type) [Field k] (n : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] (KZ DZ : Divisor Z) (GZ : QDivisor Z) (aZ : ℚ),
    IsNonvanishingDatum sZ n KZ DZ GZ aZ → HasNonvanishingProperty DZ GZ

/-- The smooth case of the induction step. -/
private theorem hasNonvanishingProperty_of_isSmoothNonvanishingDatum {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {n : ℕ} (ih : ∀ m < n, NonvanishingIn k m)
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {K D : Divisor X} {G : QDivisor X} {a : ℚ}
    (h : IsSmoothNonvanishingDatum sX n K D G a) : HasNonvanishingProperty D G := by
  classical
  by_cases hD : (Divisor.toQDivisor D).IsNumericallyTrivial k sX
  · exact ⟨0, fun m hm => h.exists_ne_zero_of_isNumericallyTrivial hD hm⟩
  have hn : 1 ≤ n := by
    by_contra hn0
    refine hD (isNumericallyTrivial_of_topologicalKrullDim_eq_zero h.isCartier ?_)
    rw [h.isKltPair.1.2.1.1]
    simp [show n = 0 by omega]
  obtain ⟨x, q, e, M, Y, _, _, _, f, s, F, b, p, r, hres⟩ :=
    h.exists_isNonvanishingAdaptedResolution hn hD
  obtain ⟨p', j', c, ht⟩ := hres.exists_isNonvanishingTieBreaker
  haveI hPY : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := ht.isProjectiveVariety_source
  haveI : AlgebraicGeometry.IsProperVariety k sX := ht.isProperVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hPY.toIsVariety
  have hsm : IsSmoothScheme (f ≫ sX) := ht.isLogResolution.isSmoothScheme
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hsm
  haveI : IsProper f := ht.isLogResolution.isProper
  haveI : IsDominant f := ht.isLogResolution.isBirationalMorphism.isDominant
  have hdim : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      ht.isLogResolution.isBirationalMorphism).symm.trans h.isKltPair.1.2.1.1
  -- the pull-back `D' = f^*D`
  obtain ⟨D', hD'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant f h.isCartier
  set ι := (F j').idealSheaf.subschemeι
  set A := tieBreakerBoundary F r b p' j' c
  -- `F = F_{j'}` is a smooth projective variety of dimension `n - 1`
  have hsmF : IsSmoothScheme (ι ≫ f ≫ sX) :=
    ht.isSNC.1 (F j') (mem_support_sum_single_one ht.injective j')
  haveI : IsIntegral (F j').idealSheaf.subscheme := (F j').integral
  haveI : Smooth (ι ≫ f ≫ sX) := (isSmoothScheme_iff _).mp hsmF
  haveI : AlgebraicGeometry.IsVariety k (ι ≫ f ≫ sX) := ⟨⟩
  haveI : IsSmoothVariety k (ι ≫ f ≫ sX) := ⟨⟩
  haveI : CompactSpace (F j').idealSheaf.subscheme := QuasiCompact.compactSpace_of_compactSpace ι
  haveI : IsLocallyNoetherian (F j').idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ f ≫ sX)
  haveI : IsNormal (F j').idealSheaf.subscheme := isNormal_of_smooth_over_field (ι ≫ f ≫ sX)
  obtain ⟨d, hd, hnd⟩ := exists_topologicalKrullDim_subscheme_eq (f ≫ sX) (F j') hdim
  obtain ⟨KF, hKF⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (ι ≫ f ≫ sX) hsmF
    (show _ = ((n - 1 : ℕ) : WithBot ℕ∞) by rw [hd, ← hnd, Nat.add_sub_cancel])
  -- a divisor `D_F` with `𝒪_F(D_F) ≅ 𝒪_Y(f^*D)|_F`
  haveI := (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D').isInvertibleModule_divisorialSheaf
  obtain ⟨DF, eDF⟩ := exists_nonempty_divisorialSheaf_iso_pullback (ι ≫ f ≫ sX) ι
    D'.divisorialSheaf
  have hDF : DF.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmF _
  -- the induction hypothesis on `F`
  have hdatum := ht.isSmoothNonvanishingDatum_restrictPrimeDivisor hD' hDF eDF
    (Int.le_ceil (a + c * (q - a))) hKF
  obtain ⟨mF, hmF⟩ := ih (n - 1) (by omega) _ _ _ _ _ _ hdatum.toIsNonvanishingDatum
  refine ⟨max (max mF ⌈a + c * (q - a)⌉) 1, fun β hβ => ?_⟩
  obtain ⟨σ, hσ⟩ := hmF β (le_trans (le_max_left _ _) (le_of_max_le_left hβ))
  -- `𝒪_F(⌈A|_F⌉) ≅ 𝒪_Y(⌈A⌉)|_F`
  haveI : IsSmoothVariety k (f ≫ sX) := ⟨⟩
  have eA := nonempty_divisorialSheaf_roundUp_restrictPrimeDivisor_iso (f ≫ sX) (F j') A
    (coeff_tieBreakerBoundary_self ht.injective) (ht.isSNC.of_support_subset
      (support_single_add_tieBreakerBoundary_subset ht.injective))
  have eb := nonempty_divisorialSheaf_nsmul_iso hsm hsmF eDF (j := β.toNat) (by omega)
  rw [Int.toNat_of_nonneg (by omega)] at eb
  obtain ⟨eβ⟩ := nonempty_divisorialSheaf_add_iso hsm hsmF eb eA
  exact ht.exists_ne_zero_divisorialSubmodule_of_nontrivial
    ((Int.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans (le_of_max_le_left hβ)))
    hD' (nontrivial_cohomologyOverField_zero_of_iso _ eβ σ hσ)

/-- Non-vanishing holds in every dimension `n`. -/
private theorem nonvanishingIn (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ) :
    NonvanishingIn k n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z _ _ _ _ sZ _ KZ DZ GZ aZ hZ
    exact hZ.hasNonvanishingProperty_of_isSmoothNonvanishingDatum
      fun _ _ _ _ _ _ _ _ _ _ _ hY => hasNonvanishingProperty_of_isSmoothNonvanishingDatum ih hY

end MMP.FourfoldProofs.Km3aNonvanishingProof

end

section

/-!
# The non-vanishing theorem

Let `k` be an algebraically closed field of characteristic `0`, `X` a proper variety over `k`,
`D` a nef Cartier divisor and `G` a `ℚ`-divisor on `X`. If `aD + G - K_X` is `ℚ`-Cartier, nef and
big for some rational `a > 0`, and `(X, -G)` is klt, then `H⁰(X, mD + ⌈G⌉) ≠ 0` for all
sufficiently large integers `m`.

The proof is by induction on `dim X`: one reduces to a smooth projective `X` with `Supp G` snc
and `aD + G - K_X` ample, treats `D ≡ 0` by Kawamata–Viehweg vanishing for the round-up, and
otherwise produces, on an adapted log resolution with a tie-breaker, a prime divisor `F` to
which sections restrict surjectively and on which the induction hypothesis applies.

## Main results

* `MMP.Mori.IsNonvanishingDatum.hasNonvanishingProperty`: the non-vanishing theorem.

## Implementation notes

The hypotheses are bundled as `MMP.Mori.IsNonvanishingDatum` and the conclusion is
`MMP.Mori.HasNonvanishingProperty`: there is `m₀ : ℤ` such that `𝒪_X(mD + ⌈G⌉)` has a nonzero
global section for every integer `m ≥ m₀`. The canonical divisor `K` and the dimension `n` are
explicit, as in `MMP.Mori.IsKltPair`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.4,
  proof in 3.5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **The non-vanishing theorem** (Kollár–Mori 3.4). Let `X` be a proper variety over an
algebraically closed field of characteristic `0`, `D` a nef Cartier divisor and `G` a
`ℚ`-divisor on `X` such that `aD + G - K_X` is `ℚ`-Cartier, nef and big for some rational
`a > 0` and `(X, -G)` is klt. Then `H⁰(X, mD + ⌈G⌉) ≠ 0` for all sufficiently large `m`. -/
@[mmp "thm_km3a_nonvanishing"]
public theorem IsNonvanishingDatum.hasNonvanishingProperty
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ}
    (h : IsNonvanishingDatum sX n K D G a) :
    HasNonvanishingProperty D G :=
  MMP.FourfoldProofs.Km3aNonvanishingProof.nonvanishingIn k n X sX K D G a h

end MMP.Mori

end
