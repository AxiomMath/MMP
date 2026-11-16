module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.Nonvanishing
public import MMP.AlgebraicGeometry.MMP.BasepointFree.TestDivisorAmple
public import MMP.AlgebraicGeometry.Positivity.AmpleAdjunctionRestriction
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy

/-!
# Non-vanishing on the tie-breaking divisor

Let `(f; F_•; a_•; p_•; r_•)` be an `m`-adapted resolution of a basepoint-free datum
`(X, Δ, D, a)` with a tie-breaker `(j', c)` and test boundary
`A = ∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j`, and put `F = F_{j'}`. Then there is an integer `b₁`
such that `H⁰(F, 𝒪_Y(b f^*D + ⌈A⌉)|_F) ≠ 0` for every integer `b ≥ b₁`. Indeed `F` is a smooth
projective variety, `f^*D|_F` is nef, `(F, -A|_F)` is klt, and by adjunction
`a_F f^*D|_F + A|_F - K_F` is ample for `a_F = ⌈cm + a⌉`, so the non-vanishing theorem applies
on `F`.

## Main results

* `MMP.Mori.IsBasepointFreeTieBreaker.exists_nontrivial_cohomologyOverField_restriction`: for
  `b` large, `H⁰(F_{j'}, i^* 𝒪_Y(b f^*D + ⌈A⌉))` is a nonzero `k`-vector space.

## Implementation notes

The restriction of `𝒪_Y(L)` to `F_{j'}` is the pull-back `i^* 𝒪_Y(L)` along the closed
immersion `i : F_{j'} ⟶ Y`, and its `H⁰` is taken over `k` through `i ≫ f ≫ sX`; this is the
target of the restriction map in
`MMP.Mori.IsBasepointFreeTieBreaker.surjective_restriction_pullback_add_roundUp`. The pull-back
`f^*D` is any `D'` with `D.IsPullback f hB D'`, and the statement is made for every such `D'`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, 3.2 Step 5
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3aBpfNonvanishingOnDivisorProof

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

end Relation

section Restriction

variable {Y : Scheme.{0}} {ι : Type*} [DecidableEq ι]

/-- The coefficients of the restriction of `∑_{j ∈ s} γ_j F_j` to a prime divisor `F_{j'}`
(`j' ∉ s`, the `F_j` distinct) are `∑_{j ∈ s} (F_j · Q) γ_j`. -/
private theorem coeff_restrictPrimeDivisor_sum_single [IsLocallyNoetherian Y] [CompactSpace Y]
    {R : Type*} [AddCommMonoid R] (F : ι → MMP.Mori.PrimeDivisor Y) (hF : Function.Injective F)
    (s : Finset ι) {j' : ι} (hj' : j' ∉ s) (γ : ι → R)
    (Q : MMP.Mori.PrimeDivisor (F j').idealSheaf.subscheme) :
    (DivisorWithCoeffs.restrictPrimeDivisor (∑ j ∈ s, Finsupp.single (F j) (γ j)) (F j')).coeff
        Q = ∑ j ∈ s, (F j).intersectionLength (F j').idealSheaf.subschemeι Q • γ j := by
  classical
  haveI : IsNoetherian Y := ⟨⟩
  have h0 : DivisorWithCoeffs.coeff (∑ j ∈ s, Finsupp.single (F j) (γ j)) (F j') = 0 := by
    rw [DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hj' (hF h ▸ hj)
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ h0,
    ← Finsupp.sum_finset_sum_index (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
  exact Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (smul_zero _)

/-- A sum `∑_{j ∈ s} ℓ_j β_j` of natural multiples with `∑_{j ∈ s} ℓ_j = 1` is one of the
`β_j`. -/
private theorem exists_sum_nsmul_eq_of_sum_eq_one {M : Type*} [AddCommMonoid M] (s : Finset ι)
    (ℓ : ι → ℕ) (β : ι → M) (h : ∑ j ∈ s, ℓ j = 1) : ∃ j ∈ s, ∑ i ∈ s, ℓ i • β i = β j := by
  obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.trans_ne one_ne_zero)
  have hsplit := Finset.add_sum_erase s ℓ hj
  rw [h] at hsplit
  have hrest : ∑ i ∈ s.erase j, ℓ i = 0 := by omega
  have hj1 : ℓ j = 1 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  refine ⟨j, hj, ?_⟩
  rw [Finset.sum_eq_single_of_mem j hj fun i hi hij => by
    rw [hrest i (Finset.mem_erase.mpr ⟨hij, hi⟩), zero_smul], hj1, one_smul]

/-- **The restriction of a combination of snc components.** Let `Y` be a smooth variety over an
algebraically closed field of characteristic zero, `F_j` distinct prime divisors of `Y` and
`j' ∉ s` such that `F_{j'} + ∑_{j ∈ s} F_j` is snc. For `A = ∑_{j ∈ s} β_j F_j`, the support of
`A|_{F_{j'}}` is an snc divisor on `F_{j'}`, and every coefficient of `A|_{F_{j'}}` is `0` or one
of the `β_j`. -/
private theorem isSNC_and_coeff_restrictPrimeDivisor {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] [Smooth sY]
    (F : ι → MMP.Mori.PrimeDivisor Y) (hF : Function.Injective F) (s : Finset ι) {j' : ι}
    (hj' : j' ∉ s)
    (hsnc : DivisorWithCoeffs.IsSNC sY
      (Finsupp.single (F j') (1 : ℤ) + ∑ j ∈ s, Finsupp.single (F j) (1 : ℤ)))
    (β : ι → ℚ) :
    DivisorWithCoeffs.IsSNC ((F j').idealSheaf.subschemeι ≫ sY)
        (DivisorWithCoeffs.restrictPrimeDivisor (∑ j ∈ s, Finsupp.single (F j) (β j)) (F j')) ∧
      ∀ Q, (DivisorWithCoeffs.restrictPrimeDivisor (∑ j ∈ s, Finsupp.single (F j) (β j))
          (F j')).coeff Q = 0 ∨
        ∃ j ∈ s, (DivisorWithCoeffs.restrictPrimeDivisor
          (∑ j ∈ s, Finsupp.single (F j) (β j)) (F j')).coeff Q = β j := by
  classical
  obtain ⟨_, _, _, _⟩ := (isVariety_iff k sY).mp ‹_›
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  set D := s.image F
  have hFD : F j' ∉ D := fun h => by
    obtain ⟨j, hj, hjF⟩ := Finset.mem_image.mp h
    exact hj' (hF hjF ▸ hj)
  have hsum : ∑ E ∈ D, Finsupp.single E (1 : ℤ) = ∑ j ∈ s, Finsupp.single (F j) (1 : ℤ) :=
    Finset.sum_image fun _ _ _ _ h => hF h
  obtain ⟨hsncT, hone⟩ :=
    DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single sY (F j') D hFD (by rwa [hsum])
  rw [hsum] at hsncT hone
  set A : QDivisor Y := ∑ j ∈ s, Finsupp.single (F j) (β j)
  set T : Divisor Y := ∑ j ∈ s, Finsupp.single (F j) (1 : ℤ)
  have hAc : ∀ Q, (A.restrictPrimeDivisor (F j')).coeff Q =
      ∑ j ∈ s, (F j).intersectionLength (F j').idealSheaf.subschemeι Q • β j :=
    coeff_restrictPrimeDivisor_sum_single F hF s hj' β
  have hTcQ : ∀ Q, (T.restrictPrimeDivisor (F j')).coeff Q =
      ((∑ j ∈ s, (F j).intersectionLength (F j').idealSheaf.subschemeι Q : ℕ) : ℤ) := by
    intro Q
    rw [coeff_restrictPrimeDivisor_sum_single F hF s hj' (fun _ => (1 : ℤ))]
    push_cast
    simp
  have hsupp :
      (A.restrictPrimeDivisor (F j')).support ⊆ (T.restrictPrimeDivisor (F j')).support := by
    intro Q hQ
    rw [Finsupp.mem_support_iff] at hQ ⊢
    change (A.restrictPrimeDivisor (F j')).coeff Q ≠ 0 at hQ
    change (T.restrictPrimeDivisor (F j')).coeff Q ≠ 0
    rw [hAc] at hQ
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
    have hl : (F j).intersectionLength (F j').idealSheaf.subschemeι Q ≠ 0 := by
      rintro h0
      exact hne (by rw [h0, zero_smul])
    rw [hTcQ]
    exact_mod_cast (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨j, hj, Nat.pos_of_ne_zero hl⟩).ne'
  refine ⟨hsncT.of_support_subset hsupp, fun Q => or_iff_not_imp_left.mpr fun hQ => ?_⟩
  have hQT := hone Q (hsupp (Finsupp.mem_support_iff.mpr hQ))
  rw [hTcQ] at hQT
  rw [hAc]
  exact exists_sum_nsmul_eq_of_sum_eq_one s _ β (by exact_mod_cast hQT)

end Restriction

section Nef

variable {k : Type} [Field k]

/-- `deg_C 𝒪_V(u^*B) = deg_{u ∘ C} 𝒪_W(B)` for the pull-back of a Cartier divisor. -/
private theorem degreeOn_eq_of_isPullback {V W C : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sV] [QuasiCompact sW] [IsLocallyNoetherian V]
    [IsNormal V] [IsIntegral V] [IsLocallyNoetherian W] [IsNormal W] (u : V ⟶ W)
    (hu : u ≫ sW = sV) {B : Divisor W} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ B.supp}
    {B' : Divisor V} (h : B.IsPullback u hB B') (hB'c : B'.IsCartier) (φ : C ⟶ V)
    [IsProper (φ ≫ sV)] [IsProper ((φ ≫ u) ≫ sW)] (hdim : topologicalKrullDim C ≤ 1) :
    B'.degreeOn k sV φ hdim hB'c = B.degreeOn k sW (φ ≫ u) hdim hBc := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sV
  haveI := QuasiCompact.compactSpace_of_compactSpace sW
  haveI := hBc.isInvertibleModule_divisorialSheaf
  haveI := hB'c.isInvertibleModule_divisorialSheaf
  change MMP.Mori.degreeOn k sV φ hdim B'.divisorialSheaf = MMP.Mori.degreeOn k sW (φ ≫ u) hdim
    B.divisorialSheaf
  rw [degreeOn_eq_of_iso k sV φ hdim (h.divisorialSheafIso (hBc := hBc))]
  exact degreeOn_pullback_eq_degreeOn_comp sV sW u φ hu hdim _

/-- The pull-back of a nef Cartier divisor along a morphism of varieties is nef. -/
private theorem isNef_of_isPullback_divisor {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV] [IsLocallyNoetherian W] [IsNormal W]
    [QuasiCompact sW] {u : V ⟶ W} (hu : u ≫ sW = sV) {D : Divisor W} (hD : D.IsNef k sW)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') : D'.IsNef k sV := by
  obtain ⟨hDc, hDn⟩ := hD
  refine ⟨h.isCartier hDc, fun C i _ _ _ hC => ?_⟩
  haveI : IsProper ((i ≫ u) ≫ sW) := by rw [Category.assoc, hu]; infer_instance
  rw [degreeOn_eq_of_isPullback u hu hDc h _ i hC.le]
  haveI : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  haveI : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  haveI := QuasiCompact.compactSpace_of_compactSpace sW
  haveI := hDc.isInvertibleModule_divisorialSheaf
  change 0 ≤ MMP.Mori.degreeOn k sW (i ≫ u) hC.le D.divisorialSheaf
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · rw [degreeOn_eq_zero_of_range_eq_singleton sW (i ≫ u) _ hpt]
  · rw [degreeOn_eq_degreeOver_mul sW (i ≫ u) _ hpt]
    haveI : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
    haveI : IsProper ((i ≫ u).imageι ≫ sW) := isProper_imageι_comp (i ≫ u) sW
    have hcurve := isCurve_imageι_comp sW (i ≫ u) hpt
    exact mul_nonneg (by positivity) (hDn _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

/-- **Restriction of a nef divisor to a closed subscheme.** If `E` is a nef Cartier divisor on
`Y` and `E'` a Cartier divisor on a closed subscheme `ι : Z ⟶ Y` with `𝒪_Z(E') ≅ ι^* 𝒪_Y(E)`,
then `E'` is nef: `deg_C 𝒪_Z(E') = deg_C 𝒪_Y(E)|_C ≥ 0` for every proper curve `C ⊆ Z`. -/
private theorem isNef_of_nonempty_divisorialSheaf_iso {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY]
    [IsLocallyNoetherian Z] [IsNormal Z] (ι : Z ⟶ Y) [IsClosedImmersion ι] [QuasiCompact (ι ≫ sY)]
    {E : Divisor Y} (hE : E.IsNef k sY) {E' : Divisor Z} (hE' : E'.IsCartier)
    (e : Nonempty (E'.divisorialSheaf ≅ (Scheme.Modules.pullback ι).obj E.divisorialSheaf)) :
    E'.IsNef k (ι ≫ sY) := by
  obtain ⟨hEc, hEn⟩ := hE
  obtain ⟨e⟩ := e
  refine ⟨hE', fun C i _ _ _ hC => ?_⟩
  haveI : IsProper ((i ≫ ι) ≫ sY) := by rw [Category.assoc]; infer_instance
  have h0 := hEn C (i ≫ ι) hC
  haveI := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := QuasiCompact.compactSpace_of_compactSpace (ι ≫ sY)
  haveI := hEc.isInvertibleModule_divisorialSheaf
  haveI := hE'.isInvertibleModule_divisorialSheaf
  unfold Divisor.degreeOn at h0 ⊢
  rw [degreeOn_eq_of_iso k (ι ≫ sY) i hC.le e,
    degreeOn_pullback_eq_degreeOn_comp (ι ≫ sY) sY ι i rfl hC.le]
  exact h0

end Nef

section TieBreaker

variable {Y : Scheme.{0}} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}

/-- Each `F_j` lies in the support of the reduced divisor `∑_j F_j`. -/
private theorem mem_support_sum_single_one (hF : Function.Injective F) (j : Fin s) :
    F j ∈ (∑ i, Finsupp.single (F i) (1 : ℤ)).support := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply, hF.eq_iff]

/-- The test boundary `∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j` does not contain `F_{j'}`. -/
private theorem coeff_tieBreakerBoundary_self (hF : Function.Injective F) (r a p : Fin s → ℚ)
    (j' : Fin s) (c : ℚ) : (tieBreakerBoundary F r a p j' c).coeff (F j') = 0 := by
  classical
  rw [tieBreakerBoundary, DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finsupp.single_apply, if_neg]
  exact fun h' => (Finset.mem_erase.mp hj).1 (hF h')

/-- `F_{j'} + ∑_{j ≠ j'} (…) F_j` is supported on the components of `∑_j F_j`. -/
private theorem support_single_add_tieBreakerBoundary_subset (hF : Function.Injective F)
    (r a p : Fin s → ℚ) (j' : Fin s) (c : ℚ) :
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
  induction e with
  | top =>
    have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
    simp only [top_add, WithBot.coe_inj] at h'
    exact absurd h' (ENat.top_ne_coe n)
  | coe e =>
    refine ⟨e, rfl, ?_⟩
    have h' : (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast h
    exact_mod_cast h'

/-- **The restricted non-vanishing datum.** Let `f : Y ⟶ X` be a basepoint-free tie-breaker
with distinguished component `F = F_{j'}`, test boundary `A` and pull-back `D' = f^*D`, and let
`D_F` be a divisor on `F` with `𝒪_F(D_F) ≅ 𝒪_Y(D')|_F`. Then
`(F, -A|_F)` with the divisor `D_F` and the multiple `⌈c m + a⌉` is a non-vanishing datum:
`(F, -A|_F)` is klt because `F + A` is snc with coefficients `> -1` off `F`, and
`⌈c m + a⌉ D_F + A|_F - K_F` is ample, being the restriction of the ample test divisor
`⌈c m + a⌉ D' + A - F - K_Y` by adjunction. -/
private theorem isNonvanishingDatum_restrictPrimeDivisor {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} {D : Divisor X} {a : ℚ} {m : ℕ} {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ} {j' : Fin s} {c : ℚ}
    (h : IsBasepointFreeTieBreaker sX n K Δ D a m f F aj pj rj j' c)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : Divisor Y} (hD' : D.IsPullback f hB D') (hsm : IsSmoothScheme (f ≫ sX))
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    [IsLocallyNoetherian (F j').idealSheaf.subscheme] [IsNormal (F j').idealSheaf.subscheme]
    [CompactSpace (F j').idealSheaf.subscheme]
    [IsSmoothVariety k ((F j').idealSheaf.subschemeι ≫ f ≫ sX)]
    [AlgebraicGeometry.IsProjectiveVariety k ((F j').idealSheaf.subschemeι ≫ f ≫ sX)]
    (hsmF : IsSmoothScheme ((F j').idealSheaf.subschemeι ≫ f ≫ sX)) (hn : n - 1 + 1 = n)
    {KF : Divisor (F j').idealSheaf.subscheme}
    (hKF : KF.IsCanonicalDivisor ((F j').idealSheaf.subschemeι ≫ f ≫ sX) (n - 1))
    {DF : Divisor (F j').idealSheaf.subscheme}
    (eDF : Nonempty (DF.divisorialSheaf ≅
      (Scheme.Modules.pullback (F j').idealSheaf.subschemeι).obj D'.divisorialSheaf)) :
    IsNonvanishingDatum ((F j').idealSheaf.subschemeι ≫ f ≫ sX) (n - 1) KF DF
      ((tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j' c).restrictPrimeDivisor (F j'))
      ⌈c * m + a⌉ := by
  classical
  haveI hPY : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hPY.toIsVariety
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hsm
  set A := tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j' c with hA
  have hAF0 : A.coeff (F j') = 0 := coeff_tieBreakerBoundary_self h.injective _ _ _ _ _
  have haF0 : 0 < ⌈c * m + a⌉ := Int.ceil_pos.mpr (by have := h.pos_c; have := h.pos; positivity)
  have hDF : DF.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmF _
  -- `N(a_F, c) = a_F f^*D + A - F - K_Y` is ample
  have hAmp : (Divisor.toQDivisor (⌈c * m + a⌉ • D') + A -
      Divisor.toQDivisor (Finsupp.single (F j') 1) - Divisor.toQDivisor KY).IsAmple := by
    refine h.toIsBasepointFreeAdaptedResolution.isAmple_of_isTieBreakerTestDivisor (KY := KY)
      (b := (⌈c * m + a⌉ : ℚ)) h.pos_c.le (Int.le_ceil _) ⟨hKY, hB, D', hD', ?_⟩
    beta_reduce
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j'), h.eq_neg_one, map_zsmul,
      ← Int.cast_smul_eq_zsmul ℚ, MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one,
      hA, tieBreakerBoundary, Finsupp.single_neg]
    abel
  have ePF := nonempty_divisorialSheaf_nsmul_iso hsm hsmF eDF (j := (⌈c * m + a⌉).toNat)
    (by omega)
  rw [Int.toNat_of_nonneg haF0.le] at ePF
  have hampF := QDivisor.isAmple_add_restrictPrimeDivisor_sub_of_isAmple (f ≫ sX) hsm (F j')
    hsmF (hn ▸ hKY) hKF (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) hAF0 hAmp
    (MMP.Fourfold.isCartier_of_isSmoothScheme hsmF _) ePF
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ] at hampF
  obtain ⟨hnef, hbig⟩ :=
    QDivisor.isNef_and_isBig_of_isAmple ((F j').idealSheaf.subschemeι ≫ f ≫ sX) hampF
  -- `(F, -A|_F)` is klt
  have hsnc' : DivisorWithCoeffs.IsSNC (f ≫ sX) (Finsupp.single (F j') (1 : ℤ) +
      ∑ j ∈ Finset.univ.erase j', Finsupp.single (F j) (1 : ℤ)) := by
    rw [Finset.add_sum_erase _ (fun j => Finsupp.single (F j) (1 : ℤ)) (Finset.mem_univ j')]
    exact h.isSNC
  obtain ⟨hsncR, hcoeff⟩ : DivisorWithCoeffs.IsSNC _ (A.restrictPrimeDivisor (F j')) ∧
      ∀ Q, (A.restrictPrimeDivisor (F j')).coeff Q = 0 ∨ ∃ j ∈ Finset.univ.erase j',
        (A.restrictPrimeDivisor (F j')).coeff Q = -c * (rj j : ℚ) + aj j - pj j :=
    isSNC_and_coeff_restrictPrimeDivisor (f ≫ sX) F h.injective _ (Finset.notMem_erase j' _)
      hsnc' (fun j => -c * (rj j : ℚ) + aj j - pj j)
  have hklt : IsKltPair ((F j').idealSheaf.subschemeι ≫ f ≫ sX) (n - 1) KF
      (-A.restrictPrimeDivisor (F j')) := by
    refine isKltPair_of_isSNC _ ⟨inferInstance, inferInstance⟩ hsmF hKF
      (hsncR.of_support_subset (by rw [Finsupp.support_neg])) fun Q => ?_
    change -(A.restrictPrimeDivisor (F j')).coeff Q < 1
    rcases hcoeff Q with h0 | ⟨j, hj, hjQ⟩
    · rw [h0]; norm_num
    · rw [hjQ]
      linarith [h.neg_one_lt j (Finset.ne_of_mem_erase hj)]
  exact
    { isProperVariety := inferInstance
      isCartier := hDF
      isNef := isNef_of_nonempty_divisorialSheaf_iso _
        (isNef_of_isPullback_divisor (sV := f ≫ sX) rfl h.isNef hD') hDF eDF
      isKltPair := hklt
      pos := by exact_mod_cast haF0
      isQCartier_add := hnef.1
      isNef_add := hnef
      isBig_add := hbig }

end MMP.FourfoldProofs.Km3aBpfNonvanishingOnDivisorProof

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km3aBpfNonvanishingOnDivisorProof in
/-- **Non-vanishing on the tie-breaking divisor** (Kollár–Mori 3.2, Step 5). Let
`(f; F_•; a_•; p_•; r_•)` be an `m`-adapted resolution of a basepoint-free datum `(X, Δ, D, a)`
with a tie-breaker `(j', c)`, let `A = ∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j` be its test boundary
and `i : F_{j'} ⟶ Y` the closed immersion, and let `D'` be a pull-back of `D` along `f`. Then
there is an integer `b₁` such that `H⁰(F_{j'}, i^* 𝒪_Y(b D' + ⌈A⌉)) ≠ 0` for every integer
`b ≥ b₁`. -/
@[mmp "lem_km3a_bpf_nonvanishing_on_divisor"]
theorem IsBasepointFreeTieBreaker.exists_nontrivial_cohomologyOverField_restriction
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ} {m : ℕ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j' : Fin s} {c : ℚ}
    (h : IsBasepointFreeTieBreaker sX n K Δ D a m f F aj pj rj j' c)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : Divisor Y} (hD' : D.IsPullback f hB D') :
    ∃ b₁ : ℤ, ∀ b : ℤ, b₁ ≤ b →
      Nontrivial (cohomologyOverField k ((F j').idealSheaf.subschemeι ≫ f ≫ sX)
        ((Scheme.Modules.pullback (F j').idealSheaf.subschemeι).obj
          (b • D' +
            (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j' c).roundUp).divisorialSheaf)
        0) := by
  classical
  haveI hPY : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hPY.toIsVariety
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hsm
  have hdim : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      h.isLogResolution.isBirationalMorphism).symm.trans h.isKltPair.1.2.1.1
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm hdim
  set ι := (F j').idealSheaf.subschemeι
  set A := tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j' c
  have hsmF : IsSmoothScheme (ι ≫ f ≫ sX) :=
    h.isSNC.1 (F j')
      (MMP.FourfoldProofs.Km3aBpfNonvanishingOnDivisorProof.mem_support_sum_single_one h.injective j')
  haveI : IsIntegral (F j').idealSheaf.subscheme := (F j').integral
  haveI : Smooth (ι ≫ f ≫ sX) := (isSmoothScheme_iff _).mp hsmF
  haveI : AlgebraicGeometry.IsVariety k (ι ≫ f ≫ sX) := ⟨⟩
  haveI : IsSmoothVariety k (ι ≫ f ≫ sX) := ⟨⟩
  haveI : CompactSpace (F j').idealSheaf.subscheme := QuasiCompact.compactSpace_of_compactSpace ι
  haveI : IsLocallyNoetherian (F j').idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ f ≫ sX)
  haveI : IsNormal (F j').idealSheaf.subscheme := isNormal_of_smooth_over_field (ι ≫ f ≫ sX)
  haveI : AlgebraicGeometry.IsProjectiveVariety k (ι ≫ f ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff_isProjectiveMorphism k _).mpr
      ((MMP.isProjectiveMorphism_of_isClosedImmersion ι).comp hPY.isProjective)
  obtain ⟨d, hd, hnd⟩ := exists_topologicalKrullDim_subscheme_eq (f ≫ sX) (F j') hdim
  obtain ⟨KF, hKF⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (ι ≫ f ≫ sX) hsmF
    (show _ = ((n - 1 : ℕ) : WithBot ℕ∞) by rw [hd, ← hnd, Nat.add_sub_cancel])
  haveI := (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D').isInvertibleModule_divisorialSheaf
  obtain ⟨DF, eDF⟩ := exists_nonempty_divisorialSheaf_iso_pullback (ι ≫ f ≫ sX) ι
    D'.divisorialSheaf
  obtain ⟨m₀, hm₀⟩ := (isNonvanishingDatum_restrictPrimeDivisor h hD' hsm hKY hsmF
    (by omega) hKF eDF).hasNonvanishingProperty
  refine ⟨max m₀ 1, fun b hb => ?_⟩
  obtain ⟨σ, hσ⟩ := hm₀ b (le_of_max_le_left hb)
  have hAF0 : A.coeff (F j') = 0 := coeff_tieBreakerBoundary_self h.injective _ _ _ _ _
  have hround := DivisorWithCoeffs.restrictPrimeDivisor_roundUp (f ≫ sX) (R := ℚ) inferInstance
    hsm (F j') hsmF 0 Divisor.isCartier_zero
    (by simpa using (show ¬ ((F j').support : Set Y) ⊆ ∅ from
      fun h' => h' (MMP.Flips.primeDivisor_genericPoint_mem_support _))) A
    hAF0 (h.isSNC.of_support_subset
      (support_single_add_tieBreakerBoundary_subset h.injective _ _ _ _ _))
  simp only [map_zero, zero_add] at hround
  haveI : IsSmoothVariety k (f ≫ sX) := ⟨⟩
  obtain ⟨-, eA, -⟩ := Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety k (f ≫ sX) (F j')
    A.roundUp (by rw [DivisorWithCoeffs.coeff_roundUp, hAF0, Int.ceil_zero])
  rw [hround] at eA
  have eb := nonempty_divisorialSheaf_nsmul_iso hsm hsmF eDF (j := b.toNat) (by omega)
  rw [Int.toNat_of_nonneg (by omega)] at eb
  obtain ⟨e⟩ := nonempty_divisorialSheaf_add_iso hsm hsmF eb eA
  exact nontrivial_cohomologyOverField_zero_of_iso _ e σ hσ

end MMP.Mori

end
