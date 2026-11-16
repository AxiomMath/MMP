module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripRestrictionSurjective
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist

@[expose] public section

section

/-!
# The strip base locus drops off the image of the tie-breaking divisor

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r`, `(j₀, c)` a tie-breaker of a
`(p, q)`-adapted resolution `f : Y ⟶ X` with test boundary `A'`, `F = F_{j₀}`, and `p', q'`
integers with `p' ≥ (1 + c) p`, `q' ≥ (1 + c) q` and `aq' - rp' ≤ aq - rp`. Write
`M' = p'H + q'a(K_X + Δ)` and `D = f^*M' + ⌈A'⌉`. If `H⁰(F, 𝒪_Y(D)|_F) ≠ 0`, then
`f(F) ⊄ L(p', q')`.

A nonzero element of `H⁰(F, 𝒪_Y(D)|_F)` is the restriction of a section `τ` of `𝒪_Y(D)`, as
restriction to `F` is onto. Since `⌈A'⌉` is effective and `f`-exceptional, `τ = f^*σ · s'` for a
section `σ` of `𝒪_X(M')`, with `s'` the canonical section of `𝒪_Y(⌈A'⌉)`. Suppose that
`f(F) ⊆ L(p', q')`. Then `f(F) ⊆ Supp (σ)₀`, so `F` occurs in `f^*(σ)₀ = div(f^*σ) + f^*M'`.
As `F` does not occur in `⌈A'⌉`, the section `τ` vanishes along `F`, that is, it lies in
`𝒪_Y(D - F)`. Its restriction to `F` is then zero, by exactness of
`0 ⟶ 𝒪_Y(D - F) ⟶ 𝒪_Y(D) ⟶ 𝒪_Y(D)|_F ⟶ 0`. This is a contradiction.

## Main results

* `MMP.Mori.IsStripTieBreaker.not_image_subset_stripBaseLocus`: `f(F_{j₀}) ⊄ L(p', q')`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, 3.4 Step 10
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3bStripBaseLocusDropsProof

/-- **Restriction to a prime divisor kills the sections vanishing along it.** On a smooth variety
`Y`, a global section of `𝒪_Y(N + F)` that is a section of `𝒪_Y(N)` restricts to zero in
`H⁰(F, i^* 𝒪_Y(N + F))`. -/
private theorem restriction_eq_zero_of_mem {k : Type} [Field k] {Y : Scheme.{0}}
    (g : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsNormal Y] (hV : MMP.Mori.IsVariety k g)
    (hsm : IsSmoothScheme g) (F : MMP.Mori.PrimeDivisor Y) (N D : Divisor Y)
    (hD : D = N + Finsupp.single F 1) (x : cohomologyOverField k g D.divisorialSheaf 0)
    (τ : N.divisorialSubmodule ⊤)
    (hx : ((cohomologyOverFieldZeroLinearIso k g D.divisorialSheaf).hom x :
      D.divisorialSubmodule ⊤).1 = τ.1) :
    (cohomologyOverFieldMap k g
        ((Scheme.Modules.pullbackPushforwardAdjunction F.idealSheaf.subschemeι).unit.app
          D.divisorialSheaf) 0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k F.idealSheaf.subschemeι g
        ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj D.divisorialSheaf) 0).inv).hom
      x = 0 := by
  subst hD
  obtain ⟨hz, hS⟩ := Divisor.IsCartier.shortExact_divisorialSheafInclusion_restriction g hV hsm F
    (MMP.Fourfold.isCartier_of_isSmoothScheme hsm N)
  obtain ⟨d, -, hfg, -, -⟩ := exists_cohomologyOverField_longExactSequence k g hS
  set x' := (cohomologyOverFieldZeroLinearIso k g N.divisorialSheaf).inv τ
  have hxx : x = cohomologyOverFieldMap k g (Divisor.divisorialSheafInclusion
      (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one) :
        N ≤ N + Finsupp.single F 1)) 0 x' := by
    apply (cohomologyOverFieldZeroLinearIso k g _).toLinearEquiv.injective
    change (cohomologyOverFieldZeroLinearIso k g _).hom x =
      (cohomologyOverFieldZeroLinearIso k g _).hom (cohomologyOverFieldMap k g _ 0 x')
    rw [cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap]
    apply Subtype.ext
    refine hx.trans ?_
    have hτ : (cohomologyOverFieldZeroLinearIso k g N.divisorialSheaf).hom x' = τ :=
      Iso.inv_hom_id_apply _ _
    rw [hτ]
    rfl
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, hxx, (hfg 0).apply_apply_eq_zero, map_zero]

/-- `f^*` of the germ of `a` at the generic point is the germ of `f^♯ a`. -/
private theorem functionFieldMap_germ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) (a : Γ(X, U)) (hx : genericPoint X ∈ U)
    (hy : genericPoint Y ∈ f ⁻¹ᵁ U) :
    functionFieldMap f (X.presheaf.germ U (genericPoint X) hx a) =
      Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hy (f.app U a) := by
  have key : X.presheaf.germ U (genericPoint X) hx ≫
      (X.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom ≫
        f.stalkMap (genericPoint Y) = f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hy := by
    simp only [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc (F := X.presheaf) (x := f (genericPoint Y))]
    exact Scheme.Hom.germ_stalkMap f U _ hy
  exact congrArg (fun g => g.hom a) key

/-- Read at the generic points, `MMP.Fourfold.fieldMap f` is `f^*` on function fields. -/
private theorem stalkSpecializes_fieldMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (ZX : irreducibleComponents X) (ZY : irreducibleComponents Y)
    (a : X.presheaf.stalk (componentGenericPoint X ZX)) :
    Y.presheaf.stalkSpecializes (genericPoint_specializes _) (MMP.Fourfold.fieldMap f ZX ZY a) =
      functionFieldMap f (X.presheaf.stalkSpecializes (genericPoint_specializes _) a) := by
  obtain ⟨V, hV, b, rfl⟩ := X.presheaf.exists_germ_eq a
  rw [MMP.Fourfold.fieldMap_germ]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ]

/-- **A section of `f^*M + E` vanishes along a prime divisor mapping into `Bs |M|`.** Let
`f : Y ⟶ X` be a proper birational morphism of normal varieties, `M` a Cartier divisor on `X` with
pull-back `B'`, and `E ≥ 0` a Cartier `f`-exceptional divisor. If `P` is a prime divisor of `Y` not
in `E` with `f(η_P)` in the base locus of `M`, then every global section of `𝒪_Y(B' + E)` is a
section of `𝒪_Y(B' + E - P)`. -/
private theorem isDivisorialSection_sub_single_of_mem_baseLocus {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    (hX : MMP.Mori.IsVariety k sX) (hY : MMP.Mori.IsVariety k (f ≫ sX))
    [IsProper f] (hbir : IsBirationalMorphism f) {M : Divisor X} (hMc : M.IsCartier)
    {hM : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ M.supp}
    {B' : Divisor Y} (hB' : M.IsPullback f hM B') {E : Divisor Y} (hEc : E.IsCartier) (hE : 0 ≤ E)
    (hEexc : ∀ P : MMP.Mori.PrimeDivisor Y, E.coeff P ≠ 0 →
      RationalMap.IsExceptional f.toRationalMap P)
    {P : MMP.Mori.PrimeDivisor Y} (hEP : E.coeff P = 0)
    (hPM : f P.genericPoint ∈ (M.baseLocus : Set X))
    (τ : (B' + E).divisorialSubmodule ⊤) :
    (B' + E - Finsupp.single P 1).IsDivisorialSection ⊤ τ.1 := by
  haveI : IsDominant f := hbir.isDominant
  by_cases hτ : τ = 0
  · rw [hτ]
    exact ((B' + E - Finsupp.single P 1).divisorialSubmodule ⊤).zero_mem
  obtain ⟨e, he⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sX f
    hX hY hbir M hMc hM B' hB' E hEc hE hEexc
  let τ' : (B' + E).divisorialSubmodule (f ⁻¹ᵁ ⊤) := ⟨τ.1, τ.2⟩
  set σ : M.divisorialSubmodule ⊤ := e.inv.app ⊤ τ'
  have hστ : (e.hom.app ⊤ σ : (B' + E).divisorialSubmodule (f ⁻¹ᵁ ⊤)) = τ' :=
    congrArg (fun φ => (φ.app ⊤).hom τ') e.inv_hom_id
  have hσ : σ ≠ 0 := by
    intro h0
    have : τ' = 0 := by
      rw [← hστ, h0]
      exact (Scheme.Modules.Hom.app e.hom ⊤).hom.map_zero
    exact hτ (Subtype.ext (congrArg Subtype.val this))
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hφB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (principalDivisor φ).supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _
  set ψ := pullbackRationalFunction f φ hφB
  have hψ (ZY : irreducibleComponents Y) : (ψ : RationalFunctions Y) ZY = τ.1 ⟨ZY, trivial⟩ := by
    let ZX : irreducibleComponents X := pointComponent (genericPoint X)
    rw [show (ψ : RationalFunctions Y) ZY = MMP.Fourfold.fieldMap f ZX ZY (φ.1 ZX) from
      MMP.Fourfold.pullbackComponent_eq_fieldMap f hφB
        (Divisor.isLocalEquation_principalDivisor φ ⊤) ZY trivial ZX]
    apply MMP.Intersection.stalkSpecializes_injective
      (genericPoint_specializes (componentGenericPoint Y ZY))
    rw [stalkSpecializes_fieldMap]
    have h2 := (he ⊤ σ ZX trivial ZY trivial).1
    rw [hστ] at h2
    exact h2.symm
  have hZc : (M.zeroDivisor σ hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hMc
  have hZ' : (M.zeroDivisor σ hσ).IsPullback f
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _)
      (principalDivisor ψ + B') :=
    ((Divisor.isPullback_principalDivisor (f := f) φ hφB).add
      (Divisor.isCartier_principalDivisor φ) hMc
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _) hB').of_eq
      (Divisor.zeroDivisor_eq _ σ hσ).symm
  obtain ⟨Q, hQ0, hηQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp <|
    MMP.Flips.preimage_supp_subset_supp_of_isPullback hZc (Divisor.zeroDivisor_nonneg _ σ hσ) hZ'
      (Divisor.baseLocus_le_supp _ σ hσ hPM)
  obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hηQ
  have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hZc (V := ⊤)
    (fun P _ => Divisor.zeroDivisor_nonneg _ σ hσ P) hZ' Q
    ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support Q, trivial⟩
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at hQ0 hnn
  intro R hR
  by_cases hRQ : R = Q
  · subst hRQ
    refine Or.inr ?_
    rw [← hψ, R.valuation_component, WithZero.exp_le_exp]
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, hEP,
      DivisorWithCoeffs.coeff_single_self]
    omega
  · rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hRQ),
      sub_zero]
    exact τ.2 R hR

/-- The strip divisor `p H + q ⌊a (K_X + Δ)⌋` of a strip tie-breaker is Cartier. -/
private theorem isCartier_stripDivisor {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ} {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) (p' q' : ℤ) :
    (stripDivisor K Δ a H p' q').IsCartier := by
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  have hr0 : (a • (Divisor.toQDivisor K + Δ)).roundDown = D₀ := by
    rw [← hD₀]
    ext E
    rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor, Int.floor_intCast]
  rw [stripDivisor, hr0]
  exact (h.isCartier_H.zsmul p').add (hD₀c.zsmul q')

end MMP.FourfoldProofs.Km3bStripBaseLocusDropsProof

end

section

/-!
## Implementation notes

The prime divisor `F = F_{j₀}` is the integral closed subscheme `(F j₀).idealSheaf.subscheme`
with inclusion `ι = (F j₀).idealSheaf.subschemeι`, a scheme over `k` through `ι ≫ f ≫ sX`.
The divisor `f^*(p'H + q'a(K_X + Δ))` is any pull-back `B'` of
`MMP.Mori.stripDivisor K Δ a H p' q'`, and `𝒪_Y(B' + ⌈A'⌉)|_F` is the pull-back of its divisorial
sheaf along `ι`; `H⁰ ≠ 0` is nontriviality of that `k`-vector space. `L(p', q')` is
`MMP.Mori.stripBaseLocus K Δ a H p' q'` and `f(F)` is the image of the support of `F_{j₀}`.
The inequalities `p' ≥ (1 + c) p` and `q' ≥ (1 + c) q` are read in `ℚ`, and
`aq' - rp' ≤ aq - rp` in `ℝ`. The ground field is algebraically closed of characteristic zero, as
the Kawamata–Viehweg vanishing behind the surjectivity of restriction requires.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bStripBaseLocusDropsProof in
/-- **The strip base locus drops** (Kollár–Mori 3.4, Step 10).
Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r` of `H` with respect to
`K_X + Δ`, `p, q > 0` integers with `0 < aq - rp`, `(j₀, c)` a tie-breaker of a `(p, q)`-adapted
resolution `(f; F_•; a_•; p_•; r_•)` with test boundary `A'`, and `ι : F_{j₀} ⟶ Y` the closed
immersion. Let `p', q'` be integers with `(1 + c) p ≤ p'`, `(1 + c) q ≤ q'` and
`aq' - rp' ≤ aq - rp`, and `B'` a pull-back of `p'H + q'a(K_X + Δ)` along `f`. If
`H⁰(F_{j₀}, ι^* 𝒪_Y(B' + ⌈A'⌉)) ≠ 0`, then `f(F_{j₀})` is not contained in the strip base locus
`L(p', q') = stripBaseLocus K Δ a H p' q'`. -/
@[mmp "lem_km3b_strip_base_locus_drops"]
public theorem IsStripTieBreaker.not_image_subset_stripBaseLocus
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hpq : 0 < (a * q : ℝ) - r * p) {p' q' : ℤ}
    (hp' : (1 + c) * p ≤ p') (hq' : (1 + c) * q ≤ q')
    (hpq' : (a * q' : ℝ) - r * p' ≤ a * q - r * p)
    {hM : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp}
    {B' : Divisor Y} (hB' : (stripDivisor K Δ a H p' q').IsPullback f hM B')
    (hne : Nontrivial (cohomologyOverField k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX)
      ((Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).obj
        (B' + (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).roundUp).divisorialSheaf)
      0)) :
    ¬ f '' (F j₀).support ⊆ (stripBaseLocus K Δ a H p' q' : Set X) := by
  intro hsub
  haveI hP : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  haveI : IsProper f := h.isLogResolution.isProper
  set A := tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c
  obtain ⟨y, hy⟩ := exists_ne (0 : cohomologyOverField k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX)
    ((Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).obj
      (B' + A.roundUp).divisorialSheaf) 0)
  obtain ⟨x, rfl⟩ := h.surjective_restriction_pullback_add_roundUp hr hpq hp' hq' hpq' hB' y
  obtain ⟨hAeff, hAexc⟩ := h.isEffective_roundUp_tieBreakerBoundary
  have hA0 : A.roundUp.coeff (F j₀) = 0 := by
    rw [DivisorWithCoeffs.coeff_roundUp]
    rcases MMP.Mori.coeff_tieBreakerBoundary h.injective (fun j ↦ (rj j : ℚ)) aj pj j₀ c
      (F j₀) with h0 | ⟨j, hj, hFj, -⟩
    · rw [h0, Int.ceil_zero]
    · exact absurd (h.injective hFj) hj
  set τ := (cohomologyOverFieldZeroLinearIso k (f ≫ sX) (B' + A.roundUp).divisorialSheaf).hom x
  exact hy <| restriction_eq_zero_of_mem (f ≫ sX) hP.toIsVariety hsm (F j₀)
    (B' + A.roundUp - Finsupp.single (F j₀) 1) _ (by abel) x
    ⟨τ.1, isDivisorialSection_sub_single_of_mem_baseLocus sX f h.isProperVariety.toIsVariety
      hP.toIsVariety h.isLogResolution.isBirationalMorphism (isCartier_stripDivisor h p' q') hB'
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) hAeff hAexc hA0
      (hsub ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support _, rfl⟩) τ⟩ rfl

end MMP.Mori

end
