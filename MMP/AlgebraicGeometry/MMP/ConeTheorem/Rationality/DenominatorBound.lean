module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.NefThresholdRational

@[expose] public section

section

/-!
# The denominator bound of the rationality theorem

Let `(X, Δ, a, H)` be a rationality datum of dimension `n` with nef threshold `r > 0`; `r` is
rational, `r = u / v` in lowest terms. If `v > a(n + 1)`, the strip base loci `L(p, q)`,
`0 < aq - rp < 1`, stabilize to a proper closed subset `Z`. The values `aq - rp` on lattice points
far out in the strip lie in `{m / v : 0 < m < v}`; at a point `(p, q)` where `aq - rp` is maximal
there is a `(p, q)`-adapted resolution with a tie-breaking divisor `F` whose image lies in `Z`.
The restricted Euler characteristic function `Q` on `F` is a nonzero polynomial of degree `≤ n`,
so it cannot vanish at every lattice point far out in the strip (its denominator would be
`≤ a(n + 1)`); at a point `(p', q')` where it does not vanish, maximality gives
`aq' - rp' ≤ aq - rp`, so `Q(p', q') = h⁰ ≠ 0` and `f(F) ⊄ L(p', q') = Z`, a contradiction.

## Main results

* `MMP.Mori.IsRationalityDatum.exists_eq_div_of_isNefThreshold`: the nef threshold is `u / v`
  with `0 < v ≤ a(n + 1)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.5
  and its proof in 3.4, Step 11
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3bRationalityFreeDenominatorProof

section Drops

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The round-down of a `ℚ`-divisor with integral coefficients is the divisor itself. -/
private theorem roundDown_toQDivisor {X : Scheme.{0}} (E : Divisor X) :
    (Divisor.toQDivisor E).roundDown = E :=
  DivisorWithCoeffs.ext' fun _ => by simp

/-- On a smooth variety, if `H¹(Y, 𝒪_Y(D)) = 0` then the restriction
`H⁰(Y, 𝒪_Y(D + F)) ⟶ H⁰(F, i^* 𝒪_Y(D + F))` to a prime divisor `F` is surjective. -/
private theorem surjective_restriction_of_subsingleton {k : Type} [Field k] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsNormal Y] (hV : MMP.Mori.IsVariety k f)
    (hsm : IsSmoothScheme f) (D : Divisor Y) (F : MMP.Mori.PrimeDivisor Y)
    (hH1 : Subsingleton (cohomologyOverField k f D.divisorialSheaf 1)) :
    Function.Surjective (cohomologyOverFieldMap k f
        ((Scheme.Modules.pullbackPushforwardAdjunction F.idealSheaf.subschemeι).unit.app
          (D + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k F.idealSheaf.subschemeι f
        ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj
          (D + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0).inv).hom := by
  obtain ⟨_, hS⟩ := Divisor.IsCartier.shortExact_divisorialSheafInclusion_restriction f hV hsm F
    (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D)
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  generalize cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k F.idealSheaf.subschemeι f
      ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj
        (D + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0 = e
  rw [ModuleCat.hom_comp]
  exact e.toLinearEquiv.symm.surjective.comp fun y => (hgd 0 y).1 (Subsingleton.elim _ _)

/-- For a rationality datum, `a(K_X + Δ)` is integral, so the strip divisor
`p'H + q'⌊a(K_X + Δ)⌋` read as a `ℚ`-divisor is `p'H + q'a(K_X + Δ)`, and it is Cartier. -/
private theorem toQDivisor_stripDivisor_and_isCartier {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} (h : IsRationalityDatum sX n K Δ a H)
    (p' q' : ℤ) :
    Divisor.toQDivisor (stripDivisor K Δ a H p' q') =
        p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ) ∧
      (stripDivisor K Δ a H p' q').IsCartier := by
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  rw [stripDivisor, ← hD₀, roundDown_toQDivisor, map_add, map_zsmul, map_zsmul, hD₀, smul_smul]
  exact ⟨rfl, (h.isCartier_H.zsmul p').add (hD₀c.zsmul q')⟩

/-- For a rationality datum, a pull-back of the integral divisor `p'H + q'a(K_X + Δ)` is a
pull-back of the `ℚ`-divisor `p'H + q'a(K_X + Δ)`. -/
private theorem isPullback_toQDivisor_stripDivisor {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} (h : IsRationalityDatum sX n K Δ a H)
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} (p' q' : ℤ)
    {hB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp}
    {B' : Divisor Y} (hB' : (stripDivisor K Δ a H p' q').IsPullback f hB B') :
    ∃ hb, (p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ)).IsPullback f hb
      (Divisor.toQDivisor B') := by
  obtain ⟨hMQ, hMc⟩ := toQDivisor_stripDivisor_and_isCartier h p' q'
  rw [← hMQ]
  exact ⟨_, QDivisor.isPullback_toQDivisor hMc
    (fun Z hZ => hB Z (by rwa [Divisor.supp_toQDivisor] at hZ)) hB'⟩

/-- The test boundary of an adapted resolution is supported on `∑_j F_j`, hence is snc. -/
private theorem isSNC_tieBreakerBoundary {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) (r : Fin s → ℚ) (j₀ : Fin s)
    (c : ℚ) : (tieBreakerBoundary F r aj pj j₀ c).IsSNC (f ≫ sX) := by
  refine h.isSNC.of_support_subset fun E hE => ?_
  rw [tieBreakerBoundary, Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hE
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hE
  obtain rfl : F j = E := by
    by_contra hne
    exact hj (Finsupp.single_eq_of_ne' hne)
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finset.sum_eq_single j
    (fun b _ hb => Finsupp.single_eq_of_ne' (h.injective.ne hb)) (by simp)]
  simp

/-- With `N = (B - E - K_Y) + A` for integral `B, E, K_Y`, the round-up satisfies
`K_Y + ⌈N⌉ = B + ⌈A⌉ - E`. -/
private theorem add_roundUp_toQDivisor_sub_sub_add {Y : Scheme.{0}} (B E KY : Divisor Y)
    (A : QDivisor Y) :
    KY + (Divisor.toQDivisor (B - E - KY) + A).roundUp = B + A.roundUp - E := by
  ext P
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundUp,
    Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_sub]
  rw [Int.ceil_intCast_add]
  ring

/-- Restriction of sections of `𝒪_Y(f^*(p'H + q'a(K_X + Δ)) + ⌈A'⌉)` to the tie-breaking divisor
`F_{j₀}` is surjective. -/
private theorem surjective_restriction_pullback_add_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hpq : 0 < (a * q : ℝ) - r * p) {p' q' : ℤ}
    (hp' : (1 + c) * p ≤ p') (hq' : (1 + c) * q ≤ q')
    (hpq' : (a * q' : ℝ) - r * p' ≤ a * q - r * p)
    {hB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp}
    {B' : Divisor Y} (hB' : (stripDivisor K Δ a H p' q').IsPullback f hB B') :
    Function.Surjective (cohomologyOverFieldMap k (f ≫ sX)
        ((Scheme.Modules.pullbackPushforwardAdjunction (F j₀).idealSheaf.subschemeι).unit.app
          (B' + (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).roundUp).divisorialSheaf)
          0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k (F j₀).idealSheaf.subschemeι
        (f ≫ sX) ((Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).obj
          (B' + (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).roundUp).divisorialSheaf)
          0).inv).hom := by
  set A := tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c
  have hLR := h.isLogResolution
  have hsm : IsSmoothScheme (f ≫ sX) := hLR.isSmoothScheme
  have hYp : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  have hYv : MMP.Mori.IsVariety k (f ≫ sX) := hYp.toIsVariety
  have : AlgebraicGeometry.IsVariety k sX := h.isKltPair.1.1.1
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hYv
  have : IsProper f := hLR.isProper
  have : IsIntegral Y := h.isCrepantBoundary.1.1.toIsIntegral
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      hLR.isBirationalMorphism).symm.trans h.isKltPair.1.2.1.1)
  -- the test divisor `N = (B' - F - K_Y) + A'` is ample, hence nef and big
  obtain ⟨hb, hpb⟩ := isPullback_toQDivisor_stripDivisor h.toIsRationalityDatum p' q' hB'
  have hN : IsStripTestDivisor sX n K Δ a H f KY F aj pj rj j₀ c p' q'
      (Divisor.toQDivisor (B' - Finsupp.single (F j₀) 1 - KY) + A) := ⟨hKY, hb, _, hpb, by
    rw [map_sub, map_sub, MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]
    abel⟩
  obtain ⟨hnef, hbig⟩ := QDivisor.isNef_and_isBig_of_isAmple (f ≫ sX)
    (h.isAmple_of_isStripTestDivisor hr hpq hp' hq' hpq' hN)
  -- Kawamata–Viehweg vanishing for `K_Y + ⌈N⌉ = B' + ⌈A'⌉ - F`
  have hKV := subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    (f ≫ sX) hsm hKY _ A (isSNC_tieBreakerBoundary h.toIsStripAdaptedResolution _ j₀ c) hnef hbig
    1 one_pos
  rw [add_roundUp_toQDivisor_sub_sub_add] at hKV
  have key := surjective_restriction_of_subsingleton (f ≫ sX) hYv hsm
    (B' + A.roundUp - Finsupp.single (F j₀) 1) (F j₀)
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k (f ≫ sX) _
      1).toEquiv.subsingleton
  rwa [sub_add_cancel] at key

end Drops

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
    rw [show (cohomologyOverFieldZeroLinearIso k g N.divisorialSheaf).hom x' = τ from
      Iso.inv_hom_id_apply _ _]
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
    {B' : Divisor Y} (hB' : M.IsPullback f hM B') {E : Divisor Y} (hEc : E.IsCartier)
    (hE : 0 ≤ E)
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

/-- The strip base locus at `(p', q')` does not contain the image of the tie-breaking divisor
`F_{j₀}` once `H⁰(F_{j₀}, 𝒪_Y(f^*(p'H + q'a(K_X + Δ)) + ⌈A'⌉)|_F) ≠ 0`. -/
private theorem not_image_subset_stripBaseLocus
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
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
  obtain ⟨x, rfl⟩ := surjective_restriction_pullback_add_roundUp h hr hpq hp' hq' hpq' hB' y
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
      hP.toIsVariety h.isLogResolution.isBirationalMorphism
      (toQDivisor_stripDivisor_and_isCartier h.toIsRationalityDatum p' q').2 hB'
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) hAeff hAexc hA0
      (hsub ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support _, rfl⟩) τ⟩ rfl

/-- A dimension `d ≠ ⊥` with `d + 1 = n` is `n - 1`, and `n ≥ 1`. -/
private theorem exists_eq_add_one_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ} (hd : d ≠ ⊥)
    (h : d + 1 = n) : ∃ m : ℕ, n = m + 1 ∧ d = m := by
  obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hd
  induction e with
  | top =>
    have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) = n := by exact_mod_cast h
    simp at h'
  | coe e =>
    have h' : e + 1 = n := by exact_mod_cast h
    exact ⟨e, h'.symm, rfl⟩

/-- **Lattice points far out with prescribed numerator.** If `u, v > 0` are coprime and `a > 0`,
then `a v y - u x = a` has solutions with `x, y ≥ N` for every `N`. -/
private theorem exists_le_le_mul_sub_mul_eq {a u v : ℤ} (N : ℤ) (ha : 0 < a) (hu : 0 < u)
    (hv : 0 < v) (huv : Int.gcd u v = 1) :
    ∃ x y : ℤ, N ≤ x ∧ N ≤ y ∧ a * v * y - u * x = a := by
  have hbez : u * Int.gcdA u v + v * Int.gcdB u v = 1 := by
    have := Int.gcd_eq_gcd_ab u v
    omega
  obtain ⟨t, ht⟩ : ∃ t, t = |N| + a * |Int.gcdA u v| + |Int.gcdB u v| := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := ht ▸ by positivity
  refine ⟨-a * Int.gcdA u v + t * (a * v), Int.gcdB u v + t * u, ?_, ?_, by
    linear_combination a * hbez⟩
  · nlinarith [le_abs_self N, abs_nonneg (Int.gcdB u v),
      mul_nonneg ha.le (sub_nonneg.2 (le_abs_self (Int.gcdA u v))),
      mul_nonneg ht0 (show 0 ≤ a * v - 1 by nlinarith)]
  · nlinarith [le_abs_self N, neg_abs_le (Int.gcdB u v),
      mul_nonneg ha.le (abs_nonneg (Int.gcdA u v)), mul_nonneg ht0 (show 0 ≤ u - 1 by omega)]

/-- **A lattice point with maximal `aq - tp` far out in the strip.** If `a > 0` and `t > 0` is
rational with `a < den t`, then for every `N` the values `aq - tp ∈ (0, 1)` at lattice points with
`p, q ≥ N` lie in `{m / den t : 0 < m < den t}`, and one of them, attained at some `(p, q)`, is
maximal. -/
private theorem exists_strip_point_isGreatest {a : ℤ} (ha : 0 < a) {t : ℚ} (ht : 0 < t)
    (hat : a < t.den) (N : ℤ) :
    ∃ p q : ℤ, N ≤ p ∧ N ≤ q ∧ 0 < (a * q : ℝ) - t * p ∧ (a * q : ℝ) - t * p < 1 ∧
      ∀ x y : ℤ, N ≤ x → N ≤ y → 0 < (a * y : ℝ) - t * x → (a * y : ℝ) - t * x < 1 →
        (a * y : ℝ) - t * x ≤ a * q - t * p := by
  classical
  have hvR : (0 : ℝ) < t.den := by exact_mod_cast t.den_pos
  have hval (x y : ℤ) :
      (a * y : ℝ) - t * x = ((a * t.den * y - t.num * x : ℤ) : ℝ) / t.den := by
    rw [Rat.cast_def]; push_cast; field_simp
  let P : ℕ → Prop := fun m => ∃ x y : ℤ, N ≤ x ∧ N ≤ y ∧ a * t.den * y - t.num * x = m
  have hPa : P a.toNat := by
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_le_le_mul_sub_mul_eq (v := t.den) N ha
      (Rat.num_pos.mpr ht) (by exact_mod_cast t.den_pos) t.reduced
    exact ⟨x, y, hx, hy, by rw [hxy, Int.toNat_of_nonneg ha.le]⟩
  have hav : a.toNat ≤ t.den - 1 := by omega
  have hm₀a : a.toNat ≤ Nat.findGreatest P (t.den - 1) := Nat.le_findGreatest hav hPa
  have hm₀v : Nat.findGreatest P (t.den - 1) ≤ t.den - 1 := Nat.findGreatest_le _
  obtain ⟨p, q, hNp, hNq, hm⟩ := Nat.findGreatest_spec hav hPa
  refine ⟨p, q, hNp, hNq, ?_, ?_, fun x y hx hy h1 h2 => ?_⟩
  · rw [hval, hm]
    exact div_pos (by exact_mod_cast (show 0 < Nat.findGreatest P (t.den - 1) by omega)) hvR
  · rw [hval, hm, div_lt_one hvR]
    exact_mod_cast (show Nat.findGreatest P (t.den - 1) < t.den by omega)
  · rw [hval x y, div_pos_iff_of_pos_right hvR] at h1
    rw [hval x y, div_lt_one hvR] at h2
    have h1' : 0 < a * t.den * y - t.num * x := by exact_mod_cast h1
    have h2' : a * t.den * y - t.num * x < t.den := by exact_mod_cast h2
    have hle := Nat.le_findGreatest (P := P) (n := t.den - 1)
      (m := (a * t.den * y - t.num * x).toNat) (by omega)
      ⟨x, y, hx, hy, by rw [Int.toNat_of_nonneg h1'.le]⟩
    rw [hval x y, hval p q, hm, div_le_div_iff_of_pos_right hvR]
    exact_mod_cast (show a * t.den * y - t.num * x ≤ (Nat.findGreatest P (t.den - 1) : ℤ) by
      omega)

/-- **A polynomial of small degree does not vanish far out in a thin strip.** Let
`Q : ℤ² → ℤ` be the values of a nonzero rational polynomial of total degree `≤ n`, `a > 0`, and
`t > 0` rational with `a(n + 1) < den t`. Then for every `N` there is a lattice point `(x, y)`,
`x, y ≥ N`, with `0 < ay - tx < 1` and `Q(x, y) ≠ 0`
(`MMP.Positivity.den_le_of_eval_eq_zero_of_strip`). -/
private theorem exists_strip_point_ne_zero {Q : (Fin 2 → ℤ) → ℤ} (hQ : Q ≠ 0)
    {PQ : MvPolynomial (Fin 2) ℚ} {n : ℕ} (hPQd : PQ.totalDegree ≤ n)
    (hPQ : ∀ w, MvPolynomial.eval (fun i => (w i : ℚ)) PQ = Q w) {a : ℤ} (ha : 0 < a) {t : ℚ}
    (ht : 0 < t) (hv : a * (n + 1) < t.den) (N : ℤ) :
    ∃ x y : ℤ, N ≤ x ∧ N ≤ y ∧ 0 < (a * y : ℝ) - t * x ∧ (a * y : ℝ) - t * x < 1 ∧
      Q ![x, y] ≠ 0 := by
  have hev (x y : ℤ) : MvPolynomial.eval ![(x : ℝ), (y : ℝ)]
      (MvPolynomial.map (algebraMap ℚ ℝ) PQ) = (Q ![x, y] : ℝ) := by
    have : ![(x : ℝ), (y : ℝ)] = algebraMap ℚ ℝ ∘ fun i => ((![x, y] i : ℤ) : ℚ) := by
      ext i; fin_cases i <;> simp
    rw [this, ← MvPolynomial.map_eval, hPQ]
    simp
  have hPR : MvPolynomial.map (algebraMap ℚ ℝ) PQ ≠ 0 := fun h0 => hQ <| funext fun w => by
    have hP0 : PQ = 0 :=
      MvPolynomial.map_injective _ (algebraMap ℚ ℝ).injective (by simpa using h0)
    simpa [hP0] using (hPQ w).symm
  by_contra! hall
  have hden := MMP.Positivity.den_le_of_eval_eq_zero_of_strip hPR
    ((Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hPQd) ha one_pos ht
    ⟨N, fun x y hx hy h1 h2 => by rw [hev, hall x y hx hy h1 h2, Int.cast_zero]⟩
  rw [div_one] at hden
  exact hv.not_ge (by exact_mod_cast hden)

/-- **The denominator bound of the rationality theorem** (Kollár–Mori, Theorem 3.5). Let
`(X, Δ, a, H)` be a rationality datum of dimension `n` and `r > 0` the nef threshold of `H` with
respect to `K_X + Δ`. Then `r = u / v` with `u, v ∈ ℤ` and `0 < v ≤ a(n + 1)`. -/
@[mmp "thm_km3b_rationality_free_denominator"]
public theorem _root_.MMP.Mori.IsRationalityDatum.exists_eq_div_of_isNefThreshold {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X}
    (hD : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hr0 : 0 < r) :
    ∃ u v : ℤ, 0 < v ∧ v ≤ a * (n + 1) ∧ r = u / v := by
  classical
  by_contra hcon
  have hrat : ∀ u v : ℤ, 0 < v → v ≤ a * (n + 1) → r ≠ (u : ℝ) / v :=
    fun u v hv hva he => hcon ⟨u, v, hv, hva, he⟩
  have ha : 0 < a := hD.pos
  -- `r = t` is rational, with `den t > a(n + 1)`
  obtain ⟨t, rfl⟩ := hD.exists_rat_eq_of_isNefThreshold hr hr0
  have ht0 : 0 < t := Rat.cast_pos.mp hr0
  have hv : a * (n + 1) < (t.den : ℤ) := by
    by_contra! hle
    exact hrat t.num t.den (by exact_mod_cast t.den_pos) hle (by
      rw [Rat.cast_def]; push_cast; rfl)
  -- the stable base locus `Z ≠ X` of the `(t, 1)`-strip
  obtain ⟨Z, hZ⟩ := hD.exists_isStableStripBaseLocus hr hr0 one_pos
  have hZtop : Z ≠ ⊤ := hD.ne_top_of_isStableStripBaseLocus hr hr0 hrat hZ
  obtain ⟨N, hN⟩ := hZ
  -- a lattice point `(p, q)` far out where `aq - tp` is maximal
  obtain ⟨p, q, hNp, hNq, hpq₀, hpq₁, hmax⟩ :=
    exists_strip_point_isGreatest ha ht0 (by nlinarith) (max N 1)
  have hp : 0 < p := by omega
  have hq : 0 < q := by omega
  have hLZ : stripBaseLocus K Δ a H p q = Z := hN p q (by omega) (by omega) hpq₀ hpq₁
  -- a nonzero section of `pH + qa(K_X + Δ)`
  have hσ : ∃ σ : (stripDivisor K Δ a H p q).divisorialSubmodule ⊤, σ ≠ 0 := by
    by_contra hno
    push Not at hno
    refine hZtop (hLZ ▸ eq_top_iff.mpr fun x _ => ?_)
    exact (Divisor.mem_baseLocus_iff _ x).mpr fun σ hσ => absurd (hno σ) hσ
  have hL0 : stripBaseLocus K Δ a H p q ≠ ⊥ := hD.stripBaseLocus_ne_bot hr hp hpq₀
  -- a `(p, q)`-adapted resolution with a tie-breaker `(j₀, c)`
  obtain ⟨Y, _, _, _, f, s, F, aj, pj, rj, hres⟩ :=
    hD.exists_isStripAdaptedResolution hr hp hq hpq₀ hpq₁ hσ
  obtain ⟨pj', j₀, c, h⟩ := hres.exists_isStripTieBreaker hr hpq₀ hpq₁ hL0
  -- `f(F_{j₀}) ⊆ L(p, q) = Z`
  have hFZ : f '' (F j₀).support ⊆ (Z : Set X) := by
    rw [← hLZ, h.toIsStripAdaptedResolution.stripBaseLocus_eq_image]
    exact Set.image_mono (Set.subset_biUnion_of_mem (u := fun j => (F j).support)
      (show j₀ ∈ {j | 0 < rj j} from h.pos_r))
  -- the restricted Euler characteristic function `Q` on `F = F_{j₀}`
  set ι := (F j₀).idealSheaf.subschemeι
  set A := tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj' j₀ c
  haveI hPY : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  have hKX : K.IsCanonicalDivisor sX n := h.isKltPair.1.2.1
  haveI : AlgebraicGeometry.IsVariety k sX := h.isKltPair.1.1.1
  have hdim : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      h.isLogResolution.isBirationalMorphism).symm.trans hKX.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hPY.toIsVariety
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hsm
  haveI : IsSmoothVariety k (f ≫ sX) := { toSmooth := inferInstance }
  haveI : IsProper f := h.isLogResolution.isProper
  have hFmem : F j₀ ∈ (∑ j, Finsupp.single (F j) (1 : ℤ)).support := by
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, h.injective.eq_iff]
  have hsmF : IsSmoothScheme (ι ≫ f ≫ sX) := h.isSNC.1 (F j₀) hFmem
  haveI : IsIntegral (F j₀).idealSheaf.subscheme := (F j₀).integral
  haveI hsF : Smooth (ι ≫ f ≫ sX) := (isSmoothScheme_iff _).mp hsmF
  haveI hvF : AlgebraicGeometry.IsVariety k (ι ≫ f ≫ sX) := ⟨⟩
  haveI : IsSmoothVariety k (ι ≫ f ≫ sX) := { toIsVariety := hvF, toSmooth := hsF }
  haveI : CompactSpace (F j₀).idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace ι
  haveI : IsLocallyNoetherian (F j₀).idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ f ≫ sX)
  haveI : IsNormal (F j₀).idealSheaf.subscheme := isNormal_of_smooth_over_field (ι ≫ f ≫ sX)
  haveI : AlgebraicGeometry.IsProjectiveVariety k (ι ≫ f ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff_isProjectiveMorphism k _).mpr
      ((MMP.isProjectiveMorphism_of_isClosedImmersion ι).comp hPY.isProjective)
  obtain ⟨m, hnm, hdimF⟩ : ∃ m : ℕ, n = m + 1 ∧
      topologicalKrullDim (F j₀).idealSheaf.subscheme = m := by
    have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sX)
      (F j₀).genericPoint
    rw [(F j₀).coheight_genericPoint, hdim,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← MMP.Mori.topologicalKrullDim_subscheme_eq] at h1
    refine exists_eq_add_one_of_add_one_eq ?_ (by exact_mod_cast h1)
    rw [ne_eq, topologicalKrullDim_eq_bot_iff_isEmpty, not_isEmpty_iff]
    infer_instance
  obtain ⟨hcY, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sX)
  obtain ⟨-, -, -, -, hinvF, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (ι ≫ f ≫ sX)
  have : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  have hHf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _ Z
  have hBf : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (a • (Divisor.toQDivisor K + Δ)).roundDown.supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _ Z
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  have hDc : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsCartier := by
    rwa [← hD₀, roundDown_toQDivisor]
  obtain ⟨H', hH'⟩ := h.isCartier_H.exists_isPullback hHf
  obtain ⟨B'', hB''⟩ := hDc.exists_isPullback hBf
  haveI := (hcY H').isInvertibleModule_divisorialSheaf
  haveI := (hcY B'').isInvertibleModule_divisorialSheaf
  obtain ⟨HF, eH⟩ := hinvF ((Scheme.Modules.pullback ι).obj H'.divisorialSheaf) inferInstance
  obtain ⟨BF, eB⟩ := hinvF ((Scheme.Modules.pullback ι).obj B''.divisorialSheaf) inferInstance
  have hQ := IsStripTieBreaker.eulerPolynomial_restrict_ne_zero h hr hr0 hpq₀ hH' hB'' eH eB
  obtain ⟨PQ, hPQd, hPQ⟩ := MMP.Mori.Divisor.exists_totalDegree_le_eval_eq_eulerPolynomial k
    (ι ≫ f ≫ sX) hsmF hdimF ![HF, BF] (A.restrictPrimeDivisor (F j₀))
  -- `Q` does not vanish at some lattice point `(x, y)` far out, where `ay - tx ≤ aq - tp`
  obtain ⟨x, y, hx, hy, h1, h2, hQne⟩ := exists_strip_point_ne_zero hQ (hPQd.trans (by omega))
    hPQ ha ht0 hv (max (max N 1) (max ⌈(1 + c) * p⌉ ⌈(1 + c) * q⌉))
  simp only [max_le_iff, Int.ceil_le] at hx hy
  have hxy := hmax x y (max_le hx.1.1 hx.1.2) (max_le hy.1.1 hy.1.2) h1 h2
  -- nonzero sections on `F` at `(x, y)`, so `f(F) ⊄ L(x, y) = Z`
  have hM : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H x y).supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _ Z
  obtain ⟨B', hB'⟩ := (toQDivisor_stripDivisor_and_isCartier hD x y).2.exists_isPullback hM
  have hQeq := IsStripTieBreaker.eulerPolynomial_restrict_eq_finrank h hr hpq₀ hx.2.1 hy.2.2
    hxy hH' hB'' eH eB hB'
  rw [hQeq] at hQne
  have hdrop := not_image_subset_stripBaseLocus h hr hpq₀ hx.2.1 hy.2.2 hxy hB'
    (Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero (by exact_mod_cast hQne)))
  rw [hN x y hx.1.1 hy.1.1 h1 h2] at hdrop
  exact hdrop hFZ

end MMP.FourfoldProofs.Km3bRationalityFreeDenominatorProof

end
