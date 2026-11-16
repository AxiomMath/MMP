module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativeBasepointFree

/-!
# Relative semiampleness of nef and big klt adjoints on projective surfaces

Let `(S, B)` be a klt pair on a normal projective `ℚ`-factorial surface `S` over an algebraically
closed field `k` of characteristic zero, with `B` an effective `ℚ`-divisor and `K` a canonical
divisor of `S`, and let `f : S ⟶ Z` be a morphism of projective varieties over `k`. If the adjoint
`L = K + B` is `f`-nef and `f`-big, then `L` is semiample over `Z`.

The proof applies the relative basepoint-free theorem to the Cartier divisor `D = m(K + B)`
supplied by `f`-bigness, with `a = 2 / m`, so that `aD - K - B = K + B`; then `bD` is `f`-free
for `b ≫ 0`. Along the way, a Cartier Weil divisor on a normal integral Noetherian scheme is
realised as the Weil divisor of a Cartier divisor.

## Main results

* `MMP.Mori.IsKltPair.isRelativelySemiample_of_isRelativelyNef_of_isRelativelyBig`: the
  relative semiampleness statement.

## Implementation notes

The klt condition is `MMP.Mori.IsKltPair` with canonical divisor `K` of dimension `2`, which
also records that `S` is a surface; `ℚ`-factoriality is `MMP.Fourfold.IsQFactorial`.
`f`-nefness, `f`-bigness and semiampleness over `Z` are `MMP.Mori.QDivisor.IsRelativelyNef`,
`MMP.Mori.QDivisor.IsRelativelyBig` and `MMP.Fourfold.QDivisor.IsRelativelySemiample`. The field
of complex numbers is replaced by an algebraically closed field of characteristic zero.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

section

namespace MMP.FourfoldProofs.MmpSurfaceProjectiveKltNefBigSemiampleProof

open CategoryTheory AlgebraicGeometry MMP.Mori

section WeilOfCartier

open Opposite MMP.Intersection

variable {Y : Scheme.{0}} [IsIntegral Y]

private theorem genericPoint_specializes (Z : irreducibleComponents Y) :
    genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

variable [IsLocallyNoetherian Y]

/-- The order of a regular function at a point of coheight one is the length of its quotient. -/
private theorem scheme_ord_algebraMap {z : Y} (hz : Order.coheight z = 1)
    {a : Y.presheaf.stalk z} (ha : a ≠ 0) :
    Y.ord (algebraMap (Y.presheaf.stalk z) Y.functionField a) z = (Ring.ord _ a).toNat := by
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hne : algebraMap (Y.presheaf.stalk z) Y.functionField a ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  rw [Scheme.ord_eq_iff hz hne]
  unfold Scheme.ordHom
  rw [Ring.ordFrac_eq_ord _ ha]
  have hnzd : a ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero ha
  exact Ring.ordMonoidWithZeroHom_eq_coe (R := Y.presheaf.stalk z) hnzd
    (ENat.natCast_toNat (Ring.ord_ne_top hnzd)).symm

/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero (A : Y.CartierDivisor) {x : Y}
    (hx : Order.coheight x = 0) : x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (Y.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (Y.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier [TopologicalSpace.NoetherianSpace Y]
    (A : Y.CartierDivisor) : ∃ w : Divisor Y, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    show P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

variable [IsNormal Y]

/-- `v_P` on the factor `𝒪_{Y,η}` of `K(Y)` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation (P : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y P.component)) :
    P.valuation s = (P.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes P.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- The principal Cartier divisor of a nonzero rational function `r` has order `ord_Q r` along
every prime divisor `Q`: a fraction `r = a / b` of the stalk at the generic point of `Q` is a local
equation, and the order of a fraction is the difference of the lengths of `a` and `b`. -/
private theorem primeDivisorOrder_principalDivisor_functionField {r : Y.functionField}
    (hr : r ≠ 0) (Q : MMP.Mori.PrimeDivisor Y) :
    primeDivisorOrder Q (MMP.Intersection.principalDivisor
      (Units.map (MMP.CartierDivisorSheaf.ofFunctionField
        (X := Y) ⊤).toMonoidHom (Units.mk0 r hr))) = Scheme.ord r Q.genericPoint := by
  set c : (Y.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := Y) ⊤).toMonoidHom
      (Units.mk0 r hr) with hc
  obtain ⟨⟨a, b⟩, hab⟩ :=
    IsLocalization.surj (nonZeroDivisors (Y.presheaf.stalk Q.genericPoint)) r
  have hbK : algebraMap _ Y.functionField (b : Y.presheaf.stalk Q.genericPoint) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero hr hbK hab
  have hfrac : IsFraction (Y.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _))
      a b := by
    refine ⟨isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors b.2, ?_⟩
    apply (totalQuotientStalkToFunctionField_bijective Q.genericPoint).1
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient]
    erw [MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField]
    exact (mul_comm _ _).trans hab
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk (primeDivisorSubvariety Q).genericPoint) :=
    krullDimLE_of_coheight_le Q.coheight_genericPoint.le
  rw [(isOrderAlong_of_isFraction (V := primeDivisorSubvariety Q)
    ⟨⊤, trivial, c, isLocalEquationOn_principalDivisor c, rfl⟩
    (mem_nonZeroDivisors_of_ne_zero ha0) b.2 hfrac).primeDivisorOrder_eq]
  have h1 := Scheme.ord_mul (x := Q.genericPoint) hr hbK
  rw [hab, scheme_ord_algebraMap Q.coheight_genericPoint ha0,
    scheme_ord_algebraMap Q.coheight_genericPoint (nonZeroDivisors.ne_zero b.2)] at h1
  change ((Ring.ord _ a).toNat : ℤ) -
    ((Ring.ord _ (b : Y.presheaf.stalk Q.genericPoint)).toNat : ℤ) = _
  omega

/-- A principal divisor on a normal integral locally Noetherian scheme is the Weil divisor of the
principal Cartier divisor of the same rational function. -/
private theorem exists_isWeilDivisorOfCartier_principalDivisor [CompactSpace Y]
    (φ : (RationalFunctions Y)ˣ) :
    ∃ A : Y.CartierDivisor, IsWeilDivisorOfCartier A (MMP.Mori.principalDivisor φ) := by
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents Y) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  have : Subsingleton (irreducibleComponents Y) :=
    (irreducibleComponents_eq_singleton (X := Y) ▸ Set.subsingleton_singleton).coe_sort
  set r₀ : Y.functionField := (Y.presheaf.stalkSpecializes (genericPoint_specializes Z₀)).hom
    ((φ : RationalFunctions Y) Z₀)
  have hr0 : r₀ ≠ 0 :=
    ((φ.isUnit.map (Pi.evalMonoidHom (fun Z : irreducibleComponents Y =>
      Y.presheaf.stalk (componentGenericPoint Y Z)) Z₀)).map
        (Y.presheaf.stalkSpecializes (genericPoint_specializes Z₀)).hom).ne_zero
  refine ⟨MMP.Intersection.principalDivisor (Units.map
    (MMP.CartierDivisorSheaf.ofFunctionField (X := Y) ⊤).toMonoidHom
      (Units.mk0 r₀ hr0)), fun Q => ?_⟩
  have hord : Q.ord φ = Scheme.ord r₀ Q.genericPoint := by
    have h := valuation_eq_inv_divisorialValuation Q ((φ : RationalFunctions Y) Q.component)
    obtain rfl := Subsingleton.elim Q.component Z₀
    rw [Q.valuation_component,
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hr0, ← WithZero.exp_neg,
      neg_neg] at h
    exact WithZero.exp_injective h
  rw [coeff_principalDivisor, hord, ← primeDivisorOrder_principalDivisor_functionField hr0]
  exact isOrderAlong_primeDivisorOrder _ Q

/-- **A Cartier Weil divisor is the Weil divisor of a Cartier divisor.** On a normal integral
Noetherian scheme, `𝒪_X(D) ≅ 𝒪_X(E₀)` for some Cartier divisor `E₀` with Weil divisor `w₀`;
then `D - w₀ = div φ`, and `E₀ + div φ` has Weil divisor `D`. -/
private theorem exists_isWeilDivisorOfCartier_of_isCartier [CompactSpace Y] {D : Divisor Y}
    (hD : D.IsCartier) : ∃ E : Y.CartierDivisor, IsWeilDivisorOfCartier E D := by
  haveI : IsNoetherian Y := ⟨⟩
  have := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E₀, ⟨e₀⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  obtain ⟨w₀, hw₀⟩ := exists_isWeilDivisorOfCartier E₀
  obtain ⟨e₁⟩ := hw₀.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e₀ ≪≫ e₁)
  obtain ⟨Pc, hPc⟩ := exists_isWeilDivisorOfCartier_principalDivisor φ
  refine ⟨E₀ + Pc, fun Q => ?_⟩
  have h := (hw₀ Q).add (hPc Q)
  rwa [← DivisorWithCoeffs.coeff_add, ← hφ, add_sub_cancel] at h

end WeilOfCartier

/-- An epimorphic counit of `f^* ⊣ f_*` stays epimorphic along an isomorphism of modules. -/
private theorem epi_counit_of_iso {X Z : Scheme.{0}} (f : X ⟶ Z) {M N : X.Modules} (e : N ≅ M)
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have heq : adj.counit.app N =
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map e.hom ≫
        adj.counit.app M ≫ e.inv := by
    rw [← Category.assoc, adj.counit.naturality e.hom, Functor.id_map, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

private theorem realization_congr {X : Scheme.{0}} {c c' : KCartierDivisor ℚ X}
    (e : c = c') (h : ∀ D, ∃ n : ℤ, c D = n) (h' : ∀ D, ∃ n : ℤ, c' D = n) :
    KCartierDivisor.realization c h = KCartierDivisor.realization c' h' := by
  subst e
  rfl

/-- A `ℚ`-divisor `Q` with `n Q` a relatively free Cartier divisor is relatively semiample. -/
private theorem isRelativelySemiample_of_isRelativelyFreeDivisor {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Z)
    (Q : QDivisor X) {n : ℕ} (hn : 0 < n) {D : Divisor X} (hDc : D.IsCartier)
    (hQ : Divisor.toQDivisor D = (n : ℚ) • Q) (hfree : MMP.Fourfold.IsRelativelyFreeDivisor f D) :
    MMP.Fourfold.QDivisor.IsRelativelySemiample f Q := by
  classical
  obtain ⟨E, hE⟩ := exists_isWeilDivisorOfCartier_of_isCartier hDc
  obtain ⟨e⟩ := hE.nonempty_sheaf_iso_divisorialSheaf
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨Finsupp.single E ((n : ℚ)⁻¹), fun P => ?_, n, hn, ?_⟩
  · rw [Finsupp.sum_single_index (by simp),
      (MMP.Intersection.isOrderAlong_primeDivisorOrder E P).unique (hE P)]
    have hP := congrArg (fun F : QDivisor X => F.coeff P) hQ
    simp only [Divisor.coeff_toQDivisor] at hP
    rw [hP]
    simp [DivisorWithCoeffs.coeff_apply]
    field_simp
  · have hc : (n : ℚ) • Finsupp.single E ((n : ℚ)⁻¹) =
        (Finsupp.single E (1 : ℤ)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
      rw [Finsupp.smul_single, Finsupp.mapRange_single, smul_eq_mul, mul_inv_cancel₀ hn',
        Int.cast_one]
    refine ⟨fun D => ⟨(Finsupp.single E (1 : ℤ)) D, by rw [hc]; rfl⟩, ?_⟩
    rw [realization_congr hc _ (fun D => ⟨(Finsupp.single E (1 : ℤ)) D, rfl⟩),
      KCartierDivisor.realization_eq_sum, Finsupp.sum_single_index (by simp), one_smul]
    exact epi_counit_of_iso f e hfree

/-- The sum defining relative nefness of a `ℚ`-Cartier `ℚ`-divisor is its intersection number. -/
private theorem sum_associatedCartier_eq_intersectionNumber {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (D : QDivisor X) (h : D.IsQCartier) (C : ProperCurve sX) :
    ((D.associatedCartier h).sum fun E c =>
      (c : ℝ) * ((E : Divisor X).degreeOn k sX C.ι C.dim_le E.2 : ℝ)) =
      (D.intersectionNumber k sX C.ι C.dim_le h : ℝ) := by
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.sum_single_index (by simp),
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D h _
      (D.cartierIndexSMul h).2 (QDivisor.toQDivisor_cartierIndexSMul D h)]
  push_cast
  ring

/-- A positive multiple of an `f`-nef `ℚ`-divisor which is a Cartier divisor is `f`-nef. -/
private theorem isRelativelyNef_of_toQDivisor_eq_smul {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y}
    {L : QDivisor X} (hL : L.IsRelativelyNef sX f) {m : ℕ} (hm : 0 < m) {D : Divisor X}
    (hDc : D.IsCartier) (hD : Divisor.toQDivisor D = (m : ℚ) • L) :
    (Divisor.toQDivisor D).IsRelativelyNef sX f := by
  obtain ⟨hLq, hLC⟩ := hL
  have hDq : (Divisor.toQDivisor D).IsQCartier := QDivisor.isQCartier_toQDivisor hDc
  refine ⟨hDq, fun C hC => ?_⟩
  have h1 := hLC C hC
  rw [sum_associatedCartier_eq_intersectionNumber] at h1 ⊢
  rw [QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le D hDc hDq]
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul k sX C.ι C.dim_le
    (Divisor.degreeOn_add k sX C.ι C.dim_le) L hLq hm D hDc
    (by rw [hD, ← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl)] at h1
  push_cast at h1
  exact_mod_cast (div_nonneg_iff.mp h1).resolve_right
    (fun h => h.2.not_gt (by exact_mod_cast hm)) |>.1

end MMP.FourfoldProofs.MmpSurfaceProjectiveKltNefBigSemiampleProof

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.FourfoldProofs.MmpSurfaceProjectiveKltNefBigSemiampleProof

namespace MMP.Mori

/-- **Relative semiampleness of klt adjoints on projective surfaces.** Let `(S, B)` be a klt pair,
with `B ≥ 0` a `ℚ`-divisor and `K` a canonical divisor, on a normal projective `ℚ`-factorial
surface `S` over an algebraically closed field `k` of characteristic zero, and let `f : S ⟶ Z` be
a morphism over `k` to a projective variety `Z`. If `K + B` is `f`-nef and `f`-big, then `K + B` is
semiample over `Z`. -/
@[mmp "thm_mmp_surface_projective_klt_nef_big_semiample"]
public theorem IsKltPair.isRelativelySemiample_of_isRelativelyNef_of_isRelativelyBig
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {S Z : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of k)}
    [IsProjectiveVariety k sS] [QuasiCompact sS] {sZ : Z ⟶ Spec (.of k)}
    [IsProjectiveVariety k sZ] {f : S ⟶ Z} (hf : f ≫ sZ = sS)
    (_hS : MMP.Fourfold.IsQFactorial sS) {K : Divisor S} {B : QDivisor S}
    (hklt : IsKltPair sS 2 K B) (hB : 0 ≤ B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sS f)
    (hbig : (Divisor.toQDivisor K + B).IsRelativelyBig f) :
    MMP.Fourfold.QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) := by
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  obtain ⟨m, hm, D, hDL, hDc, -⟩ := id hbig
  have heq : (2 / (m : ℚ)) • Divisor.toQDivisor D - Divisor.toQDivisor K - B =
      Divisor.toQDivisor K + B := by
    rw [hDL, smul_smul, div_mul_cancel₀ _ (by positivity), two_smul]
    abel
  obtain ⟨b₀, hb₀⟩ := exists_forall_ge_isRelativelyFreeDivisor_of_isKltPair
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, hf⟩ hklt hB hDc
    (isRelativelyNef_of_toQDivisor_eq_smul hnef hm hDc hDL) (a := 2 / (m : ℚ)) (by positivity)
    (heq ▸ hnef) (heq ▸ hbig)
  refine isRelativelySemiample_of_isRelativelyFreeDivisor f _ (n := (b₀ + 1) * m)
    (by positivity) (hDc.zsmul _) ?_ (hb₀ (b₀ + 1) (Nat.le_succ b₀))
  rw [map_zsmul, hDL, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  congr 1
  push_cast
  ring

end MMP.Mori

end
