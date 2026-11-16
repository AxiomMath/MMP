module

public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
public import MMP.AlgebraicGeometry.Positivity.BigNefCartier
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs

/-!
## Proof outline

Let `X` be a normal projective variety over `k`, `D` a Cartier divisor, `E ≥ 0` a `ℚ`-Cartier
`ℚ`-divisor and `Aₙ` ample `ℚ`-divisors with `D ≡ Aₙ + (1/n) E` for infinitely many `n`.

*Nef.* For a closed curve `C`, `(D · C) = (Aₙ · C) + (1/n)(E · C) ≥ (1/n)(E · C)` for infinitely
many `n`; since `(D · C)` is an integer, it is `≥ 0`.

*Big.* Fix such an `n` and `e > 0` with `F = eE` Cartier, and put `N = en`, `G = ND - F`. Then
`G = N (D - E/n)` with `D - E/n ≡ Aₙ`, so `G` is ample, and `G + D` is ample plus nef, hence
ample. Ample divisors have `h⁰(mH) > c mᵈ` for `m ≫ 0`. Sections of `j(G + D)` with
`j ≡ r mod N` give nonzero sections of `(j + t) G + t F + r D`, and multiplying by them gives
`h⁰(mD) ≥ h⁰((q - a) G)` for `m = qN + r`, which grows like `mᵈ`.
-/

namespace MMP.FourfoldProofs.Km2cNefBigOfAmpleApproximationProof

open CategoryTheory AlgebraicGeometry MMP.Mori

section QDiv

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- An ample Cartier divisor has nonnegative degree on every closed curve proper over `k`. -/
private theorem degreeOn_nonneg_of_isAmple [CompactSpace X] {C : Scheme.{0}} (i : C ⟶ X)
    [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)] (hC : topologicalKrullDim C = 1)
    (D : Divisor X) (hD : D.IsCartier) (hA : D.IsAmple hD) :
    0 ≤ D.degreeOn k sX i hC.le hD := by
  haveI : AlgebraicGeometry.IsCurve k (i ≫ sX) := (AlgebraicGeometry.isCurve_iff k _).mpr ⟨{}, hC⟩
  haveI := hD.isInvertibleModule_divisorialSheaf
  have h1 := isAmple_pullback_of_isFinite i D.divisorialSheaf
    ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).mpr hA)
  haveI := MMP.Mori.isInvertible_pullback_obj i D.divisorialSheaf
  exact (invertibleCurveDegree_pos_of_isAmple_of_isCurve k (i ≫ sX) hC.le _ h1).le

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem natCast_zsmul_eq_smul (m : ℕ) (A : QDivisor X) :
    ((m : ℤ) • A) = (m : ℚ) • A := by
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]

/-- An ample `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_of_isAmple [CompactSpace X] {A : QDivisor X} (hA : A.IsAmple) :
    A.IsQCartier := by
  obtain ⟨m, hm, D, hDA, hDc, -⟩ := hA
  exact ⟨m, by exact_mod_cast hm.ne', D, by rw [hDA, natCast_zsmul_eq_smul], hDc⟩

private theorem intersectionNumber_congr {C : Scheme.{0}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1)
    {D₁ D₂ : QDivisor X} (h : D₁ = D₂) (h₁ : D₁.IsQCartier) (h₂ : D₂.IsQCartier) :
    D₁.intersectionNumber k sX i hdim h₁ = D₂.intersectionNumber k sX i hdim h₂ := by
  subst h
  rfl

/-- An ample `ℚ`-divisor has nonnegative intersection number with every closed curve proper
over `k`. -/
private theorem intersectionNumber_nonneg_of_isAmple [CompactSpace X] {C : Scheme.{0}}
    (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
    (hC : topologicalKrullDim C = 1) {A : QDivisor X} (hA : A.IsAmple) (hAq : A.IsQCartier) :
    0 ≤ A.intersectionNumber k sX i hC.le hAq := by
  obtain ⟨m, hm, D, hDA, hDc, hamp⟩ := hA
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hC.le A hAq hm D hDc
    (by rw [hDA, natCast_zsmul_eq_smul])]
  exact div_nonneg (by exact_mod_cast degreeOn_nonneg_of_isAmple sX i hC D hDc hamp)
    (by positivity)

/-- If `F = e E`, then `F = (e n) • ((1/n) E)` as `ℚ`-divisors. -/
private theorem toQDivisor_eq_smul_inv_smul {E : QDivisor X} {F : Divisor X} {e n : ℕ}
    (hn : 0 < n) (hFE : Divisor.toQDivisor F = (e : ℤ) • E) :
    Divisor.toQDivisor F = ((e * n : ℕ) : ℤ) • ((n : ℚ)⁻¹ • E) := by
  rw [hFE, natCast_zsmul_eq_smul, natCast_zsmul_eq_smul, smul_smul]
  congr 1
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

/-- If `eE = F` with `F` Cartier and `e > 0`, then `(1/n) E` is `ℚ`-Cartier for `n > 0`. -/
private theorem isQCartier_inv_smul {E : QDivisor X} {F : Divisor X} (hF : F.IsCartier)
    {e n : ℕ} (he : 0 < e) (hn : 0 < n) (hFE : Divisor.toQDivisor F = (e : ℤ) • E) :
    ((n : ℚ)⁻¹ • E).IsQCartier :=
  ⟨((e * n : ℕ) : ℤ), by positivity, F, (toQDivisor_eq_smul_inv_smul hn hFE).symm ▸ rfl, hF⟩

/-- If `F = e E` is Cartier with `e > 0` and `D ≡ A n + (1/n) E` with `A n` ample for infinitely
many `n`, then `D` is nef. -/
private theorem isNef_of_ample_approximation [CompactSpace X] (D : Divisor X) (hD : D.IsCartier)
    (E : QDivisor X) (F : Divisor X) (hF : F.IsCartier) {e : ℕ} (he : 0 < e)
    (hFE : Divisor.toQDivisor F = (e : ℤ) • E) (A : ℕ → QDivisor X)
    (hA : {n : ℕ | (A n).IsAmple ∧
      (Divisor.toQDivisor D).NumericallyEquivalent k sX (A n + (n : ℚ)⁻¹ • E)}.Infinite) :
    D.IsNef k sX := by
  refine ⟨hD, fun C i _ _ _ hC => ?_⟩
  by_contra hneg
  rw [not_le] at hneg
  set d := D.degreeOn k sX i hC.le hD
  set f := F.degreeOn k sX i hC.le hF
  obtain ⟨n, ⟨hAn, hnum⟩, hn⟩ := hA.exists_gt f.natAbs
  have hn0 : 0 < n := by omega
  obtain ⟨h₁, h₂, heq⟩ := hnum
  have hEq := isQCartier_inv_smul hF he hn0 hFE
  have hsum := heq C i hC
  rw [QDivisor.intersectionNumber_add' k sX i hC.le _ _ (isQCartier_of_isAmple hAn) hEq h₂,
    QDivisor.intersectionNumber_toQDivisor k sX i hC.le D hD h₁,
    QDivisor.intersectionNumber_eq_of_smul k sX i hC.le _ hEq (Nat.mul_pos he hn0) F hF
      (toQDivisor_eq_smul_inv_smul hn0 hFE)]
    at hsum
  have hA0 := intersectionNumber_nonneg_of_isAmple sX i hC hAn (isQCartier_of_isAmple hAn)
  have hen : (0 : ℚ) < ((e * n : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos he hn0
  have key : (f : ℚ) ≤ (d : ℚ) * ((e * n : ℕ) : ℚ) := by
    rw [← div_le_iff₀ hen]
    linarith
  have key' : f ≤ d * ((e * n : ℕ) : ℤ) := by exact_mod_cast key
  have h1 : (n : ℤ) ≤ ((e * n : ℕ) : ℤ) := by
    push_cast
    nlinarith [(by exact_mod_cast he : (1 : ℤ) ≤ e)]
  have h2 : -(f.natAbs : ℤ) ≤ f := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le f
  have h3 : (f.natAbs : ℤ) < n := by exact_mod_cast hn
  have h4 : d ≤ -1 := by omega
  nlinarith

/-- If `D ≡ A + (1/n) E` with `A` ample and `F = e E` Cartier, then `(e n) D - F` is ample. -/
private theorem isAmple_nsmul_sub [MMP.Mori.IsProjectiveVariety k sX] [CompactSpace X]
    {D : Divisor X} (hD : D.IsCartier) {E : QDivisor X} {F : Divisor X} (hF : F.IsCartier)
    {e n : ℕ} (he : 0 < e) (hn : 0 < n) (hFE : Divisor.toQDivisor F = (e : ℤ) • E)
    {A : QDivisor X} (hA : A.IsAmple)
    (hnum : (Divisor.toQDivisor D).NumericallyEquivalent k sX (A + (n : ℚ)⁻¹ • E))
    (hG : (((e * n : ℕ) : ℤ) • D - F).IsCartier) :
    (((e * n : ℕ) : ℤ) • D - F).IsAmple hG := by
  set B : QDivisor X := Divisor.toQDivisor D - (n : ℚ)⁻¹ • E
  have hGB : Divisor.toQDivisor (((e * n : ℕ) : ℤ) • D - F) = ((e * n : ℕ) : ℚ) • B := by
    rw [map_sub, map_zsmul, toQDivisor_eq_smul_inv_smul hn hFE, natCast_zsmul_eq_smul,
      natCast_zsmul_eq_smul, smul_sub]
  have hBq : B.IsQCartier := ⟨((e * n : ℕ) : ℤ), by positivity, _,
    by rw [hGB, natCast_zsmul_eq_smul], hG⟩
  have hEq := isQCartier_inv_smul hF he hn hFE
  have hAq := isQCartier_of_isAmple hA
  have hnef0 : (0 : QDivisor X).IsNef k sX := by
    simpa using (QDivisor.isNef_toQDivisor_iff (k := k) (sX := sX) (0 : Divisor X)
      Divisor.isCartier_zero).mpr
      ⟨Divisor.isCartier_zero, fun C i _ _ _ hC => (Divisor.degreeOn_zero' k sX i hC.le).ge⟩
  have hB : B.NumericallyEquivalent k sX (A + 0) := by
    obtain ⟨h₁, h₂, heq⟩ := hnum
    refine ⟨hBq, hAq.add QDivisor.isQCartier_zero, fun C i _ _ _ hC => ?_⟩
    have h := heq C i hC
    rw [QDivisor.intersectionNumber_add' k sX i hC.le _ _ hAq hEq h₂,
      intersectionNumber_congr sX i hC.le (sub_add_cancel _ _).symm h₁ (hBq.add hEq),
      QDivisor.intersectionNumber_add' k sX i hC.le _ _ hBq hEq] at h
    rw [intersectionNumber_congr sX i hC.le (add_zero A) _ hAq]
    linarith
  exact QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sX hA hnef0 hB _
    (Nat.mul_pos he hn) _ hGB hG

/-- Ample plus nef is ample, for Cartier divisors. -/
private theorem isAmple_add_of_isNef [MMP.Mori.IsProjectiveVariety k sX] [CompactSpace X]
    {G D : Divisor X} (hG : G.IsCartier) (hD : D.IsCartier) (hGa : G.IsAmple hG)
    (hnef : D.IsNef k sX) : (G + D).IsAmple (hG.add hD) :=
  QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sX ⟨1, one_pos, G, by simp, hG, hGa⟩
    ((QDivisor.isNef_toQDivisor_iff (k := k) (sX := sX) D hD).mpr hnef)
    (show (Divisor.toQDivisor (G + D)).NumericallyEquivalent k sX
        (Divisor.toQDivisor G + Divisor.toQDivisor D) by
      rw [map_add]
      exact QDivisor.NumericallyEquivalent.refl
        ((QDivisor.isQCartier_toQDivisor hG).add (QDivisor.isQCartier_toQDivisor hD)))
    1 one_pos (G + D) (by simp) (hG.add hD)

end QDiv

section Sections

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- An injective `R`-linear map between `R`-modules that are `k`-vector spaces through a ring map
`φ : k →+* R` does not decrease the `k`-dimension. -/
private theorem finrank_compHom_le {R : Type} [CommRing R] (φ : k →+* R) {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (hg : Function.Injective g) (hN : letI := Module.compHom N φ; FiniteDimensional k N) :
    (letI := Module.compHom M φ; Module.finrank k M) ≤
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M →ₗ[k] N :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact LinearMap.finrank_le_finrank_of_injective (f := g') hg

/-- An `R`-linear equivalence between `R`-modules that are `k`-vector spaces through a ring map
`φ : k →+* R` preserves the `k`-dimension. -/
private theorem finrank_compHom_eq {R : Type} [CommRing R] (φ : k →+* R) {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M ≃ₗ[R] N) :
    (letI := Module.compHom M φ; Module.finrank k M) =
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M ≃ₗ[k] N :=
    { g.toEquiv with map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact g'.finrank_eq

omit [Field k] in
/-- The `Γ(X, 𝒪_X)`-linear isomorphism `Γ(X, L) ≃ Γ(X, L')` induced by an isomorphism `L ≅ L'`. -/
private noncomputable def sectionsLinearEquiv {L L' : X.Modules} (e : L ≅ L') :
    Γ(L, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(L', ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  map_add' := map_add _
  map_smul' _ s := Scheme.Modules.Hom.app_smul e.hom _ s
  left_inv s := by
    change ((e.hom ≫ e.inv).app ⊤) s = s
    rw [Iso.hom_inv_id]
    rfl
  right_inv s := by
    change ((e.inv ≫ e.hom).app ⊤) s = s
    rw [Iso.inv_hom_id]
    rfl

private theorem scalarsToGlobalSections_eq_appLE :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom := by
  have : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]
  rfl

variable [IsLocallyNoetherian X] [IsNormal X]

/-- `h⁰` of a Cartier divisor `A` equals `h⁰` of a divisor `D` with `𝒪_X(A) ≅ 𝒪_X(D)`. -/
private theorem cartierH0_eq_h0 (A : X.CartierDivisor) (D : Divisor X)
    (e : MMP.CartierDivisor.sheaf A ≅ D.divisorialSheaf) :
    cartierH0 k sX A = D.h0 k sX :=
  finrank_compHom_eq (scalarsToGlobalSections k sX) (sectionsLinearEquiv e)

/-- The global sections of `𝒪_X(D)`, `D` Cartier on a proper `k`-scheme, are finite over `k`. -/
private theorem finite_divisorialSubmodule_top [IsProper sX] [CompactSpace X]
    {D : Divisor X} (hD : D.IsCartier) :
    letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX);
    Module.Finite k (D.divisorialSubmodule ⊤) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sX
    D.divisorialSheaf 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sX D.divisorialSheaf 0
  have e := (cohomologyOverFieldZeroLinearIso k sX D.divisorialSheaf).toLinearEquiv
  have key : ∀ ψ : k →+* Γ(X, ⊤),
      ψ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom (D.divisorialSubmodule ⊤) ψ;
          Module.Finite k (D.divisorialSubmodule ⊤)) := by
    rintro ψ rfl
    have := Module.Finite.equiv e
    exact this
  exact key _ (scalarsToGlobalSections_eq_appLE sX)

/-- If `S` has a nonzero global section and `V + S ≤ W` with `W` Cartier, then
`h⁰(V) ≤ h⁰(W)`. -/
public theorem _root_.MMP.Mori.Divisor.h0_le_of_add_le [IsProper sX] [CompactSpace X]
    [IsIntegral X] {V S W : Divisor X} (hW : W.IsCartier) (hle : V + S ≤ W)
    (σ : S.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    V.h0 k sX ≤ W.h0 k sX := by
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hz := Divisor.zeroDivisor_nonneg S σ hσ
  rw [Divisor.zeroDivisor_eq] at hz
  have hle' : V - MMP.Mori.principalDivisor φ ≤ W := by
    refine le_trans ?_ hle
    intro E
    have := hz E
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.coe_sub, Pi.sub_apply] at this ⊢
    linarith
  let g₁ := Divisor.divisorialMulLinearMap (D := V) (D' := V - MMP.Mori.principalDivisor φ) φ
    (fun E => by
      rw [DivisorWithCoeffs.coeff_sub, MMP.Mori.coeff_principalDivisor]; ring) ⊤
  let g := Submodule.inclusion (Divisor.divisorialSubmodule_mono hle' ⊤) ∘ₗ g₁
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : (g₁ a).1 = (g₁ b).1 := congrArg (fun x => x.1) hab
    apply Subtype.ext
    funext Z
    have h2 := congrFun h1 Z
    simp only [g₁, Divisor.coe_divisorialMulLinearMap_apply] at h2
    have hu : IsUnit ((φ : RationalFunctions X) Z.1) := (Pi.isUnit_iff.mp φ.isUnit) Z.1
    exact hu.mul_left_cancel h2
  exact finrank_compHom_le (scalarsToGlobalSections k sX) g hg
    (finite_divisorialSubmodule_top sX hW)

end Sections

section Big

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor with `h⁰ > 0` has a nonzero global section. -/
private theorem exists_ne_zero_of_h0_pos {D : Divisor X} (h : 0 < D.h0 k sX) :
    ∃ σ : D.divisorialSubmodule ⊤, σ ≠ 0 := by
  by_contra hne
  simp only [ne_eq, not_exists, not_not] at hne
  haveI : Subsingleton (D.divisorialSubmodule ⊤) := ⟨fun a b => (hne a).trans (hne b).symm⟩
  unfold Divisor.h0 at h
  letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
  rw [Module.finrank_zero_of_subsingleton] at h
  exact lt_irrefl 0 h

/-- Given `𝒪_X(A) ≅ 𝒪_X(D)` with `D` Cartier, the induced isomorphisms
`𝒪_X((n + 1) • A) ≅ 𝒪_X((n + 1) • D)`. -/
private noncomputable def sheafSuccNsmulIso [CompactSpace X]
    (A : X.CartierDivisor) (D : Divisor X) (hD : D.IsCartier)
    (e : MMP.CartierDivisor.sheaf A ≅ D.divisorialSheaf) :
    ∀ n : ℕ, MMP.CartierDivisor.sheaf ((n + 1) • A) ≅
      ((n + 1) • D).divisorialSheaf
  | 0 => eqToIso (by rw [zero_add, one_smul]) ≪≫ e ≪≫ eqToIso (by rw [zero_add, one_smul])
  | n + 1 => eqToIso (by rw [succ_nsmul]) ≪≫
      (MMP.CartierDivisorSheaf.sheafMulIso ((n + 1) • A) A).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X (sheafSuccNsmulIso A D hD e n) e ≪≫
      (hD.nsmul (n + 1)).divisorialSheafTensorIso hD ≪≫ eqToIso (by rw [← succ_nsmul])

/-- **Ample divisors grow.** An ample Cartier divisor `H` on a projective variety of dimension
`d` has `h⁰(mH) > c mᵈ` for some `c > 0` and all `m ≫ 0`. -/
private theorem exists_lt_h0_of_isAmple [MMP.Mori.IsProjectiveVariety k sX] [CompactSpace X]
    (H : Divisor X) (hH : H.IsCartier) (hamp : H.IsAmple hH) :
    ∃ d : ℕ, topologicalKrullDim X = d ∧ ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℤ, 0 < k₀ ∧
      ∀ m : ℤ, k₀ ≤ m → c * (m : ℝ) ^ d < ((m • H).h0 k sX : ℝ) := by
  haveI : IsIntegral X := (inferInstance : AlgebraicGeometry.IsVariety k sX).toIsIntegral
  haveI := hH.isInvertibleModule_divisorialSheaf
  obtain ⟨A, ⟨eA⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf H.divisorialSheaf
  have hA : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A) :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).mp
      (Scheme.Modules.isAmple_of_iso eA
        ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).mpr hamp))
  obtain ⟨d, hd, c, hc, k₀, hk⟩ :=
    isBigCartier_of_linearlyEquivalent_add (E := 0) (m := 1) ‹_› one_pos hA
      MMP.Intersection.isEffective_zero (by
        simpa using MMP.Intersection.LinearlyEquivalent.refl _)
  refine ⟨d, hd, c, hc, max k₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = ((j + 1 : ℕ) : ℤ) :=
    ⟨m.toNat - 1, by have := le_of_max_le_right hm; omega⟩
  have h := hk _ (le_of_max_le_left hm)
  rw [natCast_zsmul, cartierH0_eq_h0 sX _ _ (sheafSuccNsmulIso A H hH eA.symm j)] at h
  rwa [natCast_zsmul]

/-- If `N D = G + F` and `h⁰(m (G + D)) > c mᵈ` with `c > 0` for `m ≥ j > 0`,
then `(r + N j + j) G + j F + r D` has a nonzero global section for every `r ≥ 0`. -/
private theorem exists_ne_zero_divisorialSubmodule_of_lt_h0 {G D F : Divisor X} {N : ℕ}
    (hN : 0 < N) (hDGF : (N : ℤ) • D = G + F) {c : ℝ} (hc : 0 < c) {d : ℕ} {j : ℤ}
    (hH : ∀ m : ℤ, j ≤ m → c * (m : ℝ) ^ d < ((m • (G + D)).h0 k sX : ℝ)) (hj : 0 < j)
    {r : ℤ} (hr : 0 ≤ r) :
    ∃ σ : (((r + N * j + j) • G + j • F + r • D).divisorialSubmodule ⊤), σ ≠ 0 := by
  have hjr : j ≤ r + N * j := by nlinarith [(by exact_mod_cast hN : (1 : ℤ) ≤ N)]
  have hpos := hH (r + N * j) hjr
  have h0 : 0 ≤ c * (((r + N * j : ℤ)) : ℝ) ^ d :=
    mul_nonneg hc.le (pow_nonneg (by exact_mod_cast (hj.le.trans hjr)) _)
  have heq : (r + N * j) • (G + D) = (r + N * j + j) • G + j • F + r • D := by
    rw [eq_sub_of_add_eq hDGF.symm]
    module
  rw [heq] at hpos
  exact exists_ne_zero_of_h0_pos sX (by exact_mod_cast h0.trans_lt hpos)

/-- If `N > 0`, `N • D = G + F` with `G`, `G + D` ample Cartier and `F ≥ 0` Cartier, then `D` is
big. -/
private theorem isBig_of_nsmul_eq_add [MMP.Mori.IsProjectiveVariety k sX] [CompactSpace X]
    (D : Divisor X) (hD : D.IsCartier) (G F : Divisor X) (hG : G.IsCartier) (hF : F.IsCartier)
    (hF0 : 0 ≤ F) {N : ℕ} (hN : 0 < N) (hDGF : (N : ℤ) • D = G + F) (hGa : G.IsAmple hG)
    (hHa : (G + D).IsAmple (hG.add hD)) : D.IsBig k sX := by
  haveI : IsIntegral X := (inferInstance : AlgebraicGeometry.IsVariety k sX).toIsIntegral
  haveI : IsProper sX :=
    isProper_of_isProjectiveMorphism sX
      (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sX).isProjective
  obtain ⟨d, hd, c₁, hc₁, j₁, hj₁, hGg⟩ := exists_lt_h0_of_isAmple sX G hG hGa
  obtain ⟨d₂, -, c₂, hc₂, j₂, hj₂, hHg⟩ := exists_lt_h0_of_isAmple sX (G + D) _ hHa
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  set a₀ : ℤ := N + N * j₂ + j₂ with ha₀
  have ha₀0 : 0 ≤ a₀ := by positivity
  refine ⟨d, hd, c₁ / (2 * N) ^ d, by positivity, 2 * N * (1 + a₀ + j₁ + j₂), fun m hm => ?_⟩
  set q := m / N
  set r := m % N
  have hmqr : m = N * q + r := (Int.mul_ediv_add_emod m N).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg m hNz.ne'
  have hrN : r < N := Int.emod_lt_of_pos m hNz
  set a : ℤ := r + N * j₂ + j₂ with ha
  have haa₀ : a ≤ a₀ := by omega
  have ha0 : 0 ≤ a := by positivity
  -- `2 N (q - a) ≥ m`
  have hNa : (N : ℤ) * a ≤ N * a₀ := mul_le_mul_of_nonneg_left haa₀ hNz.le
  have h2 : m ≤ 2 * N * (q - a) := by nlinarith
  have h3 : 1 + a₀ + j₁ + j₂ ≤ q - a :=
    le_of_mul_le_mul_left (hm.trans h2) (by positivity)
  obtain ⟨σ, hσ⟩ := exists_ne_zero_divisorialSubmodule_of_lt_h0 sX hN hDGF hc₂ hHg hj₂ hr0
  -- `h⁰(mD) ≥ h⁰((q - a) G)`
  have hdec : m • D = (q - a) • G + ((r + N * j₂ + j₂) • G + j₂ • F + r • D) + (q - j₂) • F := by
    have hG' : G = (N : ℤ) • D - F := eq_sub_of_add_eq hDGF.symm
    rw [hG', hmqr]
    module
  have hle : (q - a) • G + ((r + N * j₂ + j₂) • G + j₂ • F + r • D) ≤ m • D := by
    rw [hdec]
    exact le_add_of_nonneg_right (zsmul_nonneg hF0 (by omega))
  have hh0 := MMP.Mori.Divisor.h0_le_of_add_le sX (hD.zsmul m) hle σ hσ
  have hgrow := hGg (q - a) (by omega)
  -- the real inequality
  have hm0 : (0 : ℝ) ≤ m := by
    have : (0 : ℤ) ≤ m := le_trans (by positivity) hm
    exact_mod_cast this
  have hNr : (0 : ℝ) < 2 * N := by positivity
  have hmq : (m : ℝ) / (2 * N) ≤ ((q - a : ℤ) : ℝ) := by
    rw [div_le_iff₀ hNr]
    have : (m : ℝ) ≤ 2 * N * ((q - a : ℤ) : ℝ) := by exact_mod_cast h2
    linarith
  calc c₁ / (2 * N) ^ d * (m : ℝ) ^ d = c₁ * ((m : ℝ) / (2 * N)) ^ d := by rw [div_pow]; ring
    _ ≤ c₁ * ((q - a : ℤ) : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg hm0 hNr.le) hmq d) hc₁.le
    _ < (((q - a) • G).h0 k sX : ℝ) := hgrow
    _ ≤ ((m • D).h0 k sX : ℝ) := by exact_mod_cast hh0

end Big

end MMP.FourfoldProofs.Km2cNefBigOfAmpleApproximationProof

section

/-!
# Divisors approximated by ample `ℚ`-divisors are nef and big

Let `X` be a normal projective variety over a field `k`, `D` a Cartier divisor, `E` an effective
`ℚ`-Cartier `ℚ`-divisor and `Aₙ` ample `ℚ`-divisors with `D ≡ Aₙ + (1/n) E` for infinitely many
`n`. Then `D` is nef and big.

## Main results

* `MMP.Mori.Divisor.isNef_and_isBig_of_numericallyEquivalent_isAmple_add_smul`: the statement
  above.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Prop. 2.61,
  (3) ⇒ (1)
-/

public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori.Divisor

open MMP.FourfoldProofs.Km2cNefBigOfAmpleApproximationProof in
/-- **Kollár–Mori 2.61 (3) ⇒ (1).** Let `X` be a normal projective variety over a field `k`, `D`
a Cartier divisor, `E` an effective `ℚ`-Cartier `ℚ`-divisor and `A n` ample `ℚ`-divisors with
`D ≡ A n + (1/n) E` for infinitely many `n`. Then `D` is nef (`Divisor.IsNef`) and big
(`Divisor.IsBig`). -/
@[mmp "lem_km2c_nef_big_of_ample_approximation"]
public theorem isNef_and_isBig_of_numericallyEquivalent_isAmple_add_smul {k : Type} [Field k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] (D : Divisor X) (hD : D.IsCartier) (E : QDivisor X)
    (hE : 0 ≤ E) (hEQ : E.IsQCartier) (A : ℕ → QDivisor X)
    (hA : {n : ℕ | (A n).IsAmple ∧
      (Divisor.toQDivisor D).NumericallyEquivalent k sX (A n + (n : ℚ)⁻¹ • E)}.Infinite) :
    D.IsNef k sX ∧ D.IsBig k sX := by
  obtain ⟨e, he, F, hFE, hF⟩ := hEQ.exists_pos
  have hnef := isNef_of_ample_approximation sX D hD E F hF he hFE A hA
  refine ⟨hnef, ?_⟩
  obtain ⟨n, ⟨hAn, hnum⟩, hn0⟩ := hA.exists_gt 0
  -- `F = eE ≥ 0`
  have hF0 : 0 ≤ F := fun P => by
    have h1 : (F P : ℚ) = (e : ℤ) • E P := congrArg (fun Q => Q P) hFE
    have : (0 : ℚ) ≤ F P := by
      rw [h1, zsmul_eq_mul]
      exact mul_nonneg (by positivity) (hE P)
    exact_mod_cast this
  -- `G = (en) D - F` is ample, and so is `G + D`
  have hG : (((e * n : ℕ) : ℤ) • D - F).IsCartier := by
    rw [sub_eq_add_neg]
    exact (hD.zsmul _).add hF.neg
  have hGa := isAmple_nsmul_sub sX hD hF he hn0 hFE hAn hnum hG
  exact isBig_of_nsmul_eq_add sX D hD _ F hG hF hF0 (Nat.mul_pos he hn0) (sub_add_cancel _ _).symm
    hGa (isAmple_add_of_isNef sX hG hD hGa hnef)

end MMP.Mori.Divisor

end
