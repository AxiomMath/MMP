module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection

@[expose] public section

section

/-!
# The test divisors of the basepoint-free theorem are ample

Let `(f; F_•; a_•; p_•; r_•)` be an `m`-adapted resolution of a basepoint-free datum
`(X, Δ, D, a)` and `b, c ∈ ℚ` with `c ≥ 0` and `b ≥ cm + a`. Then the test divisor
`N(b, c) = b f^*D - K_Y + ∑_j (-c r_j + a_j - p_j) F_j` is ample.

Up to numerical equivalence,
`N(b, c) ≡ (b - cm - a) f^*D + c (m f^*D - ∑_j r_j F_j) + (f^*(aD - K_X - Δ) - ∑_j p_j F_j)`:
the difference is `f^*(K_X + Δ) - K_Y + ∑_j a_j F_j`, which is principal since
`K_Y - ∑_j a_j F_j ∼ f^*(K_X + Δ)` (KM 2.26). The first summand is nef because `f^*D` is, the
second because the effective divisor `f^*(σ)₀ - ∑_j r_j F_j`, linearly equivalent to it, misses
any given point, and the third is ample. Ample plus nef is ample.

## Implementation notes

The base field `k` is arbitrary. Two consequences of `f` being a log resolution replace the
perfectness of `k` used elsewhere for canonical divisors and discrepancies: `f` is an
isomorphism over the generic point of every prime divisor of `X` and over the generic point of
`X`, so these are smooth points of `X` (as `Y` is smooth); hence `K_X = div(ω)` for a rational
top form `ω`, the top forms of `k(X)` form a line, and orders of forms along prime divisors of
`X` and `Y` are computed along a fixed basis. The relation `K_Y - ∑_j a_j F_j ∼ f^*(K_X + Δ)`
is then proved coefficientwise from the definition of the discrepancy and algebraic Hartogs.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.2 Step 3
-/

namespace MMP.FourfoldProofs.Km3aBpfTestDivisorAmpleProof

open CategoryTheory AlgebraicGeometry MMP.Mori

/-! ### Nefness -/

/-- A dominant morphism of integral schemes maps the generic point outside every divisor. -/
private theorem map_componentGenericPoint_notMem_supp {X : Scheme.{0}} [IsIntegral X]
    {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R X) (Z : irreducibleComponents Y) :
    f (componentGenericPoint Y Z) ∉ D.supp := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
  exact MMP.Fourfold.genericPoint_notMem_supp _

section Nef

variable {k : Type} [Field k]

/-- **The image of a curve that is not contracted is a curve.** If `u : V ⟶ W` is a
`k`-morphism and `C ⊆ V` a proper curve whose image is not a point, then the scheme-theoretic
image of `C` is a proper curve over `k`. -/
private theorem isProper_and_isCurve_imageι {V W C : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsSeparated sW] [LocallyOfFiniteType sW] {u : V ⟶ W}
    (hu : u ≫ sW = sV) (i : C ⟶ V)
    [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (hpt : ¬ ∃ w : W, Set.range (i ≫ u) = {w}) :
    IsProper ((i ≫ u).imageι ≫ sW) ∧ AlgebraicGeometry.IsCurve k ((i ≫ u).imageι ≫ sW) := by
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
  exact ⟨isProper_imageι_comp (i ≫ u) sW, isCurve_imageι_comp sW (i ≫ u) hpt⟩

/-- **The pull-back of a nef `ℚ`-divisor is nef.** For a morphism `u : V ⟶ W` of normal varieties
over `k` and a curve `C ⊆ V`, `(u^*L · C)` is `0` if `u(C)` is a point and a nonnegative multiple
of `(L · u(C))` otherwise. -/
private theorem isNef_of_isPullback {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsNef k sW)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV := by
  refine ⟨h.isQCartier hL.1, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · exact (intersectionNumber_pullback_eq_zero k sV sW u hu i hL.1 h hpt).ge
  · obtain ⟨_, hcurve⟩ := isProper_and_isCurve_imageι hu i hpt
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i hL.1 h hcurve]
    exact mul_nonneg (by positivity)
      (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

/-- On a scheme all of whose `ℚ`-divisors are `ℚ`-Cartier (a smooth variety), the intersection
number with a fixed curve `C` is a `ℚ`-linear form `L ↦ (L · C)` on `ℚ`-divisors. -/
private noncomputable def intersectionLinearMap {W C : Scheme.{0}} [IsLocallyNoetherian W]
    [IsNormal W]
    (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] (j : C ⟶ W) [IsProper (j ≫ sW)]
    (hdim : topologicalKrullDim C ≤ 1) (hQ : ∀ L : QDivisor W, L.IsQCartier) :
    QDivisor W →ₗ[ℚ] ℚ where
  toFun L := L.intersectionNumber k sW j hdim (hQ L)
  map_add' L L' := QDivisor.intersectionNumber_add' k sW j hdim L L' (hQ L) (hQ L') (hQ _)
  map_smul' q L := MMP.Fourfold.intersectionNumber_smul sW j hdim L (hQ L) q (hQ _)

private theorem intersectionLinearMap_apply {W C : Scheme.{0}} [IsLocallyNoetherian W]
    [IsNormal W] (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] (j : C ⟶ W) [IsProper (j ≫ sW)]
    (hdim : topologicalKrullDim C ≤ 1) (hQ : ∀ L : QDivisor W, L.IsQCartier) (L : QDivisor W)
    (hL : L.IsQCartier) :
    intersectionLinearMap sW j hdim hQ L = L.intersectionNumber k sW j hdim hL := rfl

/-- **Linearity of the intersection number.** `((a • L₂ - L₃) · C) = a (L₂ · C) - (L₃ · C)`. -/
private theorem intersectionNumber_smul_sub {W C : Scheme.{0}} [IsLocallyNoetherian W]
    [IsNormal W] (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] (j : C ⟶ W) [IsProper (j ≫ sW)]
    (hdim : topologicalKrullDim C ≤ 1) {L₂ L₃ : QDivisor W} (h₂ : L₂.IsQCartier)
    (h₃ : L₃.IsQCartier) (a : ℚ) (h₁ : (a • L₂ - L₃).IsQCartier) :
    (a • L₂ - L₃).intersectionNumber k sW j hdim h₁ =
      a * L₂.intersectionNumber k sW j hdim h₂ - L₃.intersectionNumber k sW j hdim h₃ := by
  have ha := MMP.Flips.QDivisor.IsQCartier.qsmul h₂ a
  have hm := MMP.Flips.QDivisor.IsQCartier.qsmul h₃ (-1)
  rw [MMP.Fourfold.intersectionNumber_congr sW j hdim h₁ (ha.add hm)
      (by rw [neg_one_smul, sub_eq_add_neg]),
    QDivisor.intersectionNumber_add' k sW j hdim _ _ ha hm,
    MMP.Fourfold.intersectionNumber_smul sW j hdim L₂ h₂ a ha,
    MMP.Fourfold.intersectionNumber_smul sW j hdim L₃ h₃ (-1) hm]
  ring

/-- **The projection formula is linear in the divisor.** If `L₁ = a L₂ - L₃` on `W` and `L_i'` are
the pull-backs along `u : V ⟶ W`, then `(L₁' · C) = a (L₂' · C) - (L₃' · C)` for every curve
`C ⊆ V`: both sides vanish if `u(C)` is a point, and otherwise are `deg(C → u(C))` times the same
combination of intersection numbers with `u(C)`. -/
private theorem intersectionNumber_isPullback_smul_sub {V W C : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) (i : C ⟶ V)
    [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)] {L₂ L₃ : QDivisor W}
    (h₂ : L₂.IsQCartier) (h₃ : L₃.IsQCartier) (a : ℚ) {L₁ : QDivisor W}
    (hL : L₁ = a • L₂ - L₃) (h₁ : L₁.IsQCartier)
    {hB₁ : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L₂.supp}
    {hB₃ : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L₃.supp}
    {L₁' L₂' L₃' : QDivisor V} (p₁ : L₁.IsPullback u hB₁ L₁')
    (p₂ : L₂.IsPullback u hB₂ L₂') (p₃ : L₃.IsPullback u hB₃ L₃') :
    L₁'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
        (p₁.isQCartier h₁) =
      a * L₂'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
          (p₂.isQCartier h₂) -
        L₃'.intersectionNumber k sV i (IsCurve.topologicalKrullDim_eq_one (f := i ≫ sV)).le
          (p₃.isQCartier h₃) := by
  subst hL
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · rw [intersectionNumber_pullback_eq_zero k sV sW u hu i h₁ p₁ hpt,
      intersectionNumber_pullback_eq_zero k sV sW u hu i h₂ p₂ hpt,
      intersectionNumber_pullback_eq_zero k sV sW u hu i h₃ p₃ hpt]
    ring
  · obtain ⟨_, hcurve⟩ := isProper_and_isCurve_imageι hu i hpt
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i h₁ p₁ hcurve,
      intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i h₂ p₂ hcurve,
      intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i h₃ p₃ hcurve,
      intersectionNumber_smul_sub sW _ _ h₂ h₃ a h₁]
    ring

/-- **A basepoint-free part is nef** (KM 3.2, Step 3). Let `f : Y ⟶ X` be a dominant morphism
of Noetherian normal integral schemes, every divisor on `Y` Cartier, `M` a Cartier divisor on `X`
with pull-back `M'`, and `R₀` a divisor on `Y` with `f^*(σ)₀ ≥ R₀` for every nonzero section `σ`
of `𝒪_X(M)`, every point of `Y` lying outside `Supp(f^*(σ)₀ - R₀)` for some `σ`. Then
`M' - R₀` is nef: on a curve `C ∋ y`, the effective divisor `f^*(σ)₀ - R₀ ∼ M' - R₀` does not
contain `C`. -/
private theorem isNef_sub_of_forall_exists_notMem_supp {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] {f : Y ⟶ X}
    [IsDominant f] (hcart : ∀ D : Divisor Y, D.IsCartier) {M : Divisor X} (hM : M.IsCartier)
    {hMB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ M.supp}
    {M' : Divisor Y} (hM' : M.IsPullback f hMB M') (R₀ : Divisor Y)
    (hle : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0),
      ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
          (M.zeroDivisor σ hσ).supp) (Z' : Divisor Y),
        (M.zeroDivisor σ hσ).IsPullback f hB Z' ∧ R₀ ≤ Z')
    (hex : ∀ y : Y, ∃ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0)
      (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
          (M.zeroDivisor σ hσ).supp) (Z' : Divisor Y),
        (M.zeroDivisor σ hσ).IsPullback f hB Z' ∧ y ∉ ((Z' - R₀).supp : Set Y)) :
    (Divisor.toQDivisor (M' - R₀)).IsNef k sY := by
  rw [QDivisor.isNef_toQDivisor_iff _ (hcart _)]
  refine ⟨hcart _, fun C i _ _ _ hC => ?_⟩
  obtain ⟨c⟩ : Nonempty C := inferInstance
  obtain ⟨σ, hσ, hB, Z', hZ', hy⟩ := hex (i c)
  obtain ⟨hB', Z'', hZ'', hR⟩ := hle σ hσ
  have hZc : (M.zeroDivisor σ hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hM
  have hZZ : Z' = Z'' := hZ'.eq hZc hZ''
  subst hZZ
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hφB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (principalDivisor φ).supp :=
    map_componentGenericPoint_notMem_supp f _
  have hsum := (Divisor.isPullback_principalDivisor (f := f) φ hφB).add
    (Divisor.isCartier_principalDivisor φ) hM hB hM'
  have hZ2 : Z' = principalDivisor (pullbackRationalFunction f φ hφB) + M' :=
    hZ'.eq hZc (hsum.of_eq (Divisor.zeroDivisor_eq M σ hσ).symm)
  have heff : 0 ≤ Z' - R₀ := sub_nonneg.mpr hR
  have h0 := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sY i hC.le (Z' - R₀)
    (hcart _) heff ⟨c, hy⟩).1
  have hsplit : Z' - R₀ = principalDivisor (pullbackRationalFunction f φ hφB) + (M' - R₀) := by
    rw [hZ2]
    abel
  rwa [Divisor.degreeOn_congr hsplit (hcart _) ((hcart _).add (hcart _)),
    Divisor.degreeOn_add k sY i hC.le _ _ (hcart _) (hcart _),
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sY i hC.le (hcart _)
      (Divisor.linearlyEquivalent_principalDivisor_zero _), zero_add] at h0

end Nef

/-! ### Orders of forms along prime divisors with smooth generic point -/

section Forms

/-- **Cartier's equality for a formally smooth field.** For a field `K` essentially of finite
type and formally smooth over `k`, `H₁(L_{K/k}) = 0`, so `dim_K Ω_{K/k} = trdeg_k K`. -/
private theorem finrank_kaehlerDifferential_eq_trdeg_of_formallySmooth (k K : Type*) [Field k]
    [Field K] [Algebra k K] [Algebra.EssFiniteType k K] [Algebra.FormallySmooth k K] :
    Module.finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat := by
  have h := (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k K).2.2
  rw [Module.finrank_zero_of_subsingleton (M := Algebra.H1Cotangent k K), Nat.cast_zero,
    sub_zero] at h
  exact_mod_cast h.symm

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- The local ring along a prime divisor of a scheme locally of finite type over `k` is
essentially of finite type over `k`. -/
private theorem essFiniteType_localRing [IsLocallyNoetherian X] [LocallyOfFiniteType sX]
    (Γ : MMP.Mori.PrimeDivisor X) :
    letI := stalkAlgebra sX Γ.genericPoint
    Algebra.EssFiniteType k Γ.localRing := by
  let := stalkAlgebra sX Γ.genericPoint
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ Γ.genericPoint) isOpen_univ
  have hU' : IsAffineOpen U := hU
  let x : U := ⟨Γ.genericPoint, hxU⟩
  let := sectionAlgebra sX U
  have := finiteType_sectionAlgebra sX hU'
  let : Algebra Γ(X, U) Γ.localRing := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have := isScalarTower_section_stalk sX U x
  have := hU'.isLocalization_stalk x
  set q := (hU'.primeIdealOf x).asIdeal
  have : Algebra.EssFiniteType Γ(X, U) Γ.localRing := .of_isLocalization _ q.primeCompl
  exact .comp k Γ(X, U) Γ.localRing

/-- **Generators of the top forms at a smooth prime divisor.** If the generic point of a prime
divisor `Γ` of a normal integral scheme `X` locally of finite type over `k` is a smooth point,
and `d = trdeg_k k(X)`, then `Ω^d_{𝒪_{X,Γ}/k}` has a generator with nonzero image in
`Ω^d_{k(X)/k}`. -/
private theorem exists_topForms_generator_of_mem_smoothLocus [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : Γ.genericPoint ∈ smoothLocus sX) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) :
    letI := stalkAlgebra sX Γ.genericPoint
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
    ∃ σ : ⋀[Γ.localRing]^d Ω[Γ.localRing⁄k], Submodule.span Γ.localRing {σ} = ⊤ ∧
      topFormsMap k Γ.localRing X.functionField d σ ≠ 0 := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have := (MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus_iff Γ).mp hΓ
  have := essFiniteType_localRing (sX := sX) Γ
  have := Γ.isDiscreteValuationRing_localRing
  have : Module.Free Γ.localRing Ω[Γ.localRing⁄k] := Module.free_of_flat_of_isLocalRing
  have : Algebra.FormallySmooth Γ.localRing X.functionField :=
    .of_isLocalization (nonZeroDivisors Γ.localRing)
  have : Algebra.FormallySmooth k X.functionField := .comp k Γ.localRing X.functionField
  have := essFiniteType_functionField (sX := sX)
  have hK := hd ▸ finrank_kaehlerDifferential_eq_trdeg_of_formallySmooth k X.functionField
  have : Module.Finite Γ.localRing Ω[Γ.localRing⁄k] := inferInstance
  exact exists_topForms_generator_of_free
    ((finrank_kaehlerDifferential_eq_of_isFractionRing (K := X.functionField)).symm.trans hK)

/-- **The order of a form along a basis at a smooth prime divisor**: for a basis `b` of
`Ω^d_{k(X)/k}` there is an integer `N` with `ord_Γ(τ) = v_Γ(τ / b^{⊗m}) + m · N` for every `m`
and every nonzero rational `m`-canonical form `τ`. -/
private theorem exists_ordForm_eq_ord_add_mul_of_mem_smoothLocus [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : Γ.genericPoint ∈ smoothLocus sX) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k])) :
    letI := functionFieldAlgebra sX
    ∃ N : ℤ, ∀ (m : ℤ) (τ : RationalPluriForms sX d m), τ ≠ 0 →
      Γ.ordForm τ = X.ord ((ZTensorPower.basis b m).repr τ ()) Γ.genericPoint + m * N := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  exact exists_ordAt_eq_add_mul (k := k) Γ.ord_mul_of_ne_zero
    (fun _ ha => Γ.ord_algebraMap_of_isUnit ha)
    (exists_topForms_generator_of_mem_smoothLocus Γ hΓ hd)
    b

/-- **Smoothness is transported by an isomorphism of local rings.** If `f : Y ⟶ X` is a
`k`-morphism inducing an isomorphism `𝒪_{X,f(y)} ≅ 𝒪_{Y,y}` and `Y` is smooth over `k` at `y`,
then `X` is smooth over `k` at `f(y)`. -/
private theorem map_mem_smoothLocus_of_isIso_stalkMap [LocallyOfFiniteType sX] {Y : Scheme.{0}}
    (f : Y ⟶ X) [LocallyOfFiniteType (f ≫ sX)] {y : Y} (hy : y ∈ smoothLocus (f ≫ sX))
    [IsIso (f.stalkMap y)] : f y ∈ smoothLocus sX := by
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [smoothLocus_eq_smoothLocus, Scheme.Hom.mem_smoothLocus] at hy ⊢
  rw [Scheme.Hom.stalkMap_comp] at hy
  exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).mp hy

/-- **A smooth resolution is an isomorphism in codimension one, so the base is smooth in
codimension one.** If `f : Y ⟶ X` is a proper birational morphism of normal varieties with `Y`
smooth, the generic point of every prime divisor of `X` is a smooth point: it is the image of the
generic point of its strict transform, with isomorphic local rings. -/
private theorem genericPoint_mem_smoothLocus_of_isSmoothScheme [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsProper f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (hsm : IsSmoothScheme (f ≫ sX)) (Γ : MMP.Mori.PrimeDivisor X) :
    Γ.genericPoint ∈ smoothLocus sX := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  obtain ⟨E, hE, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hY hf Γ
  have hmem : E.genericPoint ∈ smoothLocus (f ≫ sX) := hsm.symm ▸ trivial
  rw [← hE]
  exact map_mem_smoothLocus_of_isIso_stalkMap f hmem

/-- **Smoothness at a point.** For `X` locally of finite type over `k`, a point `x` is a smooth
point exactly when `𝒪_{X,x}` is formally smooth over `k`. -/
private theorem mem_smoothLocus_iff_formallySmooth [LocallyOfFiniteType sX] (x : X) :
    x ∈ smoothLocus sX ↔
      letI := stalkAlgebra sX x
      Algebra.FormallySmooth k (X.presheaf.stalk x) := by
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [smoothLocus_eq_smoothLocus, Scheme.Hom.mem_smoothLocus]
  let g : CommRingCat.of k ⟶ (Spec (.of k)).presheaf.stalk (sX x) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _)
  have hiso : IsIso g := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨RingHom.injective _, MMP.Positivity.surjective_algebraMap_stalk_Spec _⟩
  have hcomp : g ≫ sX.stalkMap x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) := by
    erw [Category.assoc, Scheme.Hom.germ_stalkMap sX ⊤ x (TopologicalSpace.Opens.mem_top _)]
    rfl
  rw [← RingHom.FormallySmooth.respectsIso.cancel_left_isIso g, ← CommRingCat.hom_comp, hcomp]
  rfl

/-- **Pull-back generators along a birational morphism, at a smooth generic point.** If `X` is
integral, locally of finite type over `k` with smooth generic point, `trdeg_k k(X) = d`, and
`f^* : k(X) → k(Y)` is bijective, then `Ω^d_{k(X)/k}` has a generator whose pull-back generates
`Ω^d_{k(Y)/k}`. -/
private theorem exists_isPullbackGenerator_of_genericPoint_mem_smoothLocus [IsIntegral X]
    [LocallyOfFiniteType sX] (hη : genericPoint X ∈ smoothLocus sX) {Y : Scheme.{0}}
    [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    letI := functionFieldMapAlgebra f
    haveI := isScalarTower_functionFieldMap sX f
    ∃ ω : ⋀[X.functionField]^d Ω[X.functionField⁄k], IsPullbackGenerator Y.functionField ω := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have : Algebra.FormallyEtale X.functionField Y.functionField :=
    Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId X.functionField Y.functionField) hf)
  have := essFiniteType_functionField (sX := sX)
  have : Algebra.FormallySmooth k X.functionField := (mem_smoothLocus_iff_formallySmooth _).mp hη
  have : FiniteDimensional X.functionField Ω[X.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k X.functionField).1
  have hK := hd ▸ finrank_kaehlerDifferential_eq_trdeg_of_formallySmooth k X.functionField
  exact exists_isPullbackGenerator_of_formallyEtale hK

/-- The pull-back of a nonzero rational form along a birational morphism, at a smooth generic
point, is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero [IsIntegral X] [LocallyOfFiniteType sX]
    (hη : genericPoint X ∈ smoothLocus sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {m : ℤ} {τ : RationalPluriForms sX n m}
    (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_genericPoint_mem_smoothLocus hη f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **The order of a pull-back along a basis.** Let `f : Y ⟶ X` be a dominant morphism of
integral schemes over `k` inducing an isomorphism of function fields, `X` of dimension `n` with
smooth generic point, and `E` a prime divisor of the normal scheme `Y` with smooth generic point.
There are a basis `b` of `Ω^n_{k(X)/k}` and an integer `N` with
`ord_E(f^*τ) = v_E(f^*(τ / b^{⊗m})) + m · N` for every `m` and every nonzero `τ`. -/
private theorem exists_ordForm_pullback_eq [IsIntegral X] [LocallyOfFiniteType sX]
    (hη : genericPoint X ∈ smoothLocus sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X)
    [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (E : MMP.Mori.PrimeDivisor Y) (hE : E.genericPoint ∈ smoothLocus (f ≫ sX)) :
    letI := functionFieldAlgebra sX
    ∃ (b : Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]))
      (N : ℤ), ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 →
        pullbackRationalPluriForms sX f τ ≠ 0 ∧
        E.ordForm (pullbackRationalPluriForms sX f τ) =
          Y.ord (functionFieldMap f ((ZTensorPower.basis b m).repr τ ())) E.genericPoint +
            m * N := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_genericPoint_mem_smoothLocus hη f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hdY : (Algebra.trdeg k Y.functionField).toNat = n := by
    rwa [← trdeg_functionField_eq_of_bijective sX f hf]
  obtain ⟨N, hN⟩ := exists_ordForm_eq_ord_add_mul_of_mem_smoothLocus (sX := f ≫ sX) E hE hdY
    (basisOfSpanSingleton hω.2.1 hω.2.2)
  refine ⟨basisOfSpanSingleton hω.1 hω.ne_zero, N, fun m τ hτ => ?_⟩
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  have hne := pullbackRationalPluriForms_ne_zero hη hn f hf hτ
  refine ⟨hne, ?_⟩
  rw [hN m _ hne, hpull, hrepr]
  rfl

/-- **The discrepancy computes the pull-back of `K + Δ`** (KM 2.26, coefficientwise). Let
`f : Y ⟶ X` be a birational morphism of normal varieties, `X` smooth in codimension one and at
its generic point, `K = div(ω)` a canonical divisor, `F` a prime divisor of `Y` with smooth
generic point and `a = a(F, X, Δ)` its discrepancy. If `E = m'(K + Δ)` is a Cartier divisor with
pull-back `E'`, then `coeff_F(E') = m' (coeff_F(div(f^*ω)) - a)`.

With `τ = c' b^{⊗m}` generating `𝒪_X(m(K + Δ))` near `x = f(η_F)`, `ω = c b` and `φ` a local
equation of `E` at `x`, the rational function `φ^m c'^{m'} c^{-mm'}` has order zero along every
prime divisor through `x`, so is a unit at `x` (algebraic Hartogs) and its pull-back has order
zero along `F`. -/
private theorem coeff_isPullback_of_isDiscrepancy [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (hsmX : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX)
    (hη : genericPoint X ∈ smoothLocus sX) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ) (F : MMP.Mori.PrimeDivisor Y)
    (hF : F.genericPoint ∈ smoothLocus (f ≫ sX)) {a : ℚ}
    (hdisc : IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, F⟩ a) {m' : ℕ} {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m' : ℤ) • (Divisor.toQDivisor K + Δ)) (hEc : E.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ E.supp}
    {E' : Divisor Y} (hE' : E.IsPullback f hB E') :
    (E'.coeff F : ℚ) =
      m' * ((divisorOfForm (pullbackRationalPluriForms sX f ω)).coeff F - a) := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := hdisc
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  let := functionFieldAlgebra sX
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N', hb⟩ := exists_ordForm_pullback_eq hη hn f hf.functionFieldMap_bijective F hF
  obtain ⟨V, hxV, φ, hφ⟩ := hEc (f F.genericPoint)
  have hsub := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set c' := (ZTensorPower.basis b (m : ℤ)).repr τ () with hc'_def
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) with hg_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set G : X.functionField := g ^ (m : ℤ) * c' ^ (m' : ℤ) * c ^ (-((m : ℤ) * m')) with hG_def
  have hG : G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hg) (zpow_ne_zero _ hc')) (zpow_ne_zero _ hc)
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, f F.genericPoint ∈ Γ.support →
      X.ord G Γ.genericPoint = 0 := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := exists_ordForm_eq_ord_add_mul_of_mem_smoothLocus Γ (hsmX Γ) hd b
    have e1 : (Γ.ordForm τ : ℚ) + m * Δ.coeff Γ = 0 := hτ.2 Γ ⟨_, hΓ, hU⟩
    have e2 := hNΓ (m : ℤ) τ hτ.1
    have e3 := hNΓ 1 ω hω0
    have e4 : E.coeff Γ = X.ord g Γ.genericPoint := by
      rw [hφ Γ ⟨_, hΓ, hxV⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
        Subsingleton.elim Γ.component Z0]
    have e5 : (E.coeff Γ : ℚ) = m' * (K.coeff Γ + Δ.coeff Γ) := by
      simpa [zsmul_eq_mul, mul_add] using congrArg (fun D : QDivisor X => D.coeff Γ) hE
    rw [hG_def, Scheme.ord_mul (mul_ne_zero (zpow_ne_zero _ hg) (zpow_ne_zero _ hc'))
      (zpow_ne_zero _ hc), Scheme.ord_mul (zpow_ne_zero _ hg) (zpow_ne_zero _ hc'),
      ord_zpow _ hg, ord_zpow _ hc', ord_zpow _ hc]
    rw [← hωK Γ] at e5
    qify at e2 e3 e4 ⊢
    rw [← hc_def] at e3
    rw [← hc'_def] at e2
    simp only [zpow_one, one_mul] at e3
    rw [e4] at e5
    linear_combination (m : ℚ) * e5 + (m' : ℚ) * e1 - (m' : ℚ) * e2 + ((m : ℚ) * m') * e3
  obtain ⟨u', hu', hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hG hord
  have hY0 : Y.ord (functionFieldMap f G) F.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact F.ord_algebraMap_of_isUnit (hu'.map _)
  have hfg : functionFieldMap f g ≠ 0 := (map_ne_zero _).mpr hg
  have hfc : functionFieldMap f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap f c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hG_def, map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (mul_ne_zero (zpow_ne_zero _ hfg) (zpow_ne_zero _ hfc')) (zpow_ne_zero _ hfc),
    Scheme.ord_mul (zpow_ne_zero _ hfg) (zpow_ne_zero _ hfc'), ord_zpow _ hfg, ord_zpow _ hfc',
    ord_zpow _ hfc] at hY0
  have hcoeff : E'.coeff F = Y.ord (functionFieldMap f g) F.genericPoint :=
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hE' hφ F hxV Z0
  have hτa' : (m : ℚ) * a = F.ordForm (pullbackRationalPluriForms sX f τ) := hτa
  rw [coeff_divisorOfForm, (hb 1 ω hω0).2, ← hc_def]
  rw [(hb (m : ℤ) τ hτ.1).2, ← hc'_def] at hτa'
  rw [hcoeff]
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  apply mul_left_cancel₀ hm0
  qify at hY0
  push_cast at hτa' ⊢
  linear_combination hY0 + (m' : ℚ) * hτa'

/-- **Divisors of top forms are linearly equivalent** on a normal variety smooth in codimension
one: `div(τ) - div(ω) = div(τ / ω)`. -/
private theorem linearlyEquivalent_divisorOfForm [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    (hsm : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ ω : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hω : ω ≠ 0) : Divisor.LinearlyEquivalent (divisorOfForm τ) (divisorOfForm ω) := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  let b := Module.basisUnique Unit
    (MMP.Positivity.finrank_topForms_functionField_eq_one hX hsm hn)
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := exists_ordForm_eq_ord_add_mul_of_mem_smoothLocus Γ (hsm Γ) hd b
  have e1 := hN 1 ω hω
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm,
    coeff_divisorOfForm, e1, e2]
  ring

/-- At the generic point a birational morphism of integral schemes induces an isomorphism of
local rings, so a smooth generic point of the source gives a smooth generic point of the
target. -/
private theorem genericPoint_mem_smoothLocus_of_isBirationalMorphism [IsIntegral X]
    [LocallyOfFiniteType sX] {Y : Scheme.{0}} [IsIntegral Y] {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hf : IsBirationalMorphism f)
    (hη : genericPoint Y ∈ smoothLocus (f ≫ sX)) : genericPoint X ∈ smoothLocus sX := by
  have : IsDominant f := hf.isDominant
  have : ValuationRing (X.presheaf.stalk (f (genericPoint Y))) := by
    rw [map_genericPoint_of_isDominant]
    exact (inferInstance : ValuationRing X.functionField)
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
    (genericPoint Y)
  have h := map_mem_smoothLocus_of_isIso_stalkMap f hη
  rwa [map_genericPoint_of_isDominant] at h

/-- **The crepant boundary computes the pull-back** (KM 2.26). For a birational morphism
`f : Y ⟶ X` of normal varieties with `X` smooth in codimension one and at its generic point, `Y`
smooth in codimension one, `K = div(ω)` and `Δ_Y` the crepant boundary of `(X, Δ)` on `Y`,
`div(f^*ω) + Δ_Y = f^*(K + Δ)`. -/
private theorem isPullback_divisorOfForm_add_of_isCrepantBoundary [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    (hsmX : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX)
    (hη : genericPoint X ∈ smoothLocus sX) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (hsmY : ∀ F : MMP.Mori.PrimeDivisor Y, F.genericPoint ∈ smoothLocus (f ≫ sX)) {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ) {ΔY : QDivisor Y}
    (hcrep : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    (hB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor K + Δ).supp) :
    (Divisor.toQDivisor K + Δ).IsPullback f hB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + ΔY) := by
  intro m' hm' E hE hEc
  have hB' : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ E.supp :=
    map_componentGenericPoint_notMem_supp f E
  refine ⟨E.pullback hEc hB', ?_, Divisor.isPullback_pullback hEc _⟩
  ext F
  have h := coeff_isPullback_of_isDiscrepancy hsmX hη hY hf hω0 hωK F (hsmY F) (hcrep F) hE hEc
    (Divisor.isPullback_pullback hEc hB')
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, Int.cast_natCast]
  rw [h]
  ring

end Forms

/-- **`f^*(K_X + Δ) - K_Y + ∑_j a_j F_j` is numerically trivial** (KM 2.26). For an adapted
resolution of a basepoint-free datum, a canonical divisor `K_Y` of `Y` and the pull-backs `D'` of
`D` and `B'` of `aD - K_X - Δ`, the divisor `a D' - B' - K_Y + ∑_j a_j F_j` has degree zero on
every curve of `Y`: writing `K_X = div(ω)`, it is `f^*(K_X + Δ) - div(f^*ω) - ∑_j a_j F_j` (zero
coefficientwise) plus `div(f^*ω) - K_Y` (principal). -/
private theorem intersectionNumber_pullback_sub_canonical_eq_zero {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : Divisor X} {a : ℚ} {m : ℕ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsBasepointFreeAdaptedResolution sX n K Δ D a m f F aj pj rj) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    {hBD : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : Divisor Y} (hD' : D.IsPullback f hBD D')
    {hBB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).supp}
    {B' : QDivisor Y}
    (hB' : (a • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsPullback f hBB B')
    (C : Scheme.{0}) (i : C ⟶ Y) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ f ≫ sX)]
    (hC : topologicalKrullDim C = 1)
    (hE : (a • Divisor.toQDivisor D' - B' - Divisor.toQDivisor KY +
      ∑ j, Finsupp.single (F j) (aj j)).IsQCartier) :
    (a • Divisor.toQDivisor D' - B' - Divisor.toQDivisor KY +
      ∑ j, Finsupp.single (F j) (aj j)).intersectionNumber k (f ≫ sX) i hC.le hE = 0 := by
  obtain ⟨hYn, hcrep⟩ := h.isCrepantBoundary
  have hLR := h.isLogResolution
  have hsm : IsSmoothScheme (f ≫ sX) := hLR.isSmoothScheme
  have : IsProper f := hLR.isProper
  have hfb : IsBirationalMorphism f := hLR.isBirationalMorphism
  have : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  have : IsIntegral Y := hYn.1.toIsIntegral
  have : IsDominant f := hfb.isDominant
  have hX : IsNormalVariety k sX := h.isKltPair.1.1
  have hK : K.IsCanonicalDivisor sX n := h.isKltPair.1.2.1
  have hQ : ∀ L : QDivisor Y, L.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  have hcart : ∀ L : Divisor Y, L.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  have : AlgebraicGeometry.IsCurve k (i ≫ f ≫ sX) := { topologicalKrullDim_eq_one := hC }
  have hsmY : ∀ F : MMP.Mori.PrimeDivisor Y, F.genericPoint ∈ smoothLocus (f ≫ sX) :=
    fun _ => hsm.symm ▸ trivial
  have hsmX := genericPoint_mem_smoothLocus_of_isSmoothScheme hX hYn hfb hsm
  have hη := genericPoint_mem_smoothLocus_of_isBirationalMorphism hfb
    (hsm.symm ▸ trivial : genericPoint Y ∈ smoothLocus (f ≫ sX))
  obtain ⟨ω, hω0, hωK⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hX hsmX hK
  obtain ⟨ωY, hωY0, hωYK⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hYn hsmY hKY
  have hpb := isPullback_divisorOfForm_add_of_isCrepantBoundary hsmX hη hYn hfb hsmY hω0 hωK
    hcrep (map_componentGenericPoint_notMem_supp f _)
  have hne := pullbackRationalPluriForms_ne_zero hη hK.1 f hfb.functionFieldMap_bijective hω0
  obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm hYn hsmY hKY.1 hne hωY0
  have key := intersectionNumber_isPullback_smul_sub (sV := f ≫ sX) (sW := sX) rfl i
    (QDivisor.isQCartier_toQDivisor h.isCartier) h.isQCartier_sub a (by abel)
    h.isKltPair.1.2.2 hpb (QDivisor.isPullback_toQDivisor h.isCartier
      (map_componentGenericPoint_notMem_supp f _) hD') hB'
  set ι := intersectionLinearMap (f ≫ sX) i hC.le hQ with hι
  have key' : ι (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) +
      -∑ j, Finsupp.single (F j) (aj j)) = a * ι (Divisor.toQDivisor D') - ι B' := key
  -- `div(f^*ω) - K_Y` is principal, so has degree zero on `C`
  have h0 :
      ι (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω) - KY)) = 0 := by
    have hKYeq : KY = divisorOfForm ωY := by
      ext G
      exact (hωYK G).symm
    rw [hι, intersectionLinearMap_apply (f ≫ sX) i hC.le hQ _
        (QDivisor.isQCartier_toQDivisor (hcart _)),
      QDivisor.intersectionNumber_toQDivisor k (f ≫ sX) i hC.le _ (hcart _),
      MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent (f ≫ sX) i hC.le (hcart _)
        ⟨φ, by rw [sub_zero, hKYeq, hφ]⟩, Int.cast_zero]
  rw [← intersectionLinearMap_apply (f ≫ sX) i hC.le hQ _ hE, ← hι]
  simp only [map_add, map_sub, map_neg, map_smul, smul_eq_mul] at key' h0 ⊢
  linarith

private theorem isAmple_of_isTieBreakerTestDivisor_aux
    {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ} {m : ℕ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsBasepointFreeAdaptedResolution sX n K Δ D a m f F aj pj rj)
    {KY : Divisor Y} {b c : ℚ} {N : QDivisor Y} (hc : 0 ≤ c) (hb : c * m + a ≤ b)
    (hN : IsTieBreakerTestDivisor sX n D f KY F (fun j ↦ (rj j : ℚ)) aj pj b c N) :
    N.IsAmple := by
  obtain ⟨hKY, hBD, D', hD', hNeq⟩ := hN
  obtain ⟨hYn, -⟩ := h.isCrepantBoundary
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  have : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  have : IsIntegral Y := hYn.1.toIsIntegral
  have : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  have hQ : ∀ L : QDivisor Y, L.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  have hcart : ∀ L : Divisor Y, L.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  obtain ⟨hBB, B', hB'p, hA⟩ := h.isAmple
  -- the pieces of `N`
  set R : Divisor Y := m • D' - ∑ j, Finsupp.single (F j) (rj j : ℤ) with hR_def
  set A : QDivisor Y := B' - ∑ j, Finsupp.single (F j) (pj j) with hA_def
  set Nn : QDivisor Y := (b - c * m - a) • Divisor.toQDivisor D' + c • Divisor.toQDivisor R
    with hNn_def
  set E : QDivisor Y := a • Divisor.toQDivisor D' - B' - Divisor.toQDivisor KY +
    ∑ j, Finsupp.single (F j) (aj j) with hE_def
  have hdecomp : N = (A + Nn) + E := by
    have h1 : (∑ j, Finsupp.single (F j) (-c * (rj j : ℚ) + aj j - pj j) : QDivisor Y) =
        ∑ j, Finsupp.single (F j) (aj j) - ∑ j, Finsupp.single (F j) (pj j) -
          c • ∑ j, Finsupp.single (F j) (rj j : ℚ) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finsupp.smul_single, ← Finsupp.single_sub, ← Finsupp.single_sub, smul_eq_mul]
      congr 1
      ring
    have h2 : Divisor.toQDivisor R =
        (m : ℚ) • Divisor.toQDivisor D' - ∑ j, Finsupp.single (F j) (rj j : ℚ) := by
      rw [hR_def, map_sub, map_nsmul, map_sum, Nat.cast_smul_eq_nsmul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ext G
      classical
      change ((Finsupp.single (F j) (rj j : ℤ) : Divisor Y) G : ℚ) =
        (Finsupp.single (F j) (rj j : ℚ) : QDivisor Y) G
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp
    rw [hNeq, hA_def, hNn_def, hE_def, h2]
    simp only [] at h1 ⊢
    rw [h1]
    module
  -- `f^*D` is nef
  have hDQ : (Divisor.toQDivisor D).IsNef k sX :=
    (QDivisor.isNef_toQDivisor_iff D h.isCartier).mpr h.isNef
  have hD'nef : (Divisor.toQDivisor D').IsNef k (f ≫ sX) :=
    isNef_of_isPullback rfl hDQ (QDivisor.isPullback_toQDivisor h.isCartier
      (map_componentGenericPoint_notMem_supp f _) hD')
  -- `m f^*D - ∑ r_j F_j` is nef
  have hRnef : (Divisor.toQDivisor R).IsNef k (f ≫ sX) := by
    have hp := hD'.zsmul h.isCartier (m : ℤ) (map_componentGenericPoint_notMem_supp f _)
    rw [natCast_zsmul] at hp
    exact isNef_sub_of_forall_exists_notMem_supp hcart (h.isCartier.nsmul m)
      (hp.of_eq (natCast_zsmul D m) (hB₂ := map_componentGenericPoint_notMem_supp f _)) _
      h.le_zeroDivisor h.exists_notMem_supp
  have hNnef : Nn.IsNef k (f ≫ sX) := by
    refine ⟨hQ _, fun C i _ _ _ hC => ?_⟩
    rw [← intersectionLinearMap_apply (f ≫ sX) i hC.le hQ Nn (hQ _), hNn_def, map_add, map_smul,
      map_smul, smul_eq_mul, smul_eq_mul,
      intersectionLinearMap_apply (f ≫ sX) i hC.le hQ _ hD'nef.1,
      intersectionLinearMap_apply (f ≫ sX) i hC.le hQ _ hRnef.1]
    exact add_nonneg (mul_nonneg (by linarith) (hD'nef.2 C i hC)) (mul_nonneg hc (hRnef.2 C i hC))
  have hequiv : N.NumericallyEquivalent k (f ≫ sX) (A + Nn) := by
    refine ⟨hQ _, hQ _, fun C i _ _ _ hC => ?_⟩
    rw [← intersectionLinearMap_apply (f ≫ sX) i hC.le hQ N (hQ _),
      ← intersectionLinearMap_apply (f ≫ sX) i hC.le hQ (A + Nn) (hQ _), hdecomp, map_add,
      intersectionLinearMap_apply (f ≫ sX) i hC.le hQ E (hQ _),
      intersectionNumber_pullback_sub_canonical_eq_zero h hKY hD' hB'p C i hC, add_zero]
  obtain ⟨M, hM, G, hG⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor N
  have hG' : Divisor.toQDivisor G = (M : ℚ) • N := by
    rw [hG, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  exact ⟨M, hM, G, hG', hcart G,
    QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef (f ≫ sX) hA hNnef hequiv M hM G hG'
      (hcart G)⟩

end MMP.FourfoldProofs.Km3aBpfTestDivisorAmpleProof

end

section

/-!
# The test divisors of the basepoint-free theorem are ample

Let `(f; F_•; a_•; p_•; r_•)` be an `m`-adapted resolution of a basepoint-free datum
`(X, Δ, D, a)`. For rationals `b, c` with `c ≥ 0` and `b ≥ cm + a`, the test divisor
`N(b, c) = b f^*D - K_Y + ∑_j (-c r_j + a_j - p_j) F_j` is ample. Indeed, modulo numerical
equivalence `N(b, c)` is the sum of the nef divisor `(b - cm - a) f^*D`, the nef divisor
`c (m f^*D - ∑_j r_j F_j)` and the ample divisor `f^*(aD - K_X - Δ) - ∑_j p_j F_j`.

## Main results

* `MMP.Mori.IsBasepointFreeAdaptedResolution.isAmple_of_isTieBreakerTestDivisor`: `N(b, c)` is
  ample for `c ≥ 0` and `b ≥ cm + a`.

## Implementation notes

The test divisor is the relation `MMP.Mori.IsTieBreakerTestDivisor`: `N` is a test divisor for
some canonical divisor `K_Y` of `Y` and the pull-back of `D`. The statement holds for every
such `N`, whatever canonical divisor `K_Y` is chosen.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, 3.2 Step 3
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **The test divisors are ample** (Kollár–Mori 3.2, Step 3). Let `(f; F_•; a_•; p_•; r_•)` be
an `m`-adapted resolution of a basepoint-free datum `(X, Δ, D, a)`, and `b, c` rationals with
`0 ≤ c` and `c m + a ≤ b`. Then the test divisor
`N(b, c) = b f^*D - K_Y + ∑_j (-c r_j + a_j - p_j) F_j` is ample. -/
@[mmp "lem_km3a_bpf_test_divisor_ample"]
public theorem IsBasepointFreeAdaptedResolution.isAmple_of_isTieBreakerTestDivisor
    {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ} {m : ℕ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsBasepointFreeAdaptedResolution sX n K Δ D a m f F aj pj rj)
    {KY : Divisor Y} {b c : ℚ} {N : QDivisor Y} (hc : 0 ≤ c) (hb : c * m + a ≤ b)
    (hN : IsTieBreakerTestDivisor sX n D f KY F (fun j ↦ (rj j : ℚ)) aj pj b c N) :
    N.IsAmple :=
  MMP.FourfoldProofs.Km3aBpfTestDivisorAmpleProof.isAmple_of_isTieBreakerTestDivisor_aux h hc hb
    hN

end MMP.Mori

end

end
