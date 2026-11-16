module

public import MMP.AlgebraicGeometry.Positivity.FinitePullbackNefBig
public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegNefBig
public import MMP.AlgebraicGeometry.Positivity.NefBigOfAmpleApproximation

/-!
# The Kawamata–Viehweg vanishing theorem

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field `k`
of characteristic zero, and `B` a divisor on `X` which is numerically equivalent to `M + Δ`,
where `M` is a nef and big `ℚ`-divisor and `Δ = ∑ aᵢ Dᵢ` is a `ℚ`-divisor with simple normal
crossing support and coefficients `0 ≤ aᵢ < 1`. Then `H^i(X, 𝒪_X(-B)) = 0` for every `i < n`.

## Main results

* `MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg`: the Kawamata–Viehweg
  vanishing theorem.

## Implementation notes

The boundary `∑ aᵢ Dᵢ` with distinct prime divisors `Dᵢ` is a single `ℚ`-divisor `Δ`, and the
source's condition that `∑ Dᵢ` be snc is `MMP.Mori.DivisorWithCoeffs.IsSNC` of `Δ`, which asks
it of the components with nonzero coefficient; the two agree, since being snc passes to
subsets of the components (`MMP.Mori.DivisorWithCoeffs.IsSNC.of_support_subset`).

`H^i(X, ℱ)` for `i : ℤ` is `Stacks.Duality.derivedCohomologyOverField` of `ℱ` placed in degree
zero; it is sheaf cohomology in degrees `i ≥ 0` and vanishes in negative degrees, so the
conclusion is stated for every integer `i < n`. The sheaf `𝒪_X(-B)` is the divisorial sheaf of
`-B`, invertible since `X` is smooth.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Thm. 2.64
* [Y. Kawamata, *A generalization of Kodaira–Ramanujam's vanishing theorem*][Kaw82]
* [E. Viehweg, *Vanishing theorems*][Vie82]
-/

@[expose] public section

section

/-!
## Proof: Proof of the Kawamata–Viehweg vanishing theorem

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field of
characteristic zero and `B ≡ M + Δ` with `M` nef and big and `Δ` an snc `ℚ`-divisor with
coefficients in `[0, 1)`. The covering trick
(`MMP.Mori.exists_isFinite_retract_cohomologyOverField_divisorialSheaf_neg`) gives a finite
surjective `p : Z ⟶ X` from a smooth projective variety and a divisor `B_Z ≡ p^*M` with
`H^i(X, 𝒪_X(-B))` a retract of `H^i(Z, 𝒪_Z(-B_Z))`. The pull-back `p^*M` is nef and big, hence
so is `B_Z`; vanishing for nef and big divisors and Serre duality give `H^i(Z, 𝒪_Z(-B_Z)) = 0`
for `i < n`, and so `H^i(X, 𝒪_X(-B)) = 0`.

## Implementation notes

That `B_Z` is nef and big is proved through Kodaira's lemma rather than through top
self-intersection numbers: a positive multiple `D = m p^*M` is a nef and big Cartier divisor, so
`D ≡ Aₙ + (1/n) E` with `Aₙ` ample and `E ≥ 0` for all large `n`. Then
`B_Z ≡ (1/m) Aₙ + (1/n)((1/m) E)` with `(1/m) Aₙ` ample, and this approximation characterises nef
and big divisors (Kollár–Mori 2.61, (1) ⇔ (3)).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Thm. 2.64,
  Prop. 2.61
-/

namespace MMP.FourfoldProofs.Km2cKawamataViehwegProof

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped Stacks.SmallDerivedModel

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- **Serre duality for divisors on a smooth projective variety.** For a divisor `D` on a smooth
projective variety `X` of dimension `n`, `H^i(X, 𝒪_X(-D)) = 0` if and only if
`H^{n-i}(X, ω_X ⊗ 𝒪_X(D)) = 0`. -/
private theorem subsingleton_divisorialSheaf_neg_iff [MMP.Mori.IsProjectiveVariety k f]
    (hsm : IsSmoothScheme f) [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : Divisor X) (i : ℤ) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj (-D).divisorialSheaf) i) ↔
      Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} X.toRingedSpace.sheaf).obj
            (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).obj
              D.divisorialSheaf)) (n - i)) := by
  have hD := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D
  haveI := hD.isInvertibleModule_divisorialSheaf
  letI : HasDerivedCategory (ModuleCat.{0} k) := ModuleCat.hasDerivedCategory
  -- `𝒪_X(-D) ≅ 𝒪_X(D)^∨`, since `𝒪_X(D) ⊗ 𝒪_X(-D) ≅ 𝒪_X(D - D) = 𝒪_X`.
  let e : (-D).divisorialSheaf ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf D.divisorialSheaf :=
    Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.sheaf.obj
      X.ringCatSheaf.property D.divisorialSheaf (-D).divisorialSheaf
      (hD.divisorialSheafTensorIso (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) ≪≫
        eqToIso (congrArg Divisor.divisorialSheaf (add_neg_cancel D)) ≪≫
        Divisor.divisorialSheafZeroIso)
  rw [← subsingleton_dual_iff_subsingleton_exteriorPower_tensor f hsm n hn]
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).mapIso
    ((derivedGlobalSectionsOver f).mapIso ((DerivedCategory.singleFunctor X.Modules 0).mapIso
      e))).toLinearEquiv.toEquiv.subsingleton_congr

/-- `H^m(X, ℱ) = 0` in negative degrees `m < 0`. -/
private theorem subsingleton_derivedCohomologyOverField_of_neg (F : X.Modules) {m : ℤ}
    (hm : m < 0) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) := by
  letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
  letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  haveI := DerivedCategory.TStructure.t.isGE_shift
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0 m (-m) (by omega)
  haveI : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X))
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) :=
    ⟨fun a b => by
      rw [DerivedCategory.TStructure.t.zero a 0 (-m) (by omega),
        DerivedCategory.TStructure.t.zero b 0 (-m) (by omega)]⟩
  exact (Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) m).some.toEquiv.subsingleton

/-- On a smooth `k`-scheme, numerical equivalence of `ℚ`-divisors is preserved by rational
multiples. -/
private theorem numericallyEquivalent_smul [QuasiCompact f] [IsLocallyNoetherian X]
    [IsNormal X] (hsm : IsSmoothScheme f) {D₁ D₂ : QDivisor X}
    (h : D₁.NumericallyEquivalent k f D₂) (q : ℚ) :
    (q • D₁).NumericallyEquivalent k f (q • D₂) := by
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  refine ⟨hq _, hq _, fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_smul k f i hC.le q D₁ (hq _) (hq _),
    QDivisor.intersectionNumber_smul k f i hC.le q D₂ (hq _) (hq _),
    h.intersectionNumber_eq (hq _) (hq _) i hC]

/-- **Nefness and bigness are numerical** (Kollár–Mori 2.61). On a smooth projective variety, a
divisor `B` numerically equivalent to a nef and big `ℚ`-divisor `M` is nef and big. -/
private theorem isNef_and_isBig_of_numericallyEquivalent [MMP.Mori.IsProjectiveVariety k f]
    [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] (hsm : IsSmoothScheme f)
    {B : Divisor X} {M : QDivisor X} (hnef : M.IsNef k f) (hbig : M.IsBig k f)
    (h : (Divisor.toQDivisor B).NumericallyEquivalent k f M) :
    B.IsNef k f ∧ B.IsBig k f := by
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  have hc := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  obtain ⟨m, hm, D, hD, -, hDbig⟩ := hbig
  have hm' : (m : ℚ) ≠ 0 := by positivity
  -- `D = m M` is nef
  have hDnef : D.IsNef k f := by
    refine (QDivisor.isNef_toQDivisor_iff D (hc D)).1 (hD ▸ ⟨hq _, fun C i _ _ _ hC => ?_⟩)
    rw [QDivisor.intersectionNumber_smul k f i hC.le _ M (hq _) (hq _)]
    exact mul_nonneg (by positivity) ((QDivisor.isNef_iff M (hq M)).1 hnef C i hC)
  -- Kodaira's lemma: `D ≡ Aₙ + (1/n) E` with `Aₙ` ample and `E ≥ 0`, for `n ≥ k₀`
  obtain ⟨E, k₀, A, hE0, -, -, hA⟩ := exists_numericallyEquivalent_isAmple_add_smul f D hDnef hDbig
  have hMD : M = (m : ℚ)⁻¹ • Divisor.toQDivisor D := by
    rw [hD, smul_smul, inv_mul_cancel₀ hm', one_smul]
  refine Divisor.isNef_and_isBig_of_numericallyEquivalent_isAmple_add_smul f B (hc B)
    ((m : ℚ)⁻¹ • Divisor.toQDivisor E) ?_ (hq _) (fun n => (m : ℚ)⁻¹ • A n)
    ((Set.Ici_infinite k₀).mono fun n hn => ⟨?_, ?_⟩)
  · refine Finsupp.le_def.2 fun P => ?_
    change (0 : ℚ) ≤ (m : ℚ)⁻¹ * (E P : ℚ)
    exact mul_nonneg (by positivity) (by exact_mod_cast Finsupp.le_def.1 hE0 P)
  · obtain ⟨c, hc0, D', hD', hD'c, hamp⟩ := (hA n hn).1
    refine ⟨c * m, Nat.mul_pos hc0 hm, D', ?_, hD'c, hamp⟩
    rw [hD', smul_smul]
    congr 1
    push_cast
    field_simp
  · have h' := h.trans (hMD ▸ numericallyEquivalent_smul f hsm (hA n hn).2 (m : ℚ)⁻¹)
    convert h' using 1
    module

end MMP.FourfoldProofs.Km2cKawamataViehwegProof

end

section

public section

open CategoryTheory AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

/-- **Kawamata–Viehweg vanishing** (Kollár–Mori, Theorem 2.64). Let `X` be a smooth projective
variety of dimension `n` over an algebraically closed field `k` of characteristic zero and `B` a
divisor on `X` numerically equivalent to `M + Δ`, where `M` is a nef and big `ℚ`-divisor and `Δ`
is a `ℚ`-divisor with simple normal crossing support whose coefficients lie in `[0, 1)`. Then
`H^i(X, 𝒪_X(-B)) = 0` for every `i < n`. -/
@[mmp "thm_km2c_kawamata_viehweg"]
public theorem subsingleton_derivedCohomologyOverField_divisorialSheaf_neg {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] (hsm : IsSmoothScheme f) [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} (hn : topologicalKrullDim X = n) (B : Divisor X) (M Δ : QDivisor X)
    (hMnef : M.IsNef k f) (hMbig : M.IsBig k f) (hΔ : Δ.IsSNC f)
    (hΔ0 : ∀ E, 0 ≤ Δ E) (hΔ1 : ∀ E, Δ E < 1)
    (hB : (Divisor.toQDivisor B).NumericallyEquivalent k f (M + Δ)) (i : ℤ) (hi : i < n) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj (-B).divisorialSheaf) i) := by
  rcases lt_or_ge i 0 with hi0 | hi0
  · exact MMP.FourfoldProofs.Km2cKawamataViehwegProof.subsingleton_derivedCohomologyOverField_of_neg f _
      hi0
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) := ⟨i.toNat, by omega⟩
  haveI : Smooth f := (isSmoothScheme_iff f).1 hsm
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨Z, p, _, _, hZp, hZs, _, _, BZ, MZ, hM, hpM, hBZ, hret⟩ :=
    exists_isFinite_retract_cohomologyOverField_divisorialSheaf_neg k f B M Δ hΔ
      (fun P => ⟨hΔ0 P, hΔ1 P⟩) hB
  haveI : MMP.Mori.IsProjectiveVariety k (p ≫ f) := hZp
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (p ≫ f)
  have hsmZ : IsSmoothScheme (p ≫ f) := (isSmoothScheme_iff _).2 hZs
  have hnZ : topologicalKrullDim Z = n :=
    (topologicalKrullDim_eq_of_isFinite_of_isDominant p).trans hn
  -- `p^*M` is nef and big, hence so is `B_Z ≡ p^*M`
  obtain ⟨hMZnef, hMZbig⟩ :=
    QDivisor.IsPullback.isNef_and_isBig_of_isFinite f (p ≫ f) p rfl hMnef hMbig hM hpM
  obtain ⟨hBZnef, hBZbig⟩ :=
    MMP.FourfoldProofs.Km2cKawamataViehwegProof.isNef_and_isBig_of_numericallyEquivalent (p ≫ f) hsmZ
      hMZnef hMZbig hBZ
  -- `H^j(Z, 𝒪_Z(-B_Z)) = 0`, by Kawamata–Viehweg for `B_Z` and Serre duality
  haveI := (MMP.FourfoldProofs.Km2cKawamataViehwegProof.subsingleton_divisorialSheaf_neg_iff (p ≫ f) hsmZ
      hnZ BZ j).2 <|
    subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_of_isNef_of_isBig
      (p ≫ f) hsmZ hnZ BZ hBZnef hBZbig _ (by omega)
  haveI := (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k (p ≫ f)
    (-BZ).divisorialSheaf j).toEquiv.subsingleton
  -- and `H^j(X, 𝒪_X(-B))` is a retract of `H^j(Z, 𝒪_Z(-B_Z))`
  obtain ⟨r⟩ := hret j
  haveI := ((ModuleCat.mono_iff_injective r.i).1 inferInstance).subsingleton
  exact (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f
    (-B).divisorialSheaf j).symm.toEquiv.subsingleton

end MMP.Mori

end

end
