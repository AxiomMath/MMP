module

public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Big and nef Cartier divisors

Two facts about Cartier divisors on a projective (resp. normal proper) variety `X` over a
field `k`.

*Ample plus effective is big.* Let `D` be a Cartier divisor and `m > 0` an integer with
`mD ∼ A + E`, where `A` is ample and `E` effective. Write `K = qm + r` with `0 ≤ r < m`.
Multiplication by the canonical section `1` of `𝒪_X(qE)`, followed by the linear equivalence
`KD ∼ qA + qE + rD`, gives `h⁰(KD) ≥ h⁰(qA + rD)`. By Serre vanishing for the finitely many
sheaves `𝒪_X(rD)` twisted by `𝒪_X(A)^{⊗ q}`, `h⁰(qA + rD) = χ(qA + rD)` for `q ≫ 0`. The Euler
characteristic `χ(qA + rD)` is a polynomial `P(q, r)` of total degree `≤ n = dim X` whose `qⁿ`
coefficient is `(Aⁿ)/n! > 0` (very weak Riemann–Roch and Nakai–Moishezon), so
`χ(qA + rD) ≥ (Aⁿ)/(2 n!) qⁿ` for `q ≫ 0`; since `q ≥ K/(2m)`, `h⁰(KD)` is bounded below by a
positive multiple of `Kⁿ`, i.e. `D` is big.

*Nefness of Cartier divisors.* For a Cartier divisor `D` on a normal proper variety,
`(D · C) = deg_C 𝒪_X(D)` for every closed curve `C`, so `D` is nef in the sense of degrees if
and only if `D`, viewed as a `ℚ`-divisor, is nef in the sense of intersection numbers.

## Main results

* `MMP.Mori.isBigCartier_of_linearlyEquivalent_add`: `D` is big when `mD ∼ A + E` with `m > 0`,
  `A` ample and `E` effective.
* `MMP.Mori.QDivisor.isNef_toQDivisor_iff'`: the two notions of nefness agree for a Cartier
  divisor on a normal proper variety.

## Implementation notes

The leading coefficient of `P` is read off as the value at `(1, 0)` of its degree-`n`
homogeneous part, which avoids expanding the self-intersection `((qA + rD)ⁿ)` multilinearly.

In `MMP.Mori.QDivisor.isNef_toQDivisor_iff'` the instance arguments `[IsLocallyNoetherian X]`
and `[IsNormal X]` are needed for divisors and nefness to be stated; they follow from
`IsNormalVariety k sX`, which is kept as the source's hypothesis.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4(3)
  and 2.60
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

section BigOfAmplePlusEffective

open MMP.Intersection MMP.CartierDivisor Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A projective variety has finite dimension. -/
private theorem exists_topologicalKrullDim_eq [IsIntegral X] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) : ∃ n : ℕ, topologicalKrullDim X = n := by
  have : AlgebraicGeometry.IsVariety k sX := hX.toIsVariety
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hbot : topologicalKrullDim X ≠ ⊥ := Order.krullDim_ne_bot_iff.mpr inferInstance
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp
    (show e ≠ ⊤ by rintro rfl; exact htop he.symm)
  exact ⟨d, he.symm⟩

/-- An injective `R`-linear map between `R`-modules that are `k`-vector spaces through a ring map
`φ : k →+* R` does not decrease the `k`-dimension. -/
private theorem finrank_compHom_le {R : Type u} [CommRing R] (φ : k →+* R) {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (hg : Function.Injective g) (hN : letI := Module.compHom N φ; FiniteDimensional k N) :
    (letI := Module.compHom M φ; Module.finrank k M) ≤
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M →ₗ[k] N :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact LinearMap.finrank_le_finrank_of_injective (f := g') hg

private theorem finrank_compHom_eq {R : Type u} [CommRing R] (φ : k →+* R) {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M ≃ₗ[R] N) :
    (letI := Module.compHom M φ; Module.finrank k M) =
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M ≃ₗ[k] N :=
    { g.toEquiv with map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact g'.finrank_eq

private theorem scalarsToGlobalSections_eq (sX : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom := by
  have : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]; rfl

/-- `h⁰(D)` is the dimension of `H⁰(X, 𝒪_X(D))`. -/
private theorem cartierH0_eq_finrank (sX : X ⟶ Spec (.of k)) (D : X.CartierDivisor) :
    cartierH0 k sX D = Module.finrank k (cohomologyOverField k sX (sheaf D) 0) := by
  rw [(cohomologyOverFieldZeroLinearIso k sX (sheaf D)).toLinearEquiv.finrank_eq, cartierH0,
    scalarsToGlobalSections_eq]
  rfl

private theorem finiteDimensional_sections (sX : X ⟶ Spec (.of k)) [IsProper sX]
    (D : X.CartierDivisor) :
    letI := Module.compHom Γ(sheaf D, ⊤) (scalarsToGlobalSections k sX)
    FiniteDimensional k Γ(sheaf D, ⊤) := by
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sX
    (sheaf D) 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sX (sheaf D) 0
  have e := (cohomologyOverFieldZeroLinearIso k sX (sheaf D)).toLinearEquiv
  have key : ∀ φ : k →+* Γ(X, ⊤),
      φ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom Γ(sheaf D, ⊤) φ; FiniteDimensional k Γ(sheaf D, ⊤)) := by
    rintro φ rfl
    have := Module.Finite.equiv e
    exact this
  exact key _ (scalarsToGlobalSections_eq sX)

open MMP.CartierDivisorSheaf in
/-- Multiplication by the canonical section `1` of an effective `E`: `h⁰(F) ≤ h⁰(F + E)`. -/
private theorem cartierH0_le_add {sX : X ⟶ Spec (.of k)} [IsProper sX] {F E : X.CartierDivisor}
    (hE : MMP.Intersection.IsEffective E) : cartierH0 k sX F ≤ cartierH0 k sX (F + E) := by
  have hmem : ∀ s : Γ(sheaf F, ⊤), Mem (F + E) ⊤ (MMP.CartierDivisorSheaf.sectionVal s) := fun s =>
      by
    have := MMP.CartierDivisorSheaf.mem_mul (show ↥((sheafSubmodule F).obj (op ⊤)) from s).2
      ((mem_lineBundleSections_iff_mem E ⊤ 1).1 (one_mem_lineBundleSections hE ⊤))
    convert this using 1
    exact (mul_one _).symm
  let g : Γ(sheaf F, ⊤) →ₗ[Γ(X, ⊤)] Γ(sheaf (F + E), ⊤) :=
    { toFun := fun s => (⟨MMP.CartierDivisorSheaf.sectionVal s, hmem s⟩ : ↥((sheafSubmodule (F +
        E)).obj (op ⊤)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact finrank_compHom_le _ g
    (fun _ _ h => MMP.CartierDivisorSheaf.sectionVal_injective (by
      have := congrArg MMP.CartierDivisorSheaf.sectionVal h; exact this))
    (finiteDimensional_sections sX _)

/-- Multiplication by `c⁻¹`: `h⁰(G + div c) = h⁰(G)`. -/
private theorem cartierH0_add_principalDivisor (sX : X ⟶ Spec (.of k)) (G : X.CartierDivisor)
    (c : (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ) :
    cartierH0 k sX (G + MMP.Intersection.principalDivisor c) = cartierH0 k sX G :=
  (finrank_compHom_eq _
    ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso
      (MMP.CartierDivisor.sheafAddPrincipalIso G c)).toLinearEquiv).symm

/-- Multiplying by the canonical section of an effective divisor, followed by a linear
equivalence, gives `h⁰(F) ≤ h⁰(G)` whenever `G ∼ F + E` with `E` effective. -/
private theorem cartierH0_le_of_linearlyEquivalent_add {sX : X ⟶ Spec (.of k)}
    [IsProper sX] {F G E : X.CartierDivisor} (hE : MMP.Intersection.IsEffective E)
    (hG : MMP.Intersection.LinearlyEquivalent G (F + E)) : cartierH0 k sX F ≤ cartierH0 k sX G := by
  obtain ⟨c, hc⟩ := MMP.Intersection.mem_principalSubgroup_iff.1 hG
  have hG' : G = F + E + MMP.Intersection.principalDivisor c := by rw [hc]; abel
  calc cartierH0 k sX F ≤ cartierH0 k sX (F + E) := cartierH0_le_add hE
    _ = cartierH0 k sX G := by rw [hG', cartierH0_add_principalDivisor]

open Stacks.Ample MonoidalCategory in
private theorem nonempty_tensorPow_iso_tensorPowModule (L : X.Modules) [IsInvertibleModule X L]
    (n : ℕ) :
    Nonempty (MMP.Intersection.Scheme.Modules.tensorPow L n ≅ tensorPowModule X L (n : ℤ)) := by
  induction n with
  | zero =>
    exact ⟨(tensorPowModuleZeroIso X L).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    have h1 := tensorPowModuleAddIso X L (n : ℤ) 1
    have h2 := tensorPowModuleOneIso X L
    refine ⟨?_⟩
    refine ?_ ≪≫ (eqToIso (by push_cast; rfl) :
      tensorPowModule X L ((n : ℤ) + 1) ≅ tensorPowModule X L ((n + 1 : ℕ) : ℤ))
    refine (Iso.refl _ : MMP.Intersection.Scheme.Modules.tensorPow L (n + 1) ≅
      MMP.Intersection.Scheme.Modules.tensorPow L n ⊗ L) ≪≫ ?_ ≪≫ h1
    exact (tensorIso e h2.symm : MMP.Intersection.Scheme.Modules.tensorPow L n ⊗ L ≅
      tensorPowModule X L n ⊗ tensorPowModule X L 1)

open Stacks.RelativeVeryAmple (tensorModules tensorModulesMapIso) in
/-- `𝒪_X(qA + rD) ≅ 𝒪_X(rD) ⊗ 𝒪_X(A)^{⊗ q}`. -/
private theorem nonempty_sheaf_iso_tensorModules (A D : X.CartierDivisor) (q : ℕ) (r : ℤ) :
    Nonempty (sheaf ((q : ℤ) • A + r • D) ≅
      tensorModules X (MMP.CartierDivisor.sheaf (r • D)) (Stacks.Ample.tensorPowModule X
          (MMP.CartierDivisor.sheaf A) q)) := by
  obtain ⟨e₁⟩ := MMP.Resolution.Bridges.lineBundle_nsmul_iso_tensorPow A q
  obtain ⟨e₂⟩ := nonempty_tensorPow_iso_tensorPowModule (MMP.CartierDivisor.sheaf A) q
  have e₃ : tensorModules X (MMP.CartierDivisor.sheaf (r • D)) (Stacks.Ample.tensorPowModule X
      (MMP.CartierDivisor.sheaf A) q) ≅
      tensorModules X (MMP.CartierDivisor.sheaf (r • D)) (MMP.CartierDivisor.sheaf (q • A)) :=
    tensorModulesMapIso X (Iso.refl _) (e₁ ≪≫ e₂).symm
  have e₄ : MonoidalCategory.tensorObj (MMP.CartierDivisor.sheaf (r • D))
      (MMP.CartierDivisor.sheaf (q • A)) ≅
      sheaf ((q : ℤ) • A + r • D) :=
    MMP.CartierDivisorSheaf.sheafMulIso (r • D) (q • A) ≪≫ eqToIso (by rw [add_comm, natCast_zsmul])
  exact ⟨(e₃ ≪≫ e₄).symm⟩

/-- Serre vanishing: for `q ≫ 0`, `h⁰(qA + rD) = χ(qA + rD)`. -/
private theorem eventually_cartierH0_eq_eulerChar {sX : X ⟶ Spec (.of k)} [IsProper sX]
    {A : X.CartierDivisor} (hA : Stacks.Ample.IsAmple X (sheaf A)) (D : X.CartierDivisor)
    (r : ℤ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (cartierH0 k sX ((q : ℤ) • A + r • D) : ℤ) =
        MMP.Threefold.Mori.eulerCharCartierCombination k sX ![A, D] ![(q : ℤ), r] := by
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sX
    (MMP.CartierDivisor.sheaf (r • D)) 1
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist sX
      (MMP.CartierDivisor.sheaf (r • D)) _ hA
  refine ⟨d₀, fun q hq => ?_⟩
  obtain ⟨e⟩ := nonempty_sheaf_iso_tensorModules A D q r
  have hvan : ∀ j, 0 < j → Module.finrank k
      (cohomologyOverField k sX (sheaf ((q : ℤ) • A + r • D)) j) = 0 := by
    intro j hj
    have hz := (hd₀ q j hq hj).of_iso ((Hfunctor X.ringCatSheaf ⊤ j).mapIso e)
    haveI : Subsingleton (Hgroup X.ringCatSheaf ⊤ j (sheaf ((q : ℤ) • A + r • D))) :=
      AddCommGrpCat.subsingleton_of_isZero hz
    haveI : Subsingleton (cohomologyOverField k sX (sheaf ((q : ℤ) • A + r • D)) j) :=
      (cohomologyOverFieldAddEquivHgroup k sX _ j).subsingleton_congr.2 inferInstance
    exact Module.finrank_zero_of_subsingleton
  have hsum : ∑ i, ![(q : ℤ), r] i • ![A, D] i = (q : ℤ) • A + r • D := by
    simp [Fin.sum_univ_two]
  rw [MMP.Threefold.Mori.eulerCharCartierCombination, hsum,
    finsum_eq_single _ 0 (fun j hj => by rw [hvan j (Nat.pos_of_ne_zero hj)]; simp),
    cartierH0_eq_finrank]
  simp

open Filter Topology in
/-- A polynomial `P(q, r)` of total degree `≤ n`, divided by `qⁿ`, tends to its `qⁿ`-coefficient as
`q → ∞`, for each fixed `r`. -/
private theorem tendsto_eval_div_pow (P : MvPolynomial (Fin 2) ℚ) {n : ℕ}
    (hP : P.totalDegree ≤ n) (r : ℚ) :
    Tendsto (fun q : ℕ => ((MvPolynomial.eval ![(q : ℚ), r] P : ℚ) : ℝ) / (q : ℝ) ^ n) atTop
      (𝓝 ((P.coeff (Finsupp.single (0 : Fin 2) n) : ℚ) : ℝ)) := by
  classical
  have key : ∀ d ∈ P.support, Tendsto (fun q : ℕ =>
      ((P.coeff d * ((q : ℚ) ^ d 0 * r ^ d 1) : ℚ) : ℝ) / (q : ℝ) ^ n) atTop
        (𝓝 (if d = Finsupp.single 0 n then ((P.coeff d : ℚ) : ℝ) else 0)) := by
    intro d hd
    have hdeg : d 0 + d 1 ≤ n := by
      have h1 := MvPolynomial.le_totalDegree hd
      have h2 : d.sum (fun _ e => e) = d 0 + d 1 := by
        rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
      omega
    by_cases h : d 0 = n
    · have h1 : d 1 = 0 := by omega
      have hd' : d = Finsupp.single 0 n := by
        ext i; fin_cases i <;> simp [h, h1]
      rw [if_pos hd']
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with q hq
      have hq' : (q : ℝ) ≠ 0 := by positivity
      push_cast; rw [h, h1]; field_simp
    · have hne : d ≠ Finsupp.single 0 n := by rintro rfl; simp at h
      rw [if_neg hne]
      have ht : Tendsto (fun q : ℕ => ((q : ℝ) ^ (n - d 0))⁻¹) atTop (𝓝 0) :=
        ((tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
      have ht' := ht.const_mul (((P.coeff d : ℚ) : ℝ) * (r : ℝ) ^ d 1)
      rw [mul_zero] at ht'
      refine ht'.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with q hq
      have hq' : (q : ℝ) ≠ 0 := by positivity
      have hpow : (q : ℝ) ^ n = (q : ℝ) ^ d 0 * (q : ℝ) ^ (n - d 0) := by
        rw [← pow_add]; congr 1; omega
      push_cast; rw [hpow]; field_simp
  have hsum := tendsto_finset_sum _ key
  have hlim : (∑ d ∈ P.support, if d = Finsupp.single 0 n then ((P.coeff d : ℚ) : ℝ) else 0) =
      ((P.coeff (Finsupp.single (0 : Fin 2) n) : ℚ) : ℝ) := by
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · simp [MvPolynomial.notMem_support_iff.1 hmem]
  rw [hlim] at hsum
  refine hsum.congr' (Eventually.of_forall fun q => ?_)
  simp only
  rw [MvPolynomial.eval_eq', Rat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [Fin.prod_univ_two]

/-- The value at `(1, 0)` of the degree-`n` part of `P` is the coefficient of `X₀ⁿ`. -/
private theorem eval_homogeneousComponent_one_zero (P : MvPolynomial (Fin 2) ℚ) (n : ℕ) :
    MvPolynomial.eval (fun i => ((![1, 0] : Fin 2 → ℤ) i : ℚ))
      (MvPolynomial.homogeneousComponent n P) = P.coeff (Finsupp.single 0 n) := by
  classical
  rw [MvPolynomial.homogeneousComponent_apply, map_sum]
  rw [Finset.sum_eq_single (Finsupp.single 0 n)]
  · rw [MvPolynomial.eval_monomial, Finsupp.prod_single_index (by simp)]
    simp
  · intro d hd hne
    rw [Finset.mem_filter] at hd
    have hd1 : d 1 ≠ 0 := by
      intro h1
      apply hne
      have h2 : d.degree = d 0 + d 1 := by simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
      ext i; fin_cases i <;> simp <;> omega
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp [zero_pow hd1]
  · intro h
    rw [Finset.mem_filter, not_and_or] at h
    rcases h with h | h
    · simp [MvPolynomial.notMem_support_iff.1 h]
    · simp at h

/-- Riemann–Roch and Nakai: `χ(qA + rD) ≥ c qⁿ` for `q ≫ 0`, with `c > 0` independent of `r`. -/
private theorem exists_eulerChar_ge [IsIntegral X] {sX : X ⟶ Spec (.of k)} [IsProper sX]
    {n : ℕ} (hn : topologicalKrullDim X = n)
    {A : X.CartierDivisor} (hA : Stacks.Ample.IsAmple X (sheaf A)) (D : X.CartierDivisor) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℤ, ∃ q₁ : ℕ, ∀ q : ℕ, q₁ ≤ q →
      c * (q : ℝ) ^ n ≤
        (MMP.Threefold.Mori.eulerCharCartierCombination k sX ![A, D] ![(q : ℤ), r] : ℝ) := by
  obtain ⟨P, hPdeg, hP⟩ :=
    MMP.Resolution.Bridges.exists_polynomial_eulerChar_cartierSheaf_sum k sX n hn ![A, D]
  have hP' : ∀ m : Fin 2 → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) P =
      MMP.Threefold.Mori.eulerCharCartierCombination k sX ![A, D] m := fun m => by
    rw [hP m, MMP.Threefold.Mori.eulerCharCartierCombination]
    have h2 := (Int.castAddHom ℚ).map_finsum_of_injective Int.cast_injective
      (fun j : ℕ => (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k sX
        (sheaf (∑ i, m i • ![A, D] i)) j) : ℤ))
    simpa using h2.symm
  have hlead := MMP.Threefold.Mori.eval_homogeneousComponent_of_eulerChar k sX hn ![A, D] P hP'
    ![1, 0]
  have hsumA : ∑ i, (![1, 0] : Fin 2 → ℤ) i • ![A, D] i = A := by simp [Fin.sum_univ_two]
  rw [eval_homogeneousComponent_one_zero, hsumA] at hlead
  have hpos := MMP.Threefold.Mori.sheafSelfIntersectionNumber_pos_of_isAmple k sX (sheaf A) hA X
    (𝟙 X) n hn
  set c₀ : ℚ := P.coeff (Finsupp.single 0 n) with hc₀
  have hc₀pos : (0 : ℝ) < c₀ := by
    rw [hlead]; push_cast; exact div_pos (by exact_mod_cast hpos) (by positivity)
  refine ⟨(c₀ : ℝ) / 2, by positivity, fun r => ?_⟩
  have ht := tendsto_eval_div_pow P hPdeg (r : ℚ)
  obtain ⟨q₁, hq₁⟩ := Filter.eventually_atTop.1
    ((ht.eventually (lt_mem_nhds (half_lt_self hc₀pos))).and (Filter.eventually_ge_atTop 1))
  refine ⟨q₁, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := hq₁ q hq
  have hqpos : (0 : ℝ) < (q : ℝ) ^ n := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast h2
    positivity
  have h3 := (lt_div_iff₀ hqpos).1 h1
  have h4 : MvPolynomial.eval ![(q : ℚ), (r : ℚ)] P =
      MMP.Threefold.Mori.eulerCharCartierCombination k sX ![A, D] ![(q : ℤ), r] := by
    rw [← hP']; congr 2; funext i; fin_cases i <;> simp
  rw [h4] at h3
  push_cast at h3
  linarith

/-- The section-counting half of the argument: if `mD ∼ A + E` with `E` effective, then
`h⁰(qA + rD) ≤ h⁰((mq + r)D)`. -/
private theorem cartierH0_le_of_zsmul_linearlyEquivalent {sX : X ⟶ Spec (.of k)}
    [IsProper sX] {D A E : X.CartierDivisor} {m : ℤ} (hE : MMP.Intersection.IsEffective E)
    (hD : MMP.Intersection.LinearlyEquivalent (m • D) (A + E)) (q : ℕ) (r : ℤ) :
    cartierH0 k sX ((q : ℤ) • A + r • D) ≤ cartierH0 k sX ((m * q + r) • D) := by
  refine cartierH0_le_of_linearlyEquivalent_add (hE.nsmul q) ?_
  have e1 : (m * q + r) • D = q • (m • D) + r • D := by
    rw [add_smul, mul_comm, mul_smul, natCast_zsmul]
  have e2 : (q : ℤ) • A + r • D + q • E = q • (A + E) + r • D := by
    rw [nsmul_add, natCast_zsmul]; abel
  rw [e1, e2]
  exact (hD.nsmul q).add (MMP.Intersection.LinearlyEquivalent.refl _)

/-- **Ample plus effective is big** (Kollár–Mori 2.60, (2) ⇒ (1)). On a projective variety `X`
over `k`, a Cartier divisor `D` with `mD ∼ A + E` for some integer `m > 0`, an ample Cartier
divisor `A` and an effective Cartier divisor `E` is big. -/
@[mmp "lem_km2c_big_of_ample_plus_effective"]
public theorem isBigCartier_of_linearlyEquivalent_add [IsIntegral X] {sX : X ⟶ Spec (.of k)}
    (hX : IsProjectiveVariety k sX) {D A E : X.CartierDivisor} {m : ℤ} (hm : 0 < m)
    (hA : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A)) (hE : MMP.Intersection.IsEffective E)
    (hD : MMP.Intersection.LinearlyEquivalent (m • D) (A + E)) :
    IsBigCartier k sX D := by
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq hX
  obtain ⟨c, hc, hχ⟩ := exists_eulerChar_ge (k := k) (sX := sX) hn hA D
  choose q₁ hq₁ using hχ
  choose q₀ hq₀ using eventually_cartierH0_eq_eulerChar (k := k) (sX := sX) hA D
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm.le).symm⟩
  have hM : (0 : ℝ) < M := by exact_mod_cast hm
  -- a uniform threshold for the finitely many residues `0 ≤ r < M`
  set Q : ℕ := ∑ r ∈ Finset.range M, (q₀ r + q₁ r) with hQ
  have hQr : ∀ r < M, q₀ r ≤ Q ∧ q₁ r ≤ Q := by
    intro r hr
    have := Finset.single_le_sum (f := fun r : ℕ => q₀ r + q₁ r) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hr)
    constructor <;> simp only [hQ] <;> omega
  refine ⟨n, hn, c / 2 / (2 * M) ^ n, by positivity, (M : ℤ) * (Q + 2), fun K hK => ?_⟩
  -- `K = M q + r` with `0 ≤ r < M`
  set q : ℤ := K / M with hqdef
  set r : ℤ := K % M
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrM : r < M := Int.emod_lt_of_pos _ (by omega)
  have hKqr : K = M * q + r := (Int.mul_ediv_add_emod K M).symm
  have hqQ : (Q : ℤ) + 2 ≤ q := by
    rw [hqdef]; exact (Int.le_ediv_iff_mul_le (by omega)).2 (by linarith)
  obtain ⟨q', hq'⟩ : ∃ q' : ℕ, q = q' := ⟨q.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, (Int.toNat_of_nonneg hr0).symm⟩
  have hr'M : r' < M := by omega
  have hQq : Q ≤ q' := by omega
  have hχq := hq₁ r' q' ((hQr r' hr'M).2.trans hQq)
  have hh0 := hq₀ r' q' ((hQr r' hr'M).1.trans hQq)
  -- `q > K / (2M)`
  have hKpos : (0 : ℝ) < K := by
    have : (0 : ℤ) < K := by nlinarith
    exact_mod_cast this
  have hq2 : (K : ℝ) / (2 * M) ≤ q' := by
    have h1 : (K : ℝ) = M * q' + r' := by
      have := hKqr; rw [hq', hr'] at this; exact_mod_cast this
    have h2 : (r' : ℝ) < M := by exact_mod_cast hr'M
    have h3 : (2 : ℝ) ≤ q' := by
      have : (2 : ℤ) ≤ q' := by omega
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hKn : (0 : ℝ) < (K : ℝ) ^ n := by positivity
  calc c / 2 / (2 * M) ^ n * (K : ℝ) ^ n = c / 2 * ((K : ℝ) / (2 * M)) ^ n := by
        rw [div_pow]; ring
    _ < c * ((K : ℝ) / (2 * M)) ^ n := by
        have : 0 < ((K : ℝ) / (2 * M)) ^ n := by positivity
        nlinarith
    _ ≤ c * (q' : ℝ) ^ n := by gcongr
    _ ≤ (MMP.Threefold.Mori.eulerCharCartierCombination k sX ![A, D] ![(q' : ℤ), r'] : ℝ) := hχq
    _ = (cartierH0 k sX ((q' : ℤ) • A + (r' : ℤ) • D) : ℝ) := by
        rw [← hh0]; norm_cast
    _ ≤ (cartierH0 k sX (K • D) : ℝ) := by
        rw [hKqr, hq', hr']; exact_mod_cast cartierH0_le_of_zsmul_linearlyEquivalent hE hD q' r'

end BigOfAmplePlusEffective

/-- On a normal proper variety, a Cartier divisor `E` is nef as a `ℚ`-divisor, in the sense of
intersection numbers with closed curves, if and only if it is nef in the sense of degrees on
closed curves. -/
@[mmp "lem_km2c_nef_cartier_agrees"]
public theorem QDivisor.isNef_toQDivisor_iff' (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (E : Divisor X) (hE : E.IsCartier) :
    (Divisor.toQDivisor E).IsNef k sX ↔ E.IsNef k sX :=
  QDivisor.isNef_toQDivisor_iff E hE

end MMP.Mori
