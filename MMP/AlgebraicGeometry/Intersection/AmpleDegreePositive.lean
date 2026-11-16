module
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import StacksFrontier.AlgebraicGeometry.Curves.DifferentialsDegreeGenus
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.AutomorphismSchemeDimension

/-!
# Positivity of degrees of ample sheaves, and the cotangent degree of a curve

Three degree computations over a field `k`.

Let `X` be a proper `k`-scheme, `L` an ample invertible sheaf on `X` and `Z ⊆ X` a closed
subscheme of dimension `d`. The degree `deg Z` is `d!` times the coefficient of `t^d` in the
Hilbert polynomial `t ↦ χ(Z, L|_Z^{⊗ t})`. Substituting `n₁ + ⋯ + n_d` for `t` gives a polynomial
in `d` variables whose values are `χ(Z, L|_Z^{⊗ n₁} ⊗ ⋯ ⊗ L|_Z^{⊗ n_d})`, and its coefficient of
`n₁ ⋯ n_d` is again `d!` times that leading coefficient. So `deg Z` is the self-intersection
number `(L^d · Z)`, which is positive for ample `L` [Stacks, Tag 0BEV]. A closed subscheme
`Z ⊆ ℙᴺ_k` with `L = 𝒪(1)` is the case of [KollarMori], 1.35.

Let `f : X ⟶ Y` be a proper morphism of varieties over `k` and `D` an `f`-ample `ℚ`-Cartier
divisor. Some positive multiple `mD` is an integral Cartier divisor `E` with `𝒪_X(E)` `f`-ample,
so `deg_C 𝒪_X(E) > 0` on every proper curve `C` contracted by `f`. The degree
`E ↦ deg_C 𝒪_X(E)` is additive, hence `deg_C 𝒪_X(E) = m · (D · C)` and `(D · C) > 0`; in
particular `D` is `f`-nef.

Let `C` be a smooth proper curve over an algebraically closed field `k`. Every global function
on `C` is constant, `H⁰(C, 𝒪_C) = k`, so [Stacks, Tag 0C1A] gives
`deg Ω¹_{C/k} = 2 dim_k H¹(C, 𝒪_C) - 2`.

## Main results

* `MMP.Mori.hilbertDegree_pos`: a nonempty closed subscheme has positive degree, `0 < deg Z`.
* `MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ.intersectionNumber_pos`: `(D · C) > 0` for
  every curve `C` contracted by `f`, and `D` is `f`-nef.
* `MMP.invertibleCurveDegree_relativeDifferentials_eq_of_isAlgClosed`:
  `deg Ω¹_{C/k} = 2 dim_k H¹(C, 𝒪_C) - 2`.

## Implementation notes

The degree of a closed subscheme is `MMP.Mori.hilbertDegree`, defined for any proper `k`-scheme
and any invertible `L`; non-emptiness of `Z` is `topologicalKrullDim Z = d` with `d : ℕ`.

A contracted curve is a `MMP.Mori.ProperCurve sX`, an integral curve closed in `X` and proper
over `k`, with `MMP.Mori.ProperCurve.IsContractedBy`: `f` is constant on `C`. That the image point
is closed is not assumed.

The degree of an invertible sheaf on a curve is `AlgebraicGeometry.invertibleCurveDegree`,
`χ(C, L) - χ(C, 𝒪_C)`, and `Ω¹_{C/k}` is `Scheme.Hom.relativeDifferentials f`, invertible since
`f` is smooth of relative dimension one.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.35, Ch. 1
* [R. Hartshorne, *Algebraic geometry*][Har77], I.7
* [The Stacks project][stacks-project], Tags 0BEV, 0C1A
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

section hilbertDegree

open MvPolynomial Stacks.SheafOfModules.Invertible

/-- A polynomial in one variable read as a univariate polynomial has degree at most its total
degree. -/
private theorem natDegree_aeval_X_le_totalDegree (P : MvPolynomial (Fin 1) ℚ) :
    (aeval (fun _ => (Polynomial.X : Polynomial ℚ)) P).natDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_one]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  refine le_trans ?_ (le_totalDegree hs)
  simp [Finsupp.degree, Finsupp.sum_fintype]

/-- The coefficient of `X₁ ⋯ X_d` in `p(X₁ + ⋯ + X_d)` is `d!` times the coefficient of `X^d`
in `p`. -/
private theorem coeff_aeval_sum_X {d : ℕ} (p : Polynomial ℚ) :
    (Polynomial.aeval (∑ j : Fin d, X j : MvPolynomial (Fin d) ℚ) p).coeff
      (Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1) =
        d.factorial * p.coeff d := by
  have hsum : ((Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1).sum fun _ m => m) = d := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]; simp
  have hmult : (Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1).multinomial = d.factorial := by
    rw [Finsupp.multinomial, Finsupp.sum_fintype _ _ (fun _ => rfl),
      Finsupp.prod_fintype _ _ (fun _ => rfl)]
    simp
  rw [Polynomial.aeval_eq_sum_range' (n := max (p.natDegree + 1) (d + 1)) (by omega), coeff_sum]
  simp_rw [smul_eq_C_mul, coeff_C_mul, coeff_sum_X_pow_of_fintype, hsum, hmult]
  rw [Finset.sum_eq_single d (fun j _ hj => by simp [Ne.symm hj]) (fun h => by simp at h)]
  simp [mul_comm]

/-- `p(X₁ + ⋯ + X_d)` has total degree at most `d` when `p` has degree at most `d`. -/
private theorem totalDegree_aeval_sum_X_le {d : ℕ} (p : Polynomial ℚ) (hp : p.natDegree ≤ d) :
    (Polynomial.aeval (∑ j : Fin d, X j : MvPolynomial (Fin d) ℚ) p).totalDegree ≤ d := by
  rw [Polynomial.aeval_eq_sum_range]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j hj => ?_)
  have hj : j ≤ d := by have := Finset.mem_range.1 hj; omega
  refine (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)
  have hA : (∑ i : Fin d, X i : MvPolynomial (Fin d) ℚ).totalDegree ≤ 1 :=
    (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => le_of_eq (totalDegree_X i))
  nlinarith

/-- Evaluating a one-variable `MvPolynomial` read as a `Polynomial`. -/
private theorem eval_aeval_X (P : MvPolynomial (Fin 1) ℚ) (t : ℚ) :
    (aeval (fun _ => (Polynomial.X : Polynomial ℚ)) P).eval t = eval (fun _ => t) P := by
  induction P using MvPolynomial.induction_on <;> simp_all

/-- Evaluating `p(X₁ + ⋯ + X_d)` at `g` is evaluating `p` at `g₁ + ⋯ + g_d`. -/
private theorem eval_aeval_sum_X {d : ℕ} (p : Polynomial ℚ) (g : Fin d → ℚ) :
    eval g (Polynomial.aeval (∑ j : Fin d, X j : MvPolynomial (Fin d) ℚ) p) =
      p.eval (∑ j, g j) := by
  induction p using Polynomial.induction_on' <;> simp_all

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The twist of `𝒪_Z` by `d` copies of `M` with exponents `n` is the twist by one copy with
exponent `n₁ + ⋯ + n_d`. -/
private noncomputable def twistedSheafConstIso {d : ℕ} (M : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M] (n : Fin d → ℤ) :
    twistedSheaf (SheafOfModules.unit Z.ringCatSheaf) (fun _ : Fin d => M) n ≅
      twistedSheaf (SheafOfModules.unit Z.ringCatSheaf) (fun _ : Fin 1 => M)
        (fun _ => ∑ j, n j) :=
  MMP.Mori.Twist.twistedSheafUnitIsoTensorPower _ M (fun _ => Iso.refl _) n ≪≫
    eqToIso (congrArg (tensorPower Z.presheaf Z.ringCatSheaf.2 M) (by simp)) ≪≫
    (MMP.Mori.Twist.twistedSheafUnitIsoTensorPower _ M (fun _ => Iso.refl _) _).symm

/-- **The degree is the self-intersection number.** For any invertible `L` on a proper
`k`-scheme `X` and a closed subscheme `Z` of dimension `d`, `deg_L Z = (L^d · Z)`. -/
private theorem hilbertDegree_eq_selfIntersectionNumber (d : ℕ)
    (hd : topologicalKrullDim Z = d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    hilbertDegree k f i d hd L = selfIntersectionNumber k f i d hd.le L := by
  obtain ⟨P, hP0, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k (i ≫ f)
    (fun _ : Fin 1 => (Scheme.Modules.pullback i).obj L) (SheafOfModules.unit Z.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f))
  have hdeg : P.totalDegree ≤ d := by
    rcases hP0 with rfl | h
    · simp
    · exact_mod_cast h.trans ((topologicalKrullDim_subspace_le Z _).trans hd.le)
  set p : Polynomial ℚ := aeval (fun _ => (Polynomial.X : Polynomial ℚ)) P with hpdef
  have hpdeg : p.natDegree ≤ d := (natDegree_aeval_X_le_totalDegree P).trans hdeg
  have hpeval : ∀ t : ℚ, p.eval t = eval (fun _ => t) P := fun t => by
    rw [hpdef, eval_aeval_X]
  apply Int.cast_injective (α := ℚ)
  rw [hilbertDegree_eq_factorial_mul_coeff k f i d hd L p hpdeg fun t => by
      rw [hpeval]; exact_mod_cast hP fun _ => (t : ℤ),
    ← coeff_aeval_sum_X (d := d) p, selfIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_eq_coeff k f i d hd.le (fun _ => L) _ (fun n => ?_)
      (totalDegree_aeval_sum_X_le p hpdeg)]
  rw [eval_aeval_sum_X, hpeval]
  have h1 := hP fun _ => ∑ j, n j
  push_cast at h1
  rw [h1]
  haveI := isCoherent_twistedSheafUnitPullback k f i (fun _ : Fin 1 => L) fun _ => ∑ j, n j
  haveI := isCoherent_twistedSheafUnitPullback k f i (fun _ => L) n
  exact_mod_cast eulerCharacteristic_eq_of_iso k (i ≫ f)
    (twistedSheafConstIso ((Scheme.Modules.pullback i).obj L) n).symm

/-- **A nonempty closed subscheme has positive degree.** Let `X` be proper over a field `k`, `L`
an ample invertible sheaf on `X` and `i : Z ⟶ X` a closed subscheme of dimension `d` (in
particular `Z` is nonempty). Then its degree `deg Z = MMP.Mori.hilbertDegree k f i d hd L`
(`d!` times the coefficient of `t^d` in `χ(Z, L|_Z^{⊗ t})`) is positive: it is the
self-intersection number `(L^d · Z)`. -/
@[mmp "lem_mmp_foundation_projective_degree_positive"]
public theorem hilbertDegree_pos (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z = d) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    0 < hilbertDegree k f i d hd L := by
  rw [hilbertDegree_eq_selfIntersectionNumber]
  exact selfIntersectionNumber_pos k f i d hd L hL

end hilbertDegree

end MMP.Mori

namespace MMP.Fourfold

open MMP.Mori

section degreeOn

variable {k : Type u} [Field k] {X C : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (i : C ⟶ X)
  [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` for Cartier divisors on any scheme. -/
private theorem degreeOn_lineBundle_add (E E' : X.CartierDivisor) :
    degreeOn k sX i hdim (MMP.CartierDivisor.sheaf (E + E')) =
      degreeOn k sX i hdim (MMP.CartierDivisor.sheaf E) +
        degreeOn k sX i hdim (MMP.CartierDivisor.sheaf E') := by
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  let e : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
      X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
        (MMP.CartierDivisor.sheaf E') ≅ MMP.CartierDivisor.sheaf (E + E') :=
    MMP.CartierDivisorSheaf.sheafMulIso E E'
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sX i hdim e).symm

/-- The degree `E ↦ deg_C 𝒪_X(E)` along a curve, as an additive map on Cartier divisors. -/
private noncomputable def degreeOnHom : X.CartierDivisor →+ ℤ :=
  AddMonoidHom.mk' (fun E => degreeOn k sX i hdim (MMP.CartierDivisor.sheaf E))
    (degreeOn_lineBundle_add sX i hdim)

end degreeOn

/-- `(D · C) = ∑ⱼ cⱼ deg_C 𝒪_X(Dⱼ)` for the cycle `[C]` and a `ℚ`-Cartier divisor
`D = ∑ⱼ cⱼ Dⱼ`. -/
private theorem intersectionNumber_cycle_toReal {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (D : KCartierDivisor ℚ X) :
    (C.cycle ℝ).intersectionNumber (KCartierDivisor.toReal D) =
      D.sum fun E q => (q : ℝ) * (C.degree k (MMP.CartierDivisor.sheaf E) : ℝ) := by
  rw [OneCycle.intersectionNumber_eq_sum, KCartierDivisor.toReal]
  simp only [AddMonoidHom.coe_coe, Finsupp.mapRange.addMonoidHom_apply]
  rw [Finsupp.sum_mapRange_index (by simp)]
  refine Finsupp.sum_congr fun E _ => ?_
  rw [ProperCurve.cycle, Finsupp.sum_single_index (by simp)]
  simp

/-- `deg_C 𝒪_X(E) = m · (D · C)` when `E` is the Cartier divisor realizing `mD`. -/
private theorem degreeOn_realization_smul {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (D : KCartierDivisor ℚ X) {m : ℕ} (hm : 0 < m)
    (h : ∀ E, ∃ n : ℤ, ((m : ℚ) • D) E = n) :
    (degreeOn k sX C.ι C.dim_le
        (MMP.CartierDivisor.sheaf (KCartierDivisor.realization ((m : ℚ) • D) h)) : ℝ) =
      m * (C.cycle ℝ).intersectionNumber (KCartierDivisor.toReal D) := by
  have hdeg : ∀ E : X.CartierDivisor, C.degree k (MMP.CartierDivisor.sheaf E) =
      degreeOnHom sX C.ι C.dim_le E := fun E =>
    (degreeOn_eq_of_iso k sX C.ι C.dim_le (Iso.refl (MMP.CartierDivisor.sheaf E))).symm
  have hn : ∀ E, ((Classical.choose (h E) : ℤ) : ℝ) = m * D E := fun E => by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ))
      ((Classical.choose_spec (h E)).symm.trans (Finsupp.smul_apply _ _ _))
  change (degreeOnHom sX C.ι C.dim_le _ : ℝ) = _
  rw [intersectionNumber_cycle_toReal, KCartierDivisor.realization, map_finsuppSum,
    Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq (by positivity), Int.cast_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul, hn E, hdeg]
  ring

/-- A relatively ample `ℚ`-Cartier divisor `D` for a proper morphism `f : X ⟶ Y` of varieties
over `k` has positive degree `(D · C) > 0` on every curve `C ⊆ X` proper over `k` contracted by
`f`; in particular `D` is `f`-nef. -/
@[mmp "lem_mmp_relative_ample_contracted_curve_positive"]
public theorem KCartierDivisor.IsRelativelyAmpleQ.intersectionNumber_pos {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : AlgebraicGeometry.IsVariety k sX) (hY : AlgebraicGeometry.IsVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) [IsProper f]
    {D : KCartierDivisor ℚ X} (hD : KCartierDivisor.IsRelativelyAmpleQ f D) :
    (∀ C : ProperCurve sX, C.IsContractedBy f →
      0 < (C.cycle ℝ).intersectionNumber (KCartierDivisor.toReal D)) ∧
      KCartierDivisor.IsRelativelyNefQ sX f D := by
  obtain ⟨m, hm, h, hamp⟩ := hD
  have hpos : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 < (C.cycle ℝ).intersectionNumber (KCartierDivisor.toReal D) := fun C hC => by
    refine pos_of_mul_pos_right (a := (m : ℝ)) ?_ (by positivity)
    rw [← degreeOn_realization_smul C D hm h]
    exact_mod_cast
      MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hamp C hC
  exact ⟨hpos, fun C hC => (hpos C hC).le⟩

end MMP.Fourfold

namespace MMP

/-- **The cotangent degree of a smooth proper curve.** For a smooth proper curve
`f : C ⟶ Spec k` over an algebraically closed field `k`,
`deg Ω¹_{C/k} = 2 dim_k H¹(C, 𝒪_C) - 2`: algebraic closedness gives `H⁰(C, 𝒪_C) = k`, and
[Stacks, Tag 0C1A] applies. -/
@[mmp "lem_mmp_threefold_smooth_curve_cotangent_degree"]
public theorem invertibleCurveDegree_relativeDifferentials_eq_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] :
    haveI := smoothOfRelativeDimension_one_of_isCurve k f
    haveI := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials f
    haveI : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
        (Scheme.Hom.relativeDifferentials f) :=
      Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one C.toRingedSpace _
    invertibleCurveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
        (Scheme.Hom.relativeDifferentials f) =
      2 * (Module.finrank k (structureSheafCohomology f 1) : ℤ) - 2 := by
  haveI := GenusOne.isIso_globalSections_of_isAlgClosed f
  exact invertibleCurveDegree_relativeDifferentials_eq_two_mul_genus_sub_two f

end MMP
