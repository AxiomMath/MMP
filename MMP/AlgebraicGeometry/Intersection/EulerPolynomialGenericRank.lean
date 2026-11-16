module
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree

/-!
# Top parts of Euler polynomials, and numerically trivial intersection numbers

Let `X` be an integral scheme, proper over a field `k`, of dimension `d`, and let
`L₁, …, L_r` be invertible `𝒪_X`-modules. For a coherent `𝒪_X`-module `F` the function
`n ↦ χ(X, F ⊗ L₁^{n₁} ⊗ ⋯ ⊗ L_r^{n_r})` on `ℤ^r` is a rational polynomial of total degree at
most `d` (Snapper). Its homogeneous component of degree `d` is `q` times the corresponding
component for `𝒪_X`, where `q` is the generic rank of `F`, i.e. the dimension over the function
field of its stalk at the generic point.

This file also proves that intersection numbers against a curve-numerically trivial invertible
sheaf vanish: let `X` be a proper scheme over a field `k`, `Z ⊆ X` a closed subscheme of
dimension at most `d + 1`, and `L₀, …, L_d` invertible sheaves on `X`. If `deg_C L₀ = 0` for
every proper (equivalently, closed) integral curve `C ⊆ X`, then `(L₀ ⋯ L_d · Z) = 0`.

## Main results

* `MMP.Mori.homogeneousComponent_eulerPolynomial_eq_fiberRank_smul`: the degree-`d`
  homogeneous components of the Euler polynomials of `F` and of `𝒪_X` differ by the factor
  `AlgebraicGeometry.Scheme.Modules.fiberRank F (genericPoint X)`.
* `MMP.Mori.sheafIntersectionNumber_eq_zero_of_degree_eq_zero`: `(L₀ ⋯ L_d · Z) = 0` when
  `L₀` has degree zero on every proper curve of `X`.

## Implementation notes

The Euler polynomial is not given a name: a polynomial in `r` variables over `ℚ` is determined
by its values on `ℤ^r`, so the statement is made for any polynomials `P` and `Q` interpolating
the two Euler characteristic functions; their existence is
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`. The generic rank is
`AlgebraicGeometry.Scheme.Modules.fiberRank` at `genericPoint X`, which on an integral scheme is
the dimension of the stalk over the function field
(`AlgebraicGeometry.Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk`).

The vanishing of intersection numbers is stated for invertible sheaves rather than for the
Cartier divisors of the source; these are the sheaves `𝒪_X(L_j)` of those divisors, which is the
generality in which `MMP.Mori.sheafIntersectionNumber` is defined. The distinguished factor is
indexed by `0 : Fin (d + 1)`. The closed curves of `X` are the points of `MMP.Mori.ProperCurve`:
on a proper `k`-scheme every closed integral curve is proper over `k`. The proof goes through
the Chow group: the intersection number is the cap degree of `[Z]_{d+1}`, peeling off the last
`d` factors leaves the cap with `L₀` on a class in `A_1(X)`, which is a finite combination of
integral curves, on each of which the cap degree is the curve degree of `L₀`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.33–1.36
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

/-- A rational polynomial in `r` variables is determined by its values on `ℤ^r`. -/
private theorem eq_of_forall_eval_intCast {r : ℕ} {A B : MvPolynomial (Fin r) ℚ}
    (h : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) A =
      MvPolynomial.eval (fun j => (n j : ℚ)) B) : A = B := by
  refine MvPolynomial.funext_set (s := fun _ => Set.range ((↑) : ℤ → ℚ))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
  choose n hn using fun j => hx j (Set.mem_univ j)
  have : x = fun j => (n j : ℚ) := funext fun j => (hn j).symm
  subst this
  exact h n

/-- A proper closed subset of an irreducible space is nowhere dense. -/
private theorem isNowhereDense_of_isClosed_of_ne_univ {Y : Type*} [TopologicalSpace Y]
    [IrreducibleSpace Y] {Z : Set Y} (hZ : IsClosed Z) (hne : Z ≠ Set.univ) :
    IsNowhereDense Z := by
  rw [hZ.isNowhereDense_iff]
  by_contra h
  have hd : Dense (interior Z) :=
    isOpen_interior.dense (Set.nonempty_iff_ne_empty.mpr h)
  exact hne (by simpa [hZ.closure_eq] using (hd.mono interior_subset).closure_eq)

/-- If `R₂ = R₁ + R₃` and `a₂ = a₁ + a₃`, then any two of the relations `R i = a i • Q` imply
the third. -/
private theorem two_out_of_three_of_add {M : Type*} [AddCommGroup M] [Module ℚ M]
    {R₁ R₂ R₃ Q : M} {a₁ a₂ a₃ : ℚ} (hR : R₂ = R₁ + R₃) (ha : a₂ = a₁ + a₃) :
    (R₁ = a₁ • Q ∧ R₂ = a₂ • Q → R₃ = a₃ • Q) ∧ (R₁ = a₁ • Q ∧ R₃ = a₃ • Q → R₂ = a₂ • Q) ∧
      (R₂ = a₂ • Q ∧ R₃ = a₃ • Q → R₁ = a₁ • Q) := by
  subst hR ha
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨h₁, h₃⟩ => ?_, fun ⟨h₂, h₃⟩ => ?_⟩
  · rw [add_smul, h₁, add_right_inj] at h₂; exact h₂
  · rw [h₁, h₃, add_smul]
  · rw [add_smul, h₃, add_left_inj] at h₂; exact h₂

/-- On an integral scheme proper over `k` of dimension `d`, a coherent sheaf supported on a
proper closed subset has Euler polynomial of total degree less than `d`, so its degree-`d`
component vanishes. -/
private theorem homogeneousComponent_eulerPolynomial_eq_zero_of_supp_subset
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) [IsProper f] (d : ℕ) (hd : topologicalKrullDim X = d)
    {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (G : X.Modules) (hG : SheafOfModules.IsCoherent G) {Z : Set X} (hZ : IsClosed Z)
    (hZne : Z ≠ Set.univ) (hGZ : _root_.SheafOfModules.supp G ⊆ Z)
    (R : MvPolynomial (Fin r) ℚ)
    (hR : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) R =
      (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
        (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)) :
    MvPolynomial.homogeneousComponent d R = 0 := by
  obtain ⟨R', hdeg, hR'⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f L G hG
  rw [eq_of_forall_eval_intCast fun n => (hR n).trans (hR' n).symm]
  rcases hdeg with h0 | hdeg
  · rw [h0, map_zero]
  refine MvPolynomial.homogeneousComponent_eq_zero _ _ ?_
  have := hG.isFiniteType
  have hlt := ((isNowhereDense_of_isClosed_of_ne_univ hZ hZne).mono
    hGZ).topologicalKrullDim_add_one_le (_root_.SheafOfModules.isClosed_supp G)
  rw [hd] at hlt
  have : ((R'.totalDegree + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
    push_cast
    exact le_trans (by gcongr) hlt
  exact_mod_cast this

/-- The generic point lies outside the support of a sheaf supported on a proper closed
subset. -/
private theorem genericPoint_notMem_supp {X : Scheme.{u}} [IsIntegral X] (G : X.Modules)
    [G.IsFiniteType] {Z : Set X} (hZne : Z ≠ Set.univ)
    (hGZ : _root_.SheafOfModules.supp G ⊆ Z) :
    genericPoint X ∉ _root_.SheafOfModules.supp G := fun hη => hZne <|
  Set.eq_univ_of_univ_subset <| by
    rw [← genericPoint_spec X]
    exact ((_root_.SheafOfModules.isClosed_supp G).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hη)).trans hGZ

/-- **The top Euler-polynomial part is multiplied by the generic rank.** Let `X` be an integral
scheme, proper over a field `k` via `f`, of dimension `d`; let `L₁, …, L_r` be invertible and `F`
coherent. If `P` and `Q` are rational polynomials with `P(n) = χ(X, F(n₁L₁ + ⋯ + n_rL_r))` and
`Q(n) = χ(X, 𝒪_X(n₁L₁ + ⋯ + n_rL_r))` for all `n ∈ ℤ^r`, then the degree-`d` homogeneous
component of `P` is the generic rank of `F` times that of `Q`. -/
@[mmp "lem_mmp_foundation_euler_top_part_generic_rank"]
public theorem homogeneousComponent_eulerPolynomial_eq_fiberRank_smul
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f] (d : ℕ) (hd : topologicalKrullDim X = d)
    {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F)
    (P Q : MvPolynomial (Fin r) ℚ)
    (hP : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
        (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ))
    (hQ : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) Q =
      (@eulerCharacteristic k _ X f _ (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) L n)
        (@twistedSheaf_isCoherent X r _ L _
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f) n) : ℚ)) :
    MvPolynomial.homogeneousComponent d P =
      (Scheme.Modules.fiberRank F (genericPoint X) : ℚ) •
        MvPolynomial.homogeneousComponent d Q := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  refine Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_isIntegral X
    (fun G => ∀ (hG : SheafOfModules.IsCoherent G) (R : MvPolynomial (Fin r) ℚ),
      (∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) R =
        (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
          (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)) →
      MvPolynomial.homogeneousComponent d R =
        (Scheme.Modules.fiberRank G (genericPoint X) : ℚ) •
          MvPolynomial.homogeneousComponent d Q) ?_ ?_ ?_ F hF hF P hP
  · intro S hS h1 h2 h3
    obtain ⟨R₁, -, hR₁⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f L S.X₁ h1
    obtain ⟨R₂, -, hR₂⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f L S.X₂ h2
    obtain ⟨R₃, -, hR₃⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f L S.X₃ h3
    have hadd : R₂ = R₁ + R₃ := eq_of_forall_eval_intCast fun n => by
      rw [map_add, hR₁, hR₂, hR₃]
      exact_mod_cast eulerCharacteristic_twistedSheaf_add_of_shortExact k f L
        (forall_finiteDimensional_cohomologyOverField_of_isProper k f) hS h1 h2 h3 n
    have hrk : (Scheme.Modules.fiberRank S.X₂ (genericPoint X) : ℚ) =
        Scheme.Modules.fiberRank S.X₁ (genericPoint X) +
          Scheme.Modules.fiberRank S.X₃ (genericPoint X) := by
      have := h1; have := h2; have := h3
      exact_mod_cast Scheme.Modules.fiberRank_genericPoint_add_of_shortExact S hS
    obtain ⟨t₃, t₂, t₁⟩ := two_out_of_three_of_add
      (Q := MvPolynomial.homogeneousComponent d Q)
      (hadd ▸ map_add (MvPolynomial.homogeneousComponent d) R₁ R₃) hrk
    refine ⟨fun ⟨p1, p2⟩ hG R hR => ?_, fun ⟨p1, p3⟩ hG R hR => ?_,
      fun ⟨p2, p3⟩ hG R hR => ?_⟩
    · rw [eq_of_forall_eval_intCast fun n => (hR n).trans (hR₃ n).symm]
      exact t₃ ⟨p1 h1 R₁ hR₁, p2 h2 R₂ hR₂⟩
    · rw [eq_of_forall_eval_intCast fun n => (hR n).trans (hR₂ n).symm]
      exact t₂ ⟨p1 h1 R₁ hR₁, p3 h3 R₃ hR₃⟩
    · rw [eq_of_forall_eval_intCast fun n => (hR n).trans (hR₁ n).symm]
      exact t₁ ⟨p2 h2 R₂ hR₂, p3 h3 R₃ hR₃⟩
  · intro G Z hZ hZne hGZ hG R hR
    have := hG.isFiniteType
    rw [homogeneousComponent_eulerPolynomial_eq_zero_of_supp_subset k f d hd L G hG hZ hZne hGZ
      R hR, Scheme.Modules.fiberRank_eq_zero_of_notMem_supp G _
      (genericPoint_notMem_supp G hZne hGZ), Nat.cast_zero, zero_smul]
  · intro hG R hR
    rw [eq_of_forall_eval_intCast fun n => (hR n).trans (hQ n).symm,
      Scheme.Modules.fiberRank_unit_eq_one, Nat.cast_one, one_smul]

section NumericallyTrivial

open Stacks.Chow

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

private theorem isIntegral_curveSubschemeAt (x : X) :
    AlgebraicGeometry.IsIntegral (curveSubschemeAt x) :=
  StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure

private theorem curveSubschemeAtι_genericPoint (x : X) :
    have := isIntegral_curveSubschemeAt x
    curveSubschemeAtι x (genericPoint (curveSubschemeAt x)) = x :=
  Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x

private theorem topologicalKrullDim_curveSubschemeAt (x : X) :
    have := isIntegral_curveSubschemeAt x
    topologicalKrullDim (curveSubschemeAt x) =
      ((relativeDimension (fieldChowSituation k).dimensionFunction f x).toNat : WithBot ℕ∞) := by
  have := isIntegral_curveSubschemeAt x
  have := topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k) (fun _ _ => rfl) f
    (curveSubschemeAtι x) (genericPoint (curveSubschemeAt x))
    ((IrreducibleSpace.isIrreducible_univ _).isGenericPoint_genericPoint isClosed_univ)
  rwa [curveSubschemeAtι_genericPoint] at this

private theorem relativeDimension_eq_one_of_isProperCurve (x : X) (hx : IsProperCurve f x) :
    relativeDimension (fieldChowSituation k).dimensionFunction f x = 1 := by
  have h := topologicalKrullDim_curveSubschemeAt f x
  rw [hx.dim_eq] at h
  have hn := relativeDimension_nonneg (fieldChowSituation k) (fun _ _ => rfl) f x
  have : (relativeDimension (fieldChowSituation k).dimensionFunction f x).toNat = 1 := by
    exact_mod_cast h.symm
  omega

private theorem isProperCurve_of_relativeDimension_eq_one (x : X)
    (h : relativeDimension (fieldChowSituation k).dimensionFunction f x = 1) :
    IsProperCurve f x := by
  refine isProperCurve_of_isProper f ?_
  rw [topologicalKrullDim_curveSubschemeAt f x, h]
  simp

private theorem curveCycle_apply_self (x : X) (hx : IsProperCurve f x) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (curveSubschemeAtι x) 1).1 x =
      1 := by
  have := isIntegral_curveSubschemeAt x
  have h := cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint (fieldChowSituation k) f
    (curveSubschemeAtι x) 1 (by
      rw [curveSubschemeAtι_genericPoint]
      exact relativeDimension_eq_one_of_isProperCurve f x hx)
  rwa [curveSubschemeAtι_genericPoint] at h

private theorem curveCycle_apply_of_ne (x y : X) (hy : y ≠ x) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (curveSubschemeAtι x) 1).1 y =
      0 := by
  have := isIntegral_curveSubschemeAt x
  exact cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne (fieldChowSituation k) f
    (curveSubschemeAtι x) 1 (by rwa [curveSubschemeAtι_genericPoint])

private theorem cycle_eq_sum_curveCycle (α : CycleGroup (fieldChowSituation k) f 1) :
    ∃ S : Finset X, (∀ x ∈ S, IsProperCurve f x) ∧ α = ∑ x ∈ S, (α.1 x) •
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (curveSubschemeAtι x) 1 := by
  classical
  have := QuasiCompact.compactSpace_of_compactSpace f
  have hfin : (Function.support α.1).Finite := by
    simpa using α.1.locallyFiniteSupport.finite_inter_support_of_isCompact
      (CompactSpace.isCompact_univ (X := X))
  have hS : ∀ x ∈ hfin.toFinset, IsProperCurve f x := fun x hx => by
    refine isProperCurve_of_relativeDimension_eq_one f x ?_
    exact (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) f 1 α.1).1 α.2 x
      (by simpa using hx)
  refine ⟨hfin.toFinset, hS, ?_⟩
  refine Subtype.ext ?_
  ext y
  simp only [AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul,
    Function.locallyFinsuppWithin.coe_sum,
    Function.locallyFinsuppWithin.coe_zsmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hy : y ∈ hfin.toFinset
  · rw [Finset.sum_eq_single y]
    · rw [curveCycle_apply_self f y (hS y hy), mul_one]
    · intro b _ hb
      rw [curveCycle_apply_of_ne f b y (Ne.symm hb), mul_zero]
    · intro h; exact absurd hy h
  · rw [Finset.sum_eq_zero]
    · simpa using hy
    · intro b hb
      rw [curveCycle_apply_of_ne f b y (fun h => hy (h ▸ hb)), mul_zero]

private theorem capDegree_curveCycle_eq_zero (L0 : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L0]
    (hL : ∀ C : ProperCurve f, C.degree k L0 = 0) (x : X) (hx : IsProperCurve f x) :
    capDegree k f (fun _ : Fin 1 => L0)
      (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f ((1 : ℕ) : ℤ))
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (curveSubschemeAtι x) 1)) =
      0 := by
  have hd : topologicalKrullDim (curveSubschemeAt x) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    simpa using hx.dim_eq.le
  have e := intersectionNumber_eq_capDegree_of_le k 1 f (curveSubschemeAtι x) hd (fun _ => L0)
  have h2 := intersectionNumber_one_eq_invertibleCurveDegree k f (curveSubschemeAtι x) hd L0
  exact e.symm.trans (h2.trans (hL ⟨x, hx⟩))

private theorem capDegree_one_eq_zero_of_degree_eq_zero (L0 : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L0]
    (hL : ∀ C : ProperCurve f, C.degree k L0 = 0)
    (β : chowGroup (fieldChowSituation k) f ((1 : ℕ) : ℤ)) :
    capDegree k f (fun _ : Fin 1 => L0) β = 0 := by
  induction β using QuotientAddGroup.induction_on with
  | H α =>
    obtain ⟨S, hS, hα⟩ := cycle_eq_sum_curveCycle f α
    have : (QuotientAddGroup.mk α : chowGroup (fieldChowSituation k) f ((1 : ℕ) : ℤ)) =
        ∑ x ∈ S, (α.1 x) • (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f
          ((1 : ℕ) : ℤ)) (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (curveSubschemeAtι x) 1)) := by
      conv_lhs => rw [hα]
      simp
    rw [this, map_sum]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [map_zsmul, capDegree_curveCycle_eq_zero f L0 hL x (hS x hx), smul_zero]

private theorem capDegree_eq_zero_of_degree_eq_zero (n : ℕ) (L : Fin (n + 1) → X.Modules)
    [hinv : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hL : ∀ C : ProperCurve f, C.degree k (L 0) = 0)
    (a : chowGroup (fieldChowSituation k) f ((n + 1 : ℕ) : ℤ)) :
    capDegree k f L a = 0 := by
  induction n with
  | zero =>
    obtain ⟨M, hM⟩ : ∃ M, L = fun _ : Fin (0 + 1) => M :=
      ⟨L 0, funext fun j => by rw [Fin.eq_zero j]⟩
    subst hM
    have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M := hinv 0
    exact capDegree_one_eq_zero_of_degree_eq_zero f M hL a
  | succ n ih =>
    rw [capDegree_succ]
    exact ih (fun j => L j.castSucc) hL _

end NumericallyTrivial

/-- If an invertible sheaf `L 0` on a proper `k`-scheme `X` has degree zero on every proper curve
of `X`, then every intersection number `(L 0 ⋯ L d · Z)` with a closed subscheme `Z` of dimension
at most `d + 1` is zero. -/
@[mmp "lem_mmp_foundation_numerically_trivial_mixed_intersection"]
public theorem sheafIntersectionNumber_eq_zero_of_degree_eq_zero (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (L : Fin (d + 1) → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hL : ∀ C : ProperCurve f, C.degree k (L 0) = 0) :
    sheafIntersectionNumber k f i (d + 1) hd L = 0 := by
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_eq_capDegree_of_le k (d + 1) f i hd L]
  exact capDegree_eq_zero_of_degree_eq_zero f d L hL _

end MMP.Mori

