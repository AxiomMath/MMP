module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
import MMP.AlgebraicGeometry.Intersection.Surface.EffectiveDisjointness
import MMP.AlgebraicGeometry.Intersection.NumericalDivisorLattice
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.Intersection.Surface.RiemannRochHodgeIndex
import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts

/-!
# The elementary intersection theory of a smooth projective surface

Let `S` be a smooth projective surface over an algebraically closed field `k` of characteristic
zero (for instance `k = ℂ`). Every divisor on `S` is Cartier, so the intersection number
`(C · C')` of two prime divisors (integral curves) is defined, and it extends bilinearly to the
intersection pairing `(A · B) = ∑_{C, C'} A(C) B(C') (C · C')` of `ℚ`-divisors. Then:

* two distinct integral curves `C ≠ C'` satisfy `(C · C') ≥ 0`, with equality exactly when
  `C ∩ C' = ∅`;
* (Hodge index) if `(A²) > 0` and `(A · B) = 0`, then `(B²) ≤ 0`, with equality exactly when `B`
  is numerically trivial;
* a nef `ℚ`-divisor `A` has `(A²) ≥ 0`;
* the group of integral divisors modulo numerical equivalence is finitely generated; in
  particular the set of numerical classes of integral curves is countable.

The proof: every divisor is Cartier because the local rings are regular, hence factorial. For
distinct curves `(C · C') = deg_{C'} 𝒪_S(C)`, by cutting down along `C'`. The Hodge index
theorem for rational combinations of invertible sheaves applies to the sheaves `𝒪_S(C)` of the
components of `A` and `B`. A nef `ℚ`-divisor `A` has a Cartier multiple `mA = E` with `𝒪_S(E)`
nef, and Kleiman's theorem gives `(E²) ≥ 0`. Finally `D ↦ (z ↦ (𝒪_S(D) · z))` maps the divisors
into the group of numerical divisor classes, which is free of finite rank in characteristic zero,
with kernel the numerically trivial divisors.

## Main results

* `MMP.Mori.exists_forall_isCartier_and_intersectionNumberOn_of_smooth`

## Implementation notes

The intersection number of two prime divisors `C, C'` is
`MMP.Mori.Divisor.intersectionNumberOn` of the Cartier divisors `C, C'` against `S` itself, that
is, the Euler-characteristic intersection number of `𝒪_S(C)` and `𝒪_S(C')`. The pairing of
`ℚ`-divisors is its bilinear extension in the coefficients. Nefness and numerical triviality are
`MMP.Mori.QDivisor.IsNef` and `MMP.Mori.QDivisor.IsNumericallyTrivial`: degrees on every integral
curve. The subgroup of numerically trivial integral divisors is characterised by its membership,
and the classes of integral curves are the images of the prime divisors in the quotient.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, §1.
* [Har77] R. Hartshorne, *Algebraic geometry*, V.1.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-! ### Finitely supported sums -/

/-- An additive map on finitely supported `ℤ`-valued functions is the sum of its values on the
basis vectors, weighted by the coefficients. -/
private theorem map_eq_sum_single {α : Type*} (φ : (α →₀ ℤ) →+ ℤ) (D : α →₀ ℤ) :
    φ D = D.sum fun P n => n * φ (Finsupp.single P 1) := by
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun P _ => ?_
  rw [← Finsupp.smul_single_one, map_zsmul, smul_eq_mul]

/-- A double sum over a rescaled finitely supported function. -/
private theorem sum_sum_smul {α : Type*} (A : α →₀ ℚ) (r : ℚ) (g : α → α → ℚ) :
    ((r • A).sum fun C a => (r • A).sum fun C' b => a * b * g C C') =
      r * r * (A.sum fun C a => A.sum fun C' b => a * b * g C C') := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · simp only [Finsupp.sum, Finsupp.support_smul_eq hr, Finsupp.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

/-- A sum over the support of a finitely supported function, reindexed by an enumeration of a
finite set containing the support. -/
private theorem sum_eq_sum_fin {α : Type*} {T : Finset α} (e : Fin T.card ≃ T) (A : α →₀ ℚ)
    (hA : A.support ⊆ T) (g : α → ℚ → ℚ) (hg : ∀ a, g a 0 = 0) :
    A.sum g = ∑ i, g (e i) (A (e i)) := by
  rw [Finsupp.sum_of_support_subset A hA g fun a _ => hg a, ← Finset.sum_coe_sort T]
  exact (e.sum_comp fun x : T => g x (A x)).symm

/-- A sum over a divisor regarded as a `ℚ`-divisor. -/
private theorem sum_toQDivisor {X : Scheme.{u}} (D : Divisor X)
    (g : PrimeDivisor X → ℚ → ℚ) (hg : ∀ P, g P 0 = 0) :
    (Divisor.toQDivisor D).sum g = D.sum fun P n => g P n :=
  Finsupp.sum_mapRange_index (f := Int.castAddHom ℚ) (hf := map_zero _) hg

section Pairing

variable (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim S ≤ (2 : ℕ))

/-- The pair `![N₁, N₂]` of invertible sheaves is a family of invertible sheaves. -/
private theorem isInvertible_pair (N₁ N₂ : S.Modules)
    [h₁ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [h₂ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    ∀ j : Fin 2, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![N₁, N₂] j) := by
  intro j
  fin_cases j
  exacts [h₁, h₂]

/-- The intersection pairing `(N₁ · N₂)` of two invertible sheaves on a proper surface. -/
private noncomputable def pair (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] : ℤ :=
  haveI := isInvertible_pair N₁ N₂
  AlgebraicGeometry.intersectionNumber k f (𝟙 S) 2 hd ![N₁, N₂]

private theorem pair_def (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    haveI := isInvertible_pair N₁ N₂
    pair k f hd N₁ N₂ = AlgebraicGeometry.intersectionNumber k f (𝟙 S) 2 hd ![N₁, N₂] := rfl

/-- The pairing is symmetric. -/
private theorem pair_comm (N₁ N₂ : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    pair k f hd N₁ N₂ = pair k f hd N₂ N₁ := by
  haveI := isInvertible_pair N₁ N₂
  haveI := isInvertible_pair N₂ N₁
  rw [pair_def, pair_def,
    ← AlgebraicGeometry.intersectionNumber_comp_perm k f (𝟙 S) 2 hd ![N₂, N₁] (Equiv.swap 0 1)]
  exact AlgebraicGeometry.intersectionNumber_congr_family k f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

/-- The pairing is additive in the first divisor: `(𝒪(D + D') · N) = (𝒪(D) · N) + (𝒪(D') · N)`. -/
private theorem pair_divisorialSheaf_add [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
    {D D' : Divisor S} (hD : D.IsCartier) (hD' : D'.IsCartier) (N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
      hD.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
      hD'.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (D + D').divisorialSheaf :=
      (hD.add hD').isInvertibleModule_divisorialSheaf
    pair k f hd (D + D').divisorialSheaf N =
      pair k f hd D.divisorialSheaf N + pair k f hd D'.divisorialSheaf N := by
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D.divisorialSheaf :=
    hD.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf :=
    hD'.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (D + D').divisorialSheaf :=
    (hD.add hD').isInvertibleModule_divisorialSheaf
  haveI := isInvertible_pair (D + D').divisorialSheaf N
  haveI := isInvertible_pair D.divisorialSheaf N
  haveI := isInvertible_pair D'.divisorialSheaf N
  rw [pair_def, pair_def, pair_def]
  exact AlgebraicGeometry.intersectionNumber_tensor k f (𝟙 S) 2 hd 0 _ _ _
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (hD.divisorialSheafTensorIso hD').symm

/-- **Cutting down by a curve.** On a smooth proper surface, the pairing of an invertible sheaf
`I ≅ 𝒪_S(P)` of a prime divisor `P` with `N` is the degree of `N` on `P`. -/
private theorem pair_eq_degreeOn_of_iso_invertibleSheaf [IsLocallyNoetherian S] [IsNormal S]
    (hsm : IsSmoothScheme f) (P : PrimeDivisor S)
    [IsProper (P.idealSheaf.subschemeι ≫ f)]
    (hP : topologicalKrullDim P.idealSheaf.subscheme ≤ 1) (I N : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 I]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N]
    (e : I ≅ (Stacks.Divisors.invertibleSheaf' P.idealSheaf : S.Modules)) :
    pair k f hd I N = degreeOn k f P.idealSheaf.subschemeι hP N := by
  haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
  haveI := isInvertible_pair I N
  have hL : (Scheme.Modules.pullback (𝟙 S)).obj (![I, N] 0) ≅
      (Stacks.Divisors.invertibleSheaf P.idealSheaf : S.Modules) :=
    (Scheme.Modules.pullbackId S).app I ≪≫ e
  rw [pair_def, AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 S) 1
    hd ![I, N] P.idealSheaf hL, degreeOn,
    ← AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree k f
      P.idealSheaf.subschemeι hP N,
    AlgebraicGeometry.intersectionNumber_congr_family k f _ 1 _
      (show (fun t : Fin 1 => ![I, N] t.succ) = fun _ => N from
        funext fun t => by fin_cases t <;> rfl),
    ← Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  have hker : (P.idealSheaf.subschemeι ≫ 𝟙 S).ker = P.idealSheaf.subschemeι.ker := by
    rw [Category.comp_id]
  exact (sheafIntersectionNumber_eq_of_ker_eq k f _ _ hker 1 _ hP _).trans
    (Snapper.sheafIntersectionNumber_eq_intersectionNumber k f _ 1 _ _)

/-- An intersection number of two sheaves on `S` is their pairing. -/
private theorem sheafIntersectionNumber_two_eq_pair (L : Fin 2 → S.Modules)
    [hL : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (L j)]
    (hd' : topologicalKrullDim S ≤ (2 : ℕ)) :
    sheafIntersectionNumber k f (𝟙 S) 2 hd' L = pair k f hd (L 0) (L 1) := by
  haveI := isInvertible_pair (L 0) (L 1)
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber, pair_def]
  exact AlgebraicGeometry.intersectionNumber_congr_family k f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

/-- The self-intersection `(M²)` of a rational combination `M = ∑ cᵢ Mᵢ`, as a double sum of
pairings. -/
private theorem sheafCombinationIntersectionNumber_two_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → S.Modules) [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (hd' : topologicalKrullDim S ≤ ((2 + 0 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
    sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 2 ![] hd' =
      ∑ i, ∑ j, c i * c j * (pair k f hd (M i) (M j) : ℚ) := by
  haveI : ∀ j : Fin 0, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![] : Fin 0 → S.Modules) j) := fun j => j.elim0
  rw [sheafCombinationIntersectionNumber, ← Fintype.sum_prod_type',
    ← (finTwoArrowEquiv (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun p => ?_
  rw [Fin.prod_univ_two]
  congr 1
  exact_mod_cast sheafIntersectionNumber_two_eq_pair k f hd _ hd'
    (hL := isInvertible_finAppend (a := 2) (b := 0) _ _)

/-- The intersection number `(M · H)` of a rational combination `M = ∑ cᵢ Mᵢ` with `H`, as a sum
of pairings. -/
private theorem sheafCombinationIntersectionNumber_one_eq_sum {s : ℕ} (c : Fin s → ℚ)
    (M : Fin s → S.Modules) [∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (M j)]
    (H : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    (hd' : topologicalKrullDim S ≤ ((1 + 1 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        ((![H] : Fin 1 → S.Modules) j) := fun _ => by simpa
    sheafCombinationIntersectionNumber k f (𝟙 S) ℚ c M 1 ![H] hd' =
      ∑ i, c i * (pair k f hd (M i) H : ℚ) := by
  haveI : ∀ j : Fin 1, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((![H] : Fin 1 → S.Modules) j) := fun _ => by simpa
  rw [sheafCombinationIntersectionNumber, ← (Equiv.funUnique (Fin 1) (Fin s)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [Fin.prod_univ_one]
  congr 1
  exact_mod_cast sheafIntersectionNumber_two_eq_pair k f hd _ hd'
    (hL := isInvertible_finAppend (a := 1) (b := 1) _ _)

end Pairing

/-! ### The intersection pairing of divisors -/

section DivisorPairing

variable (k : Type u) [Field k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim S ≤ (2 : ℕ)) [CompactSpace S] [IsLocallyNoetherian S] [IsNormal S]
  (hC : ∀ D : Divisor S, D.IsCartier)

/-- The intersection number `(D · D')` of two divisors is the pairing of their sheaves. -/
private theorem intersectionNumberOn_eq_pair (D D' : Divisor S) :
    haveI := (hC D).isInvertibleModule_divisorialSheaf
    haveI := (hC D').isInvertibleModule_divisorialSheaf
    Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D, D'] (fun _ => hC _) =
      pair k f hd D.divisorialSheaf D'.divisorialSheaf := by
  haveI := fun D : Divisor S => (hC D).isInvertibleModule_divisorialSheaf
  exact sheafIntersectionNumber_two_eq_pair k f hd _ hd

/-- The intersection number of divisors is symmetric. -/
private theorem intersectionNumberOn_comm (D D' : Divisor S) :
    Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D, D'] (fun _ => hC _) =
      Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D', D] (fun _ => hC _) := by
  haveI := fun D : Divisor S => (hC D).isInvertibleModule_divisorialSheaf
  rw [intersectionNumberOn_eq_pair k f hd hC, intersectionNumberOn_eq_pair k f hd hC, pair_comm]

/-- The intersection number of divisors is additive in the first divisor. -/
private theorem intersectionNumberOn_add_left (D D' E : Divisor S) :
    Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D + D', E] (fun _ => hC _) =
      Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D, E] (fun _ => hC _) +
        Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D', E] (fun _ => hC _) := by
  haveI := fun D : Divisor S => (hC D).isInvertibleModule_divisorialSheaf
  rw [intersectionNumberOn_eq_pair k f hd hC, intersectionNumberOn_eq_pair k f hd hC,
    intersectionNumberOn_eq_pair k f hd hC]
  exact pair_divisorialSheaf_add k f hd (hC D) (hC D') _

/-- The intersection number of divisors expanded in the first divisor. -/
private theorem intersectionNumberOn_eq_sum_left (D E : Divisor S) :
    Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D, E] (fun _ => hC _) =
      D.sum fun P n => n * Divisor.intersectionNumberOn k f (𝟙 S) 2 hd
        ![Finsupp.single P 1, E] (fun _ => hC _) :=
  map_eq_sum_single (AddMonoidHom.mk'
    (fun D => Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D, E] fun _ => hC _)
    fun D D' => intersectionNumberOn_add_left k f hd hC D D' E) D

/-- **Bilinearity.** `(D · E) = ∑_{P, P'} D(P) E(P') (P · P')`. -/
private theorem intersectionNumberOn_eq_sum_sum (D E : Divisor S) :
    Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D, E] (fun _ => hC _) =
      D.sum fun P n => E.sum fun P' n' => n * n' * Divisor.intersectionNumberOn k f (𝟙 S) 2 hd
        ![Finsupp.single P 1, Finsupp.single P' 1] (fun _ => hC _) := by
  rw [intersectionNumberOn_eq_sum_left k f hd hC]
  refine Finsupp.sum_congr fun P _ => ?_
  rw [intersectionNumberOn_comm k f hd hC, intersectionNumberOn_eq_sum_left k f hd hC,
    Finsupp.mul_sum]
  refine Finsupp.sum_congr fun P' _ => ?_
  rw [intersectionNumberOn_comm k f hd hC]
  ring

/-- **Cutting down by a prime divisor.** On a smooth proper surface, `(D · P)` is the degree of
`𝒪_S(D)` on the prime divisor `P`. -/
private theorem intersectionNumberOn_single_eq_degreeOn (hsm : IsSmoothScheme f) (D : Divisor S)
    (P : PrimeDivisor S) [IsProper (P.idealSheaf.subschemeι ≫ f)]
    (hP : topologicalKrullDim P.idealSheaf.subscheme ≤ 1) :
    Divisor.intersectionNumberOn k f (𝟙 S) 2 hd ![D, Finsupp.single P 1] (fun _ => hC _) =
      D.degreeOn k f P.idealSheaf.subschemeι hP (hC D) := by
  haveI := fun D : Divisor S => (hC D).isInvertibleModule_divisorialSheaf
  haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
  obtain ⟨e⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P
    inferInstance (hC _)
  rw [intersectionNumberOn_comm k f hd hC, intersectionNumberOn_eq_pair k f hd hC,
    pair_eq_degreeOn_of_iso_invertibleSheaf k f hd hsm P hP _ _ e]
  rfl

end DivisorPairing

/-! ### Curves -/

section Curves

variable {k : Type u} [Field k]

/-- A closed immersion with reduced source has kernel the vanishing ideal of its image. -/
private theorem ker_eq_vanishingIdeal_support {A B : Scheme.{u}} (g : A ⟶ B)
    [IsClosedImmersion g] [IsReduced A] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal g.ker.support := by
  have hg : IsIso g.toImage := by
    apply IsClosedImmersion.isIso_of_ker_eq g g.imageι g.toImage <;> simp [Scheme.Hom.imageι]
  have : IsReduced g.ker.subscheme := isReduced_of_isOpenImmersion (asIso g.toImage).inv
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme g.ker g.ker.support rfl

/-- **Integral curves are proper curves.** On a proper `k`-scheme, every one-dimensional integral
closed subscheme `i : C ⟶ X` has, for every invertible sheaf, the same degree as some proper
curve. -/
private theorem exists_properCurve_degreeOn_eq {X C : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsProper sX] (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
    (hC : topologicalKrullDim C = 1) :
    ∃ Γ : ProperCurve sX, ∀ (L : X.Modules)
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      degreeOn k sX i hC.le L = Γ.degree k L := by
  set x : X := i (genericPoint C)
  have hrange : Set.range i = closure ({x} : Set X) := by
    rw [← Set.image_univ, ← (genericPoint_spec C).def, ← i.isClosedEmbedding.closure_image_eq,
      Set.image_singleton]
  have hsupp : i.ker.support = TopologicalSpace.Closeds.closure ({x} : Set X) := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_closure, hrange, closure_closure]
  have hker : i.ker = (curveSubschemeAtι x).ker := by
    rw [ker_eq_vanishingIdeal_support i, hsupp, Scheme.IdealSheafData.ker_subschemeι]
  haveI := IsClosedImmersion.isIso_lift (curveSubschemeAtι x) i hker.symm
  let e : C ≅ curveSubschemeAt x :=
    asIso (IsClosedImmersion.lift (curveSubschemeAtι x) i hker.symm.le)
  have hdimx : topologicalKrullDim (curveSubschemeAt x) = 1 := by
    rw [← hC]
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm
  exact ⟨⟨x, isProperCurve_of_isProper sX hdimx⟩, fun L _ =>
    MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i _ hC.le hdimx.le e
      (IsClosedImmersion.lift_fac _ _ _) L⟩

variable {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X] (hC : ∀ D : Divisor X, D.IsCartier)

/-- **The intersection number with a curve is linear in the divisor.** If every divisor is
Cartier, `(B · C) = ∑_P B(P) deg_C 𝒪_X(P)`. -/
private theorem intersectionNumber_eq_sum {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (B : QDivisor X) (hB : B.IsQCartier) :
    B.intersectionNumber k sX i hdim hB =
      B.sum fun P c => c * (Divisor.degreeOn k sX i hdim (Finsupp.single P 1) (hC _) : ℚ) := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hB.exists_pos
  let φ : Divisor X →+ ℤ := AddMonoidHom.mk' (fun D => D.degreeOn k sX i hdim (hC D))
    fun D D' => Divisor.degreeOn_add k sX i hdim D D' (hC D) (hC D')
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hdim B hB hm E hEc hE]
  change (φ E : ℚ) / m = _
  have hE' : (φ E : ℚ) =
      (Divisor.toQDivisor E).sum fun P c => c * (φ (Finsupp.single P 1) : ℚ) := by
    rw [sum_toQDivisor E (fun P c => c * (φ (Finsupp.single P 1) : ℚ)) fun _ => zero_mul _,
      map_eq_sum_single φ E]
    push_cast
    rfl
  rw [hE', hE, ← Int.cast_smul_eq_zsmul ℚ, Finsupp.sum_smul_index (fun _ => zero_mul _),
    Int.cast_natCast, Finsupp.sum, Finsupp.sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun P _ => ?_
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  rfl

/-- **Numerical triviality is tested on proper curves.** On a proper `k`-scheme on which every
divisor is Cartier, a `ℚ`-divisor is numerically trivial if and only if it has degree zero on
every proper curve. -/
private theorem isNumericallyTrivial_iff_forall_properCurve [IsProper sX] (B : QDivisor X)
    (hB : B.IsQCartier) :
    B.IsNumericallyTrivial k sX ↔ ∀ Γ : ProperCurve sX,
      (B.sum fun P c => c *
        (Divisor.degreeOn k sX Γ.ι Γ.dim_le (Finsupp.single P 1) (hC _) : ℚ)) = 0 := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  rw [QDivisor.isNumericallyTrivial_iff]
  constructor
  · rintro ⟨_, h⟩ Γ
    haveI : IsIntegral Γ.scheme :=
      StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
        isIrreducible_singleton.closure
    have := h Γ.scheme Γ.ι Γ.dim_eq
    rwa [intersectionNumber_eq_sum sX hC] at this
  · intro h
    refine ⟨hB, fun C i _ _ _ hCdim => ?_⟩
    obtain ⟨Γ, hΓ⟩ := exists_properCurve_degreeOn_eq sX i hCdim
    rw [intersectionNumber_eq_sum sX hC, ← h Γ]
    refine Finsupp.sum_congr fun P _ => ?_
    haveI := (hC (Finsupp.single P 1)).isInvertibleModule_divisorialSheaf
    exact congrArg (fun n : ℤ => B P * (n : ℚ)) (hΓ (Divisor.divisorialSheaf (Finsupp.single P 1)))

end Curves

/-! ### The four assertions -/

section Package

variable (k : Type) [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  (hd : topologicalKrullDim X ≤ (2 : ℕ)) (hC : ∀ D : Divisor X, D.IsCartier)

/-- The bilinear extension `(A · B) = ∑_{C, C'} A(C) B(C') (C · C')` of the intersection numbers
of prime divisors to `ℚ`-divisors. -/
private noncomputable def qPair (A B : QDivisor X) : ℚ :=
  A.sum fun C a => B.sum fun C' b => a * b *
    (Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd ![Finsupp.single C 1, Finsupp.single C' 1]
      (fun _ => hC _) : ℚ)

/-- On integral divisors the pairing is the intersection number. -/
private theorem qPair_toQDivisor (D E : Divisor X) :
    qPair k sX hd hC (Divisor.toQDivisor D) (Divisor.toQDivisor E) =
      Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd ![D, E] (fun _ => hC _) := by
  rw [intersectionNumberOn_eq_sum_sum k sX hd hC, qPair, sum_toQDivisor]
  · rw [Finsupp.sum, Finsupp.sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [sum_toQDivisor]
    · rw [Finsupp.sum, Finsupp.sum, Int.cast_sum]
      push_cast
      rfl
    · intro P'
      simp
  · intro P
    simp [Finsupp.sum]

/-- The pairing in coordinates on a finite set of prime divisors containing both supports. -/
private theorem qPair_eq_sum_fin {T : Finset (PrimeDivisor X)} (e : Fin T.card ≃ T)
    (D D' : QDivisor X) (hD : D.support ⊆ T) (hD' : D'.support ⊆ T) :
    qPair k sX hd hC D D' = ∑ i, ∑ j, D (e i) * D' (e j) *
      (Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd
        ![Finsupp.single (e i).1 1, Finsupp.single (e j).1 1] (fun _ => hC _) : ℚ) := by
  rw [qPair, sum_eq_sum_fin e D hD _ (fun _ => by simp [Finsupp.sum])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_eq_sum_fin e D' hD' _ (fun _ => by simp)]

/-- `Divisor.toQDivisor` of a prime divisor. -/
private theorem toQDivisor_single (P : PrimeDivisor X) :
    Divisor.toQDivisor (Finsupp.single P 1) = Finsupp.single P (1 : ℚ) := by
  change Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) _ = _
  rw [Finsupp.mapRange_single]
  simp

/-- **Distinct curves** meet nonnegatively, and in degree zero exactly when disjoint. -/
private theorem intersectionNumberOn_nonneg_and_eq_zero_iff_of_ne
    (hX : IsProjectiveVariety k sX) (hdim : topologicalKrullDim X = 2) (hsm : IsSmoothScheme sX)
    (C C' : PrimeDivisor X) (hne : C ≠ C') :
    0 ≤ Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd ![Finsupp.single C 1, Finsupp.single C' 1]
        (fun _ => hC _) ∧
      (Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd ![Finsupp.single C 1, Finsupp.single C' 1]
        (fun _ => hC _) = 0 ↔ Disjoint C.support C'.support) := by
  have heff : ∀ P : PrimeDivisor X,
      DivisorWithCoeffs.IsEffective (Divisor.toQDivisor (Finsupp.single P 1)) := by
    intro P E
    rw [toQDivisor_single, DivisorWithCoeffs.coeff_apply]
    exact (Finsupp.single_nonneg.2 zero_le_one : (0 : QDivisor X) ≤ _) E
  have hsupp : ∀ P : PrimeDivisor X,
      (Divisor.toQDivisor (Finsupp.single P 1)).support = {P} := fun P => by
    rw [toQDivisor_single, Finsupp.support_single_ne_zero _ one_ne_zero]
  have hdisj : Disjoint (Divisor.toQDivisor (Finsupp.single C 1)).support
      (Divisor.toQDivisor (Finsupp.single C' 1)).support := by
    rwa [hsupp, hsupp, Finset.disjoint_singleton]
  obtain ⟨x, hx, hnn, hiff⟩ := MMP.Flips.intersectionNumber_nonneg_and_eq_zero_iff_disjoint k sX
    hX hdim (QDivisor.isQCartier_toQDivisor (hC _)) (heff C) (heff C') hdisj
  obtain ⟨hp, hdim', hA', hxC⟩ := hx C' (by rw [hsupp, Finset.mem_singleton])
  have hsum : ((Divisor.toQDivisor (Finsupp.single C' 1)).sum fun C b => b * x C) = x C' := by
    rw [toQDivisor_single, Finsupp.sum_single_index (by simp), one_mul]
  have hval : (Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd
      ![Finsupp.single C 1, Finsupp.single C' 1] (fun _ => hC _) : ℚ) = x C' := by
    rw [← hxC, QDivisor.intersectionNumber_toQDivisor k sX _ hdim' _ (hC _) hA']
    haveI := hp
    rw [intersectionNumberOn_single_eq_degreeOn k sX hd hC hsm _ C' hdim']
  refine ⟨?_, ?_⟩
  · rw [hsum, ← hval] at hnn
    exact_mod_cast hnn
  · rw [← Int.cast_eq_zero (α := ℚ), hval, ← hsum, hiff, Divisor.supp_toQDivisor,
      Divisor.supp_toQDivisor, DivisorWithCoeffs.coe_supp, DivisorWithCoeffs.coe_supp,
      Finsupp.support_single_ne_zero _ one_ne_zero, Finsupp.support_single_ne_zero _ one_ne_zero]
    simp

/-- **Hodge index.** If `(A²) > 0` and `(A · B) = 0`, then `(B²) ≤ 0`, with equality exactly when
`B` is numerically trivial. -/
private theorem qPair_self_nonpos_and_eq_zero_iff [IsAlgClosed k] [Smooth sX]
    (hX : IsProjectiveVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hQC : ∀ B : QDivisor X, B.IsQCartier) (A B : QDivisor X) (hA : 0 < qPair k sX hd hC A A)
    (hAB : qPair k sX hd hC A B = 0) :
    qPair k sX hd hC B B ≤ 0 ∧ (qPair k sX hd hC B B = 0 ↔ B.IsNumericallyTrivial k sX) := by
  classical
  set T : Finset (PrimeDivisor X) := A.support ∪ B.support
  let e : Fin T.card ≃ T := T.equivFin.symm
  let M : Fin T.card → X.Modules := fun j => Divisor.divisorialSheaf (Finsupp.single (e j).1 1)
  haveI hM : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j) := fun j =>
    (hC _).isInvertibleModule_divisorialSheaf
  have hpair : ∀ i j, pair k sX hd (M i) (M j) = Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd
      ![Finsupp.single (e i).1 1, Finsupp.single (e j).1 1] (fun _ => hC _) := fun i j =>
    (intersectionNumberOn_eq_pair k sX hd hC _ _).symm
  have hAT : A.support ⊆ T := Finset.subset_union_left
  have hBT : B.support ⊆ T := Finset.subset_union_right
  have hAA : qPair k sX hd hC A A =
      ∑ i, ∑ j, A (e i) * A (e j) * (pair k sX hd (M i) (M j) : ℚ) := by
    rw [qPair_eq_sum_fin k sX hd hC e A A hAT hAT]
    simp only [hpair]
  have hBB : qPair k sX hd hC B B =
      ∑ i, ∑ j, B (e i) * B (e j) * (pair k sX hd (M i) (M j) : ℚ) := by
    rw [qPair_eq_sum_fin k sX hd hC e B B hBT hBT]
    simp only [hpair]
  have hABs : ∑ j, B (e j) * ∑ i, A (e i) * (pair k sX hd (M i) (M j) : ℚ) =
      qPair k sX hd hC A B := by
    rw [qPair_eq_sum_fin k sX hd hC e A B hAT hBT]
    simp only [hpair, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have H := MMP.Mori.sheafCombinationIntersectionNumber_two_nonpos_of_pos k sX hX hdim
    (fun j => A (e j)) M (fun j => B (e j)) M
  rw [sheafCombinationIntersectionNumber_two_eq_sum k sX hd,
    sheafCombinationIntersectionNumber_two_eq_sum k sX hd] at H
  simp only [sheafCombinationIntersectionNumber_one_eq_sum k sX hd] at H
  obtain ⟨h1, h2⟩ := H (by rwa [← hAA]) (by rwa [hABs])
  refine ⟨by rwa [hBB], ?_⟩
  rw [hBB, h2, isNumericallyTrivial_iff_forall_properCurve sX hC B (hQC B)]
  refine forall_congr' fun Γ => ?_
  rw [sum_eq_sum_fin e B hBT
    (fun P c => c * (Divisor.degreeOn k sX Γ.ι Γ.dim_le (Finsupp.single P 1) (hC _) : ℚ))
    (fun _ => zero_mul _)]
  rfl

/-- **Nef divisors** have nonnegative square. -/
private theorem qPair_self_nonneg_of_isNef (hX : IsProjectiveVariety k sX)
    [IsIntegral X] (hdim : topologicalKrullDim X = 2) (A : QDivisor X) (hAnef : A.IsNef k sX) :
    0 ≤ qPair k sX hd hC A A := by
  haveI := fun D : Divisor X => (hC D).isInvertibleModule_divisorialSheaf
  obtain ⟨hA, hpos⟩ := hAnef
  obtain ⟨m, hm, E, hE, hEc⟩ := hA.exists_pos
  have hnef : MMP.Mori.IsNef k sX E.divisorialSheaf := by
    intro C i _ _ _ hCdim
    have h := hpos C i hCdim
    rw [QDivisor.intersectionNumber_eq_of_smul k sX i hCdim.le A hA hm E hEc hE] at h
    rw [le_div_iff₀ (by exact_mod_cast hm), zero_mul] at h
    exact_mod_cast h
  have hK := MMP.Mori.sheafSelfIntersectionNumber_nonneg_of_isNef k sX hX E.divisorialSheaf
    hnef X (𝟙 X) (d := 2) hdim
  have h1 : sheafSelfIntersectionNumber k sX (𝟙 X) 2 hdim.le E.divisorialSheaf =
      Divisor.intersectionNumberOn k sX (𝟙 X) 2 hd ![E, E] (fun _ => hC _) := by
    rw [intersectionNumberOn_eq_pair k sX hd hC, sheafSelfIntersectionNumber]
    exact sheafIntersectionNumber_two_eq_pair k sX hd _ _
  have hEE : (sheafSelfIntersectionNumber k sX (𝟙 X) 2 hdim.le E.divisorialSheaf : ℚ) =
      m * m * qPair k sX hd hC A A := by
    rw [h1, ← qPair_toQDivisor, hE, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    exact sum_sum_smul A (m : ℚ) _
  have : (0 : ℚ) ≤ m * m * qPair k sX hd hC A A := by
    rw [← hEE]
    exact_mod_cast hK
  exact nonneg_of_mul_nonneg_right this (by positivity)

/-- An invertible sheaf is numerically trivial exactly when it has degree zero on every proper
curve. -/
private theorem numericalCurveClasses_degree_eq_zero_iff (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    NumericalCurveClasses.degree sX L = 0 ↔ ∀ Γ : ProperCurve sX, Γ.degree k L = 0 := by
  constructor
  · intro h Γ
    have := LinearMap.congr_fun h (OneCycle.numericalClass sX (Finsupp.single Γ 1))
    change NumericalCurveClasses.degree sX _ _ = 0 at this
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_apply,
      Finsupp.sum_single_index (by simp), one_mul] at this
    exact_mod_cast this
  · intro h
    refine LinearMap.ext fun z => ?_
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    change NumericalCurveClasses.degree sX _ _ = 0
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_apply]
    simp [h]

include hC in
/-- **The numerical lattice.** The divisors modulo numerical equivalence form a finitely
generated group, through `D ↦ (z ↦ (𝒪_X(D) · z))` into the numerical divisor group. -/
private theorem exists_addSubgroup_mem_iff_isNumericallyTrivial_and_fg [IsAlgClosed k]
    [CharZero k] (hX : IsProjectiveVariety k sX) (hQC : ∀ B : QDivisor X, B.IsQCartier) :
    ∃ N : AddSubgroup (Divisor X),
      (∀ D : Divisor X, D ∈ N ↔ (Divisor.toQDivisor D).IsNumericallyTrivial k sX) ∧
      AddGroup.FG (Divisor X ⧸ N) ∧
      (Set.range fun C : PrimeDivisor X =>
        (QuotientAddGroup.mk (Finsupp.single C 1) : Divisor X ⧸ N)).Countable := by
  haveI hinv := fun D : Divisor X => (hC D).isInvertibleModule_divisorialSheaf
  haveI : MMP.Mori.IsProperVariety k sX := (MMP.Mori.isProperVariety_iff k sX).2
    ⟨((MMP.Mori.isProjectiveVariety_iff k sX).1 hX).1, inferInstance⟩
  haveI : Module.Finite ℤ (numericalDivisorGroup sX) :=
    (MMP.Mori.numericalDivisorGroup_free_finrank_and_basis.{0} sX).2.1
  have hdegadd : ∀ (D D' : Divisor X) (Γ : ProperCurve sX),
      Γ.degree k (D + D').divisorialSheaf =
        Γ.degree k D.divisorialSheaf + Γ.degree k D'.divisorialSheaf := fun D D' Γ =>
    Divisor.degreeOn_add k sX Γ.ι Γ.dim_le D D' (hC D) (hC D')
  let Φ : Divisor X →+ Module.Dual ℝ (NumericalCurveClasses sX) :=
    AddMonoidHom.mk' (fun D => NumericalCurveClasses.degree sX D.divisorialSheaf) fun D D' => by
      refine LinearMap.ext fun z => ?_
      obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
      rw [LinearMap.add_apply, NumericalCurveClasses.degree_numericalClass,
        NumericalCurveClasses.degree_numericalClass, NumericalCurveClasses.degree_numericalClass,
        OneCycle.degree_apply, OneCycle.degree_apply, OneCycle.degree_apply, ← Finsupp.sum_add]
      refine Finsupp.sum_congr fun Γ _ => ?_
      rw [hdegadd]
      push_cast
      ring
  have hmemΦ : ∀ D, Φ D ∈ numericalDivisorGroup sX := fun D =>
    AddSubgroup.subset_closure ⟨D.divisorialSheaf, hinv D, rfl⟩
  let Φ' : Divisor X →+ numericalDivisorGroup sX := Φ.codRestrict _ hmemΦ
  have hΦ0 : ∀ D, Φ D = 0 ↔ ∀ Γ : ProperCurve sX, Γ.degree k D.divisorialSheaf = 0 := fun D =>
    numericalCurveClasses_degree_eq_zero_iff k sX D.divisorialSheaf
  have hfg : AddGroup.FG (Divisor X ⧸ Φ'.ker) := by
    have h1 : (Φ'.range.toIntSubmodule).FG := IsNoetherian.noetherian _
    have h2 : Module.Finite ℤ Φ'.range.toIntSubmodule := Module.Finite.iff_fg.mpr h1
    have h3 : AddGroup.FG Φ'.range := Module.Finite.iff_addGroup_fg.mp h2
    exact AddGroup.fg_of_surjective
      (f := (QuotientAddGroup.quotientKerEquivRange Φ').symm.toAddMonoidHom)
      (QuotientAddGroup.quotientKerEquivRange Φ').symm.surjective
  refine ⟨Φ'.ker, fun D => ?_, hfg, ?_⟩
  · rw [AddMonoidHom.mem_ker, ← ZeroMemClass.coe_eq_zero, AddMonoidHom.codRestrict_apply, hΦ0,
      isNumericallyTrivial_iff_forall_properCurve sX hC _ (hQC _)]
    refine forall_congr' fun Γ => ?_
    rw [← intersectionNumber_eq_sum sX hC Γ.ι Γ.dim_le _ (hQC _),
      QDivisor.intersectionNumber_toQDivisor k sX Γ.ι Γ.dim_le D (hC D), Int.cast_eq_zero]
    exact Iff.rfl
  · haveI : Module.Finite ℤ (Divisor X ⧸ Φ'.ker) := Module.Finite.iff_addGroup_fg.mpr hfg
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' ℤ (Divisor X ⧸ Φ'.ker)
    haveI : Countable (Divisor X ⧸ Φ'.ker) := hg.countable
    exact Set.to_countable _

end Package

/-- **The elementary intersection package of a smooth projective surface.** Let `X` be a smooth
projective surface over an algebraically closed field `k` of characteristic zero. Every divisor
on `X` is Cartier; writing `(C · C')` for the intersection number of prime divisors and
`(A · B) = ∑ A(C) B(C') (C · C')` for its bilinear extension to `ℚ`-divisors:
distinct integral curves satisfy `(C · C') ≥ 0`, with equality iff they are disjoint; if
`(A²) > 0` and `(A · B) = 0` then `(B²) ≤ 0`, with equality iff `B` is numerically trivial; a nef
`ℚ`-divisor has nonnegative square; and the integral divisors modulo numerical equivalence form a
finitely generated group, in which the classes of the integral curves form a countable set. -/
@[mmp "lem_mmp_fa15_smooth_surface_intersection_package"]
public theorem exists_forall_isCartier_and_intersectionNumberOn_of_smooth
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [Smooth sX]
    (hdim : topologicalKrullDim X = 2) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsNormal (Spec (.of k)) :=
      isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
    haveI : IsNormal X := isNormal_of_smooth sX
    ∃ hC : ∀ D : Divisor X, D.IsCartier,
      let I : PrimeDivisor X → PrimeDivisor X → ℤ := fun C C' =>
        Divisor.intersectionNumberOn k sX (𝟙 X) 2 hdim.le
          ![Finsupp.single C 1, Finsupp.single C' 1] fun _ => hC _
      let Q : QDivisor X → QDivisor X → ℚ := fun A B =>
        A.sum fun C a => B.sum fun C' b => a * b * I C C'
      (∀ C C' : PrimeDivisor X, C ≠ C' →
        0 ≤ I C C' ∧ (I C C' = 0 ↔ Disjoint C.support C'.support)) ∧
      (∀ A B : QDivisor X, 0 < Q A A → Q A B = 0 →
        Q B B ≤ 0 ∧ (Q B B = 0 ↔ B.IsNumericallyTrivial k sX)) ∧
      (∀ A : QDivisor X, A.IsNef k sX → 0 ≤ Q A A) ∧
      ∃ N : AddSubgroup (Divisor X),
        (∀ D : Divisor X, D ∈ N ↔ (Divisor.toQDivisor D).IsNumericallyTrivial k sX) ∧
        AddGroup.FG (Divisor X ⧸ N) ∧
        (Set.range fun C : PrimeDivisor X =>
          (QuotientAddGroup.mk (Finsupp.single C 1) : Divisor X ⧸ N)).Countable := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  haveI : IsNormal X := isNormal_of_smooth sX
  have hX : IsProjectiveVariety k sX := inferInstance
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hsm : IsSmoothScheme sX := (isSmoothScheme_iff sX).2 inferInstance
  have hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x =>
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
    (MMP.Resolution.Bridges.uniqueFactorization_and_exists_isWeilDivisorOfCartier.1 _).2
  have hC : ∀ D : Divisor X, D.IsCartier := by
    intro D
    induction D using Finsupp.induction_linear with
    | zero => exact Divisor.isCartier_zero
    | add D D' hD hD' => exact hD.add hD'
    | single P n =>
      rw [← Finsupp.smul_single_one]
      exact (MMP.Threefold.Mori.isCartier_single_of_forall_uniqueFactorizationMonoid hUFD P).zsmul n
  have hQC : ∀ B : QDivisor X, B.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  exact ⟨hC, intersectionNumberOn_nonneg_and_eq_zero_iff_of_ne k sX hdim.le hC hX hdim hsm,
    qPair_self_nonpos_and_eq_zero_iff k sX hdim.le hC hX hdim hQC,
    qPair_self_nonneg_of_isNef k sX hdim.le hC hX hdim,
    exists_addSubgroup_mem_iff_isNumericallyTrivial_and_fg k sX hC hX hQC⟩

end MMP.Mori
