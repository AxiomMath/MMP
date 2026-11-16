module

public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SmoothCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroDegreeZero
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections

/-!
# Low-genus curves, nef divisors on threefolds, and the Nakai criterion on surfaces

Three results used in the abundance argument for threefolds.

Let `C` be a smooth proper geometrically connected curve over a field `K`. Smoothness makes `C`
geometrically normal, so by properness and geometric connectedness `H⁰(C, 𝒪_C) = K`. If `C` has
genus zero, a degree-zero invertible module has `χ = 1`, hence a nonzero section, hence is
trivial. If `C` has genus one, `h⁰(Ω¹_{C/K}) = g = 1` and `deg Ω¹_{C/K} = 2g - 2 = 0`, so a
nonzero section trivialises `Ω¹_{C/K}`. No rational point is assumed.

Let `X` be a normal projective threefold, `L` a nef `ℚ`-Cartier divisor with numerical dimension
`ν(X, L) ≥ 2` and `H` ample. Then `(L² · H) > 0`. Write `D₀` for an ample Cartier multiple of
`H` and `E` for a Cartier multiple of `L`. By the definition of `ν` there is a subvariety `V` of
dimension `d ∈ {2, 3}` with `(E^d · V) > 0` (Kleiman). If `d = 2`, a divisor `Y ∈ |N D₀|`
containing `V` gives `N (D₀ · E · E) ≥ ℓ_V (E² · V) > 0`; if `d = 3`, an effective divisor
`Y ∈ |aD₀ - E|` gives `a (D₀ · E · E) = (Y · E · E) + (E³) > 0`.

Let `S` be a projective surface and `L` invertible with `(L²) > 0` and `deg_C L > 0` for every
integral curve `C ⊆ S`. The positive-dimensional closed integral subschemes of `S` are its
integral curves and `S` itself, so the Nakai–Moishezon criterion shows that `L` is ample.

## Main results

* `MMP.isTrivial_of_genus_eq_zero_and_isTrivial_relativeDifferentials_of_genus_eq_one`:
  degree-zero line bundles on a genus-zero curve, and the canonical sheaf of a genus-one curve,
  are trivial.
* `MMP.Flips.intersectionNumberOn_pos_of_two_le_numericalDimension`: `(L² · H) > 0` for `L` nef
  with `ν ≥ 2` and `H` ample.
* `MMP.Flips.isAmple_of_sheafSelfIntersectionNumber_pos_of_degreeOn_pos`: the Nakai criterion on
  a projective surface.

## Implementation notes

The genus is `AlgebraicGeometry.genus` (`dim_K H¹(C, 𝒪_C)`), the degree of an invertible module
on a curve is `AlgebraicGeometry.invertibleCurveDegree` (`χ(L) - χ(𝒪_C)`), and the canonical
line bundle of a smooth curve is `Scheme.Hom.relativeDifferentials f`.

The `ℚ`-divisors `L` and `H` have no intersection number of their own; `(L² · H)` is computed
from integral Cartier multiples `E = mL` and `F = nH`, `m, n > 0`, as `(E · E · F · X)`, which is
`m² n (L² · H)`, and positivity is asserted for every such choice. The numerical dimension
`MMP.Flips.numericalDimension` is defined for normal proper varieties, so `X` is normal.

On the surface, `(L²)` is `MMP.Mori.sheafSelfIntersectionNumber` against `S`, and `deg_C L` is
`MMP.Mori.degreeOn` along a closed immersion `i : C ⟶ S` from an integral scheme of dimension
one.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], chapter 15
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 1.37
* [Stacks Project, Tag 0C6M](https://stacks.math.columbia.edu/tag/0C6M)
* [Stacks Project, Tag 0C1A](https://stacks.math.columbia.edu/tag/0C1A)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP

/-- On a proper integral curve over `K`, an invertible module with `h⁰ > 0` and nonpositive
degree is trivial. -/
private theorem isTrivial_of_finrank_pos_of_invertibleCurveDegree_nonpos
    {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsProper f] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1) (L : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.property L]
    (hpos : 0 < Module.finrank K (cohomologyOverField K f L 0))
    (hdeg : invertibleCurveDegree K f hdim L ≤ 0) :
    SheafOfModules.IsTrivial C.presheaf C.ringCatSheaf.property L := by
  have := Module.nontrivial_of_finrank_pos hpos
  have := (cohomologyOverFieldZeroEquivSections K f L).injective.nontrivial
  obtain ⟨t, ht⟩ := exists_ne (0 : Γ(L, ⊤))
  letI : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    inferInstanceAs (SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.property L)
  exact isTrivial_of_invertibleCurveDegree_nonpos K f hdim L
    (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf L t)
    (ne_of_eq_of_ne (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top L t) ht) hdeg

/-- On a smooth proper curve with `H⁰(C, 𝒪_C) = K` and genus one, `Ω¹_{C/K}` is trivial:
`h⁰(Ω¹) = g = 1` and `deg Ω¹ = 2g - 2 = 0`. -/
private theorem isTrivial_relativeDifferentials_of_genus_eq_one
    {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [Smooth f]
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (hg : genus f = 1) :
    SheafOfModules.IsTrivial C.presheaf C.ringCatSheaf.property
      (Scheme.Hom.relativeDifferentials f) := by
  have := smoothOfRelativeDimension_one_of_isCurve K f
  have := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials f
  have : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Scheme.Hom.relativeDifferentials f) :=
    Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one C.toRingedSpace _
  have hdeg := curveDegree_relativeDifferentials_eq_two_mul_genus_sub_two f
  refine isTrivial_of_finrank_pos_of_invertibleCurveDegree_nonpos f
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le _ ?_ ?_
  · rw [finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus, hg]; exact one_pos
  · rw [invertibleCurveDegree_eq_curveDegree, hdeg, hg]
    norm_num

/-- **Line bundles on curves of genus zero and one.** Let `f : C ⟶ Spec K` be a smooth proper
geometrically connected curve over a field `K`. If `C` has genus zero, every invertible
`𝒪_C`-module of degree zero is isomorphic to `𝒪_C`; if `C` has genus one, the canonical sheaf
`Ω¹_{C/K}` is isomorphic to `𝒪_C`. -/
@[mmp "lem_mmp_fa15_low_genus_line_bundles"]
public theorem isTrivial_of_genus_eq_zero_and_isTrivial_relativeDifferentials_of_genus_eq_one
    {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [Smooth f]
    [IsProper f] [GeometricallyConnected f] :
    (genus f = 0 → ∀ (L : C.Modules)
        [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.property L],
        invertibleCurveDegree K f (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)).le L = 0 →
          SheafOfModules.IsTrivial C.presheaf C.ringCatSheaf.property L) ∧
      (genus f = 1 → SheafOfModules.IsTrivial C.presheaf C.ringCatSheaf.property
        (Scheme.Hom.relativeDifferentials f)) := by
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) := by
    have h := (isIso_globalSections_tfae_geometricallyConnected_irreducible_integral K f
      (isGeometricallyNormal_of_smooth f)).out 1 2
    exact h.mpr inferInstance
  exact ⟨fun hg L _ hdeg =>
    isTrivial_of_genus_eq_zero_of_invertibleCurveDegree_eq_zero K f L hg hdeg,
    isTrivial_relativeDifferentials_of_genus_eq_one f⟩

end MMP

namespace MMP.Flips

open MMP.Mori TopologicalSpace Opposite

section NefSquare

variable {k : Type u} [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
  [IsLocallyNoetherian X] [IsNormal X] (i : Z ⟶ X) [IsClosedImmersion i]

/-- Intersection numbers of Cartier divisors are additive in each slot. -/
private theorem intersectionNumberOn_update_add (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (D : Fin d → Divisor X) (hD : ∀ j, (D j).IsCartier) (j : Fin d) {A B : Divisor X}
    (hA : A.IsCartier) (hB : B.IsCartier) (hAB : D j = A + B) :
    Divisor.intersectionNumberOn k sX i d hd D hD =
      Divisor.intersectionNumberOn k sX i d hd (Function.update D j A)
          (by intro t; rcases eq_or_ne t j with rfl | h <;> simp_all) +
        Divisor.intersectionNumberOn k sX i d hd (Function.update D j B)
          (by intro t; rcases eq_or_ne t j with rfl | h <;> simp_all) := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := fun j => (hD j).isInvertibleModule_divisorialSheaf
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hB.isInvertibleModule_divisorialSheaf
  unfold Divisor.intersectionNumberOn
  simp only [Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  rw [intersectionNumber_update_tensor k sX i d hd j (fun t => (D t).divisorialSheaf)
    A.divisorialSheaf B.divisorialSheaf
    (eqToIso (congrArg Divisor.divisorialSheaf hAB) ≪≫ (hA.divisorialSheafTensorIso hB).symm)]
  haveI := isInvertible_update (fun t => (D t).divisorialSheaf) j A.divisorialSheaf
  haveI := isInvertible_update (fun t => (D t).divisorialSheaf) j B.divisorialSheaf
  have hA' : ∀ t, (Function.update D j A t).IsCartier := by
    intro t; rcases eq_or_ne t j with rfl | h <;> simp_all
  have hB' : ∀ t, (Function.update D j B t).IsCartier := by
    intro t; rcases eq_or_ne t j with rfl | h <;> simp_all
  haveI := fun t => (hA' t).isInvertibleModule_divisorialSheaf
  haveI := fun t => (hB' t).isInvertibleModule_divisorialSheaf
  congr 1
  · refine intersectionNumber_congr_family k sX i d hd ?_
    funext t; rcases eq_or_ne t j with rfl | h <;> simp [*]
  · refine intersectionNumber_congr_family k sX i d hd ?_
    funext t; rcases eq_or_ne t j with rfl | h <;> simp [*]

/-- Intersection numbers of Cartier divisors depend only on the family of divisors. -/
private theorem intersectionNumberOn_congr {d : ℕ} {hd : topologicalKrullDim Z ≤ d}
    {D D' : Fin d → Divisor X} (hD : ∀ j, (D j).IsCartier) (h : D = D') :
    Divisor.intersectionNumberOn k sX i d hd D hD =
      Divisor.intersectionNumberOn k sX i d hd D' (h ▸ hD) := by
  subst h; rfl

/-- Intersection numbers of Cartier divisors are homogeneous in each slot. -/
private theorem intersectionNumberOn_eq_mul_of_eq_nsmul (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (D : Fin d → Divisor X) (hD : ∀ j, (D j).IsCartier) (j : Fin d) {A : Divisor X}
    (hA : A.IsCartier) (n : ℕ) (h : D j = n • A) :
    Divisor.intersectionNumberOn k sX i d hd D hD =
      n * Divisor.intersectionNumberOn k sX i d hd (Function.update D j A)
          (by intro t; rcases eq_or_ne t j with rfl | h <;> simp_all) := by
  induction n generalizing D with
  | zero =>
    have h0 := intersectionNumberOn_update_add sX i d hd D hD j
      (Divisor.isCartier_zero (X := X)) (Divisor.isCartier_zero (X := X)) (by simpa using h)
    have h1 : Function.update D j 0 = D := by
      funext t; rcases eq_or_ne t j with rfl | h' <;> simp [*]
    rw [intersectionNumberOn_congr sX i _ h1] at h0
    simp only [CharP.cast_eq_zero, zero_mul]
    omega
  | succ n ih =>
    have hn : (n • A).IsCartier := hA.nsmul n
    rw [intersectionNumberOn_update_add sX i d hd D hD j hn hA (by rw [h, succ_nsmul])]
    rw [ih (Function.update D j (n • A)) _ (by simp)]
    simp only [Function.update_idem]
    push_cast; ring

/-- The `d`-th self-intersection of a multiple: `((nG)^d · Z) = n^d (G^d · Z)`. -/
private theorem intersectionNumberOn_const_nsmul (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    {G : Divisor X} (hG : G.IsCartier) (n : ℕ) :
    Divisor.intersectionNumberOn k sX i d hd (fun _ => n • G) (fun _ => hG.nsmul n) =
      n ^ d * Divisor.intersectionNumberOn k sX i d hd (fun _ => G) (fun _ => hG) := by
  classical
  suffices key : ∀ s : Finset (Fin d),
      Divisor.intersectionNumberOn k sX i d hd (fun t => if t ∈ s then n • G else G)
          (fun t => by split_ifs; exacts [hG.nsmul n, hG]) =
        n ^ s.card * Divisor.intersectionNumberOn k sX i d hd (fun _ => G) (fun _ => hG) by
    have := key Finset.univ
    simpa using this
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [intersectionNumberOn_eq_mul_of_eq_nsmul sX i d hd _ _ a hG n (by simp)]
    have h1 : Function.update (fun t => if t ∈ insert a s then n • G else G) a G =
        fun t => if t ∈ s then n • G else G := by
      funext t; rcases eq_or_ne t a with rfl | h' <;> simp [*]
    rw [intersectionNumberOn_congr sX i _ h1, ih, Finset.card_insert_of_notMem ha]
    push_cast; ring

/-- Intersection numbers of Cartier divisors are symmetric. -/
private theorem intersectionNumberOn_comp_perm (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (D : Fin d → Divisor X) (hD : ∀ j, (D j).IsCartier) (σ : Equiv.Perm (Fin d)) :
    Divisor.intersectionNumberOn k sX i d hd (fun j => D (σ j)) (fun j => hD (σ j)) =
      Divisor.intersectionNumberOn k sX i d hd D hD := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := fun j => (hD j).isInvertibleModule_divisorialSheaf
  unfold Divisor.intersectionNumberOn
  simp only [Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact intersectionNumber_comp_perm k sX i d hd (fun j => (D j).divisorialSheaf) σ

/-- Against a constant family, `Divisor.intersectionNumberOn` is the self-intersection number
of `𝒪_X(G)`. -/
private theorem intersectionNumberOn_const [CompactSpace X] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ d) {G : Divisor X} (hG : G.IsCartier) :
    haveI := hG.isInvertibleModule_divisorialSheaf
    Divisor.intersectionNumberOn k sX i d hd (fun _ => G) (fun _ => hG) =
      intersectionNumber k sX i d hd (fun _ => G.divisorialSheaf) := by
  haveI := hG.isInvertibleModule_divisorialSheaf
  unfold Divisor.intersectionNumberOn
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber]

/-- `(A · E · E)` as the intersection number of the invertible sheaves `𝒪_X(A)`, `𝒪_X(E)`. -/
private theorem intersectionNumberOn_triple [CompactSpace X] (hd : topologicalKrullDim Z ≤ 3)
    {A E : Divisor X}
    (hA : A.IsCartier) (hE : E.IsCartier) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    haveI := hE.isInvertibleModule_divisorialSheaf
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (![A.divisorialSheaf, E.divisorialSheaf, E.divisorialSheaf] t) := by
      intro t; fin_cases t <;> assumption
    Divisor.intersectionNumberOn k sX i 3 hd ![A, E, E] (by intro j; fin_cases j <;> assumption) =
      intersectionNumber k sX i 3 hd
        ![A.divisorialSheaf, E.divisorialSheaf, E.divisorialSheaf] := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hE.isInvertibleModule_divisorialSheaf
  have hA3 : ∀ j, (![A, E, E] j).IsCartier := by intro j; fin_cases j <;> assumption
  haveI := fun j => (hA3 j).isInvertibleModule_divisorialSheaf
  haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![A.divisorialSheaf, E.divisorialSheaf, E.divisorialSheaf] t) := by
    intro t; fin_cases t <;> assumption
  unfold Divisor.intersectionNumberOn
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine intersectionNumber_congr_family k sX _ _ _ ?_
  funext t; fin_cases t <;> rfl

/-- `((aA) · E · E) = a (A · E · E)`. -/
private theorem intersectionNumberOn_nsmul_triple (hd : topologicalKrullDim Z ≤ 3)
    {A E : Divisor X} (hA : A.IsCartier) (hE : E.IsCartier) (a : ℕ) :
    Divisor.intersectionNumberOn k sX i 3 hd ![a • A, E, E]
        (by intro j; fin_cases j; exacts [hA.nsmul a, hE, hE]) =
      a * Divisor.intersectionNumberOn k sX i 3 hd ![A, E, E]
        (by intro j; fin_cases j <;> assumption) := by
  rw [intersectionNumberOn_eq_mul_of_eq_nsmul sX i 3 hd _ _ 0 hA a rfl, intersectionNumberOn_congr sX i _
    (show Function.update ![a • A, E, E] 0 A = ![A, E, E] by funext t; fin_cases t <;> rfl)]

/-- For `P` nef and `W ⊆ X` an integral closed subscheme of dimension `e`, `0 ≤ (P^e · W)`. -/
private theorem intersectionNumber_const_nonneg (hX : Mori.IsProjectiveVariety k sX)
    (P : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P] (hP : IsNef k sX P)
    {W : Scheme.{u}} (w : W ⟶ X) [IsClosedImmersion w] [IsIntegral W] {e : ℕ}
    (hW : topologicalKrullDim W = e) :
    0 ≤ intersectionNumber k sX w e hW.le (fun _ => P) := by
  have h := sheafSelfIntersectionNumber_nonneg_of_isNef k sX hX P hP W w hW
  unfold sheafSelfIntersectionNumber at h
  rwa [Snapper.sheafIntersectionNumber_eq_intersectionNumber] at h

/-- **Cutting by an effective Cartier divisor.** On an integral threefold `X` projective over
`k`, with `P` nef and `𝒪_X(Y) ≅ A` for an effective Cartier divisor `Y`, the number
`(A · P · P · X)` is nonnegative, and positive if `Y` contains a surface `V = \overline{\{x\}}`
with `(P² · V) > 0`. -/
private theorem intersectionNumber_cut_nonneg_and_pos (hX : Mori.IsProjectiveVariety k sX)
    (hdim : topologicalKrullDim X = 3) (P A : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A] (hP : IsNef k sX P)
    (Y : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Y] [Nonempty Y.subscheme]
    [IsIntegral X] (e : A ≅ Stacks.Divisors.invertibleSheaf Y) :
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![A, P, P] t) := by
      intro t; fin_cases t <;> assumption
    0 ≤ intersectionNumber k sX (𝟙 X) 3 hdim.le ![A, P, P] ∧
      ∀ (x : X) (hx : topologicalKrullDim
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme = 2),
        closure {x} ⊆ (Y.support : Set X) →
        0 < intersectionNumber k sX
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι 2
          hx.le (fun _ => P) →
        0 < intersectionNumber k sX (𝟙 X) 3 hdim.le ![A, P, P] := by
  haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![A, P, P] t) := by
    intro t; fin_cases t <;> assumption
  have hYdim : topologicalKrullDim Y.subscheme = (2 : ℕ) :=
    topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k sX Y inferInstance
      (by rw [hdim]; rfl)
  have hcut := intersectionNumber_eq_of_isEffectiveCartierDivisor k sX (𝟙 X) 2 hdim.le
    ![A, P, P] Y hYdim.le ((Scheme.Modules.pullbackId X).app A ≪≫ e)
  have hsum := intersectionNumber_eq_sum_topDimComponents k sX (Y.subschemeι ≫ 𝟙 X) 2 hYdim
    (fun t : Fin 2 => ![A, P, P] t.succ)
  have hfam : (fun t : Fin 2 => ![A, P, P] t.succ) = fun _ => P := by
    funext t; fin_cases t <;> rfl
  have hterm : ∀ W : TopDimIntegralSubscheme ((Scheme.Modules.pushforward (Y.subschemeι ≫ 𝟙 X)).obj
      (Stacks.Ample.unitModule Y.subscheme)),
      0 ≤ Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pushforward (Y.subschemeι ≫ 𝟙 X)).obj
          (Stacks.Ample.unitModule Y.subscheme)) W.genericPt *
        intersectionNumber k sX W.1.subschemeι 2
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme _ hYdim W)
          (fun t : Fin 2 => ![A, P, P] t.succ) := by
    intro W
    have := W.2.1
    refine mul_nonneg (sheafMultiplicity_genericPt_pos k sX _ W).le ?_
    rw [intersectionNumber_congr_family k sX _ _ _ hfam]
    exact intersectionNumber_const_nonneg sX hX P hP W.1.subschemeι
      (by rw [W.2.2.2, Stacks.Chow.supp_pushforwardStructureSheaf, topologicalKrullDim_range_eq,
        hYdim])
  have h3 := hcut.trans hsum
  refine ⟨by rw [h3]; exact finsum_nonneg hterm, fun x hx hxY hpos => ?_⟩
  have := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    (Closeds.closure ({x} : Set X)) (by rw [Closeds.coe_closure]; exact isIrreducible_singleton.closure)
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).support :
      Set X) = closure {x} :=
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _).trans (Closeds.coe_closure _)
  let W : TopDimIntegralSubscheme ((Scheme.Modules.pushforward (Y.subschemeι ≫ 𝟙 X)).obj
      (Stacks.Ample.unitModule Y.subscheme)) :=
    ⟨Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)), this,
      by
        rw [hsupp, Stacks.Chow.supp_pushforwardStructureSheaf, Category.comp_id,
          Y.range_subschemeι]
        exact hxY,
      by rw [hx, Stacks.Chow.supp_pushforwardStructureSheaf, topologicalKrullDim_range_eq,
        hYdim]; rfl⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : Finite (TopDimIntegralSubscheme ((Scheme.Modules.pushforward (Y.subschemeι ≫ 𝟙 X)).obj
      (Stacks.Ample.unitModule Y.subscheme))) := finite_topDimIntegralSubscheme k sX _
  haveI := Fintype.ofFinite (TopDimIntegralSubscheme
    ((Scheme.Modules.pushforward (Y.subschemeι ≫ 𝟙 X)).obj (Stacks.Ample.unitModule Y.subscheme)))
  have hWpos : 0 < Stacks.Chow.sheafMultiplicity
      ((Scheme.Modules.pushforward (Y.subschemeι ≫ 𝟙 X)).obj
          (Stacks.Ample.unitModule Y.subscheme)) W.genericPt *
        intersectionNumber k sX W.1.subschemeι 2
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme _ hYdim W)
          (fun t : Fin 2 => ![A, P, P] t.succ) := by
    refine mul_pos (sheafMultiplicity_genericPt_pos k sX _ W) ?_
    rw [intersectionNumber_congr_family k sX _ _ _ hfam]
    exact hpos
  rw [h3, finsum_eq_sum_of_fintype]
  exact Finset.sum_pos' (fun W _ => hterm W) ⟨W, Finset.mem_univ _, hWpos⟩

/-- **An effective Cartier divisor in a power of an ample module containing a given closed
subset** ([Stacks, Tag 09NV]): on an integral scheme `W` with an ample invertible module `𝓜` and a
closed subset `T ≠ W`, some `𝓜^{⊗ n}`, `n ≥ 1`, is `𝒪_W(D)` for an effective Cartier divisor `D`
whose support contains `T`. -/
private theorem exists_effectiveCartierDivisor_subset_supportSet {W : Scheme.{u}}
    [IsIntegral W] (M : W.Modules) [Stacks.Ample.IsInvertibleModule W M]
    (hM : Stacks.Ample.IsAmple W M) (T : Set W) (hT : IsClosed T) (hTne : T ≠ Set.univ) :
    ∃ (n : ℕ) (D : W.IdealSheafData), 1 ≤ n ∧
      Stacks.Divisors.IsEffectiveCartierDivisor D ∧ T ⊆ D.supportSet ∧
      Nonempty (Stacks.Ample.tensorPowModule W M (n : ℤ) ≅
        Stacks.Divisors.invertibleSheaf D) := by
  classical
  obtain ⟨x₀, hx₀T⟩ := (Set.ne_univ_iff_exists_notMem T).mp hTne
  obtain ⟨n, hn, s, -, hTs, hsub⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite M hM
      (Set.finite_singleton x₀) ⟨Tᶜ, hT.isOpen_compl⟩ (by simpa using hx₀T)
  have : SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  have hx₀ : x₀ ∈ Stacks.Ample.nonvanishingLocus
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) s :=
    (Stacks.AmpleTheory.coe_powNonvanishingOpen W M n s) ▸ hTs rfl
  have hne0 : s ≠ 0 := by
    intro h
    rw [h, Stacks.Ample.mem_nonvanishingLocus_iff] at hx₀
    exact hx₀ (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) s).eval (op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) s).eval (op ⊤) ≠ 0 := by
    rw [hevaltop]; exact hne0
  have hreg : IsRegularSection W.sheaf.obj W.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule W M (n : ℤ)) s) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  refine ⟨n, zeroScheme W (Stacks.Ample.tensorPowModule W M (n : ℤ))
      ((Stacks.SheafOfModules.sectionsOfTop
        (Stacks.Ample.tensorPowModule W M (n : ℤ)) s).eval (op ⊤)),
    hn, (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection W _ _).2 hreg, ?_, ?_⟩
  · have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) _ hne0'
    have hloc : Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule W M (n : ℤ)) s =
        (zeroScheme W (Stacks.Ample.tensorPowModule W M (n : ℤ))
          ((Stacks.SheafOfModules.sectionsOfTop
            (Stacks.Ample.tensorPowModule W M (n : ℤ)) s).eval (op ⊤))).supportSetᶜ := by
      conv_lhs => rw [← hevaltop]
      rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval W _
        (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule W M (n : ℤ)) s)]
      exact hcompl
    intro t ht
    by_contra hnot
    have h1 : t ∈ Stacks.Ample.nonvanishingLocus
        (Stacks.Ample.tensorPowModule W M (n : ℤ)) s := by
      rw [hloc]; exact hnot
    rw [← Stacks.AmpleTheory.coe_powNonvanishingOpen W M n s] at h1
    exact hsub h1 ht
  · obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme W _ _ hreg).exists
    exact ⟨e.symm⟩

/-- `𝒪_X(nL) ≅ 𝒪_X(L)^{⊗ n}` for a Cartier divisor `L` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso [CompactSpace X] {L : Divisor X} (hL : L.IsCartier) (n : ℕ) (hn : 1 ≤ n) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    Nonempty ((n • L).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule X L.divisorialSheaf (n : ℤ)) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_nsmul L)) ≪≫
      (Stacks.Ample.tensorPowModuleOneIso X _).symm⟩
  | succ n hn ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul L n)) ≪≫
      ((hL.nsmul n).divisorialSheafTensorIso hL).symm ≪≫ ?_ ≪≫
      Stacks.Ample.tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; rfl)⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso X _).symm

/-- On an integral scheme with `𝒪_X(D₀)` ample, for every Cartier `E` some `𝒪_X(aD₀ - E)` is the
sheaf of an effective Cartier divisor. -/
private theorem exists_isEffectiveCartierDivisor_iso_nsmul_sub [IsIntegral X] [CompactSpace X]
    {D₀ E : Divisor X} (hD₀ : D₀.IsCartier) (hE : E.IsCartier)
    (hamp : D₀.IsAmple hD₀) :
    ∃ (a : ℕ) (Y : X.IdealSheafData), Stacks.Divisors.IsEffectiveCartierDivisor Y ∧
      Nonempty ((a • D₀ - E).divisorialSheaf ≅ Stacks.Divisors.invertibleSheaf Y) := by
  haveI := hD₀.isInvertibleModule_divisorialSheaf
  have hE' := hE.neg
  haveI := hE'.isInvertibleModule_divisorialSheaf
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple
      D₀.divisorialSheaf hamp).2 (-E).divisorialSheaf inferInstance
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _)
  set a : ℕ := n₀.toNat + 1
  have ha : 1 ≤ a := by omega
  obtain ⟨g⟩ := hn₀ a (by omega)
  obtain ⟨eN⟩ := nonempty_divisorialSheaf_nsmul_iso hD₀ a ha
  have hG := (hD₀.nsmul a).sub hE
  haveI := hG.isInvertibleModule_divisorialSheaf
  let e : @MonoidalCategory.tensorObj _ _
      (Stacks.SheafInternalHom.schemeMonoidalCategory X).toMonoidalCategoryStruct
      (-E).divisorialSheaf (Stacks.Ample.tensorPowModule X D₀.divisorialSheaf (a : ℤ)) ≅
      (a • D₀ - E).divisorialSheaf :=
    (Stacks.SheafInternalHom.tensorLeftIso X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso eN.symm ≪≫
      hE'.divisorialSheafTensorIso (hD₀.nsmul a) ≪≫
      eqToIso (congrArg Divisor.divisorialSheaf (neg_add_eq_sub _ _))
  haveI : Epi e.hom := ⟨fun f₁ f₂ h => by simpa using congrArg (fun t => e.inv ≫ t) h⟩
  let g' := @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ g e.hom this
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨i, hi⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing _ g' x
  haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (a • D₀ - E).divisorialSheaf :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  have hne : (g'.s i).eval (op ⊤) ≠ 0 := by
    intro h
    apply hi
    change _ ∈ _
    rw [h, map_zero]
    exact zero_mem _
  have hreg := isRegularSection_of_eval_top_ne_zero _ _ hne
  refine ⟨a, zeroScheme X (a • D₀ - E).divisorialSheaf ((g'.s i).eval (op ⊤)),
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X _ _).2 hreg, ?_⟩
  obtain ⟨e', -⟩ := (existsUnique_invertibleSheafIso_zeroScheme X _ _ hreg).exists
  exact ⟨e'.symm⟩

/-- On an integral scheme `X` proper over `k` of positive dimension, for `D₀` Cartier with
`𝒪_X(D₀)` ample and `E` Cartier, some `𝒪_X(aD₀ - E)` is the sheaf of a nonempty effective
Cartier divisor. -/
private theorem exists_effectiveCartierDivisor_nsmul_sub {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsIntegral X] [CompactSpace X]
    (hdim : 0 < topologicalKrullDim X)
    {D₀ E : Divisor X} (hD₀ : D₀.IsCartier) (hE : E.IsCartier)
    (hamp : D₀.IsAmple hD₀) :
    ∃ (a : ℕ) (Y : X.IdealSheafData), Stacks.Divisors.IsEffectiveCartierDivisor Y ∧
      Nonempty Y.subscheme ∧
      Nonempty ((a • D₀ - E).divisorialSheaf ≅ Stacks.Divisors.invertibleSheaf Y) := by
  haveI := hD₀.isInvertibleModule_divisorialSheaf
  obtain ⟨a, Y, hY, ⟨eY⟩⟩ := exists_isEffectiveCartierDivisor_iso_nsmul_sub hD₀ hE hamp
  obtain ⟨N, D, hN, hD, ⟨d⟩, ⟨eD⟩⟩ := exists_effectiveCartierDivisor_tensorPower_of_isAmple k sX
    hdim D₀.divisorialSheaf (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _ hamp)
  haveI := hY
  haveI := hD
  obtain ⟨eN⟩ := nonempty_divisorialSheaf_nsmul_iso hD₀ N hN
  have hG := (hD₀.nsmul a).sub hE
  have eD' : (N • D₀).divisorialSheaf ≅ Stacks.Divisors.invertibleSheaf D :=
    eN ≪≫ (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X _ (N : ℤ)).symm ≪≫ eD
  refine ⟨a + N, Y * D, isEffectiveCartierDivisor_mul _ _ hY hD, ?_, ?_⟩
  · have hsub : D.support ≤ (Y * D).support :=
      Scheme.IdealSheafData.support_antitone (mul_le_of_le_one_left' le_top)
    have hd : D.subschemeι d ∈ ((Y * D).support : Set X) := by
      apply hsub
      have : D.subschemeι d ∈ Set.range D.subschemeι := ⟨d, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι] at this
    rw [← Scheme.IdealSheafData.range_subschemeι] at hd
    obtain ⟨y, -⟩ := hd
    exact ⟨y⟩
  · exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (by rw [add_nsmul]; abel)) ≪≫
      (hG.divisorialSheafTensorIso (hD₀.nsmul N)).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso eY).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso eD' ≪≫
      Stacks.Divisors.invertibleSheafSumIso Y D⟩

/-- A closed embedding `f : Y → X` into an irreducible space with `dim X ≤ n ≤ dim Y` is
surjective. -/
private theorem surjective_of_topologicalKrullDim_le {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [IrreducibleSpace X] {f : Y → X} (hf : Topology.IsClosedEmbedding f)
    {n : ℕ} (hX : topologicalKrullDim X ≤ n) (hY : (n : WithBot ℕ∞) ≤ topologicalKrullDim Y) :
    Function.Surjective f := by
  by_contra hns
  have hne : Set.range f ≠ Set.univ := fun h => hns (Set.range_eq_univ.mp h)
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hY
  let φ : TopologicalSpace.IrreducibleCloseds Y → TopologicalSpace.IrreducibleCloseds X :=
    fun Z => ⟨f '' Z, Z.isIrreducible.image f hf.continuous.continuousOn,
      hf.isClosedMap _ Z.isClosed⟩
  have hφ : StrictMono φ := fun a b hab =>
    (hf.injective.image_strictMono : StrictMono (f '' ·)) (show (a : Set Y) < b from hab)
  let top : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hlt : φ l.last < top := by
    change f '' (l.last : Set Y) < Set.univ
    exact lt_of_le_of_lt (Set.image_subset_range f _) (Set.ssubset_univ_iff.mpr hne)
  have h := Order.LTSeries.length_le_krullDim ((l.map φ hφ).snoc top hlt)
  have hlen : ((l.map φ hφ).snoc top hlt).length = n + 1 := by
    change l.length + 1 = n + 1
    omega
  rw [hlen] at h
  have h2 := h.trans hX
  norm_cast at h2
  omega

/-- A closed subvariety of `X` of the dimension of `X` computes the intersection numbers
of `X`. -/
private theorem intersectionNumber_vanishingIdeal_closure_eq [IsIntegral X] {d : ℕ}
    (hdim : topologicalKrullDim X = d) (x : X)
    (hx : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme = d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι d
        hx.le L =
      intersectionNumber k sX (𝟙 X) d hdim.le L := by
  have h1 := topologicalKrullDim_range_eq
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure, hx] at h1
  have huniv : closure ({x} : Set X) = Set.univ := by
    simpa using Set.range_eq_univ.mpr (surjective_of_topologicalKrullDim_le
      isClosed_closure.isClosedEmbedding_subtypeVal (n := d) hdim.le h1.ge)
  have hC : Closeds.closure ({x} : Set X) = ⊤ := Closeds.ext (by simpa using huniv)
  have hker : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι.ker = Scheme.Hom.ker (𝟙 X) := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hC, Scheme.Hom.ker_eq_bot_of_isIso]
    exact Scheme.IdealSheafData.support_eq_top_iff.mp rfl
  have := sheafIntersectionNumber_eq_of_ker_eq k sX _ (𝟙 X) hker d hx.le hdim.le L
  rwa [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber] at this

/-- A point whose closure has dimension smaller than `X` has closure a proper subset. -/
private theorem closure_ne_univ_of_topologicalKrullDim_lt {d e : ℕ}
    (hdim : topologicalKrullDim X = d) (x : X)
    (hx : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme = e)
    (hlt : e < d) : closure ({x} : Set X) ≠ Set.univ := by
  intro h
  have h1 := topologicalKrullDim_range_eq
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure, h, hx] at h1
  have h2 : topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
    (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
  rw [h2, hdim] at h1
  have : d = e := by exact_mod_cast h1
  omega

/-- A Cartier divisor `E = mL`, for `L` a nef `ℚ`-divisor and `m > 0`, has nef sheaf `𝒪_X(E)`. -/
private theorem isNef_divisorialSheaf_of_toQDivisor_eq_smul {L : QDivisor X} (hL : L.IsNef k sX)
    {m : ℕ} (hm : 0 < m) {E : Divisor X} (hE : E.IsCartier)
    [Stacks.Ample.IsInvertibleModule X E.divisorialSheaf]
    (hEL : Divisor.toQDivisor E = (m : ℚ) • L) : IsNef k sX E.divisorialSheaf := by
  obtain ⟨hQ, hLC⟩ := hL
  intro C c _ _ _ hC
  have h1 := hLC C c hC
  rw [QDivisor.intersectionNumber_eq_of_smul k sX c hC.le L hQ hm E hE
    (by rw [hEL]; norm_cast)] at h1
  have h2 : (0 : ℚ) ≤ E.degreeOn k sX c hC.le hE := by
    have := mul_nonneg h1 (Nat.cast_nonneg (α := ℚ) m)
    rwa [div_mul_cancel₀ _ (by exact_mod_cast hm.ne')] at this
  exact_mod_cast h2

/-- If `m₀ F = n D₀`, then `m₀ (E · E · F) = n (D₀ · E · E)`. -/
private theorem intersectionNumberOn_mul_eq_of_nsmul_eq (hdim : topologicalKrullDim X = 3)
    {D₀ E F : Divisor X} (hD₀ : D₀.IsCartier) (hE : E.IsCartier) (hF : F.IsCartier) {m₀ n : ℕ}
    (hFD : m₀ • F = n • D₀) :
    (m₀ : ℤ) * Divisor.intersectionNumberOn k sX (𝟙 X) 3 hdim.le ![E, E, F]
        (by intro j; fin_cases j <;> assumption) =
      n * Divisor.intersectionNumberOn k sX (𝟙 X) 3 hdim.le ![D₀, E, E]
        (by intro j; fin_cases j <;> assumption) := by
  have hG : ∀ j, (![E, E, m₀ • F] j).IsCartier := by
    intro j; fin_cases j; exacts [hE, hE, hF.nsmul m₀]
  have h1 := intersectionNumberOn_eq_mul_of_eq_nsmul sX (𝟙 X) 3 hdim.le _ hG 2 hF m₀ rfl
  have h2 := intersectionNumberOn_eq_mul_of_eq_nsmul sX (𝟙 X) 3 hdim.le _ hG 2 hD₀ n (by simpa using hFD)
  have e1 : Function.update ![E, E, m₀ • F] 2 F = ![E, E, F] := by
    funext t; fin_cases t <;> rfl
  have e2 : Function.update ![E, E, m₀ • F] 2 D₀ = fun j => ![D₀, E, E] (finRotate 3 j) := by
    funext t; fin_cases t <;> rfl
  rw [intersectionNumberOn_congr sX (𝟙 X) _ e1] at h1
  rw [intersectionNumberOn_congr sX (𝟙 X) _ e2,
    intersectionNumberOn_comp_perm sX (𝟙 X) 3 hdim.le ![D₀, E, E]
      (by intro j; fin_cases j <;> assumption) (finRotate 3)] at h2
  exact h1.symm.trans h2

/-- On a projective threefold, `(D₀ · E · E) > 0` for `D₀` ample and `E` nef with `(E² · V) > 0`
for a surface `V = \overline{\{x\}}`. -/
private theorem intersectionNumberOn_pos_of_surface (hX : Mori.IsProjectiveVariety k sX)
    [CompactSpace X] [IsIntegral X] (hdim : topologicalKrullDim X = 3) {D₀ E : Divisor X}
    (hD₀ : D₀.IsCartier) (hD₀a : D₀.IsAmple hD₀) (hE : E.IsCartier)
    [Stacks.Ample.IsInvertibleModule X D₀.divisorialSheaf]
    [Stacks.Ample.IsInvertibleModule X E.divisorialSheaf]
    (hEnef : IsNef k sX E.divisorialSheaf) (x : X)
    (hV : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme =
        ((2 : ℕ) : WithBot ℕ∞))
    (hVpos : 0 < intersectionNumber k sX
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι 2 hV.le
      (fun _ => E.divisorialSheaf)) :
    0 < Divisor.intersectionNumberOn k sX (𝟙 X) 3 hdim.le ![D₀, E, E]
      (by intro j; fin_cases j <;> assumption) := by
  have hT := closure_ne_univ_of_topologicalKrullDim_lt hdim x hV (by norm_num : 2 < 3)
  obtain ⟨N, Y, hN, hYc, hTY, ⟨e⟩⟩ := exists_effectiveCartierDivisor_subset_supportSet
    D₀.divisorialSheaf hD₀a (closure {x}) isClosed_closure hT
  have := hYc
  obtain ⟨y, -⟩ : x ∈ Set.range Y.subschemeι := by
    rw [Y.range_subschemeι]; exact hTY (subset_closure rfl)
  have : Nonempty Y.subscheme := ⟨y⟩
  obtain ⟨eN⟩ := nonempty_divisorialSheaf_nsmul_iso hD₀ N hN
  have := (hD₀.nsmul N).isInvertibleModule_divisorialSheaf
  have hc := (intersectionNumber_cut_nonneg_and_pos sX hX hdim E.divisorialSheaf
    (N • D₀).divisorialSheaf hEnef Y (eN ≪≫ e)).2 x (by rw [hV]; rfl) hTY hVpos
  have h1 := intersectionNumberOn_nsmul_triple sX (𝟙 X) hdim.le hD₀ hE N
  rw [intersectionNumberOn_triple sX (𝟙 X) hdim.le (hD₀.nsmul N) hE] at h1
  rw [h1] at hc
  exact pos_of_mul_pos_right hc (by positivity)

/-- On a projective threefold, `(D₀ · E · E) > 0` for `D₀` ample and `E` nef with `E³ > 0`. -/
private theorem intersectionNumberOn_pos_of_cube (hX : Mori.IsProjectiveVariety k sX)
    [CompactSpace X] [IsIntegral X] (hdim : topologicalKrullDim X = 3) {D₀ E : Divisor X}
    (hD₀ : D₀.IsCartier) (hD₀a : D₀.IsAmple hD₀) (hE : E.IsCartier)
    [Stacks.Ample.IsInvertibleModule X D₀.divisorialSheaf]
    [Stacks.Ample.IsInvertibleModule X E.divisorialSheaf]
    (hEnef : IsNef k sX E.divisorialSheaf) (x : X)
    (hV : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme =
        ((3 : ℕ) : WithBot ℕ∞))
    (hVpos : 0 < intersectionNumber k sX
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι 3 hV.le
      (fun _ => E.divisorialSheaf)) :
    0 < Divisor.intersectionNumberOn k sX (𝟙 X) 3 hdim.le ![D₀, E, E]
      (by intro j; fin_cases j <;> assumption) := by
  have hXV := intersectionNumber_vanishingIdeal_closure_eq sX hdim x hV
    (fun _ => E.divisorialSheaf)
  obtain ⟨a, Y, hYc, hYne, ⟨e⟩⟩ := exists_effectiveCartierDivisor_nsmul_sub sX
    (by rw [hdim]; exact_mod_cast (by norm_num : (0 : ℕ) < 3)) hD₀ hE hD₀a
  have := hYc
  have hG := (hD₀.nsmul a).sub hE
  have := hG.isInvertibleModule_divisorialSheaf
  have hc := (intersectionNumber_cut_nonneg_and_pos sX hX hdim E.divisorialSheaf
    (a • D₀ - E).divisorialSheaf hEnef Y e).1
  have hca : ∀ j, (![a • D₀, E, E] j).IsCartier := by
    intro j; fin_cases j; exacts [hD₀.nsmul a, hE, hE]
  have h2 := intersectionNumberOn_update_add sX (𝟙 X) 3 hdim.le _ hca 0 hG hE
    (sub_add_cancel _ _).symm
  have e2 : Function.update ![a • D₀, E, E] 0 (a • D₀ - E) = ![a • D₀ - E, E, E] := by
    funext t; fin_cases t <;> rfl
  have e3 : Function.update ![a • D₀, E, E] 0 E = fun _ => E := by
    funext t; fin_cases t <;> rfl
  rw [intersectionNumberOn_congr sX (𝟙 X) _ e2, intersectionNumberOn_congr sX (𝟙 X) _ e3,
    intersectionNumberOn_triple sX (𝟙 X) hdim.le hG hE,
    intersectionNumberOn_nsmul_triple sX (𝟙 X) hdim.le hD₀ hE a,
    intersectionNumberOn_const sX (𝟙 X) 3 hdim.le hE, ← hXV] at h2
  have : 0 < (a : ℤ) * Divisor.intersectionNumberOn k sX (𝟙 X) 3 hdim.le ![D₀, E, E]
      (by intro j; fin_cases j <;> assumption) := by
    rw [h2]; exact add_pos_of_nonneg_of_pos hc hVpos
  exact pos_of_mul_pos_right this (by positivity)

end NefSquare

/-- **A nef divisor with `ν ≥ 2` has positive square against an ample divisor.** Let `X` be a
normal projective threefold over a field `k` of characteristic zero, `L` a nef `ℚ`-Cartier
`ℚ`-divisor with `MMP.Flips.numericalDimension` at least `2`, and `H` an ample `ℚ`-divisor. Then
`(L² · H) > 0`: for all Cartier divisors `E = mL` and `F = nH` with `m, n > 0`,
`(E · E · F · X) > 0`. -/
@[mmp "lem_mmp_fa15_nef_square_ample_test"]
public theorem intersectionNumberOn_pos_of_two_le_numericalDimension {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [hXp : Mori.IsProjectiveVariety k sX]
    [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] (hdim : topologicalKrullDim X = 3)
    {L H : QDivisor X} (hL : L.IsNef k sX)
    (hν : 2 ≤ numericalDimension k sX inferInstance L hL) (hH : H.IsAmple)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (E F : Divisor X) (hE : E.IsCartier) (hF : F.IsCartier)
    (hEL : Divisor.toQDivisor E = (m : ℚ) • L) (hFH : Divisor.toQDivisor F = (n : ℚ) • H) :
    0 < Divisor.intersectionNumberOn k sX (𝟙 X) 3 hdim.le ![E, E, F]
      (by intro j; fin_cases j <;> assumption) := by
  haveI : IsIntegral X := hXp.toIsIntegral
  haveI := hE.isInvertibleModule_divisorialSheaf
  have hEnef := isNef_divisorialSheaf_of_toQDivisor_eq_smul sX hL hm hE hEL
  obtain ⟨m₀, hm₀, D₀, hD₀H, hD₀, hD₀a⟩ := hH
  haveI := hD₀.isInvertibleModule_divisorialSheaf
  have hFD : m₀ • F = n • D₀ := Divisor.toQDivisor_injective (by
    rw [map_nsmul, map_nsmul, hFH, hD₀H, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, smul_smul, mul_comm])
  have hred := intersectionNumberOn_mul_eq_of_nsmul_eq sX hdim hD₀ hE hF hFD
  suffices hpos : 0 < Divisor.intersectionNumberOn k sX (𝟙 X) 3 hdim.le ![D₀, E, E]
      (by intro j; fin_cases j <;> assumption) by
    refine pos_of_mul_pos_right (a := (m₀ : ℤ)) ?_ (by positivity)
    rw [hred]
    exact mul_pos (by exact_mod_cast hn) hpos
  have hbdd : BddAbove (numericalDimensionSet k sX L) := ⟨3, fun d hd => by
    rcases hd with rfl | ⟨hle, -⟩
    · omega
    · rw [hdim] at hle; exact_mod_cast hle⟩
  have hmem := Nat.sSup_mem ⟨0, zero_mem_numericalDimensionSet k sX L⟩ hbdd
  have hν' : 2 ≤ sSup (numericalDimensionSet k sX L) := hν
  generalize sSup (numericalDimensionSet k sX L) = d at hmem hν'
  rcases hmem with h0 | ⟨hle, x, hV, m', E', hE', hm', hE'L, hne⟩
  · omega
  have hd3 : d ≤ 3 := by rw [hdim] at hle; exact_mod_cast hle
  set V := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  have := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    (Closeds.closure ({x} : Set X)) (by rw [Closeds.coe_closure]; exact isIrreducible_singleton.closure)
  have hEE' : m • E' = m' • E := Divisor.toQDivisor_injective (by
    rw [map_nsmul, map_nsmul, hE'L, hEL, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, smul_smul, mul_comm])
  have hEV : Divisor.intersectionNumberOn k sX V.subschemeι d hV.le (fun _ => E)
      (fun _ => hE) ≠ 0 := by
    have k1 := intersectionNumberOn_const_nsmul sX V.subschemeι d hV.le hE' m
    have k2 := intersectionNumberOn_const_nsmul sX V.subschemeι d hV.le hE m'
    rw [intersectionNumberOn_congr sX V.subschemeι _ (funext fun _ => hEE'), k2] at k1
    intro h0
    rw [h0, mul_zero] at k1
    exact hne ((mul_eq_zero.mp k1.symm).resolve_left (pow_ne_zero _ (by exact_mod_cast hm.ne')))
  have hVpos : 0 < intersectionNumber k sX V.subschemeι d hV.le (fun _ => E.divisorialSheaf) := by
    rw [intersectionNumberOn_const sX V.subschemeι d hV.le hE] at hEV
    exact lt_of_le_of_ne (intersectionNumber_const_nonneg sX hXp _ hEnef V.subschemeι hV)
      (Ne.symm hEV)
  obtain rfl | rfl : d = 2 ∨ d = 3 := by omega
  · exact intersectionNumberOn_pos_of_surface sX hXp hdim hD₀ hD₀a hE hEnef x hV hVpos
  · exact intersectionNumberOn_pos_of_cube sX hXp hdim hD₀ hD₀a hE hEnef x hV hVpos

/-- **The Nakai criterion on a projective surface.** Let `S` be a projective surface over a field
`k` of characteristic zero and `L` an invertible sheaf on `S` with `(L · L · S) > 0` and
`deg_C L > 0` for every closed integral curve `i : C ⟶ S`. Then `L` is ample. -/
@[mmp "lem_mmp_fa15_projective_surface_nakai"]
public theorem isAmple_of_sheafSelfIntersectionNumber_pos_of_degreeOn_pos {k : Type u} [Field k]
    [CharZero k] {S : Scheme.{u}} (sS : S ⟶ Spec (.of k)) [Mori.IsProjectiveVariety k sS]
    (hS : topologicalKrullDim S = 2)
    (L : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L]
    (hL2 : 0 < sheafSelfIntersectionNumber k sS (𝟙 S) 2 hS.le L)
    (hdeg : ∀ (C : Scheme.{u}) (i : C ⟶ S) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ sS)] (hC : topologicalKrullDim C = 1), 0 < degreeOn k sS i hC.le L) :
    Stacks.Ample.IsAmple S L := by
  have hP : IsProjective sS := ((isProjectiveVariety_iff_isProjective' k sS).1 inferInstance).2
  refine isAmple_of_sheafSelfIntersectionNumber_pos_of_dim_pos k sS hP L
    fun V i _ _ d hd hd0 => ?_
  have hVS : topologicalKrullDim V ≤ 2 :=
    ((topologicalKrullDim_range_eq i).symm.le.trans (topologicalKrullDim_subspace_le S _)).trans
      hS.le
  have hd2 : d ≤ 2 := by
    rw [hd] at hVS
    exact_mod_cast hVS
  obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
  · have hC : topologicalKrullDim V = 1 := by rw [hd]; rfl
    have h := hdeg V i hC
    rw [degreeOn_eq_invertibleCurveDegree, ← intersectionNumber_one_eq_invertibleCurveDegree] at h
    rw [sheafSelfIntersectionNumber, Snapper.sheafIntersectionNumber_eq_intersectionNumber]
    exact h
  · haveI : Surjective i := ⟨surjective_of_topologicalKrullDim_le i.isClosedEmbedding (n := 2)
      (by rw [hS]; rfl) (by rw [hd])⟩
    haveI : IsIso i := isIso_of_isClosedImmersion_of_surjective i
    rw [sheafSelfIntersectionNumber,
      sheafIntersectionNumber_eq_of_iso k sS i (𝟙 S) (asIso i) (by simp) 2 hd.le hS.le]
    exact hL2

end MMP.Flips

end
