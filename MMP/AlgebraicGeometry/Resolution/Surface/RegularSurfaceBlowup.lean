module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.PointBlowupComposites
import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Dehomogenization

/-!
# Regular surfaces, depth, and Euler characteristic polynomials

This file collects four results from commutative algebra and the geometry of surfaces and
varieties.

*Principal quotients of a two-dimensional regular local ring.* Let `(A, 𝔫)` be a regular local
ring of Krull dimension `2` and `h ∈ 𝔫` nonzero. Since `A` is a domain, `h` is a
non-zero-divisor, so `dim A ⧸ (h) + 1 = dim A = 2` and `A ⧸ (h)` has Krull dimension `1`; in
particular it is not Artinian, hence does not have finite length as an `A`-module.

*The blow-up of a closed point of a regular surface.* Let `S` be a regular surface
(`MMP.Resolution.IsRegularSurface`: Noetherian, regular, with two-dimensional local rings at
closed points) and `p ∈ S` a closed point, with blow-up `π : B_pS → S` and exceptional curve
`E = π⁻¹(p)`. Since every point of the Noetherian scheme `S` specializes to a closed point, `S`
has dimension two, so `B_pS` is a regular Noetherian scheme by the global form of
[Stacks, Tag 0AGR]. Off `E`, `π` is an isomorphism, so the local rings of `B_pS` at closed points
off `E` are local rings of `S` at closed points (`π` is closed); along `E` they have dimension
two. Hence `B_pS` is again a regular surface (Kollár 1.36, stated there as "`B₀S` is smooth").

*Depth is at most dimension.* Let `(R, 𝔪)` be a Noetherian local ring and `N ≠ 0` a finite
`R`-module. Every `N`-regular sequence in `𝔪` has length at most `dim N`, the Krull dimension of
the support of `N`; that is, `depth N ≤ dim N`.

*The Euler characteristic function is a polynomial.* Let `Y` be a smooth proper normal scheme of
dimension `n` over a field `k` (in the source, a smooth projective variety), let `Dᵢ` (`i ∈ ι`)
be divisors (Cartier, since `Y` is smooth) and `A` a `ℚ`-divisor on `Y`. The function
`u ↦ χ(Y, 𝒪_Y(∑ᵢ uᵢ Dᵢ + ⌈A⌉))` on `ℤ^ι` is the restriction of a polynomial in
`ℚ[uᵢ : i ∈ ι]` of total degree at most `n`. With `L₀ = ⌈A⌉`, which is Cartier since `Y` is
smooth, Snapper's theorem gives a polynomial `Q(k₀, k)` of total degree at most `n` computing
`χ(Y, 𝒪_Y(k₀ L₀ + ∑ᵢ kᵢ Dᵢ))`, and `P(u) = Q(1, u)`; substituting `k₀ = 1` does not raise the
total degree.

## Main results

* `MMP.Resolution.ringKrullDim_quotient_span_singleton_eq_one_and_not_isFiniteLength`:
  `ringKrullDim (A ⧸ (h)) = 1` and `A ⧸ (h)` is not of finite length over `A`.
* `MMP.Resolution.isRegularSurface_blowUp`: the blow-up of a closed point of a regular surface
  is a regular surface.
* `MMP.Mori.localDepth_le_supportDim`: `depth N ≤ dim N`, with the depth `MMP.Mori.localDepth`
  and the dimension `Module.supportDim`.
* `MMP.Mori.Divisor.exists_totalDegree_le_eval_eq_eulerPolynomial`: the Euler characteristic
  function `MMP.Mori.Divisor.eulerPolynomial` is interpolated on `ℤ^ι` by a rational polynomial
  of total degree at most `dim Y`.

## Implementation notes

The depth `MMP.Mori.localDepth` is the supremum of the lengths of weakly regular sequences in
`𝔪`. For `N` finite and nonzero, Nakayama's lemma makes every weakly regular sequence in `𝔪`
regular, so it agrees with `Module.depth R 𝔪 N`, and the inequality is then
`Module.depth_le_supportDim`. Both hypotheses on `N` are needed: for `N = 0` the depth is `⊤`
while the support is empty; for `N` the fraction field of a discrete valuation ring, every power
sequence of the uniformizer is weakly regular. The ring is Noetherian, as in the source's
convention for local rings.

## References

* [H. Matsumura, *Commutative Ring Theory*][matsumura1989], Theorem 13.5.
* [Stacks, Tag 0AGR]
* [Kollár, *Lectures on resolution of singularities*, 1.36][kollar2007]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4 Step 2
  and 5.1.
-/

@[expose] public section

universe u

open IsLocalRing AlgebraicGeometry CategoryTheory

namespace MMP.Resolution

/-- In a two-dimensional regular local ring `A`, the quotient by a nonzero element `h` of the
maximal ideal has Krull dimension `1`, and in particular is not of finite length over `A`. -/
@[mmp "lem_kr1c_principal_quotient_infinite_length"]
public theorem ringKrullDim_quotient_span_singleton_eq_one_and_not_isFiniteLength
    {A : Type*} [CommRing A] [IsRegularLocalRing A] (hA : ringKrullDim A = 2)
    {h : A} (h0 : h ≠ 0) (hh : h ∈ maximalIdeal A) :
    ringKrullDim (A ⧸ Ideal.span {h}) = 1 ∧ ¬ IsFiniteLength A (A ⧸ Ideal.span {h}) := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have hdim : ringKrullDim (A ⧸ Ideal.span {h}) = 1 := ENat.WithBot.add_one_cancel.mp <| by
    rw [ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero h0) hh, hA, one_add_one_eq_two]
  refine ⟨hdim, fun hfin => ?_⟩
  -- A finite-length quotient is an Artinian ring, hence of Krull dimension at most `0`.
  have : IsArtinianRing (A ⧸ Ideal.span {h}) :=
    isArtinian_of_tower A (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  have := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 (A ⧸ Ideal.span {h}))
  exact absurd (hdim ▸ this) (by decide)

/-- Off the exceptional curve, the blow-up morphism induces isomorphisms of local rings. -/
private theorem isIso_stalkMap_blowUpToBase_of_notMem {S : Scheme.{u}}
    {I : S.IdealSheafData} {q : blowUp I} (hq : q ∉ (exceptionalIdeal I).support) :
    IsIso ((blowUpToBase I).stalkMap q) :=
  isIso_stalkMap_of_isIso_morphismRestrict (blowUpToBase I)
    (isIso_blowUp_restrict_compl_support I) (x := q) fun h => hq <| by
      change q ∈ ((I.comap (blowUpToBase I)).support : Set _)
      rw [Scheme.IdealSheafData.support_comap]
      exact h

/-- The dimension of local rings grows along specialization. -/
private theorem ringKrullDim_stalk_le_of_specializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim (X.presheaf.stalk y) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Order.coheight_anti (α := X) (show y ≤ x from h)

/-- A regular surface with a closed point has dimension two. -/
private theorem topologicalKrullDim_eq_two {S : Scheme.{u}} (hS : IsRegularSurface S) {p : S}
    (hp : IsClosed ({p} : Set S)) : topologicalKrullDim S = 2 := by
  obtain ⟨hN, -, hD⟩ := hS
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    obtain ⟨y, hy, hyc⟩ := (isClosed_closure (s := ({x} : Set S))).exists_closed_singleton
      ⟨x, subset_closure rfl⟩
    exact (ringKrullDim_stalk_le_of_specializes (specializes_iff_mem_closure.mpr hy)).trans
      (hD y hyc).le
  · exact (hD p hp).symm.le.trans (le_iSup (fun z => ringKrullDim (S.presheaf.stalk z)) p)

/-- The local rings of the blow-up of a closed point of a regular surface at closed points have
dimension two. -/
private theorem ringKrullDim_stalk_eq_two {S : Scheme.{u}}
    (hS : IsRegularSurface S) (p : S) (hp : IsClosed ({p} : Set S))
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hq : IsClosed ({q} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)))) :
    ringKrullDim
      ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).presheaf.stalk q) = 2 := by
  obtain ⟨hN, hreg, hdim⟩ := hS
  by_cases hqE : q ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support
  · exact (isRegularLocalRing_stalk_blowUp_of_mem_support_exceptionalIdeal p hp (hreg p)
      (hdim p hp) q hqE).2.1 hq
  · haveI := isIso_stalkMap_blowUpToBase_of_notMem hqE
    haveI : IsLocallyNoetherian S := IsNoetherian.toIsLocallyNoetherian
    rw [← ringKrullDim_eq_of_ringEquiv
      (asIso ((blowUpToBase _).stalkMap q)).commRingCatIsoToRingEquiv]
    exact hdim _ (by simpa only [Set.image_singleton] using (blowUpToBase _).isClosedMap _ hq)

/-- The blow-up of a closed point of a regular surface is a regular surface (Kollár 1.36). -/
@[mmp "lem_kr1b_blowup_regular"]
public theorem isRegularSurface_blowUp {S : Scheme.{u}} (hS : IsRegularSurface S) (p : S)
    (hp : IsClosed ({p} : Set S)) :
    IsRegularSurface (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) := by
  haveI : IsNoetherian S := hS.1
  have hreg : IsRegular S :=
    (isRegular_iff_regular_stalks S).2 ⟨IsNoetherian.toIsLocallyNoetherian, hS.2.1⟩
  obtain ⟨hreg', -⟩ := isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton S hreg
    (topologicalKrullDim_eq_two hS hp) p hp
  exact ⟨Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _,
    ((isRegular_iff_regular_stalks _).1 hreg').2, ringKrullDim_stalk_eq_two hS p hp⟩

end MMP.Resolution

namespace MMP.Mori

/-- The depth of a nonzero finite module over a Noetherian local ring is at most the dimension
of its support. -/
@[mmp "lem_km5a_depth_le_dim"]
public theorem localDepth_le_supportDim
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N] :
    (localDepth R N : WithBot ℕ∞) ≤ Module.supportDim R N := by
  have hdepth : localDepth R N = Module.depth R (maximalIdeal R) N :=
    (Module.depth_eq_iSup_isWeaklyRegular_length R (maximalIdeal R) N).symm
  rw [hdepth]
  exact Module.depth_le_supportDim R (maximalIdeal R) N
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm

end MMP.Mori

namespace MMP.Mori.Divisor

section Sheaves

open Stacks.SheafOfModules.Invertible

private noncomputable abbrev tens (X : Scheme.{u}) : X.Modules ⥤ X.Modules ⥤ X.Modules :=
  Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
    (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩

private theorem nonempty_iso_of_tensor_iso {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {A B : X.Modules}
    (h : ((tens X).obj A).obj L ≅ ((tens X).obj B).obj L) : Nonempty (A ≅ B) := by
  haveI : ((tens X).flip.obj L).IsEquivalence :=
    (isInvertible_iff_tensorRightFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L).1
      inferInstance
  exact ⟨((tens X).flip.obj L).preimageIso h⟩

/-- `𝒪_X(n D) ≅ 𝒪_X(D)^{⊗ n}` for a Cartier divisor `D` and an integer `n`. -/
private theorem nonempty_divisorialSheaf_zsmul_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D : Divisor X} (hD : D.IsCartier) (n : ℤ) :
    haveI := hD.isInvertibleModule_divisorialSheaf
    Nonempty ((n • D).divisorialSheaf ≅
      tensorPower X.presheaf X.ringCatSheaf.2 D.divisorialSheaf n) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  set L := D.divisorialSheaf
  induction n using Int.induction_on with
  | zero => exact ⟨eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso⟩
  | succ i ih =>
    obtain ⟨e⟩ := ih
    have h : (((i : ℤ) + 1) • D).divisorialSheaf ≅
        ((tens X).obj ((i : ℤ) • D).divisorialSheaf).obj L :=
      eqToIso (by rw [add_smul, one_smul]) ≪≫ (((hD.zsmul i).divisorialSheafTensorIso hD)).symm
    exact ⟨h ≪≫ ((tens X).mapIso e).app L ≪≫ tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L i⟩
  | pred i ih =>
    obtain ⟨e⟩ := ih
    have h : ((tens X).obj ((-(i : ℤ) - 1) • D).divisorialSheaf).obj L ≅
        ((-(i : ℤ)) • D).divisorialSheaf :=
      (hD.zsmul _).divisorialSheafTensorIso hD ≪≫
        eqToIso (by rw [sub_smul, one_smul, sub_add_cancel])
    have h2 : ((tens X).obj (tensorPower X.presheaf X.ringCatSheaf.2 L (-(i : ℤ) - 1))).obj L ≅
        ((-(i : ℤ)) • D).divisorialSheaf :=
      tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L _ ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 L (n := -(i : ℤ) - 1 + 1) (m := -(i : ℤ))
          (by ring) ≪≫ e.symm
    exact nonempty_iso_of_tensor_iso L (h.trans h2.symm)

private theorem nonempty_fold_iso {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {r : ℕ} (L : Fin r → Divisor X) (hL : ∀ i, (L i).IsCartier)
    (n : Fin r → ℤ) (l : List (Fin r)) :
    haveI := fun i => (hL i).isInvertibleModule_divisorialSheaf
    ∀ (M : X.Modules) (D : Divisor X), D.IsCartier → Nonempty (D.divisorialSheaf ≅ M) →
      Nonempty (l.foldl (fun M i => ((tens X).obj M).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 (L i).divisorialSheaf (n i))) M ≅
        (D + (l.map fun i => n i • L i).sum).divisorialSheaf) := by
  haveI := fun i => (hL i).isInvertibleModule_divisorialSheaf
  induction l with
  | nil => exact fun M D _ ⟨e⟩ => ⟨e.symm ≪≫ eqToIso (by simp)⟩
  | cons a l ih =>
    intro M D hDc ⟨e⟩
    obtain ⟨e'⟩ := nonempty_divisorialSheaf_zsmul_iso (hL a) (n a)
    have h : (D + n a • L a).divisorialSheaf ≅ ((tens X).obj M).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 (L a).divisorialSheaf (n a)) :=
      (hDc.divisorialSheafTensorIso ((hL a).zsmul (n a))).symm ≪≫
        tensorProductIso X.presheaf X.ringCatSheaf.2 e e'
    obtain ⟨g⟩ := ih _ _ (hDc.add ((hL a).zsmul (n a))) ⟨h⟩
    exact ⟨g ≪≫ eqToIso (by simp [add_assoc])⟩

/-- `𝒪_X(∑ᵢ nᵢ Lᵢ)` is the twist of `𝒪_X` by the `𝒪_X(Lᵢ)^{⊗ nᵢ}`, for Cartier divisors `Lᵢ`. -/
private theorem nonempty_divisorialSheaf_sum_iso_twistedSheaf {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {r : ℕ} (L : Fin r → Divisor X)
    (hL : ∀ i, (L i).IsCartier) (n : Fin r → ℤ) :
    haveI := fun i => (hL i).isInvertibleModule_divisorialSheaf
    Nonempty ((∑ i, n i • L i).divisorialSheaf ≅
      twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun i => (L i).divisorialSheaf) n) := by
  haveI := fun i => (hL i).isInvertibleModule_divisorialSheaf
  obtain ⟨g⟩ := nonempty_fold_iso L hL n (List.finRange r) _ 0 Divisor.isCartier_zero
    ⟨Divisor.divisorialSheafZeroIso⟩
  refine ⟨eqToIso ?_ ≪≫ g.symm⟩
  rw [zero_add, Fin.sum_univ_def]

end Sheaves

/-- **Snapper's theorem for Cartier Weil divisors.** On a scheme `X` proper over a field `k`, of
dimension `n`, with Cartier divisors `L₀, …, L_{r-1}`, the function
`m ↦ χ(X, 𝒪_X(∑ⱼ mⱼ Lⱼ))` on `ℤ^r` is a rational polynomial of total degree at most `n`. -/
private theorem exists_eval_eq_eulerSum_divisorialSheaf_sum (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [IsProper f]
    {n : ℕ} (hn : topologicalKrullDim X = n) {r : ℕ} (L : Fin r → Divisor X)
    (hL : ∀ j, (L j).IsCartier) :
    ∃ Q : MvPolynomial (Fin r) ℚ, Q.totalDegree ≤ n ∧
      ∀ m : Fin r → ℤ, MvPolynomial.eval (fun j => (m j : ℚ)) Q =
        ((∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k f
          (∑ j, m j • L j).divisorialSheaf j) : ℤ) : ℤ) : ℚ) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI := fun j => (hL j).isInvertibleModule_divisorialSheaf
  obtain ⟨Q, hQ0, hQ⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f
    (fun j => (L j).divisorialSheaf) (SheafOfModules.unit X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f)
  refine ⟨Q, ?_, fun m => ?_⟩
  · rcases hQ0 with rfl | h
    · simp
    · rw [topologicalKrullDim_supp_unit, hn] at h
      exact_mod_cast h
  · obtain ⟨g⟩ := nonempty_divisorialSheaf_sum_iso_twistedSheaf L hL m
    rw [hQ m, eulerCharacteristic_eq_finsum]
    exact congrArg _ (finsum_congr fun j => by rw [finrank_cohomologyOverField_eq_of_iso k f g j])

/-- **The Euler characteristic function is a polynomial** (Kollár–Mori 3.4 Step 2). Let `Y` be a
smooth proper normal scheme of dimension `n` over `k`, `Dᵢ` (`i ∈ ι`) divisors and `A` a
`ℚ`-divisor on `Y`. Then there is a polynomial `P ∈ ℚ[uᵢ : i ∈ ι]` of total degree at most `n`
whose value at every `u ∈ ℤ^ι` is `χ(Y, 𝒪_Y(∑ᵢ uᵢ Dᵢ + ⌈A⌉))`. -/
@[mmp "lem_km3b_multidivisor_euler_polynomial_is_polynomial"]
public theorem exists_totalDegree_le_eval_eq_eulerPolynomial (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [IsProper f]
    (hsm : IsSmoothScheme f) {n : ℕ} (hn : topologicalKrullDim X = n) {ι : Type*} [Fintype ι]
    (D : ι → Divisor X) (A : QDivisor X) :
    ∃ P : MvPolynomial ι ℚ, P.totalDegree ≤ n ∧
      ∀ u : ι → ℤ, MvPolynomial.eval (fun i => (u i : ℚ)) P = eulerPolynomial k f D A u := by
  let e := Fintype.equivFin ι
  -- `L₀ = ⌈A⌉` and `Lⱼ₊₁ = D (e.symm j)`; every divisor on the smooth `X` is Cartier.
  let L : Fin (Fintype.card ι + 1) → Divisor X :=
    Fin.cons (DivisorWithCoeffs.roundUp A) (D ∘ e.symm)
  obtain ⟨Q, hQd, hQ⟩ := exists_eval_eq_eulerSum_divisorialSheaf_sum k f hn L
    fun _ => MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _
  -- `P(u) = Q(1, u)`.
  let g : Fin (Fintype.card ι + 1) → MvPolynomial ι ℚ := Fin.cons 1 (MvPolynomial.X ∘ e.symm)
  refine ⟨MvPolynomial.bind₁ g Q, (MvPolynomial.totalDegree_aeval_le g
    (Fin.cases (by simp [g]) fun j => by simp [g]) Q).trans hQd, fun u => ?_⟩
  let m : Fin (Fintype.card ι + 1) → ℤ := Fin.cons 1 (u ∘ e.symm)
  have hg : (fun j => MvPolynomial.eval (fun i => (u i : ℚ)) (g j)) = fun j => (m j : ℚ) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [g, m]
  have hL : ∑ j, m j • L j = ∑ i, u i • D i + DivisorWithCoeffs.roundUp A := by
    rw [Fin.sum_univ_succ, add_comm]
    simp only [m, L, Fin.cons_zero, Fin.cons_succ, Function.comp_apply, one_smul]
    rw [Equiv.sum_comp e.symm fun i => u i • D i]
  rw [show MvPolynomial.eval _ (MvPolynomial.bind₁ g Q) =
      MvPolynomial.eval (fun j => MvPolynomial.eval (fun i => (u i : ℚ)) (g j)) Q from
    MvPolynomial.aeval_bind₁ _ g Q, hg, hQ, hL]
  rfl

end MMP.Mori.Divisor

end
