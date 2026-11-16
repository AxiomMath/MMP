/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# Adapted coordinates along a smooth flag

Let `X` be a smooth scheme over a field `k` of characteristic `0`, `Z ⊆ X` a smooth closed
subscheme lying on a smooth hypersurface `S ⊇ Z`, and `p ∈ Z` a closed point. There are local
coordinates `x_1, …, x_r, y_1, …, y_m` at `p` on a neighbourhood `U`, `r = codim_p(Z, X) ≥ 1`,
with `Z ∩ U = (x_1 = ⋯ = x_r = 0)`, `S ∩ U = (x_1 = 0)` and the `y_j|_{Z ∩ U}` local coordinates
on `Z ∩ U`.

Conventions (closed subschemes as ideal sheaves, equations read on affine opens, local
dimensions through `ringKrullDim` of stalks) are those of
`MMP.Foundations.Flips.ResolutionInputs.SmoothParameters`.

## Main results

* `MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesAt_flag`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Def. 3.73, 3.75]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace MMP.Flips.ResolutionInputs

open MMP.Resolution

/-! ### Regular systems of parameters adapted to a flag of regular quotients -/

section FlagAlgebra

open MMP.Mori

/-- The image of the ideal spanned by a family is spanned by the image family. -/
theorem map_span_range_eq_of_forall {A B F ι : Type*} [Semiring A] [Semiring B] [FunLike F A B]
    [RingHomClass F A B] (f : F) {v : ι → A} {w : ι → B} (h : ∀ i, f (v i) = w i) :
    (Ideal.span (Set.range v)).map f = Ideal.span (Set.range w) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 2
  exact funext h

/-- The image of the remaining parameters under a surjection of local rings killing the first
ones is a regular system of parameters, when the target has the expected dimension. -/
theorem isRegularSystemOfParameters_map_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) (hφ : Function.Surjective φ) {r m : ℕ}
    {x : Fin r → A} {y : Fin m → A} (h : IsRegularSystemOfParameters (Fin.append x y))
    (hker : RingHom.ker φ = Ideal.span (Set.range x)) (hdim : ringKrullDim B = m) :
    IsRegularSystemOfParameters (fun j => φ (y j)) := by
  refine ⟨?_, hdim⟩
  have h1 : Ideal.span (Set.range fun j => φ (y j)) = (Ideal.span (Set.range y)).map φ :=
    (map_span_range_eq_of_forall φ (v := y) fun _ => rfl).symm
  have h2 : (Ideal.span (Set.range x)).map φ = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, hker]
  rw [h1, ← map_maximalIdeal_of_surjective φ hφ, ← h.1, span_range_append, Ideal.map_sup, h2,
    bot_sup_eq]

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- A regular quotient `R / I` of a regular local ring is the quotient by a finite family of
`dim R - dim R / I` elements. -/
theorem exists_fin_span_eq_of_isRegularLocalRing_quotient (I : Ideal R)
    (hI : IsRegularLocalRing (R ⧸ I)) :
    ∃ (k : ℕ) (h : Fin k → R), Ideal.span (Set.range h) = I ∧
      ringKrullDim (R ⧸ I) + k = ringKrullDim R := by
  obtain ⟨xs, -, -, c, hc, hcI, hdim⟩ :=
    IsRegularLocalRing.exists_ofList_eq_maximalIdeal_length_eq_spanFinrank_and_ofList_take_eq I hI
  refine ⟨(xs.take c).length, fun i => (xs.take c).get i, ?_, ?_⟩
  · rw [← ofList_ofFn, List.ofFn_get, hcI]
  · rwa [List.length_take_of_le hc]

/-- A regular quotient `R / I` of a regular local ring of codimension one is the quotient by a
single element. -/
theorem exists_eq_span_singleton_of_isRegularLocalRing_quotient (I : Ideal R)
    (hI : IsRegularLocalRing (R ⧸ I)) (hIdim : ringKrullDim (R ⧸ I) + 1 = ringKrullDim R) :
    ∃ f, I = Ideal.span {f} := by
  obtain ⟨k, h, hhI, hkdim⟩ := exists_fin_span_eq_of_isRegularLocalRing_quotient I hI
  have hdI : ringKrullDim (R ⧸ I) = ((maximalIdeal (R ⧸ I)).spanFinrank : ℕ) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)).symm
  rw [← hIdim, hdI] at hkdim
  have hk : k = 1 := by
    have : (maximalIdeal (R ⧸ I)).spanFinrank + k = (maximalIdeal (R ⧸ I)).spanFinrank + 1 := by
      exact_mod_cast hkdim
    omega
  subst hk
  refine ⟨h 0, ?_⟩
  rw [← hhI, Set.range_unique]
  rfl

/-- In a regular local ring, the quotient by a prime of height one has codimension one. -/
theorem ringKrullDim_quotient_add_one_of_height_eq_one (P : Ideal R) [P.IsPrime]
    (hP : P.height = 1) : ringKrullDim (R ⧸ P) + 1 = ringKrullDim R := by
  rw [(IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
    R).2.ringKrullDim_eq_height_add_ringKrullDim_quotient P, hP, add_comm]
  rfl

/-- **Parameters adapted to a flag of regular quotients.** Let `R` be a regular local ring of
dimension `r + m`, `r ≥ 1`, and `I ≤ J` ideals with `R / I` regular of dimension `r + m - 1` and
`R / J` regular of dimension `m`. There is a regular system of parameters
`x_1, …, x_r, y_1, …, y_m` with `J = (x_1, …, x_r)` and `I = (x_1)`. -/
theorem exists_flag_isRegularSystemOfParameters {I J : Ideal R} (hIJ : I ≤ J)
    (hI : IsRegularLocalRing (R ⧸ I)) (hIdim : ringKrullDim (R ⧸ I) + 1 = ringKrullDim R)
    (hJ : IsRegularLocalRing (R ⧸ J)) {r m : ℕ} (hr : 1 ≤ r)
    (hR : ringKrullDim R = (r + m : ℕ)) (hJdim : ringKrullDim (R ⧸ J) = m) :
    ∃ (x : Fin r → R) (y : Fin m → R), IsRegularSystemOfParameters (Fin.append x y) ∧
      Ideal.span (Set.range x) = J ∧ I = Ideal.span {x ⟨0, hr⟩} := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨f, hIf⟩ := exists_eq_span_singleton_of_isRegularLocalRing_quotient I hI hIdim
  set R' := R ⧸ I
  have hdI : ringKrullDim R' = ((maximalIdeal R').spanFinrank : ℕ) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R')).symm
  set dI := (maximalIdeal R').spanFinrank
  have hdI' : dI + 1 = r' + 1 + m := by
    rw [hdI, hR] at hIdim
    exact_mod_cast hIdim
  have hIne : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  set J' := J.map (Ideal.Quotient.mk I)
  let e : R' ⧸ J' ≃+* R ⧸ J := DoubleQuot.quotQuotEquivQuotOfLE hIJ
  have hJ' : IsRegularLocalRing (R' ⧸ J') := IsRegularLocalRing.of_ringEquiv e.symm
  have hJ'dim : ringKrullDim (R' ⧸ J') = m := by rw [ringKrullDim_eq_of_ringEquiv e, hJdim]
  obtain ⟨k', h', hh'J, hk'dim⟩ := exists_fin_span_eq_of_isRegularLocalRing_quotient J' hJ'
  have hk' : r' = k' := by
    rw [hJ'dim, hdI] at hk'dim
    have : m + k' = dI := by exact_mod_cast hk'dim
    omega
  subst hk'
  obtain ⟨m', t, htt⟩ := (isRegularLocalRing_quotient_and_add_eq_iff h').mp
    ⟨by rwa [hh'J], by rwa [hh'J]⟩
  have hm' : m = m' := by
    have := htt.2
    rw [hdI] at this
    have : dI = r' + m' := by exact_mod_cast this
    omega
  subst hm'
  choose x' hx' using fun i => Ideal.Quotient.mk_surjective (I := I) (h' i)
  choose y hy using fun j => Ideal.Quotient.mk_surjective (I := I) (t j)
  have hmapf : (Ideal.span {f}).map (Ideal.Quotient.mk I) = ⊥ := by
    rw [← hIf, Ideal.map_quotient_self]
  have hmapx' := map_span_range_eq_of_forall (Ideal.Quotient.mk I) hx'
  have hmapy := map_span_range_eq_of_forall (Ideal.Quotient.mk I) hy
  set x : Fin (r' + 1) → R := Fin.cons f x'
  have hspanx : Ideal.span (Set.range x) = Ideal.span {f} ⊔ Ideal.span (Set.range x') := by
    rw [Fin.range_cons, Ideal.span_insert]
  have hIx : I ≤ Ideal.span (Set.range x) := by
    rw [hspanx, hIf]
    exact le_sup_left
  have hxJ : Ideal.span (Set.range x) = J := by
    rw [← Ideal.comap_map_mk hIx, ← Ideal.comap_map_mk hIJ]
    congr 1
    rw [hspanx, Ideal.map_sup, hmapf, bot_sup_eq, hmapx', hh'J]
  refine ⟨x, y, ⟨?_, ?_⟩, hxJ, hIf⟩
  · have hIK : I ≤ Ideal.span (Set.range (Fin.append x y)) := by
      rw [span_range_append]
      exact le_sup_of_le_left hIx
    rw [← Ideal.comap_map_mk hIK, ← Ideal.comap_map_mk (le_maximalIdeal hIne),
      map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← htt.1]
    congr 1
    rw [span_range_append, span_range_append, Ideal.map_sup, hspanx, Ideal.map_sup, hmapf,
      bot_sup_eq, hmapx', hmapy]
  · rw [hR]

end FlagAlgebra

/-! ### Closed subschemes: stalks, smoothness, codimension one, spreading out -/

section Subschemes

/-- Restriction along `U ⊆ V ⊆ W` is restriction along `U ⊆ W`. -/
theorem presheaf_map_homOfLE_comp_apply {Y : Scheme.{u}} {U V W : Y.Opens} (h1 : V ≤ W)
    (h2 : U ≤ V) (a : Γ(Y, W)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom a) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- If the images of `J` in a localization lie in those of `J'` and `J` is finitely generated,
some `a ∈ M` multiplies `J` into `J'`. -/
theorem exists_mem_forall_mul_mem_of_map_le {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] {J J' : Ideal A} (hJ : J.FG)
    (h : J.map (algebraMap A S) ≤ J'.map (algebraMap A S)) : ∃ a ∈ M, ∀ g ∈ J, a * g ∈ J' := by
  classical
  obtain ⟨G, rfl⟩ := hJ
  have hg : ∀ g ∈ G, ∃ a ∈ M, a * g ∈ J' := by
    intro g hg
    have hmem : algebraMap A S g ∈ J'.map (algebraMap A S) :=
      h (Ideal.mem_map_of_mem _ (Ideal.subset_span hg))
    obtain ⟨⟨b, c⟩, hbc⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hmem
    rw [← map_mul] at hbc
    obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := M) hbc
    refine ⟨d * c, mul_mem d.2 c.2, ?_⟩
    have : (d : A) * c * g = d * b := by
      rw [← hd]
      ring
    rw [this]
    exact J'.mul_mem_left _ b.2
  choose! a ha hag using hg
  refine ⟨∏ g ∈ G, a g, prod_mem fun g hg => ha g hg, fun g hgJ => ?_⟩
  induction hgJ using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.mul_prod_erase G a hg, mul_comm (a g), mul_assoc]
    exact J'.mul_mem_left _ (hag g hg)
  | zero => simp
  | add u v _ _ hu hv =>
    rw [mul_add]
    exact J'.add_mem hu hv
  | smul c u _ hu =>
    rw [smul_eq_mul, mul_left_comm]
    exact J'.mul_mem_left _ hu

/-- If `b` maps to a unit and multiplies `K` into `K'`, the image of `K` lies in that of `K'`. -/
theorem map_le_map_of_isUnit_of_forall_mul_mem {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) {K K' : Ideal A} {b : A} (hb : IsUnit (f b)) (hK : ∀ g ∈ K, b * g ∈ K') :
    K.map f ≤ K'.map f := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hb, ← map_mul]
  exact Ideal.mem_map_of_mem _ (hK g hg)

/-- A prime lying between an ideal `J` and the contraction of `P = J S` from a localization at a
prime is that contraction. -/
theorem eq_under_of_le_of_map_eq {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (𝔭 : Ideal A) [𝔭.IsPrime] [IsLocalization.AtPrime S 𝔭] {P : Ideal S} {J : Ideal A}
    (hPJ : P = J.map (algebraMap A S)) (hP𝔭 : P.under A ≤ 𝔭) {q : Ideal A} [q.IsPrime]
    (hqP : q ≤ P.under A) (hJq : J ≤ q) : q = P.under A := by
  refine le_antisymm hqP ?_
  have h1 : q.map (algebraMap A S) = P :=
    le_antisymm ((Ideal.map_mono hqP).trans (IsLocalization.map_under 𝔭.primeCompl _ P).le)
      (hPJ ▸ Ideal.map_mono hJq)
  have hdisj : Disjoint (𝔭.primeCompl : Set A) q :=
    Set.disjoint_left.mpr fun a ha hb => ha (hP𝔭 (hqP hb))
  rw [← IsLocalization.under_map_of_isPrime_disjoint 𝔭.primeCompl S inferInstance hdisj, h1]

variable {X : Scheme.{u}}

/-- The local ring of a closed subscheme is the quotient by the stalk of its ideal sheaf. -/
def stalkQuotientEquiv (T : X.IdealSheafData) (z : T.subscheme) :
    X.presheaf.stalk (T.subschemeι z) ⧸ IdealSheafData.stalk T (T.subschemeι z) ≃+*
      T.subscheme.presheaf.stalk z :=
  (Ideal.quotEquivOfEq (IdealSheafData.ker_stalkMap_subschemeι_eq_stalk T z).symm).trans
    (RingHom.quotientKerEquivOfSurjective (T.subschemeι.stalkMap_surjective z))

/-- Stalks of ideal sheaves are monotone. -/
theorem stalk_mono {T T' : X.IdealSheafData} (h : T ≤ T') (x : X) :
    IdealSheafData.stalk T x ≤ IdealSheafData.stalk T' x :=
  iSup_mono fun U => iSup_mono fun _ => Ideal.map_mono (h U)

/-- At a point of a closed subscheme smooth over a perfect field, the quotient of the local ring
by the stalk of the ideal sheaf is regular. -/
theorem isRegularLocalRing_quotient_stalk {k : Type u} [Field k] [PerfectField k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (T : X.IdealSheafData)
    (hT : MMP.Mori.IsSmoothScheme (T.subschemeι ≫ sX)) {x : X} (hx : x ∈ T.support) :
    IsRegularLocalRing (X.presheaf.stalk x ⧸ IdealSheafData.stalk T x) := by
  obtain ⟨z, rfl⟩ : ∃ z, T.subschemeι z = x := by
    rwa [← SetLike.mem_coe, ← T.range_subschemeι] at hx
  have : LocallyOfFinitePresentation (T.subschemeι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := T.subschemeι ≫ sX)).mpr
      inferInstance
  have : Smooth (T.subschemeι ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hT
  have := (smooth_iff_forall_isRegularLocalRing_stalk (T.subschemeι ≫ sX)).mp inferInstance z
  exact IsRegularLocalRing.of_ringEquiv (stalkQuotientEquiv T z).symm

/-- A point of an affine open `W` lies in the support of `T` iff its prime contains the ideal of
`T` on `W`. -/
theorem fromSpec_mem_support_iff (T : X.IdealSheafData) {W : X.Opens} (hW : IsAffineOpen W)
    (q : Spec Γ(X, W)) : hW.fromSpec q ∈ T.support ↔ T.ideal ⟨W, hW⟩ ≤ q.asIdeal := by
  have hqW : hW.fromSpec q ∈ W := by
    rw [← SetLike.mem_coe, ← hW.range_fromSpec]
    exact ⟨q, rfl⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hqW, ← Set.mem_preimage,
    hW.fromSpec_preimage_zeroLocus]
  exact PrimeSpectrum.mem_zeroLocus _ _

/-- A prime minimal over the ideal of `T` on an affine open is the generic point of an
irreducible component of the support of `T`. -/
theorem maximal_irreducibleSetEquivPoints_symm_fromSpec (T : X.IdealSheafData) {W : X.Opens}
    (hW : IsAffineOpen W) (q : Spec Γ(X, W)) (hTq : T.ideal ⟨W, hW⟩ ≤ q.asIdeal)
    (hmin : ∀ q' : Spec Γ(X, W), T.ideal ⟨W, hW⟩ ≤ q'.asIdeal → q'.asIdeal ≤ q.asIdeal → q' = q) :
    Maximal (fun W' : TopologicalSpace.IrreducibleCloseds X => (W' : Set X) ⊆ T.support)
      (irreducibleSetEquivPoints.symm (hW.fromSpec q)) := by
  set e := irreducibleSetEquivPoints (α := X)
  set F := hW.fromSpec
  have hFind : Topology.IsInducing F := F.isOpenEmbedding.isInducing
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {F q} ⊆ _
    exact closure_minimal (Set.singleton_subset_iff.mpr ((fromSpec_mem_support_iff T hW q).2 hTq))
      T.support.isClosed
  · set ξ := e W'
    have hξη : ξ ⤳ F q := by
      have := e.monotone hle
      rwa [e.apply_symm_apply] at this
    have hqW : F q ∈ W := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]
      exact ⟨q, rfl⟩
    obtain ⟨ξ', hξ'⟩ : ξ ∈ Set.range F := by
      rw [hW.range_fromSpec]
      exact hξη.mem_open W.2 hqW
    have hξ'q : ξ'.asIdeal ≤ q.asIdeal := by
      rw [← hξ'] at hξη
      exact (PrimeSpectrum.le_iff_specializes _ _).mpr (hFind.specializes_iff.mp hξη)
    have hξmem : ξ ∈ (W' : Set X) := by
      have hW'ξ : (W' : Set X) = closure {ξ} := by
        conv_lhs => rw [← e.symm_apply_apply W']
        rfl
      rw [hW'ξ]
      exact subset_closure rfl
    have hξq : ξ = F q := by
      rw [← hξ', hmin ξ' ((fromSpec_mem_support_iff T hW ξ').1 (hξ' ▸ hW' hξmem)) hξ'q]
    rw [← e.le_iff_le, e.apply_symm_apply]
    exact hξq.le

/-- **A smooth hypersurface is cut out by a height-one prime.** If the support of `T` has pure
codimension one and the stalk of `T` at `x` is prime, it has height one. -/
theorem height_stalk_eq_one_of_isPureCodimOne [IsLocallyNoetherian X] (T : X.IdealSheafData)
    (hT : MMP.Mori.IsPureCodimOne T.support) {x : X}
    [hP : (IdealSheafData.stalk T x).IsPrime] : (IdealSheafData.stalk T x).height = 1 := by
  obtain ⟨W0, hW0, hxW0, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let W0a : X.affineOpens := ⟨W0, hW0⟩
  let : Algebra Γ(X, W0) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxW0⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hW0.primeIdealOf ⟨x, hxW0⟩).asIdeal :=
    hW0.isLocalization_stalk ⟨x, hxW0⟩
  set 𝔭 := hW0.primeIdealOf ⟨x, hxW0⟩
  set P := IdealSheafData.stalk T x
  set J := T.ideal W0a
  have hPJ : P = J.map (algebraMap Γ(X, W0) (X.presheaf.stalk x)) :=
    IdealSheafData.stalk_eq_map_germ T x W0a hxW0
  set Q := P.under Γ(X, W0)
  have hQ𝔭 : Q ≤ 𝔭.asIdeal := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x) 𝔭.asIdeal]
    exact Ideal.comap_mono (le_maximalIdeal hP.ne_top)
  have hPQ : P.height = Q.height := (IsLocalization.height_under 𝔭.asIdeal.primeCompl P).symm
  have hJQ : J ≤ Q := fun g hg => by
    change algebraMap _ _ g ∈ P
    rw [hPJ]
    exact Ideal.mem_map_of_mem _ hg
  set F := hW0.fromSpec
  let qQ : Spec Γ(X, W0) := (⟨Q, inferInstance⟩ : PrimeSpectrum Γ(X, W0))
  set η := F qQ
  set e := irreducibleSetEquivPoints (α := X)
  set Wη := e.symm η
  have hmax : Maximal (fun W' : TopologicalSpace.IrreducibleCloseds X =>
      (W' : Set X) ⊆ T.support) Wη :=
    maximal_irreducibleSetEquivPoints_symm_fromSpec T hW0 qQ hJQ fun q' hJq' hq' =>
      PrimeSpectrum.ext (eq_under_of_le_of_map_eq 𝔭.asIdeal hPJ hQ𝔭 hq' hJq')
  have h1 : codimension Wη = Order.coheight η := by
    change Order.coheight Wη = _
    rw [← Order.coheight_orderIso e Wη, e.apply_symm_apply]
  have h2 : Order.coheight η = Q.height := by
    change Order.coheight (F qQ) = _
    rw [coheight_eq_of_isOpenImmersion F, ← idealHeight_eq_coheight]
  rw [hPQ, ← h2, ← h1, hT Wη hmax]

/-- **Spreading out an equality of ideals from a stalk.** If the germs at `x` of finitely many
sections `s_i` over `V ∋ x` generate the stalk of `T` at `x`, then the `s_i` generate `T` on
every affine open inside some neighbourhood `U ⊆ V` of `x`. -/
theorem exists_ideal_eq_span_of_stalk_eq [IsLocallyNoetherian X] (T : X.IdealSheafData)
    {V : X.Opens} {x : X} (hx : x ∈ V) {ι : Type*} [Finite ι] (s : ι → Γ(X, V))
    (hs : IdealSheafData.stalk T x =
      Ideal.span (Set.range fun i => (X.presheaf.germ V x hx).hom (s i))) :
    ∃ (U : X.Opens) (hUV : U ≤ V), x ∈ U ∧ ∀ (W : X.affineOpens) (h : W.1 ≤ U),
      T.ideal W = Ideal.span (Set.range fun i => restrictSection W (h.trans hUV) (s i)) := by
  obtain ⟨W0, hW0, hxW0, hW0V'⟩ := exists_isAffineOpen_mem_and_subset hx
  have hW0V : W0 ≤ V := hW0V'
  let W0a : X.affineOpens := ⟨W0, hW0⟩
  let : Algebra Γ(X, W0) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxW0⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hW0.primeIdealOf ⟨x, hxW0⟩).asIdeal :=
    hW0.isLocalization_stalk ⟨x, hxW0⟩
  have halg : algebraMap Γ(X, W0) (X.presheaf.stalk x) = (X.presheaf.germ W0 x hxW0).hom := rfl
  set J := T.ideal W0a
  set J' := Ideal.span (Set.range fun i => restrictSection W0a hW0V (s i))
  have hJ : J.map (algebraMap _ _) = IdealSheafData.stalk T x := by
    rw [halg, IdealSheafData.stalk_eq_map_germ T x W0a hxW0]
  have hJ' : J'.map (algebraMap _ _) = IdealSheafData.stalk T x := by
    rw [hs, halg]
    exact map_span_range_eq_of_forall _ fun i => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have : IsNoetherianRing Γ(X, W0) := IsLocallyNoetherian.component_noetherian W0a
  set M := (hW0.primeIdealOf ⟨x, hxW0⟩).asIdeal.primeCompl
  obtain ⟨a1, ha1, h1⟩ := exists_mem_forall_mul_mem_of_map_le (S := X.presheaf.stalk x) M
    (IsNoetherian.noetherian J) (hJ.trans hJ'.symm).le
  obtain ⟨a2, ha2, h2⟩ := exists_mem_forall_mul_mem_of_map_le (S := X.presheaf.stalk x) (J := J')
    M (Submodule.fg_span (Set.finite_range _)) (hJ'.trans hJ.symm).le
  set a := a1 * a2
  have hxa : x ∈ X.basicOpen a := by
    rw [Scheme.mem_basicOpen X a x hxW0]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) _ a).mpr
      (mul_mem ha1 ha2)
  refine ⟨X.basicOpen a, (X.basicOpen_le a).trans hW0V, hxa, fun W hW => ?_⟩
  have hWW0 : W.1 ≤ W0 := hW.trans (X.basicOpen_le a)
  set ρ := (X.presheaf.map (homOfLE hWW0).op).hom
  have hu : IsUnit (ρ a) := by
    have h1 : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom a) :=
      RingedSpace.isUnit_res_basicOpen X.toRingedSpace a
    have := h1.map (X.presheaf.map (homOfLE hW).op).hom
    rwa [← CommRingCat.comp_apply, ← Functor.map_comp] at this
  have hu' : IsUnit (ρ a1 * ρ a2) := by rwa [← map_mul]
  have hTW : T.ideal W = J.map ρ := (T.map_ideal (show W ≤ W0a from hWW0)).symm
  have hsW : Ideal.span (Set.range fun i =>
      restrictSection W (hW.trans ((X.basicOpen_le a).trans hW0V)) (s i)) = J'.map ρ :=
    (map_span_range_eq_of_forall ρ (v := fun i => restrictSection W0a hW0V (s i)) fun i =>
      presheaf_map_homOfLE_comp_apply hW0V hWW0 (s i)).symm
  rw [hTW, hsW]
  exact le_antisymm
    (map_le_map_of_isUnit_of_forall_mul_mem ρ (isUnit_of_mul_isUnit_left hu') h1)
    (map_le_map_of_isUnit_of_forall_mul_mem ρ (isUnit_of_mul_isUnit_right hu') h2)

/-- Finitely many sections with the same germs at `y` agree on a neighbourhood of `y`. -/
theorem exists_res_eq_of_germ_eq {Y : Scheme.{u}} {V V' : Y.Opens} {y : Y} (hy : y ∈ V)
    (hy' : y ∈ V') {ι : Type*} [Finite ι] (a : ι → Γ(Y, V)) (b : ι → Γ(Y, V'))
    (h : ∀ i, (Y.presheaf.germ V y hy).hom (a i) = (Y.presheaf.germ V' y hy').hom (b i)) :
    ∃ (W : Y.Opens) (hW : W ≤ V) (hW' : W ≤ V'), y ∈ W ∧
      ∀ i, (Y.presheaf.map (homOfLE hW).op).hom (a i) =
        (Y.presheaf.map (homOfLE hW').op).hom (b i) := by
  choose W hyW iU iV hW using fun i => Y.presheaf.germ_eq y hy hy' (a i) (b i) (h i)
  let W0 : Y.Opens := V ⊓ V' ⊓ ⟨⋂ i, (W i : Set Y), isOpen_iInter_of_finite fun i => (W i).2⟩
  have hle : ∀ i, W0 ≤ W i := fun i _ h => Set.mem_iInter.mp h.2 i
  refine ⟨W0, fun _ h => h.1.1, fun _ h => h.1.2, ⟨⟨hy, hy'⟩, Set.mem_iInter.mpr hyW⟩, fun i => ?_⟩
  have e := congrArg (Y.presheaf.map (homOfLE (hle i)).op).hom (hW i)
  rwa [← CommRingCat.comp_apply, ← Functor.map_comp, ← CommRingCat.comp_apply,
    ← Functor.map_comp] at e

end Subschemes

/-! ### Restricting local coordinates -/

section Restrict

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- Restricting a section from `U` to `U'` and then to an affine open `W ≤ U'` agrees with
restricting it from `U` to `W` directly. -/
theorem restrictSection_res {U U' : X.Opens} (hU : U' ≤ U) (W : X.affineOpens) (h : W.1 ≤ U')
    (f : Γ(X, U)) :
    restrictSection W h ((X.presheaf.map (homOfLE hU).op).hom f) =
      restrictSection W (h.trans hU) f :=
  presheaf_map_homOfLE_comp_apply hU h f

/-- Local coordinates on `U` restrict to local coordinates on a smaller open. -/
theorem IsLocalCoordinatesOn.res {U U' : X.Opens} (hU : U' ≤ U) {n : ℕ} {x : Fin n → Γ(X, U)}
    (hx : IsLocalCoordinatesOn sX U x) :
    IsLocalCoordinatesOn sX U' (fun i => (X.presheaf.map (homOfLE hU).op).hom (x i)) := by
  intro W hW
  obtain ⟨b, hb⟩ := hx W (hW.trans hU)
  exact ⟨b, fun i => by rw [hb i, restrictSection_res]⟩

/-- Local coordinates at `p` on `U` restrict to local coordinates at `p` on a smaller open. -/
theorem IsLocalCoordinatesAt.res {U U' : X.Opens} (hU : U' ≤ U) {n : ℕ} {x : Fin n → Γ(X, U)}
    {p : X} (hp : p ∈ U') (hx : IsLocalCoordinatesAt sX U x p (hU hp)) :
    IsLocalCoordinatesAt sX U' (fun i => (X.presheaf.map (homOfLE hU).op).hom (x i)) p hp := by
  refine ⟨IsLocalCoordinatesOn.res hU hx.1, fun i => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply]
  exact hx.2 i

end Restrict

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- At a point `p` of `Z ⊆ S ⊆ X`, all smooth over a perfect field with `S` a hypersurface, the
local ring `𝒪_{X,p}` has a regular system of parameters adapted to the stalks of `S` and `Z`. -/
theorem exists_flag_isRegularSystemOfParameters_stalk [PerfectField k] [Smooth sX]
    (Z S : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hS : IsSmoothHypersurface sX S) (hZS : S ≤ Z) (q : Z.subscheme) {r m : ℕ} (hr : 1 ≤ r)
    (hdimX : ringKrullDim (X.presheaf.stalk (Z.subschemeι q)) = (r + m : ℕ))
    (hdimZ : ringKrullDim (Z.subscheme.presheaf.stalk q) = m) :
    ∃ (x : Fin r → X.presheaf.stalk (Z.subschemeι q))
      (y : Fin m → X.presheaf.stalk (Z.subschemeι q)),
      MMP.Mori.IsRegularSystemOfParameters (Fin.append x y) ∧
      Ideal.span (Set.range x) = IdealSheafData.stalk Z (Z.subschemeι q) ∧
      IdealSheafData.stalk S (Z.subschemeι q) = Ideal.span {x ⟨0, hr⟩} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set p := Z.subschemeι q
  set R := X.presheaf.stalk p
  have hpZ : p ∈ Z.support := by
    rw [← SetLike.mem_coe, ← Z.range_subschemeι]
    exact ⟨q, rfl⟩
  set IS := IdealSheafData.stalk S p
  have hISreg : IsRegularLocalRing (R ⧸ IS) :=
    isRegularLocalRing_quotient_stalk sX S hS.1 (Scheme.IdealSheafData.support_antitone hZS hpZ)
  have : IsRegularLocalRing R :=
    (smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance p
  have : IS.IsPrime := by
    have : IsDomain (R ⧸ IS) := IsRegularLocalRing.isDomain _
    exact (Ideal.Quotient.isDomain_iff_prime IS).mp this
  have hIZdim : ringKrullDim (R ⧸ IdealSheafData.stalk Z p) = m := by
    rw [← hdimZ]
    exact ringKrullDim_eq_of_ringEquiv (stalkQuotientEquiv Z q)
  exact exists_flag_isRegularSystemOfParameters (stalk_mono hZS p) hISreg
    (ringKrullDim_quotient_add_one_of_height_eq_one IS
      (height_stalk_eq_one_of_isPureCodimOne S hS.2))
    (isRegularLocalRing_quotient_stalk sX Z hZ hpZ) hr hdimX hIZdim

/-- Coordinates at a closed point `p` of `X` with given germs, generating the ideals of `Z` and
`S` on every affine open inside a neighbourhood `U` of `p`, when the germs do so in the stalk. -/
theorem exists_isLocalCoordinatesAt_ideal_eq_span [CharZero k] [Smooth sX]
    (Z S : X.IdealSheafData) {p : X} (hp : IsClosed ({p} : Set X)) {r m : ℕ} (hr : 1 ≤ r)
    {x : Fin r → X.presheaf.stalk p} {y : Fin m → X.presheaf.stalk p}
    (ht : MMP.Mori.IsRegularSystemOfParameters (Fin.append x y))
    (hx : Ideal.span (Set.range x) = IdealSheafData.stalk Z p)
    (hS : IdealSheafData.stalk S p = Ideal.span {x ⟨0, hr⟩}) :
    ∃ (V : X.Opens) (hpV : p ∈ V) (s : Fin (r + m) → Γ(X, V)) (U : X.Opens) (hUV : U ≤ V),
      p ∈ U ∧ (∀ i, (X.presheaf.germ V p hpV).hom (s i) = Fin.append x y i) ∧
      IsLocalCoordinatesAt sX V s p hpV ∧
      (∀ (W : X.affineOpens) (h : W.1 ≤ U),
        Z.ideal W = Ideal.span (Set.range fun i => restrictSection W (h.trans hUV)
          (s (Fin.castAdd m i)))) ∧
      ∀ (W : X.affineOpens) (h : W.1 ≤ U),
        S.ideal W = Ideal.span {restrictSection W (h.trans hUV) (s (Fin.castAdd m ⟨0, hr⟩))} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨V, hpV, s, hs, hsc⟩ :=
    exists_isLocalCoordinatesAt_of_isRegularSystemOfParameters sX p hp _ ht
  have hsx : ∀ i, (X.presheaf.germ V p hpV).hom (s (Fin.castAdd m i)) = x i := fun i => by
    simp [hs]
  obtain ⟨U1, hU1V, hpU1, hU1⟩ := exists_ideal_eq_span_of_stalk_eq Z hpV
    (fun i => s (Fin.castAdd m i)) (by simpa only [hsx] using hx.symm)
  obtain ⟨U2, hU2V, hpU2, hU2⟩ := exists_ideal_eq_span_of_stalk_eq S hpV
    (fun _ : Fin 1 => s (Fin.castAdd m ⟨0, hr⟩)) (by rwa [hsx, Set.range_const])
  refine ⟨V, hpV, s, U1 ⊓ U2, inf_le_left.trans hU1V, ⟨hpU1, hpU2⟩, hs, hsc,
    fun W h => hU1 W (h.trans inf_le_left), fun W h => ?_⟩
  rw [hU2 W (h.trans inf_le_right), Set.range_const]

/-- Coordinates on a smooth closed subscheme `Z` at a closed point `q`, with germs the images of
the parameters complementary to a family generating the stalk of the ideal of `Z`. -/
theorem exists_isLocalCoordinatesAt_subscheme [CharZero k] [LocallyOfFiniteType sX]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (q : Z.subscheme)
    (hq : IsClosed ({Z.subschemeι q} : Set X)) {r m : ℕ}
    {x : Fin r → X.presheaf.stalk (Z.subschemeι q)} {y : Fin m → X.presheaf.stalk (Z.subschemeι q)}
    (ht : MMP.Mori.IsRegularSystemOfParameters (Fin.append x y))
    (hx : Ideal.span (Set.range x) = IdealSheafData.stalk Z (Z.subschemeι q))
    (hdimZ : ringKrullDim (Z.subscheme.presheaf.stalk q) = m) :
    ∃ (VZ : Z.subscheme.Opens) (hqVZ : q ∈ VZ) (z : Fin m → Γ(Z.subscheme, VZ)),
      IsLocalCoordinatesAt (Z.subschemeι ≫ sX) VZ z q hqVZ ∧
      ∀ j, (Z.subscheme.presheaf.germ VZ q hqVZ).hom (z j) =
        (Z.subschemeι.stalkMap q).hom (y j) := by
  have : LocallyOfFinitePresentation (Z.subschemeι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := Z.subschemeι ≫ sX)).mpr
      inferInstance
  have : Smooth (Z.subschemeι ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hZ
  have hker : RingHom.ker (Z.subschemeι.stalkMap q).hom = Ideal.span (Set.range x) := by
    rw [hx]
    exact IdealSheafData.ker_stalkMap_subschemeι_eq_stalk Z q
  have hqcl : IsClosed ({q} : Set Z.subscheme) := by
    have h2 : Z.subschemeι ⁻¹' {Z.subschemeι q} = {q} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact Z.subschemeι.isEmbedding.injective.eq_iff
    simpa only [h2] using hq.preimage Z.subschemeι.continuous
  obtain ⟨VZ, hqVZ, z, hz, hzc⟩ := exists_isLocalCoordinatesAt_of_isRegularSystemOfParameters
    (Z.subschemeι ≫ sX) q hqcl _ (isRegularSystemOfParameters_map_of_surjective _
      (Z.subschemeι.stalkMap_surjective q) ht hker hdimZ)
  exact ⟨VZ, hqVZ, z, hzc, hz⟩

/-- **Adapted coordinates at a closed point of a smooth flag `Z ⊆ S ⊆ X`.** Let `X` be smooth
over a field `k` of characteristic `0`, `Z ⊆ X` a closed subscheme smooth over `k`, `S ⊆ X` a
smooth hypersurface with `Z ⊆ S`, and `p ∈ Z` a closed point (the image of `q ∈ Z`), with
`dim_p X = r + m` and `codim_p(Z, X) = r ≥ 1` (so `dim_p Z = m`). There are an open
neighbourhood `U` of `p` and local coordinates `x_1, …, x_r, y_1, …, y_m` at `p` on `U`
(Kollár Def. 3.73) such that `Z ∩ U = (x_1 = ⋯ = x_r = 0)` and `S ∩ U = (x_1 = 0)` as
subschemes, and `y_1|_{Z ∩ U}, …, y_m|_{Z ∩ U}` are local coordinates on `Z ∩ U`. -/
@[mmp "lem_mmp_foundation_closed_smooth_flag_parameters"]
theorem exists_isLocalCoordinatesAt_flag [CharZero k] (hX : MMP.Mori.IsSmoothScheme sX)
    (Z S : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hS : IsSmoothHypersurface sX S) (hZS : S ≤ Z) (q : Z.subscheme)
    (hq : IsClosed ({Z.subschemeι q} : Set X)) {r m : ℕ} (hr : 1 ≤ r)
    (hdimX : ringKrullDim (X.presheaf.stalk (Z.subschemeι q)) = (r + m : ℕ))
    (hdimZ : ringKrullDim (Z.subscheme.presheaf.stalk q) = m) :
    ∃ (U : X.Opens) (hpU : Z.subschemeι q ∈ U) (x : Fin r → Γ(X, U)) (y : Fin m → Γ(X, U)),
      IsLocalCoordinatesAt sX U (Fin.append x y) (Z.subschemeι q) hpU ∧
      (∀ (W : X.affineOpens) (h : W.1 ≤ U),
        Z.ideal W = Ideal.span (Set.range fun i => restrictSection W h (x i))) ∧
      (∀ (W : X.affineOpens) (h : W.1 ≤ U),
        S.ideal W = Ideal.span {restrictSection W h (x ⟨0, hr⟩)}) ∧
      IsLocalCoordinatesOn (Z.subschemeι ≫ sX) (Z.subschemeι ⁻¹ᵁ U)
        (fun j => (Z.subschemeι.app U).hom (y j)) := by
  have : Smooth sX := by
    have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
      (fun U : {U : X.Opens // Smooth (U.ι ≫ sX)} => U.1) ?_ fun U => U.2
    rw [← hX, MMP.Mori.smoothLocus, sSup_eq_iSup']
    rfl
  set p := Z.subschemeι q
  obtain ⟨x0, y0, ht, hx0, hIS⟩ :=
    exists_flag_isRegularSystemOfParameters_stalk sX Z S hZ hS hZS q hr hdimX hdimZ
  obtain ⟨V, hpV, s, U0, hU0V, hpU0, hs, hsc, hZU0, hSU0⟩ :=
    exists_isLocalCoordinatesAt_ideal_eq_span sX Z S hq hr ht hx0 hIS
  obtain ⟨VZ, hqVZ, z, hzc, hz⟩ := exists_isLocalCoordinatesAt_subscheme sX Z hZ q hq ht hx0 hdimZ
  have hzy : ∀ j, (Z.subscheme.presheaf.germ (Z.subschemeι ⁻¹ᵁ V) q hpV).hom
      ((Z.subschemeι.app V).hom (s (Fin.natAdd r j))) =
        (Z.subscheme.presheaf.germ VZ q hqVZ).hom (z j) := fun j => by
    rw [hz, ← show (X.presheaf.germ V p hpV).hom (s (Fin.natAdd r j)) = y0 j by simp [hs],
      Scheme.Hom.germ_stalkMap_apply]
  obtain ⟨WZ, hWZV, hWZ', hqWZ, hWZeq⟩ := exists_res_eq_of_germ_eq (Y := Z.subscheme)
    (show q ∈ Z.subschemeι ⁻¹ᵁ V from hpV) hqVZ _ _ hzy
  obtain ⟨O, hO, hOpre⟩ := (Z.subschemeι.isEmbedding.isInducing.isOpen_iff).1 WZ.2
  let U : X.Opens := U0 ⊓ ⟨O, hO⟩
  have hpU : p ∈ U := ⟨hpU0, show Z.subschemeι q ∈ O from
    (show q ∈ Z.subschemeι ⁻¹' O from hOpre ▸ hqWZ)⟩
  have hUU0 : U ≤ U0 := inf_le_left
  have hUV : U ≤ V := hUU0.trans hU0V
  have hUWZ : Z.subschemeι ⁻¹ᵁ U ≤ WZ := fun a ha => by
    have : a ∈ Z.subschemeι ⁻¹' O := ha.2
    rwa [hOpre] at this
  refine ⟨U, hpU, fun i => (X.presheaf.map (homOfLE hUV).op).hom (s (Fin.castAdd m i)),
    fun j => (X.presheaf.map (homOfLE hUV).op).hom (s (Fin.natAdd r j)), ?_, fun W h => ?_,
    fun W h => ?_, ?_⟩
  · have happ : Fin.append (fun i => (X.presheaf.map (homOfLE hUV).op).hom (s (Fin.castAdd m i)))
        (fun j => (X.presheaf.map (homOfLE hUV).op).hom (s (Fin.natAdd r j))) =
          fun i => (X.presheaf.map (homOfLE hUV).op).hom (s i) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
    rw [happ]
    exact IsLocalCoordinatesAt.res hUV hpU hsc
  · rw [hZU0 W (h.trans hUU0)]
    simp_rw [restrictSection_res]
  · rw [hSU0 W (h.trans hUU0), restrictSection_res]
  · have hzU : ∀ j, (Z.subschemeι.app U).hom
        ((X.presheaf.map (homOfLE hUV).op).hom (s (Fin.natAdd r j))) =
          (Z.subscheme.presheaf.map (homOfLE (hUWZ.trans hWZ')).op).hom (z j) := fun j => by
      rw [← presheaf_map_homOfLE_comp_apply hWZ' hUWZ (z j), ← hWZeq j,
        presheaf_map_homOfLE_comp_apply hWZV hUWZ]
      exact NatTrans.naturality_apply Z.subschemeι.c (homOfLE hUV).op _
    simp_rw [hzU]
    exact IsLocalCoordinatesOn.res (hUWZ.trans hWZ') hzc.1

end MMP.Flips.ResolutionInputs
