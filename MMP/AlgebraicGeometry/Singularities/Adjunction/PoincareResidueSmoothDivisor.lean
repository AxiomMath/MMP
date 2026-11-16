module
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Local
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible

/-!
# Poincaré residues along a smooth divisor

Let `Y` be a smooth variety of dimension `n + 1` over a field `k`, `T ⊂ Y` a smooth prime divisor
and `τ` a nonzero rational top form on `Y` with a simple pole along `T`. Writing
`τ = g · dt/t ∧ dx₁ ∧ ⋯ ∧ dx_n` in the local ring of `Y` at the generic point of `T`, with `t`
a uniformizer, the *residue* `Res_T τ = ḡ · dx̄₁ ∧ ⋯ ∧ dx̄_n` is a well-defined nonzero rational
top form on `T`, and `div_T(Res_T τ) = (div_Y τ + T)|_T`.
Residues commute with pull-back along a proper birational morphism `g : Y₁ ⟶ Y` of smooth
varieties which is an isomorphism at the generic point of `T`: the residue of `g^*τ` along the
strict transform `T₁` of `T` is the pull-back of `Res_T τ` along `T₁ ⟶ T`.

## Main results

* `MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one`: the residue exists, is unique
  and nonzero, has the stated divisor, and commutes with pull-back to strict transforms.
* `MMP.Fourfold.IsPoincareResidue.pullback`: on a normal variety over a perfect field, the
  residue of `g^*τ` along `T₁` is the pull-back of a residue of `τ` along `T`, for every dominant
  `g : Y₁ ⟶ Y` inducing an isomorphism of the local rings at the generic points of `T₁` and `T`.
* `MMP.Mori.exists_poincareResidue`: the residue on all forms of order `≥ -1`, additive and
  `𝒪_{Y,y}`-semilinear, inducing the exact sequence `0 → ω_Y → ω_Y(T) → ι_* ω_T → 0`
  (the Poincaré residue sequence).
* `MMP.Mori.PrimeDivisor.ord_stalkMap_eq_sum_intersectionLength_mul_ord`: for `T ⟶ Y` a smooth
  integral closed subscheme of a smooth `Y`,
  `v_Q(r|_T) = ∑_E length(𝒪_{T,Q}/I_E 𝒪_{T,Q}) · v_E(r)`.

## Implementation notes

The residue is `MMP.Fourfold.IsPoincareResidue` for `m = 1`, a relation characterising
`Res_T τ` by a presentation in the local ring at the generic point of `T`; the statement asserts
that exactly one form `ρ` satisfies it. The divisor `T` on `Y` is the prime divisor `P` whose
generic point is the image of the generic point of `T`, and `(div_Y τ + T)|_T` is
`MMP.Mori.DivisorWithCoeffs.restrict` along the closed immersion `j : T ⟶ Y`. The strict
transform is an integral closed subscheme `j₁ : T₁ ⟶ Y₁` together with a dominant
`h : T₁ ⟶ T` with `h ≫ j = j₁ ≫ g`; the residue of `g^*τ` is then compared with `h^*(Res_T τ)`
after identifying the structure morphisms `h ≫ j ≫ s_Y = j₁ ≫ g ≫ s_Y`.

Rational forms are elements of `Ω^{n+1}_{k(Y)/k}`, so they are germs at the generic point, and
the residue is a function of the generic-point germ of `σ` at `y`. The sections of `ω_Y(D)`
(`MMP.Mori.twistedCanonicalSheaf`) over an open `U` are the subgroup
`MMP.Mori.pluricanonicalSections sY (n + 1) 1 D U` of rational forms, and restriction maps are
inclusions on nonempty opens. Accordingly the sheaf map `ω_Y(T) → ι_* ω_T` is `Res_T` on every
open `U` meeting `T`, and zero on the opens missing `T`, over which `ι_* ω_T` vanishes. Its
`𝒪_Y`-linearity is the semilinearity over `𝒪_{Y,y}`, through which every section of `𝒪_Y` over
an open meeting `T` acts. Surjectivity of the sheaf map is local surjectivity on sections. The
formula `Res_T (ds/s ∧ τ) = τ|_T` for a regular `n`-form `τ` is the characterisation through
`MMP.Fourfold.IsPoincareResidue`, extended additively over the decomposable forms
`g · dx₁ ∧ ⋯ ∧ dx_n` that generate the regular `n`-forms at `y`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.73
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori.SmoothDivisorResidue

open KaehlerDifferential TensorProduct

private theorem alt_eq_det_smul {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι] (e : Module.Basis ι R M)
    (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) : f v = e.det v • f e := by
  have : f = e.det.smulRight (f e) := by
    refine e.ext_alternating fun σ hσ => ?_
    let p := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσ)
    have h1 : (fun i => e (σ i)) = ⇑e ∘ ⇑p := rfl
    rw [h1, AlternatingMap.smulRight_apply, f.map_perm, e.det.map_perm, e.det_self]
    rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, mul_one, Int.cast_smul_eq_zsmul]
  conv_lhs => rw [this]
  rfl

private theorem ιMulti_sum_eq_det_smul {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {n : ℕ} (c : Matrix (Fin n) (Fin n) R) (u : Fin n → W) :
    exteriorPower.ιMulti R n (fun i => ∑ j, c i j • u j) =
      c.det • exteriorPower.ιMulti R n u := by
  let L : (Fin n → R) →ₗ[R] W := Fintype.linearCombination R u
  let f := (exteriorPower.ιMulti R n (M := W)).compLinearMap L
  have h := alt_eq_det_smul (Pi.basisFun R (Fin n)) f (fun i => c i)
  have e1 : f (fun i => c i) = exteriorPower.ιMulti R n (fun i => ∑ j, c i j • u j) := by
    simp [f, L, Fintype.linearCombination_apply]
  have e2 : f (Pi.basisFun R (Fin n)) = exteriorPower.ιMulti R n u := by
    simp only [f, AlternatingMap.compLinearMap_apply]
    congr 1; funext i
    simp [L, Fintype.linearCombination_apply_single]
  rw [← e1, h, e2, Module.Basis.det_apply]
  congr 1
  rw [← Matrix.det_transpose]
  congr 1

/-- `ιMulti` of a spanning family of `n` vectors generates the `n`-th exterior power. -/
private theorem span_ιMulti_eq_top {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {n : ℕ}
    (e : Fin n → W) (he : Submodule.span R (Set.range e) = ⊤) :
    Submodule.span R {exteriorPower.ιMulti R n e} = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span R n W, Submodule.span_le]
  rintro - ⟨v, rfl⟩
  have : ∀ i, ∃ c : Fin n → R, ∑ j, c j • e j = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).mp (he ▸ Submodule.mem_top)
  choose c hc using this
  have hv : v = fun i => ∑ j, (Matrix.of c) i j • e j := funext fun i => (hc i).symm
  rw [hv, ιMulti_sum_eq_det_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- If `Ω^d_{A/k}` has a generator with nonzero image in `Ω^d_{K/k}` (`d ≠ 0`), then `Ω_{A/k}`
has rank `d`. -/
private theorem finrank_eq_of_generator {k A K : Type*} [CommRing k] [CommRing A] [IsDomain A]
    [Algebra k A] [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [IsFractionRing A K] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] {d : ℕ} (hd : d ≠ 0)
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : MMP.Mori.topFormsMap k A K d σ ≠ 0) : Module.finrank A Ω[A⁄k] = d := by
  have hK := MMP.Mori.finrank_kaehlerDifferential_eq_of_isFractionRing (k := k) (A := A) (K := K)
  have : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis
    ((Module.Free.chooseBasis A Ω[A⁄k]).ofIsLocalizedModule K (nonZeroDivisors A)
      (KaehlerDifferential.map k k A K))
  have hspan := MMP.Mori.span_singleton_topFormsMap (k := k) (K := K) (d := d)
    (nonZeroDivisors A) hσ
  have h1 : Module.finrank K (⋀[K]^d Ω[K⁄k]) = 1 := by
    apply le_antisymm
    · rw [← finrank_top, ← hspan]
      exact (finrank_span_singleton h0).le
    · exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, h0⟩
  rw [exteriorPower.finrank_eq, hK, Nat.choose_eq_one_iff] at h1
  exact h1.resolve_left hd

private theorem map_det_eq_of_row_zero {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (h : ∀ j : Fin n, φ (M 0 j.succ) = 0) :
    φ M.det = φ (M 0 0) * φ (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, map_sum, Fin.sum_univ_succ]
  have : ∑ j : Fin n, φ ((-1) ^ (j.succ : ℕ) * M 0 j.succ *
      (M.submatrix Fin.succ j.succ.succAbove).det) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [map_mul, map_mul, h j, mul_zero, zero_mul]
  rw [this, add_zero, map_mul, map_mul]
  simp [Fin.succAbove_zero]

/-- `Matrix.map` commutes with `det`, in the direction used for rewriting. -/
private theorem det_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) : (M.map f).det = f M.det :=
  (RingHom.map_det f M).symm

section Core

variable {k A K B : Type*} [CommRing k] [CommRing A] [IsDomain A] [Algebra k A] [Field K]
  [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] [Field B] [Algebra k B]
      [Algebra A B] [IsScalarTower k A B]

/-- The image of a combination of differentials under `Ω_A → Ω_R`. -/
private theorem map_sum_smul {R : Type*} [CommRing R] [Algebra k R] [Algebra A R]
    [IsScalarTower k A R]
    {n : ℕ} (c : Fin n → A) (e : Fin n → Ω[A⁄k]) :
    KaehlerDifferential.map k k A R (∑ j, c j • e j) =
      ∑ j, algebraMap A R (c j) • KaehlerDifferential.map k k A R (e j) := by
  simp only [map_sum, LinearMap.map_smul, algebraMap_smul]

/-- **The residue does not depend on the presentation.** -/
private theorem residue_core {n : ℕ} (t0 a0 : A) (x0 : Fin n → A) (ht0 : algebraMap A B t0 = 0)
    (hspan : Submodule.span A (Set.range (Fin.cons (D k A t0) fun i => D k A (x0 i) :
      Fin (n + 1) → Ω[A⁄k])) = ⊤)
    (hne : exteriorPower.ιMulti K (n + 1) (Fin.cons (D k K (algebraMap A K t0))
      fun i => D k K (algebraMap A K (x0 i)) : Fin (n + 1) → Ω[K⁄k]) ≠ 0)
    {t g u : A} (x : Fin n → A) (hu : IsUnit u) (ht : t = u * t0)
    (hτ : (algebraMap A K g * (algebraMap A K t)⁻¹) • exteriorPower.ιMulti K (n + 1)
        (Fin.cons (D k K (algebraMap A K t)) fun i => D k K (algebraMap A K (x i)) :
          Fin (n + 1) → Ω[K⁄k]) =
      (algebraMap A K a0 * (algebraMap A K t0)⁻¹) • exteriorPower.ιMulti K (n + 1)
        (Fin.cons (D k K (algebraMap A K t0)) fun i => D k K (algebraMap A K (x0 i)) :
          Fin (n + 1) → Ω[K⁄k])) :
    algebraMap A B g • exteriorPower.ιMulti B n (fun i => D k B (algebraMap A B (x i))) =
      algebraMap A B a0 • exteriorPower.ιMulti B n (fun i => D k B (algebraMap A B (x0 i))) := by
  classical
  set e : Fin (n + 1) → Ω[A⁄k] := Fin.cons (D k A t0) fun i => D k A (x0 i) with he
  have hmem : ∀ ω : Ω[A⁄k], ∃ c : Fin (n + 1) → A, ∑ j, c j • e j = ω := fun ω =>
    (Submodule.mem_span_range_iff_exists_fun A).mp (hspan ▸ Submodule.mem_top)
  obtain ⟨c, hc⟩ := hmem (D k A u)
  choose r hr using fun i => hmem (D k A (x i))
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
    Fin.cons (fun j => (if j = 0 then u else 0) + t0 * c j) r
  have hM0 : ∀ j, M 0 j = (if j = 0 then u else 0) + t0 * c j := fun j => rfl
  have hMs : ∀ i j, M i.succ j = r i j := fun i j => rfl
  -- the rows of `M` express `dt, dx_i` in terms of `e`
  have hrow : ∀ i, ∑ j, M i j • e j = (Fin.cons (D k A t) fun i => D k A (x i) :
      Fin (n + 1) → Ω[A⁄k]) i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [hM0, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_smul, ← Finset.smul_sum, hc,
        Fin.cons_zero, ht, Derivation.leibniz]
      simp only [he, Fin.cons_zero]
    · simp only [hMs, hr, Fin.cons_succ]
  -- the `K`-side
  have hK : (Fin.cons (D k K (algebraMap A K t)) fun i => D k K (algebraMap A K (x i)) :
      Fin (n + 1) → Ω[K⁄k]) = fun i => ∑ j, (M.map (algebraMap A K)) i j •
        (Fin.cons (D k K (algebraMap A K t0)) fun i => D k K (algebraMap A K (x0 i)) :
          Fin (n + 1) → Ω[K⁄k]) j := by
    funext i
    have := congrArg (KaehlerDifferential.map k k A K) (hrow i)
    rw [map_sum_smul] at this
    calc _ = KaehlerDifferential.map k k A K ((Fin.cons (D k A t) fun i => D k A (x i) :
          Fin (n + 1) → Ω[A⁄k]) i) := by refine Fin.cases ?_ (fun i => ?_) i <;> simp
      _ = _ := this.symm
      _ = _ := Finset.sum_congr rfl fun j _ => by
        rw [Matrix.map_apply]
        congr 1
        refine Fin.cases ?_ (fun j => ?_) j <;> simp [he]
  rw [hK, ιMulti_sum_eq_det_smul, det_map, smul_smul] at hτ
  have hT0 : algebraMap A K t0 ≠ 0 := by
    intro h0
    apply hne
    apply AlternatingMap.map_coord_zero _ (0 : Fin (n + 1))
    simp [h0]
  have hcoef := smul_left_injective K hne hτ
  have hT : algebraMap A K t = algebraMap A K u * algebraMap A K t0 := by rw [ht, map_mul]
  have hkey : g * M.det = a0 * u := by
    apply IsFractionRing.injective A K
    have hu0 : algebraMap A K u ≠ 0 := (hu.map _).ne_zero
    rw [hT] at hcoef
    field_simp at hcoef
    rw [map_mul, map_mul]
    linear_combination hcoef
  -- the `B`-side
  set φ := algebraMap A B
  have hrow0 : ∀ j : Fin n, φ (M 0 j.succ) = 0 := fun j => by
    rw [hM0]; simp [ht0]
  have hdet := map_det_eq_of_row_zero φ M hrow0
  rw [hM0, if_pos rfl] at hdet
  simp only [map_add, map_mul, ht0, zero_mul, add_zero] at hdet
  have hB : (fun i => D k B (φ (x i))) = fun i => ∑ l, ((M.submatrix Fin.succ Fin.succ).map φ) i l •
      (fun l => D k B (φ (x0 l))) l := by
    funext i
    have := congrArg (KaehlerDifferential.map k k A B) (hrow i.succ)
    rw [map_sum_smul, Fin.sum_univ_succ] at this
    simp only [Fin.cons_succ, KaehlerDifferential.map_D, Fin.cons_zero, he] at this
    rw [← this]
    simp [φ, ht0, hMs]
  rw [hB, ιMulti_sum_eq_det_smul, det_map, smul_smul]
  congr 1
  have h2 := congrArg φ hkey
  rw [map_mul, map_mul, hdet] at h2
  have hu' : IsUnit (φ u) := hu.map φ
  apply hu'.mul_right_cancel
  linear_combination h2

end Core

/-- **Nakayama**, for a surjection `A → B` of local rings: a family whose image in `B ⊗ M` is a
basis spans `M`. -/
private theorem span_eq_top_of_isBasis_tmul {A B M : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Nontrivial B] [Algebra A B] (hsurj : Function.Surjective (algebraMap A B))
    [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M] {m : ℕ}
    (hm : Module.finrank A M = m) (v : Fin m → M)
    (hli : LinearIndependent B (fun i => (1 : B) ⊗ₜ[A] v i))
    (hsp : Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] v i) = ⊤) :
    Submodule.span A (Set.range v) = ⊤ := by
  classical
  let b₀ := Module.Free.chooseBasis A M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A M) = m := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hm]
  let b : Module.Basis (Fin m) A M := b₀.reindex (Fintype.equivFinOfCardEq hcard)
  let bB := Algebra.TensorProduct.basis B b
  have hdetB := (bB.is_basis_iff_det).mp ⟨hli, hsp⟩
  have hmat : bB.toMatrix (fun i => (1 : B) ⊗ₜ[A] v i) =
      (b.toMatrix v).map (algebraMap A B) := by
    ext i j
    simp [Module.Basis.toMatrix_apply, bB, Algebra.TensorProduct.basis_repr_tmul]
  rw [Module.Basis.det_apply, hmat, det_map, ← Module.Basis.det_apply] at hdetB
  have hdet : IsUnit (b.det v) := by
    obtain ⟨U, hU⟩ := hdetB
    obtain ⟨w', hw'⟩ := hsurj (↑U⁻¹ : B)
    have hk : b.det v * w' - 1 ∈ RingHom.ker (algebraMap A B) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, hw', ← hU, Units.mul_inv, sub_self]
    have hker : RingHom.ker (algebraMap A B) ≤ IsLocalRing.maximalIdeal A :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    by_contra hnu
    have h1 : b.det v * w' ∈ IsLocalRing.maximalIdeal A :=
      Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have h2 := Ideal.sub_mem _ h1 (hker hk)
    rw [sub_sub_cancel] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  exact ((b.is_basis_iff_det).mpr hdet).2

/-- **Coordinates adapted to a principal smooth quotient of a local ring.** -/
private theorem exists_coordinates_local {k A C : Type*} [Field k] [CommRing A] [IsDomain A]
    [IsLocalRing A] [Algebra k A] [Algebra.FormallySmooth k A] [Module.Free A Ω[A⁄k]]
    [Module.Finite A Ω[A⁄k]] [CommRing C] [IsLocalRing C] [Algebra k C] [Algebra A C]
    [IsScalarTower k A C] [Algebra.FormallySmooth k C] [Module.FinitePresentation C Ω[C⁄k]]
    (hsurj : Function.Surjective (algebraMap A C)) {t0 : A} (ht0 : t0 ≠ 0)
    (hker : RingHom.ker (algebraMap A C) = Ideal.span {t0}) {n : ℕ}
    (hrank : Module.finrank A Ω[A⁄k] = n + 1) :
    ∃ x0 : Fin n → A, Submodule.span A (Set.range (Fin.cons (D k A t0) fun i => D k A (x0 i) :
        Fin (n + 1) → Ω[A⁄k])) = ⊤ ∧
      LinearIndependent C (fun i => D k C (algebraMap A C (x0 i))) ∧
      Submodule.span C (Set.range fun i => D k C (algebraMap A C (x0 i))) = ⊤ := by
  classical
  set φ := algebraMap A C with hφ
  have ht0mem : t0 ∈ RingHom.ker φ := hker ▸ Ideal.mem_span_singleton_self t0
  have hφt0 : φ t0 = 0 := RingHom.mem_ker.mp ht0mem
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := A) (A := C)
    hsurj).mp inferInstance
  set w0 : C ⊗[A] Ω[A⁄k] := (1 : C) ⊗ₜ D k A t0 with hw0def
  have hw0 : kerCotangentToTensor k A C ((RingHom.ker φ).toCotangent ⟨t0, ht0mem⟩) = w0 := by
    rw [kerCotangentToTensor_toCotangent]
  -- `c • w0 = 0` forces `c = 0`
  have hw0inj : ∀ c : C, c • w0 = 0 → c = 0 := by
    intro c hc
    obtain ⟨c', rfl⟩ := hsurj c
    have h1 : c' • (RingHom.ker φ).toCotangent ⟨t0, ht0mem⟩ = 0 := by
      have h2 := congrArg l (show c' • w0 = 0 by rw [← algebraMap_smul C c' w0]; exact hc)
      rw [map_smul, map_zero, ← hw0] at h2
      rw [← h2]
      exact congrArg (c' • ·) (LinearMap.congr_fun hl _).symm
    rw [← map_smul, Ideal.toCotangent_eq_zero] at h1
    have h3 : c' * t0 ∈ (Ideal.span {t0}) ^ 2 := by rw [← hker]; exact h1
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3
    obtain ⟨d, hd⟩ := h3
    have h4 : c' = t0 * d := by
      apply mul_right_cancel₀ ht0
      rw [hd]; ring
    rw [h4, map_mul, hφt0, zero_mul]
  -- the differentials of `C` are free and generated by the `d(φ a)`
  have : Module.Free C Ω[C⁄k] := Module.free_of_flat_of_isLocalRing
  have hspanC : Submodule.span C (Set.range fun a : A => D k C (φ a)) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := hsurj c
    exact Submodule.subset_span ⟨a, rfl⟩
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _ hspanC
  have : Finite κ := Module.Finite.finite_basis b
  let : Fintype κ := Fintype.ofFinite κ
  -- the family `1 ⊗ dt₀, 1 ⊗ d(a i)` is a basis of `C ⊗ Ω_A`
  let w : Fin 1 ⊕ κ → C ⊗[A] Ω[A⁄k] := Sum.elim (fun _ => w0) (fun i => (1 : C) ⊗ₜ D k A (a i))
  have hmapw : ∀ i, KaehlerDifferential.mapBaseChange k A C (w (Sum.inr i)) = b i := by
    intro i
    simp [w, hb, KaehlerDifferential.mapBaseChange_tmul, hφ]
  have hmapw0 : KaehlerDifferential.mapBaseChange k A C w0 = 0 := by
    simp [w0, KaehlerDifferential.mapBaseChange_tmul, ← hφ, hφt0]
  have hker' : ∀ z, KaehlerDifferential.mapBaseChange k A C z = 0 → ∃ c : C, z = c • w0 := by
    intro z hz
    obtain ⟨y, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange k A C hsurj z).mp hz
    obtain ⟨⟨e, he⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
    rw [hker, Ideal.mem_span_singleton'] at he
    obtain ⟨d, rfl⟩ := he
    refine ⟨φ d, ?_⟩
    rw [kerCotangentToTensor_toCotangent, Derivation.leibniz, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← algebraMap_smul C t0,
      ← algebraMap_smul C d, ← hφ, hφt0, zero_smul, add_zero]
  have hli : LinearIndependent C w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hm := congrArg (KaehlerDifferential.mapBaseChange k A C) hg
    rw [map_sum, map_zero, Fintype.sum_sum_type] at hm
    simp only [map_smul, w, Sum.elim_inl, Sum.elim_inr, hmapw0, smul_zero,
      Finset.sum_const_zero, zero_add] at hm
    have hgr : ∀ i, g (Sum.inr i) = 0 := by
      have := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun i => g (Sum.inr i))
      refine this ?_
      rw [← hm]
      exact Finset.sum_congr rfl fun i _ => by rw [← hmapw i]; rfl
    have hgl : g (Sum.inl 0) = 0 := by
      apply hw0inj
      rw [Fintype.sum_sum_type] at hg
      simpa [w, hgr] using hg
    rintro (i | i)
    · rw [Subsingleton.elim i 0]; exact hgl
    · exact hgr i
  have hsp : Submodule.span C (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    set c := b.repr (KaehlerDifferential.mapBaseChange k A C z)
    have hz : KaehlerDifferential.mapBaseChange k A C
        (z - ∑ i, c i • w (Sum.inr i)) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, hmapw]
      rw [b.sum_repr, sub_self]
    obtain ⟨c0, hc0⟩ := hker' _ hz
    have : z = c0 • w (Sum.inl 0) + ∑ i, c i • w (Sum.inr i) := by
      show z = c0 • w0 + _
      rw [← hc0, sub_add_cancel]
    rw [this]
    refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  have hcard : Fintype.card κ = n := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)
    rw [Module.finrank_baseChange, hrank, Fintype.card_sum, Fintype.card_fin] at this
    omega
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  have hbe : (fun i => D k C (φ (a (e.symm i)))) = b ∘ e.symm := by
    funext i; simp [hb]
  refine ⟨fun i => a (e.symm i), ?_, ?_, ?_⟩
  · let σ : Fin (n + 1) → Fin 1 ⊕ κ := Fin.cons (Sum.inl 0) fun i => Sum.inr (e.symm i)
    have heq : w ∘ σ = fun i => (1 : C) ⊗ₜ[A]
        (Fin.cons (D k A t0) fun i => D k A (a (e.symm i)) : Fin (n + 1) → Ω[A⁄k]) i := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [σ, w, w0]
      · simp [σ, w]
    have hσ : Function.Bijective σ := by
      refine ⟨?_, ?_⟩
      · rw [Fin.cons_injective_iff]
        exact ⟨by simp, Sum.inr_injective.comp e.symm.injective⟩
      · rintro (i | i)
        · exact ⟨0, by rw [Subsingleton.elim i 0]; rfl⟩
        · exact ⟨(e i).succ, by simp [σ]⟩
    apply span_eq_top_of_isBasis_tmul hsurj hrank
    · exact heq ▸ hli.comp σ hσ.1
    · rw [← heq, Set.range_comp, hσ.2.range_eq, Set.image_univ, hsp]
  · rw [hbe]
    exact b.linearIndependent.comp _ e.symm.injective
  · rw [hbe, Set.range_comp, e.symm.surjective.range_eq, Set.image_univ, b.span_eq]

section Stalks

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k))

private theorem isScalarTower_stalkMap (j : T ⟶ Y) (x : T) :
    letI := MMP.Mori.stalkAlgebra sY (j x)
    letI := MMP.Mori.stalkAlgebra (j ≫ sY) x
    letI := (j.stalkMap x).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk (j x)) (T.presheaf.stalk x) := by
  let := MMP.Mori.stalkAlgebra sY (j x)
  let := MMP.Mori.stalkAlgebra (j ≫ sY) x
  let := (j.stalkMap x).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ sY).appTop ≫
        T.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
        Y.presheaf.germ ⊤ (j x) (TopologicalSpace.Opens.mem_top _)) ≫ j.stalkMap x := by
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Hom.germ_stalkMap]
    rfl
  exact congrArg CommRingCat.Hom.hom h

variable [IsIntegral Y] [IsLocallyNoetherian Y]

/-- On a scheme smooth over a field, the local ring at a point of codimension one is a discrete
valuation ring. -/
private theorem isDiscreteValuationRing_stalk [Smooth sY] (y : Y) (hy : Order.coheight y = 1) :
    IsDiscreteValuationRing (Y.presheaf.stalk y) := by
  have := isRegularLocalRing_stalk_of_smooth_over_field sY y
  have := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk y)
  have h5 : IsNoetherianRing (Y.presheaf.stalk y) ∧ IsLocalRing (Y.presheaf.stalk y) ∧
      IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) ∧
      ringKrullDim (Y.presheaf.stalk y) = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, by
      rw [ringKrullDim_stalk_eq_coheight, hy]; rfl⟩
  obtain ⟨_, h⟩ := ((_root_.isDiscreteValuationRing_tfae (Y.presheaf.stalk y)).out 5 1).mp h5
  exact h

variable {sY}

private theorem ordHom_algebraMap_irreducible (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {ϖ : Y.presheaf.stalk y}
    (hϖ : Irreducible ϖ) :
    Y.ordHom y hy (algebraMap _ Y.functionField ϖ) = WithZero.exp 1 :=
  Ring.ordFrac_irreducible hϖ

private theorem ordHom_algebraMap_isUnit (y : Y) (hy : Order.coheight y = 1)
    {a : Y.presheaf.stalk y} (ha : IsUnit a) :
    Y.ordHom y hy (algebraMap _ Y.functionField a) = 1 := by
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
  exact Ring.ordFrac_of_isUnit ha

/-- A uniformizer of the local ring at a codimension-one point has order one. -/
private theorem ord_algebraMap_irreducible (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {ϖ : Y.presheaf.stalk y}
    (hϖ : Irreducible ϖ) : Y.ord (algebraMap _ Y.functionField ϖ) y = 1 := by
  rw [Scheme.ord_eq_iff hy ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero),
    ordHom_algebraMap_irreducible y hy hϖ]
  rfl

/-- A unit of the local ring at a codimension-one point has order zero. -/
private theorem ord_algebraMap_of_isUnit (y : Y) (hy : Order.coheight y = 1)
    {a : Y.presheaf.stalk y} (ha : IsUnit a) : Y.ord (algebraMap _ Y.functionField a) y = 0 := by
  rw [Scheme.ord_eq_iff hy ((ha.map _).ne_zero), ordHom_algebraMap_isUnit y hy ha]
  rfl

/-- An element of order one in the local ring at a codimension-one point is a unit multiple of
a uniformizer. -/
private theorem exists_isUnit_eq_mul_of_ord_eq_one (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {ϖ : Y.presheaf.stalk y}
    (hϖ : Irreducible ϖ) {t : Y.presheaf.stalk y}
    (ht : Y.ord (algebraMap _ Y.functionField t) y = 1) :
    ∃ v : Y.presheaf.stalk y, IsUnit v ∧ t = v * ϖ := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  obtain ⟨m, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hϖ
  rw [Scheme.ord_eq_iff hy ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht0), map_mul,
    map_mul, map_pow, map_pow, ordHom_algebraMap_irreducible y hy hϖ,
    ordHom_algebraMap_isUnit y hy w.isUnit, one_mul,
    ← WithZero.exp_nsmul, WithZero.exp_eq_coe_ofAdd] at ht
  have hm : (m : ℤ) • (1 : ℤ) = 1 := by exact_mod_cast WithZero.coe_injective ht
  obtain rfl : m = 1 := by simpa using hm
  exact ⟨w, w.isUnit, by rw [pow_one]⟩

/-- A rational function of order `-1` at a codimension-one point is `a / ϖ` for a unit `a`. -/
private theorem exists_isUnit_eq_div_of_ord_eq_neg_one (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {ϖ : Y.presheaf.stalk y}
    (hϖ : Irreducible ϖ) {f : Y.functionField} (hf0 : f ≠ 0) (hf : Y.ord f y = -1) :
    ∃ a : Y.presheaf.stalk y, IsUnit a ∧
      f = algebraMap _ Y.functionField a * (algebraMap _ Y.functionField ϖ)⁻¹ := by
  obtain ⟨z, w, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hf0
  rw [Scheme.ord_eq_iff hy hf0, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
    ordHom_algebraMap_irreducible y hy hϖ, ordHom_algebraMap_isUnit y hy w.isUnit, one_mul,
    ← WithZero.exp_zsmul, WithZero.exp_eq_coe_ofAdd] at hf
  have hz : z • (1 : ℤ) = -1 := by exact_mod_cast WithZero.coe_injective hf
  obtain rfl : z = -1 := by simpa using hz
  exact ⟨w, w.isUnit, by rw [Units.smul_def, Algebra.smul_def, zpow_neg_one]⟩

end Stalks

private theorem ιMulti_ne_zero_of_linearIndependent {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W]
    {n : ℕ} {v : Fin n → W} (hv : LinearIndependent K v) : exteriorPower.ιMulti K n v ≠ 0 := by
  classical
  let b := Module.Basis.span hv
  have hb : (fun i => ((b i : Submodule.span K (Set.range v)) : W)) = v := by
    funext i
    simp [b, Module.Basis.span_apply]
  have hmap : exteriorPower.map n (Submodule.span K (Set.range v)).subtype
      (exteriorPower.ιMulti K n b) = exteriorPower.ιMulti K n v := by
    rw [exteriorPower.map_apply_ιMulti]
    exact congrArg _ hb
  intro h0
  have h1 : exteriorPower.ιMulti K n b = 0 := by
    apply exteriorPower.map_injective_field (n := n) (Submodule.injective_subtype _)
    rw [hmap, h0, map_zero]
  have h2 := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h1
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero, b.det_self] at h2
  exact one_ne_zero h2

private theorem eq_smul_tprod_iff {K M : Type*} [CommSemiring K] [AddCommMonoid M] [Module K M]
    (a : TensorPower K 1 M) (c : K) (w : M) :
    a = c • PiTensorProduct.tprod K (fun _ : Fin 1 => w) ↔
      PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => M) 0 a = c • w := by
  rw [← (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => M) 0).injective.eq_iff,
    map_smul, PiTensorProduct.subsingletonEquiv_apply_tprod]

private theorem eq_smul_tprod_smul_iff {K M : Type*} [CommSemiring K] [AddCommMonoid M]
    [Module K M]
    (a : TensorPower K 1 M) (c d : K) (w : M) :
    a = c • PiTensorProduct.tprod K (fun _ : Fin 1 => d • w) ↔
      PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => M) 0 a = (c * d) • w := by
  rw [eq_smul_tprod_iff, mul_smul]

section Presentation

open MMP.Mori

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y]

/-- A form with a simple pole at `y` forces the top forms of `𝒪_{Y,y}` to have a generator with
nonzero image in the rational forms. -/
private theorem exists_generator_of_ordAt_eq_neg_one (y : Y) {d : ℕ}
    (τ : RationalPluriForms sY d 1)
    (hτ : (letI := stalkAlgebra sY y; letI := functionFieldAlgebra sY;
      haveI := isScalarTower_stalk_functionField sY y
      ordAt (k := k) (d := d) (m := 1) (Y.presheaf.stalk y) (fun f => Y.ord f y) τ) = -1) :
    letI := stalkAlgebra sY y; letI := functionFieldAlgebra sY
    haveI := isScalarTower_stalk_functionField sY y
    ∃ σ : ⋀[Y.presheaf.stalk y]^d Ω[Y.presheaf.stalk y⁄k],
      Submodule.span (Y.presheaf.stalk y) {σ} = ⊤ ∧
        topFormsMap k (Y.presheaf.stalk y) Y.functionField d σ ≠ 0 := by
  classical
  by_contra h
  simp only [ordAt, dif_neg h] at hτ
  exact absurd hτ (by decide)

/-- A presentation `τ = a₀ · dϖ/ϖ ∧ dx₀` from any coordinates `(ϖ, x₀)` at a codimension-one
point where `τ` has a simple pole. -/
private theorem exists_unit_presentation (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {n : ℕ}
    (τ : RationalPluriForms sY (n + 1) 1) (hτ0 : τ ≠ 0)
    (hτy : (letI := stalkAlgebra sY y; letI := functionFieldAlgebra sY;
      haveI := isScalarTower_stalk_functionField sY y
      ordAt (k := k) (d := n + 1) (m := 1) (Y.presheaf.stalk y) (fun f => Y.ord f y) τ) = -1)
    (ϖ : Y.presheaf.stalk y) (x0 : Fin n → Y.presheaf.stalk y) (hϖ : Irreducible ϖ)
    (hspan : letI := stalkAlgebra sY y
      Submodule.span (Y.presheaf.stalk y) (Set.range
        (Fin.cons (D k _ ϖ) fun i => D k _ (x0 i) : Fin (n + 1) → Ω[Y.presheaf.stalk y⁄k])) = ⊤) :
    letI := functionFieldAlgebra sY
    ∃ a0 : Y.presheaf.stalk y, IsUnit a0 ∧
      exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) ≠ 0 ∧
      PiTensorProduct.subsingletonEquiv (R := Y.functionField)
          (s := fun _ : Fin 1 => ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) 0 τ =
        (algebraMap _ Y.functionField a0 * (algebraMap _ Y.functionField ϖ)⁻¹) •
          exteriorPower.ιMulti Y.functionField (n + 1)
            (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
              fun i => D k Y.functionField (algebraMap _ _ (x0 i))) := by
  classical
  let := stalkAlgebra sY y
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY y
  obtain ⟨σ, hσ, hσ0⟩ := exists_generator_of_ordAt_eq_neg_one sY y τ hτy
  set e : Fin (n + 1) → Ω[Y.presheaf.stalk y⁄k] := Fin.cons (D k _ ϖ) fun i => D k _ (x0 i)
  have hgen := span_ιMulti_eq_top e hspan
  have himage : topFormsMap k _ Y.functionField (n + 1) (exteriorPower.ιMulti _ (n + 1) e) =
      exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [e]
  have hω0 : topFormsMap k _ Y.functionField (n + 1) (exteriorPower.ιMulti _ (n + 1) e) ≠ 0 := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hgen ▸ Submodule.mem_top (x := σ))
    intro h0
    apply hσ0
    rw [map_smul, h0, smul_zero]
  have hord := ordAt_eq (k := k) (A := Y.presheaf.stalk y) (v := fun f => Y.ord f y) (m := 1)
    (fun _ _ hx hy' => Scheme.ord_mul hx hy') (fun _ ha => ord_algebraMap_of_isUnit y hy ha) hgen
    hω0 τ
  set f := formCoeff (k := k) (m := 1) (Y.presheaf.stalk y) hgen hω0 τ
  have hf : f ≠ 0 := fun h0 => hτ0 ((formCoeff_eq_zero_iff (m := 1) hgen hω0 τ).mp h0)
  obtain ⟨a0, ha0, hfa⟩ := exists_isUnit_eq_div_of_ord_eq_neg_one y hy hϖ hf (hord ▸ hτy)
  refine ⟨a0, ha0, himage ▸ hω0, ?_⟩
  have hτf := (formCoeff_smul_basis (k := k) (m := 1) (A := Y.presheaf.stalk y) hgen hω0 τ).symm
  rw [← hfa, ← himage]
  have hb := ZTensorPower.basis_ofNat (topFormsBasis (Y.presheaf.stalk y) hgen hω0) 1
  rw [topFormsBasis_apply] at hb
  exact (eq_smul_tprod_iff τ f _).mp (hτf.trans (congrArg (f • ·) hb))

end Presentation

section Main

open MMP.Mori

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y] (j : T ⟶ Y) [IsIntegral T]

private theorem ordForm_eq_ordAt (P : MMP.Mori.PrimeDivisor Y) {d : ℕ} {m : ℤ}
    (τ : RationalPluriForms sY d m) (y : Y) (hy : y = P.genericPoint) :
    P.ordForm τ = (letI := stalkAlgebra sY y; letI := functionFieldAlgebra sY;
      haveI := isScalarTower_stalk_functionField sY y
      ordAt (k := k) (Y.presheaf.stalk y) (fun f => Y.ord f y) τ) := by
  subst hy; rfl

private theorem isPoincareResidue_iff {n : ℕ} (τ : RationalPluriForms sY (n + 1) 1)
    (ρ : RationalPluriForms (j ≫ sY) n 1) :
    MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ ↔
      (letI := functionFieldAlgebra sY
      letI := functionFieldAlgebra (j ≫ sY)
      ∃ (t g : Y.presheaf.stalk (j (genericPoint T)))
        (x : Fin n → Y.presheaf.stalk (j (genericPoint T))),
        Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 ∧
        PiTensorProduct.subsingletonEquiv (R := Y.functionField)
            (s := fun _ : Fin 1 => ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) 0 τ =
          (algebraMap _ Y.functionField g * (algebraMap _ Y.functionField t)⁻¹) •
            exteriorPower.ιMulti Y.functionField (n + 1)
              (Fin.cons (D k Y.functionField (algebraMap _ _ t))
                fun i => D k Y.functionField (algebraMap _ _ (x i))) ∧
        PiTensorProduct.subsingletonEquiv (R := T.functionField)
            (s := fun _ : Fin 1 => ⋀[T.functionField]^n Ω[T.functionField⁄k]) 0 ρ =
          (j.stalkMap (genericPoint T)).hom g • exteriorPower.ιMulti T.functionField n
            fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x i))) := by
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  unfold MMP.Fourfold.IsPoincareResidue
  refine exists_congr fun t => exists_congr fun g => exists_congr fun x => and_congr Iff.rfl
    (and_congr ?_ ?_)
  · exact eq_smul_tprod_smul_iff _ _ _ _
  · exact eq_smul_tprod_iff _ _ _

private theorem exists_residue_data [Smooth sY] [Smooth (j ≫ sY)] [IsClosedImmersion j]
    (P : MMP.Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) {n : ℕ}
    (τ : RationalPluriForms sY (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (j ≫ sY)
    ∃ (ϖ a0 : Y.presheaf.stalk (j (genericPoint T)))
      (x0 : Fin n → Y.presheaf.stalk (j (genericPoint T))),
      Irreducible ϖ ∧ IsUnit a0 ∧
      Submodule.span (Y.presheaf.stalk (j (genericPoint T))) (Set.range
        (Fin.cons (D k _ ϖ) fun i => D k _ (x0 i) :
          Fin (n + 1) → Ω[Y.presheaf.stalk (j (genericPoint T))⁄k])) = ⊤ ∧
      LinearIndependent T.functionField
        (fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i))) ∧
      Submodule.span T.functionField
        (Set.range fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i))) = ⊤ ∧
      exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) ≠ 0 ∧
      PiTensorProduct.subsingletonEquiv (R := Y.functionField)
          (s := fun _ : Fin 1 => ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) 0 τ =
        (algebraMap _ Y.functionField a0 * (algebraMap _ Y.functionField ϖ)⁻¹) •
          exteriorPower.ιMulti Y.functionField (n + 1)
            (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
              fun i => D k Y.functionField (algebraMap _ _ (x0 i))) ∧
      Module.finrank Y.functionField Ω[Y.functionField⁄k] = n + 1 ∧
      Module.Finite Y.functionField Ω[Y.functionField⁄k] := by
  classical
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  set y := j (genericPoint T) with hydef
  have := isDiscreteValuationRing_stalk sY y hy
  let := stalkAlgebra sY y
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY y
  let := functionFieldAlgebra (j ≫ sY)
  let := (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalkMap sY j (genericPoint T)
  obtain ⟨hfsA, -, hefA⟩ := MMP.Flips.ResolutionInputs.stalk_facts sY y
  obtain ⟨hfsB, -, hefB⟩ := MMP.Flips.ResolutionInputs.stalk_facts (j ≫ sY) (genericPoint T)
  have : Module.Free (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] :=
    Module.free_of_flat_of_isLocalRing
  have hsurj : Function.Surjective
      (algebraMap (Y.presheaf.stalk y) (T.presheaf.stalk (genericPoint T))) :=
    j.stalkMap_surjective _
  rw [ordForm_eq_ordAt sY P τ y hP] at hτ
  obtain ⟨σ, hσ, hσ0⟩ := exists_generator_of_ordAt_eq_neg_one sY y τ hτ
  have hrank := finrank_eq_of_generator (Nat.succ_ne_zero n) hσ hσ0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y)
  have hker : RingHom.ker (algebraMap (Y.presheaf.stalk y) (T.presheaf.stalk (genericPoint T))) =
      Ideal.span {ϖ} :=
    (IsLocalRing.ker_eq_maximalIdeal _ hsurj).trans
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ)
  obtain ⟨x0, hspan, hli, hspanB⟩ := exists_coordinates_local (k := k) hsurj hϖ.ne_zero hker hrank
  obtain ⟨a0, ha0, hne, hτE⟩ := exists_unit_presentation sY y hy τ hτ0 hτ ϖ x0 hϖ hspan
  refine ⟨ϖ, a0, x0, hϖ, ha0, hspan, hli, hspanB, hne, hτE, ?_, ?_⟩
  · exact (MMP.Mori.finrank_kaehlerDifferential_eq_of_isFractionRing (k := k)
      (A := Y.presheaf.stalk y) (K := Y.functionField)).trans hrank
  · exact Module.Finite.of_basis
      ((Module.Free.chooseBasis (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k]).ofIsLocalizedModule
        Y.functionField (nonZeroDivisors _) (KaehlerDifferential.map k k _ Y.functionField))

/-- Every residue is the residue `ā₀ · dx̄₀` of a fixed presentation `(ϖ, a₀, x₀)`. -/
private theorem residue_eq_of_isPoincareResidue [IsClosedImmersion j] {n : ℕ}
    (hy : Order.coheight (j (genericPoint T)) = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk (j (genericPoint T)))]
    (τ : RationalPluriForms sY (n + 1) 1) {ρ : RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ)
    (ϖ a0 : Y.presheaf.stalk (j (genericPoint T)))
    (x0 : Fin n → Y.presheaf.stalk (j (genericPoint T))) (hϖ : Irreducible ϖ)
    (hspan : letI := stalkAlgebra sY (j (genericPoint T))
      Submodule.span (Y.presheaf.stalk (j (genericPoint T))) (Set.range
        (Fin.cons (D k _ ϖ) fun i => D k _ (x0 i) :
          Fin (n + 1) → Ω[Y.presheaf.stalk (j (genericPoint T))⁄k])) = ⊤)
    (hne : letI := functionFieldAlgebra sY
      exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) ≠ 0)
    (hτE : letI := functionFieldAlgebra sY
      PiTensorProduct.subsingletonEquiv (R := Y.functionField)
          (s := fun _ : Fin 1 => ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) 0 τ =
        (algebraMap _ Y.functionField a0 * (algebraMap _ Y.functionField ϖ)⁻¹) •
          exteriorPower.ιMulti Y.functionField (n + 1)
            (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
              fun i => D k Y.functionField (algebraMap _ _ (x0 i)))) :
    letI := functionFieldAlgebra (j ≫ sY)
    PiTensorProduct.subsingletonEquiv (R := T.functionField)
        (s := fun _ : Fin 1 => ⋀[T.functionField]^n Ω[T.functionField⁄k]) 0 ρ =
      (j.stalkMap (genericPoint T)).hom a0 • exteriorPower.ιMulti T.functionField n
        fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i)) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  let := functionFieldAlgebra (j ≫ sY)
  let := (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalkMap sY j (genericPoint T)
  obtain ⟨t, g, x, ht, hτ', hρ⟩ := (isPoincareResidue_iff sY j τ ρ).mp h
  obtain ⟨v, hv, rfl⟩ := exists_isUnit_eq_mul_of_ord_eq_one _ hy hϖ ht
  rw [hρ]
  have hφϖ : (j.stalkMap (genericPoint T)).hom ϖ = 0 := by
    have hmem : ϖ ∈ RingHom.ker (j.stalkMap (genericPoint T)).hom := by
      rw [IsLocalRing.ker_eq_maximalIdeal _ (j.stalkMap_surjective _)]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
    exact hmem
  exact residue_core (k := k) (K := Y.functionField) (B := T.functionField) ϖ a0 x0 hφϖ hspan
    hne x hv rfl (hτ'.symm.trans hτE)

end Main

/-- The stalk map at `y₁` of a morphism which restricts to an isomorphism over `U ∋ g y₁` is an
isomorphism. -/
private theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : X ⟶ Y)
    (U : Y.Opens)
    [IsIso (g ∣_ U)] (x : X) (hx : g x ∈ U) : IsIso (g.stalkMap x) := by
  have e := morphismRestrictStalkMap g U ⟨x, hx⟩
  have h1 : IsIso ((g ∣_ U).stalkMap ⟨x, hx⟩) :=
    ((isIso_iff_isIso_stalkMap (g ∣_ U)).mp inferInstance).2 _
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).mp h1

section PullbackForms

open MMP.Mori

variable {k : Type u} [Field k]

private theorem subsingletonEquiv_basis_one {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Module.Basis Unit K L) :
    PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => L) 0
      (ZTensorPower.basis b 1 ()) = b () := by
  erw [ZTensorPower.basis_ofNat b 1]
  exact PiTensorProduct.subsingletonEquiv_apply_tprod _ _

/-- Pull-back of top forms along a pull-back generator is `topFormsMap`. -/
private theorem subsingletonEquiv_pullbackForms {K K' : Type u} [Field K] [Field K'] [Algebra k K]
    [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ} {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : IsPullbackGenerator K' ω) (τ : PluriForms k K d 1) :
    PiTensorProduct.subsingletonEquiv (R := K') (s := fun _ : Fin 1 => ⋀[K']^d Ω[K'⁄k]) 0
        (pullbackForms (K' := K') 1 τ) =
      topFormsMap k K K' d
        (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => ⋀[K]^d Ω[K⁄k]) 0 τ) := by
  rw [pullbackForms_eq hω]
  unfold pullbackFormsAlong
  set b := basisOfSpanSingleton hω.1 hω.ne_zero
  conv_rhs => rw [← basis_unit_repr_smul (ZTensorPower.basis b 1) τ]
  erw [LinearEquiv.map_smul, LinearEquiv.map_smul, subsingletonEquiv_basis_one,
    subsingletonEquiv_basis_one, LinearMap.map_smul, algebraMap_smul]
  simp [b]

end PullbackForms

section StalkCompat

variable {Y Y₁ T T₁ : Scheme.{u}} (g : Y₁ ⟶ Y) (j : T ⟶ Y) (j₁ : T₁ ⟶ Y₁) (h : T₁ ⟶ T)
  [IsIntegral T] [IsIntegral T₁] [IsIntegral Y] [IsIntegral Y₁] [IsDominant h] [IsDominant g]

private theorem map_genericPoint_eq (hh : h ≫ j = j₁ ≫ g) :
    g (j₁ (genericPoint T₁)) = j (genericPoint T) := by
  have := congrArg (fun f : T₁ ⟶ Y => f (genericPoint T₁)) hh
  simp only [Scheme.Hom.comp_apply] at this
  rw [← this, map_genericPoint_of_isDominant]

/-- The stalk map `𝒪_{Y, j(η_T)} → 𝒪_{Y₁, j₁(η_{T₁})}` of `g`. -/
private noncomputable def stalkMapAt (hh : h ≫ j = j₁ ≫ g) :
    Y.presheaf.stalk (j (genericPoint T)) ⟶ Y₁.presheaf.stalk (j₁ (genericPoint T₁)) :=
  (Y.presheaf.stalkCongr (.of_eq (map_genericPoint_eq g j j₁ h hh).symm)).hom ≫
    g.stalkMap (j₁ (genericPoint T₁))

private theorem stalkMapAt_functionField (hh : h ≫ j = j₁ ≫ g) (a : Y.presheaf.stalk (j
    (genericPoint T))) :
    algebraMap (Y₁.presheaf.stalk (j₁ (genericPoint T₁))) Y₁.functionField
        ((stalkMapAt g j j₁ h hh).hom a) =
      functionFieldMap g (algebraMap _ Y.functionField a) := by
  have key : stalkMapAt g j j₁ h hh ≫
        Y₁.presheaf.stalkSpecializes ((genericPoint_spec Y₁).specializes trivial) =
      Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
        (Y.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant g).symm)).hom ≫
          g.stalkMap (genericPoint Y₁) := by
    simp only [stalkMapAt, TopCat.Presheaf.stalkCongr_hom, Category.assoc]
    rw [← Scheme.Hom.stalkSpecializes_stalkMap, ← Category.assoc, ← Category.assoc]
    congr 1
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hV
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes,
      TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact congrArg (fun f => f.hom a) key

private theorem stalkMapAt_stalkMap (hh : h ≫ j = j₁ ≫ g) (a : Y.presheaf.stalk (j
    (genericPoint T))) :
    (j₁.stalkMap (genericPoint T₁)).hom ((stalkMapAt g j j₁ h hh).hom a) =
      functionFieldMap h ((j.stalkMap (genericPoint T)).hom a) := by
  have key : stalkMapAt g j j₁ h hh ≫ j₁.stalkMap (genericPoint T₁) =
      j.stalkMap (genericPoint T) ≫
        (T.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant h).symm)).hom ≫
          h.stalkMap (genericPoint T₁) := by
    simp only [stalkMapAt, Category.assoc, ← Scheme.Hom.stalkMap_comp]
    rw [Scheme.Hom.stalkMap_congr_point_assoc j _ _ (map_genericPoint_of_isDominant h).symm,
      ← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom (h ≫ j) (j₁ ≫ g) hh]
    simp only [TopCat.Presheaf.stalkCongr_hom]
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hV
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc,
      TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rfl
  exact congrArg (fun f => f.hom a) key

end StalkCompat

section Cast

open MMP.Mori

variable {k : Type u} [Field k]

/-- Transport of a residue presentation along an equality of structure morphisms. -/
private theorem subsingletonEquiv_cast {T₁ : Scheme.{u}} [IsIntegral T₁] {n : ℕ}
    {s s' : T₁ ⟶ Spec (.of k)} (e : s = s')
    (H : RationalPluriForms s n 1 = RationalPluriForms s' n 1) (X : RationalPluriForms s n 1)
    (c : T₁.functionField) (v : Fin n → T₁.functionField)
    (hX : letI := functionFieldAlgebra s
      PiTensorProduct.subsingletonEquiv (R := T₁.functionField)
          (s := fun _ : Fin 1 => ⋀[T₁.functionField]^n Ω[T₁.functionField⁄k]) 0 X =
        c • exteriorPower.ιMulti T₁.functionField n (fun i => D k T₁.functionField (v i))) :
    letI := functionFieldAlgebra s'
    PiTensorProduct.subsingletonEquiv (R := T₁.functionField)
        (s := fun _ : Fin 1 => ⋀[T₁.functionField]^n Ω[T₁.functionField⁄k]) 0 (cast H X) =
      c • exteriorPower.ιMulti T₁.functionField n (fun i => D k T₁.functionField (v i)) := by
  subst e
  exact hX

end Cast

section PullbackResidue

open MMP.Mori

/-- **Residues commute with pull-back**, given the dimensions of the differentials of the function
fields. If `g : Y₁ ⟶ Y` induces an isomorphism `ψ` of the local rings at the generic points of
`T₁` and `T`, then a presentation `τ = a · dt/t ∧ dx` with residue `ρ = ā · dx̄` is carried by `ψ`
to the presentation `g^*τ = ψa · dψt/ψt ∧ dψx`, whose residue is `h^*ρ`. -/
private theorem isPoincareResidue_pullback_of_finrank {k : Type u} [Field k] {Y T : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] {j : T ⟶ Y} [IsIntegral T]
    {n : ℕ} {τ : RationalPluriForms sY (n + 1) 1} {ρ : RationalPluriForms (j ≫ sY) n 1}
    {Y₁ T₁ : Scheme.{u}} (g : Y₁ ⟶ Y) [IsIntegral Y₁] [IsLocallyNoetherian Y₁] [IsDominant g]
    (j₁ : T₁ ⟶ Y₁) [IsClosedImmersion j₁] [IsIntegral T₁]
    [IsIso (g.stalkMap (j₁ (genericPoint T₁)))] (h : T₁ ⟶ T) [IsDominant h]
    (hh : h ≫ j = j₁ ≫ g) (hy : Order.coheight (j (genericPoint T)) = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk (j (genericPoint T)))]
    (hKY : letI := functionFieldAlgebra sY
      Module.finrank Y.functionField Ω[Y.functionField⁄k] = n + 1 ∧
        Module.Finite Y.functionField Ω[Y.functionField⁄k])
    (hKT : letI := functionFieldAlgebra (j ≫ sY)
      Module.finrank T.functionField Ω[T.functionField⁄k] = n ∧
        Module.Finite T.functionField Ω[T.functionField⁄k])
    (hρ : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) :
    MMP.Fourfold.IsPoincareResidue (g ≫ sY) j₁ n 1 (pullbackRationalPluriForms sY g τ)
      (cast (by rw [← Category.assoc, hh, Category.assoc]; rfl)
        (pullbackRationalPluriForms (j ≫ sY) h ρ)) := by
  classical
  obtain ⟨ϖ, a0, x0, ht, hτE, hρE⟩ := (isPoincareResidue_iff sY j τ ρ).mp hρ
  obtain ⟨hKrank, hKfin⟩ := hKY
  obtain ⟨hTrank, hTfin⟩ := hKT
  have hϖ : Irreducible ϖ := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
      (Y.presheaf.stalk (j (genericPoint T)))
    obtain ⟨v, hv, rfl⟩ := exists_isUnit_eq_mul_of_ord_eq_one _ hy hπ ht
    exact (irreducible_isUnit_mul hv).mpr hπ
  have hψiso : IsIso (stalkMapAt g j j₁ h hh) := by unfold stalkMapAt; infer_instance
  have hψ : Function.Bijective (stalkMapAt g j j₁ h hh).hom :=
    ConcreteCategory.bijective_of_isIso (stalkMapAt g j j₁ h hh)
  let eψ := RingEquiv.ofBijective (stalkMapAt g j j₁ h hh).hom hψ
  have hy₁ : Order.coheight (j₁ (genericPoint T₁)) = 1 := by
    have h1 := ringKrullDim_eq_of_ringEquiv eψ
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hy] at h1
    exact_mod_cast h1.symm
  have : IsDiscreteValuationRing (Y₁.presheaf.stalk (j₁ (genericPoint T₁))) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eψ
  have hϖ₁ : Irreducible ((stalkMapAt g j j₁ h hh).hom ϖ) :=
    (MulEquiv.irreducible_iff eψ.toMulEquiv).mpr hϖ
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (g ≫ sY)
  refine (isPoincareResidue_iff (g ≫ sY) j₁ _ _).mpr ⟨(stalkMapAt g j j₁ h hh).hom ϖ,
    (stalkMapAt g j j₁ h hh).hom a0, fun i => (stalkMapAt g j j₁ h hh).hom (x0 i), ?_, ?_, ?_⟩
  · exact ord_algebraMap_irreducible _ hy₁ hϖ₁
  · let := functionFieldMapAlgebra g
    have := isScalarTower_functionFieldMap sY g
    have hΦ : ∀ a, algebraMap Y.functionField Y₁.functionField (algebraMap _ Y.functionField a) =
        algebraMap _ Y₁.functionField ((stalkMapAt g j j₁ h hh).hom a) :=
      fun a => (stalkMapAt_functionField g j j₁ h hh a).symm
    have hbij : Function.Bijective (algebraMap Y.functionField Y₁.functionField) := by
      refine ⟨RingHom.injective _, fun z => ?_⟩
      obtain ⟨a, b, -, rfl⟩ :=
        IsFractionRing.div_surjective (A := Y₁.presheaf.stalk (j₁ (genericPoint T₁))) z
      obtain ⟨a', rfl⟩ := hψ.2 a
      obtain ⟨b', rfl⟩ := hψ.2 b
      exact ⟨algebraMap _ Y.functionField a' / algebraMap _ Y.functionField b', by
        rw [map_div₀, hΦ, hΦ]⟩
    have := Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij)
    obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_formallyEtale (k := k)
      (K := Y.functionField) (K' := Y₁.functionField) hKrank
    refine (subsingletonEquiv_pullbackForms hω τ).trans ?_
    rw [hτE, LinearMap.map_smul, topFormsMap_ιMulti,
      ← algebraMap_smul Y₁.functionField, map_mul, map_inv₀, hΦ, hΦ]
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [KaehlerDifferential.map_D, hΦ]
  · let := functionFieldAlgebra (j ≫ sY)
    let := functionFieldAlgebra (h ≫ j ≫ sY)
    let := functionFieldMapAlgebra h
    have := isScalarTower_functionFieldMap (j ≫ sY) h
    have hΦ : ∀ a, algebraMap T.functionField T₁.functionField ((j.stalkMap
        (genericPoint T)).hom a) =
        (j₁.stalkMap (genericPoint T₁)).hom ((stalkMapAt g j j₁ h hh).hom a) :=
      fun a => (stalkMapAt_stalkMap g j j₁ h hh a).symm
    have hbij : Function.Bijective (algebraMap T.functionField T₁.functionField) := by
      refine ⟨RingHom.injective _, fun z => ?_⟩
      obtain ⟨a, rfl⟩ := j₁.stalkMap_surjective _ z
      obtain ⟨a', rfl⟩ := hψ.2 a
      exact ⟨(j.stalkMap (genericPoint T)).hom a', hΦ a'⟩
    have := Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij)
    obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_formallyEtale (k := k)
      (K := T.functionField) (K' := T₁.functionField) hTrank
    refine subsingletonEquiv_cast (k := k) (by rw [← Category.assoc, hh, Category.assoc]) _ _ _ _ ?_
    refine (subsingletonEquiv_pullbackForms hω ρ).trans ?_
    rw [hρE, LinearMap.map_smul, topFormsMap_ιMulti,
      ← algebraMap_smul T₁.functionField, hΦ]
    congr 2
    funext i
    simp [KaehlerDifferential.map_D, hΦ]

/-- **Residues commute with pull-back.** Let `Y` be a normal integral scheme of dimension `n + 1`,
locally of finite type over a perfect field `k`, `j : T ⟶ Y` an integral closed subscheme whose
generic point is that of the prime divisor `P`, and `ρ` a residue of `τ` along `T`. Let
`g : Y₁ ⟶ Y` be a dominant morphism of integral schemes, `j₁ : T₁ ⟶ Y₁` an integral closed
subscheme and `h : T₁ ⟶ T` dominant with `h ≫ j = j₁ ≫ g`, such that `g` induces an isomorphism
of the local rings at the generic points of `T₁` and `T`. Then `h^*ρ` is a residue of `g^*τ`
along `T₁`. -/
public theorem _root_.MMP.Fourfold.IsPoincareResidue.pullback {k : Type u} [Field k]
    [PerfectField k] {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1) {j : T ⟶ Y} [IsClosedImmersion j] [IsIntegral T]
    (P : PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {τ : RationalPluriForms sY (n + 1) 1} {ρ : RationalPluriForms (j ≫ sY) n 1}
    (hρ : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ)
    {Y₁ T₁ : Scheme.{u}} (g : Y₁ ⟶ Y) [IsIntegral Y₁] [IsLocallyNoetherian Y₁] [IsDominant g]
    (j₁ : T₁ ⟶ Y₁) [IsClosedImmersion j₁] [IsIntegral T₁]
    [IsIso (g.stalkMap (j₁ (genericPoint T₁)))] (h : T₁ ⟶ T) [IsDominant h]
    (hh : h ≫ j = j₁ ≫ g) :
    MMP.Fourfold.IsPoincareResidue (g ≫ sY) j₁ n 1 (pullbackRationalPluriForms sY g τ)
      (cast (by rw [← Category.assoc, hh, Category.assoc]; rfl)
        (pullbackRationalPluriForms (j ≫ sY) h ρ)) := by
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  have : IsDiscreteValuationRing (Y.presheaf.stalk (j (genericPoint T))) := by
    rw [hP]; exact P.isDiscreteValuationRing_localRing
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  have := essFiniteType_functionField (sX := sY)
  have := essFiniteType_functionField (sX := j ≫ sY)
  have hdY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (d := n + 1)
    (by exact_mod_cast hY)
  have hdT := MMP.Fourfold.trdeg_add_one_of_eq_genericPoint (sY := sY) P hP
  refine isPoincareResidue_pullback_of_finrank g j₁ h hh hy ⟨?_, ?_⟩ ⟨?_, ?_⟩ hρ
  · rw [finrank_kaehlerDifferential_eq_trdeg, hdY]
  · exact (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k _).1
  · rw [finrank_kaehlerDifferential_eq_trdeg]
    omega
  · exact (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k _).1

end PullbackResidue

section StalkIdeal

variable {X : Scheme.{u}}

private theorem stalkIdeal_eq_stalk' (I : X.IdealSheafData) (x : X) :
    I.stalkIdeal x = IdealSheafData.stalk I x := by
  unfold Scheme.IdealSheafData.stalkIdeal
  apply le_antisymm
  · exact iSup_le fun U => (IdealSheafData.stalk_eq_map_germ I x U.1 U.2).symm.le
  · obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
    rw [IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU]
    exact le_iSup (fun U : {U : X.affineOpens // x ∈ U.1.1} =>
      Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1)) ⟨⟨U, hU⟩, hxU⟩

private theorem stalkIdeal_primeDivisor (E : MMP.Mori.PrimeDivisor X) {x : X}
    (hx : E.genericPoint ⤳ x) :
    E.idealSheaf.stalkIdeal x = MMP.Intersection.primeOfSpecializes hx := by
  have hE : E = AlgebraicGeometry.PrimeDivisor.ofCoheightOne E.genericPoint
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E) :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
  have h1 : E.idealSheaf = Stacks.Chow.integralComponentAt E.genericPoint := by
    conv_lhs => rw [hE]
    rfl
  rw [h1, stalkIdeal_eq_stalk']
  have h2 := Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk x
    ⟨MMP.Intersection.primeOfSpecializes hx, inferInstance⟩
  rwa [MMP.Intersection.fromSpecStalk_primeOfSpecializes hx] at h2

private theorem ord_algebraMap_eq_toNat_ord [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (hx : Order.coheight x = 1) {c : X.presheaf.stalk x} (hc : c ≠ 0) :
    X.ord (algebraMap _ X.functionField c) x = ((Ring.ord (X.presheaf.stalk x) c).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hne : algebraMap _ X.functionField c ≠ 0 := by
    rwa [map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  rw [Scheme.ord_eq_iff hx hne]
  change Ring.ordFrac _ _ = _
  rw [Ring.ordFrac_eq_ord _ hc]
  have hnz : c ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero hc
  rw [Ring.ordMonoidWithZeroHom_eq_coe _ hnz (n := (Ring.ord _ c).toNat)
    (ENat.coe_toNat (Ring.ord_ne_top hnz)).symm]

private theorem genericPoint_specializes_of_mem_support (E : MMP.Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ E.support) : E.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
  exact specializes_iff_mem_closure.mpr hx

end StalkIdeal

section PrimeCase

open MMP.Intersection

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y] [Smooth sY] (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T]
      [IsLocallyNoetherian T] [Smooth (j ≫ sY)]

private theorem eq_of_specializes_of_coheight_eq_one {X : Scheme.{u}} {x y : X} (h : x ⤳ y)
    (hx : Order.coheight x = 1) (hy : Order.coheight y = 1) : x = y := by
  by_contra hne
  by_cases h' : y ⤳ x
  · exact hne (h.antisymm h').eq
  have hlt : y < x := lt_of_le_not_ge h h'
  have := Order.coheight_strictAnti hlt (by rw [hx]; decide)
  rw [hx, hy] at this
  exact lt_irrefl _ this

open MMP.Intersection in
private theorem coheight_fromSpecStalk_span_eq_one {X : Scheme.{u}} [IsIntegral X] {y' : X}
    [IsNoetherianRing (X.presheaf.stalk y')] {p0 : X.presheaf.stalk y'} (hp : Prime p0) :
    Order.coheight (X.fromSpecStalk y'
      ⟨Ideal.span {p0}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp⟩) = 1 := by
  set q : PrimeSpectrum (X.presheaf.stalk y') :=
    ⟨Ideal.span {p0}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp⟩
  have hz : X.fromSpecStalk y' q ⤳ y' := fromSpecStalk_specializes y' q
  have hpz : primeOfSpecializes hz = Ideal.span {p0} :=
    comap_maximalIdeal_stalkSpecializes_fromSpecStalk y' q
  apply le_antisymm (coheight_le_one_of_primeOfSpecializes_eq_span hz hpz)
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]
  intro h0
  have hmax := Order.coheight_eq_zero.mp h0
  have hzη : X.fromSpecStalk y' q = genericPoint X :=
    (Specializes.antisymm (hmax (genericPoint_specializes _)) (genericPoint_specializes _)).eq
  have hbot : primeOfSpecializes hz = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_bot]
    have hc' : X.presheaf.stalkSpecializes hz c ∈ IsLocalRing.maximalIdeal _ := hc
    have hfield : IsField (X.presheaf.stalk (X.fromSpecStalk y' q)) := by
      rw [hzη]; exact Field.toIsField X.functionField
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield, Ideal.mem_bot] at hc'
    exact stalkSpecializes_injective hz (hc'.trans (map_zero _).symm)
  rw [hpz, Ideal.span_singleton_eq_bot] at hbot
  exact hp.ne_zero hbot

open MMP.Intersection in
/-- `primeOfSpecializes` depends only on the generizing point, not on the specialization proof. -/
private theorem primeOfSpecializes_congr {X : Scheme.{u}} {a b y' : X} (e : a = b) (h1 : a ⤳ y')
    (h2 : b ⤳ y') : primeOfSpecializes h1 = primeOfSpecializes h2 := by
  subst e; rfl

open MMP.Intersection Classical in
/-- Along a prime divisor `E` through `y'`, a prime `p₀` of `𝒪_{X,y'}` cutting out the
codimension-one point `z` has order one if `η_E = z` and zero otherwise. -/
private theorem ord_prime_eq_ite {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {y' : X}
    {p0 : X.presheaf.stalk y'} (hp : Prime p0) {z : X} (hz : z ⤳ y')
    (hpz : primeOfSpecializes hz = Ideal.span {p0}) (hz1 : Order.coheight z = 1)
    (E : MMP.Mori.PrimeDivisor X) (hE : y' ∈ E.support) :
    X.ord (algebraMap _ X.functionField p0) E.genericPoint =
      if E.genericPoint = z then 1 else 0 := by
  have hsp := genericPoint_specializes_of_mem_support E hE
  have hspπ : X.presheaf.stalkSpecializes hsp p0 ≠ 0 := fun h0 =>
    hp.ne_zero (stalkSpecializes_injective hsp (h0.trans (map_zero _).symm))
  rw [← algebraMap_stalkSpecializes hsp, ord_algebraMap_eq_toNat_ord _
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E) hspπ]
  split_ifs with hEz
  · rw [ord_stalkSpecializes_eq_one hsp ((primeOfSpecializes_congr hEz hsp hz).trans hpz)]
    rfl
  · have hnot : p0 ∉ primeOfSpecializes hsp := by
      intro hmem
      apply hEz
      have hle : primeOfSpecializes hz ≤ primeOfSpecializes hsp := by
        rwa [hpz, Ideal.span_le, Set.singleton_subset_iff]
      exact (eq_of_specializes_of_coheight_eq_one (specializes_of_primeOfSpecializes_le hz hsp hle)
        hz1 (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E)).symm
    rw [ord_stalkSpecializes_of_notMem hsp hnot]
    rfl

include sY in
open Classical in
/-- **The prime case of the restriction of a principal divisor.** A prime `p0` of `𝒪_{Y,y'}`,
`y' = j(η_Q)`, with nonzero restriction to `T` is a uniformizer exactly along one prime divisor
`E_π` of `Y` through `y'`, it is a unit along the others, and `v_Q(p0|_T)` is the local
intersection length of `E_π` with `T` at `Q`. -/
private theorem exists_primeDivisor_of_prime (Q : MMP.Mori.PrimeDivisor T)
    {p0 : Y.presheaf.stalk (j Q.genericPoint)} (hπ : Prime p0)
    (hψp0 : (j.stalkMap Q.genericPoint).hom p0 ≠ 0) :
    ∃ Eπ : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ Eπ.support ∧
      (∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
        Y.ord (algebraMap _ Y.functionField p0) E.genericPoint = if E = Eπ then 1 else 0) ∧
      T.ord (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
          ((j.stalkMap Q.genericPoint).hom p0)) Q.genericPoint =
        (Eπ.intersectionLength j Q : ℤ) := by
  classical
  have := isRegularLocalRing_stalk_of_smooth_over_field sY (j Q.genericPoint)
  let q : PrimeSpectrum (Y.presheaf.stalk (j Q.genericPoint)) :=
    ⟨Ideal.span {p0}, (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ⟩
  set z := Y.fromSpecStalk (j Q.genericPoint) q
  have hz : z ⤳ (j Q.genericPoint) := fromSpecStalk_specializes (j Q.genericPoint) q
  have hpz : primeOfSpecializes hz = Ideal.span {p0} :=
    comap_maximalIdeal_stalkSpecializes_fromSpecStalk (j Q.genericPoint) q
  have hz1 : Order.coheight z = 1 := coheight_fromSpecStalk_span_eq_one hπ
  let Eπ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hz1
  have hEπ : Eπ.genericPoint = z := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hz1
  have hy'Eπ : (j Q.genericPoint) ∈ Eπ.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change (j Q.genericPoint) ∈ closure {Eπ.genericPoint}
    rw [hEπ]
    exact hz.mem_closure
  refine ⟨Eπ, hy'Eπ, fun E hE => ?_, ?_⟩
  · rw [ord_prime_eq_ite hπ hz hpz hz1 E hE, ← hEπ]
    exact if_congr AlgebraicGeometry.PrimeDivisor.genericPoint_injective.eq_iff rfl rfl
  · have hC := ord_algebraMap_eq_toNat_ord Q.genericPoint
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q) hψp0
    rw [hC]
    have hsp : Eπ.genericPoint ⤳ (j Q.genericPoint) := hEπ ▸ hz
    unfold MMP.Mori.PrimeDivisor.intersectionLength
    rw [stalkIdeal_primeDivisor Eπ hsp]
    have : primeOfSpecializes hsp = Ideal.span {p0} := by
      rw [← hpz]
      congr 1
    rw [this, Ideal.map_span, Set.image_singleton]
    rfl

private theorem ord_algebraMap_isUnit_at {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {x x' : X} (h : x' ⤳ x) (hx' : Order.coheight x' = 1) {c : X.presheaf.stalk x}
    (hc : IsUnit c) : X.ord (algebraMap _ X.functionField c) x' = 0 := by
  rw [← algebraMap_stalkSpecializes h]
  exact ord_algebraMap_of_isUnit x' hx' (hc.map _)

end PrimeCase

section LocalCoordinates

private theorem span_map_D_eq_top {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A]
    [Algebra k B] [Algebra A B] [IsScalarTower k A B] (M : Submonoid A) [IsLocalization M B]
    {m : ℕ} (v : Fin m → A) (hv : Submodule.span A (Set.range fun i => D k A (v i)) = ⊤) :
    Submodule.span B (Set.range fun i => D k B (algebraMap A B (v i))) = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_map_derivation_of_isLocalization k A B M,
    Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have ha : D k A a ∈ Submodule.span A (Set.range fun i => D k A (v i)) := hv ▸ Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := KaehlerDifferential.map k k A B) ha
  rw [Submodule.map_span, ← Set.range_comp] at h2
  have h3 : (KaehlerDifferential.map k k A B ∘ fun i => D k A (v i)) =
      fun i => D k B (algebraMap A B (v i)) := by
    funext i; simp
  rw [h3] at h2
  exact Submodule.span_le_restrictScalars A B _ h2

variable {k : Type u} [Field k]

private theorem isScalarTower_stalkSpecializes {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {x x' : X}
    (h : x' ⤳ x) :
    letI := MMP.Mori.stalkAlgebra sX x
    letI := MMP.Mori.stalkAlgebra sX x'
    letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsScalarTower k (X.presheaf.stalk x) (X.presheaf.stalk x') := by
  let := MMP.Mori.stalkAlgebra sX x
  let := MMP.Mori.stalkAlgebra sX x'
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x' (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _)) ≫
          X.presheaf.stalkSpecializes h := by
    simp
  exact congrArg CommRingCat.Hom.hom this

private theorem formCoeff_eq_of_subsingletonEquiv {A K : Type*} [CommRing A] [Algebra k A]
    [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : MMP.Mori.topFormsMap k A K d σ ≠ 0) (τ : MMP.Mori.PluriForms k K d 1) (c : K)
    (h : PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => ⋀[K]^d Ω[K⁄k]) 0 τ =
      c • MMP.Mori.topFormsMap k A K d σ) :
    MMP.Mori.formCoeff A hσ h0 τ = c := by
  have hb := MMP.Mori.ZTensorPower.basis_ofNat (MMP.Mori.topFormsBasis A hσ h0) 1
  rw [MMP.Mori.topFormsBasis_apply] at hb
  have hτ : τ = c • MMP.Mori.ZTensorPower.basis (MMP.Mori.topFormsBasis A hσ h0) 1 () := by
    have := (eq_smul_tprod_iff τ c _).mpr h
    exact this.trans (congrArg (c • ·) hb.symm)
  rw [hτ, MMP.Mori.formCoeff_smul]
  unfold MMP.Mori.formCoeff
  rw [Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]

private theorem cons_D_eq {k' A : Type*} [CommRing k'] [CommRing A] [Algebra k' A] {n : ℕ} (t : A)
    (x : Fin n → A) :
    (Fin.cons (D k' A t) fun i => D k' A (x i) : Fin (n + 1) → Ω[A⁄k']) =
      fun i => D k' A ((Fin.cons t x : Fin (n + 1) → A) i) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

private theorem ord_mul_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) (z : X) : X.ord (f * g⁻¹) z = X.ord f z - X.ord g z := by
  have h1 : X.ord (g * g⁻¹) z = X.ord g z + X.ord g⁻¹ z := Scheme.ord_mul hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, Scheme.ord_one] at h1
  rw [Scheme.ord_mul hf (inv_ne_zero hg)]
  omega

private theorem ord_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X.functionField} (hf : f ≠ 0) (z : X) : X.ord f⁻¹ z = -X.ord f z := by
  simpa [Scheme.ord_one] using ord_mul_inv one_ne_zero hf z

end LocalCoordinates

section PrincipalRestriction

open MMP.Mori Classical

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y] [Smooth sY] (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T]
      [IsLocallyNoetherian T] [Smooth (j ≫ sY)]

include sY in
/-- **Restriction of a principal divisor.** Let `Q` be a prime divisor of `T`, `y' = j(η_Q)`, and
`r ∈ 𝒪_{Y,y'}` with nonzero restriction `r|_T ∈ 𝒪_{T,Q}`. Then
`v_Q(r|_T) = ∑_E length(𝒪_{T,Q}/I_E 𝒪_{T,Q}) · v_E(r)`, the sum over the (finitely many) prime
divisors `E` of `Y` through `y'` along which `r` vanishes. -/
public theorem _root_.MMP.Mori.PrimeDivisor.ord_stalkMap_eq_sum_intersectionLength_mul_ord
    (Q : MMP.Mori.PrimeDivisor T)
    (r : Y.presheaf.stalk (j Q.genericPoint)) (hr : (j.stalkMap Q.genericPoint).hom r ≠ 0) :
    ∃ S0 : Finset (MMP.Mori.PrimeDivisor Y),
      (∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
        Y.ord (algebraMap _ Y.functionField r) E.genericPoint ≠ 0 → E ∈ S0) ∧
      ∀ S : Finset (MMP.Mori.PrimeDivisor Y), S0 ⊆ S →
        T.ord (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
            ((j.stalkMap Q.genericPoint).hom r)) Q.genericPoint =
          ∑ E ∈ S, if j Q.genericPoint ∈ E.support then
            (E.intersectionLength j Q : ℤ) * Y.ord (algebraMap _ Y.functionField r) E.genericPoint
          else 0 := by
  classical
  have := isRegularLocalRing_stalk_of_smooth_over_field sY (j Q.genericPoint)
  have := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk (j Q.genericPoint))
  induction r using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd (map_zero _) hr
  | h₂ x hx =>
    have hv : ∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
        Y.ord (algebraMap _ Y.functionField x) E.genericPoint = 0 := fun E hE =>
      ord_algebraMap_isUnit_at (genericPoint_specializes_of_mem_support E hE)
        (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E) hx
    refine ⟨∅, fun E hE hne => (hne (hv E hE)).elim, fun S _ => ?_⟩
    rw [ord_algebraMap_isUnit_at specializes_rfl
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q) (hx.map _)]
    symm
    refine Finset.sum_eq_zero fun E _ => ?_
    split_ifs with hE
    · rw [hv E hE, mul_zero]
    · rfl
  | h₃ a p ha hp ih =>
    have hpa : (j.stalkMap Q.genericPoint).hom p * (j.stalkMap Q.genericPoint).hom a ≠ 0 := by
      rwa [← map_mul]
    obtain ⟨S0, hS0, hf⟩ := ih (right_ne_zero_of_mul hpa)
    obtain ⟨Eπ, hEπ, hv, hT⟩ := exists_primeDivisor_of_prime sY j Q hp (left_ne_zero_of_mul hpa)
    have hpK : algebraMap _ Y.functionField p ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]; exact hp.ne_zero
    have haK : algebraMap _ Y.functionField a ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]; exact ha
    have hmul : ∀ E : MMP.Mori.PrimeDivisor Y,
        Y.ord (algebraMap _ Y.functionField (p * a)) E.genericPoint =
          Y.ord (algebraMap _ Y.functionField p) E.genericPoint +
            Y.ord (algebraMap _ Y.functionField a) E.genericPoint := fun E => by
      rw [map_mul, Scheme.ord_mul hpK haK]
    refine ⟨insert Eπ S0, fun E hE hne => ?_, fun S hS => ?_⟩
    · rw [hmul, hv E hE] at hne
      by_cases h : E = Eπ
      · rw [h]; exact Finset.mem_insert_self _ _
      · rw [if_neg h, zero_add] at hne
        exact Finset.mem_insert_of_mem (hS0 E hE hne)
    · have hC : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
          ((j.stalkMap Q.genericPoint).hom p) ≠ 0 := by
        rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]; exact left_ne_zero_of_mul hpa
      have hC' : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
          ((j.stalkMap Q.genericPoint).hom a) ≠ 0 := by
        rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]; exact right_ne_zero_of_mul hpa
      rw [map_mul, map_mul, Scheme.ord_mul hC hC', hT,
        hf S ((Finset.subset_insert _ _).trans hS)]
      have hsplit : ∀ E ∈ S, (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
          Y.ord (algebraMap _ Y.functionField (p * a)) E.genericPoint else 0) =
          (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
            Y.ord (algebraMap _ Y.functionField p) E.genericPoint else 0) +
          (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
            Y.ord (algebraMap _ Y.functionField a) E.genericPoint else 0) := by
        intro E _
        split_ifs
        · rw [hmul, mul_add]
        · rw [add_zero]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single_of_mem Eπ (hS (Finset.mem_insert_self _ _))]
      · rw [if_pos hEπ, hv Eπ hEπ, if_pos rfl, mul_one]
      · intro E _ hE
        split_ifs with h
        · rw [hv E h, if_neg hE, mul_zero]
        · rfl

end PrincipalRestriction

section Obligations

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [CompactSpace Y] [IsLocallyNoetherian Y] [Smooth sY] {n : ℕ} (hY : topologicalKrullDim Y = n + 1)
      (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [CompactSpace T] [IsLocallyNoetherian T]
          [Smooth (j ≫ sY)] (P : MMP.Mori.PrimeDivisor Y) (hP : j
              (genericPoint T) = P.genericPoint) (τ : MMP.Mori.RationalPluriForms sY (n + 1) 1)
                  (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)

include hY hP hτ0 hτ

/-- **The residues of `τ` in coordinates.** There is a presentation `τ = a₀ · dϖ/ϖ ∧ dx₀` in the
local ring at the generic point of `T`, with `a₀` a unit and `dx̄₀` linearly independent on `T`
(a uniformizer `ϖ` and lifts `x₀` of smooth coordinates on `T` give a basis `dϖ, dx₀` of the
differentials of `𝒪_{Y,T}`), and the residues of `τ` are exactly the forms `ā₀ · dx̄₀`. -/
private theorem exists_isPoincareResidue_iff :
    letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
    ∃ (a0 : Y.presheaf.stalk (j (genericPoint T)))
      (x0 : Fin n → Y.presheaf.stalk (j (genericPoint T))), IsUnit a0 ∧
      LinearIndependent T.functionField
        (fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i))) ∧
      ∀ ρ, MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ ↔
        PiTensorProduct.subsingletonEquiv (R := T.functionField)
            (s := fun _ : Fin 1 => ⋀[T.functionField]^n Ω[T.functionField⁄k]) 0 ρ =
          (j.stalkMap (genericPoint T)).hom a0 • exteriorPower.ιMulti T.functionField n
            fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i)) := by
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  have := isDiscreteValuationRing_stalk sY _ hy
  obtain ⟨ϖ, a0, x0, hϖ, ha0, hspan, hli, -, hne, hτE, -, -⟩ :=
    exists_residue_data sY j P hP τ hτ0 hτ
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  refine ⟨a0, x0, ha0, hli, fun ρ => ⟨fun h =>
    residue_eq_of_isPoincareResidue sY j hy τ h ϖ a0 x0 hϖ hspan hne hτE, fun h =>
    (isPoincareResidue_iff sY j τ ρ).mpr ⟨ϖ, a0, x0, ord_algebraMap_irreducible _ hy hϖ, hτE, h⟩⟩⟩

private theorem exists_isPoincareResidue :
    ∃ ρ, MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ := by
  obtain ⟨a0, x0, -, -, H⟩ := exists_isPoincareResidue_iff sY hY j P hP τ hτ0 hτ
  exact ⟨_, (H _).mpr (LinearEquiv.apply_symm_apply _ _)⟩

/-- Well-definedness of the residue of a form with a simple pole. -/
private theorem isPoincareResidue_unique_of_ordForm_eq_neg_one
    {ρ ρ' : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ)
    (h' : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ') : ρ = ρ' := by
  obtain ⟨a0, x0, -, -, H⟩ := exists_isPoincareResidue_iff sY hY j P hP τ hτ0 hτ
  let := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  exact (PiTensorProduct.subsingletonEquiv (R := T.functionField)
    (s := fun _ : Fin 1 => ⋀[T.functionField]^n Ω[T.functionField⁄k]) 0).injective
    (((H ρ).mp h).trans ((H ρ').mp h').symm)

/-- The residue of a form with a simple pole is nonzero. -/
private theorem ne_zero_of_isPoincareResidue
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) : ρ ≠ 0 := by
  obtain ⟨a0, x0, ha0, hli, H⟩ := exists_isPoincareResidue_iff sY hY j P hP τ hτ0 hτ
  let := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  rintro rfl
  exact smul_ne_zero (ha0.map _).ne_zero (ιMulti_ne_zero_of_linearIndependent hli)
    (((H 0).mp h).symm.trans (map_zero _))

open MMP.Mori MMP.Intersection in
/-- **The residue in local coordinates at a point of `T`.** At a prime divisor `Q` of `T`, with
`y' = j(η_Q)`, there are `a, b ∈ 𝒪_{Y,y'}` with nonzero restrictions to `T` such that
`ord_Q(Res τ) = v_Q(a|_T) - v_Q(b|_T)` and `div_Y τ + T` has coefficient `v_E(a) - v_E(b)` along
every prime divisor `E` through `y'`: with `t'` a generator of the ideal of `T` at `y'` and `x'`
adapted coordinates, `τ = (a/b) · dt'/t' ∧ dx'`, the residue is `(a/b)|_T · dx̄'`, and `dx̄'`
generates the top forms of `𝒪_{T,Q}`. -/
private theorem exists_local_presentation_at
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) (Q : MMP.Mori.PrimeDivisor T) :
    ∃ a b : Y.presheaf.stalk (j Q.genericPoint),
      (j.stalkMap Q.genericPoint).hom a ≠ 0 ∧ (j.stalkMap Q.genericPoint).hom b ≠ 0 ∧
      Q.ordForm ρ =
        T.ord (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
            ((j.stalkMap Q.genericPoint).hom a)) Q.genericPoint -
          T.ord (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
            ((j.stalkMap Q.genericPoint).hom b)) Q.genericPoint ∧
      ∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
        (MMP.Mori.divisorOfForm τ + Finsupp.single P (1 : ℤ) : MMP.Mori.Divisor Y) E =
          Y.ord (algebraMap _ Y.functionField a) E.genericPoint -
            Y.ord (algebraMap _ Y.functionField b) E.genericPoint := by
  classical
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  have := isDiscreteValuationRing_stalk sY _ hy
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hKrank, -⟩ := exists_residue_data sY j P hP τ hτ0 hτ
  have hTsp : genericPoint T ⤳ Q.genericPoint := genericPoint_specializes _
  have hsp : j (genericPoint T) ⤳ j Q.genericPoint := j.base.hom.map_specializes hTsp
  have := isRegularLocalRing_stalk_of_smooth_over_field sY (j Q.genericPoint)
  have := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk (j Q.genericPoint))
  have hTinj := stalkSpecializes_injective hTsp
  have hcompat : ∀ a, (j.stalkMap (genericPoint T)).hom (Y.presheaf.stalkSpecializes hsp a) =
      T.presheaf.stalkSpecializes hTsp ((j.stalkMap Q.genericPoint).hom a) := fun a =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ hTsp a
  have hkerψ : RingHom.ker (j.stalkMap Q.genericPoint).hom = primeOfSpecializes hsp := by
    ext a
    rw [RingHom.mem_ker]
    change _ ↔ Y.presheaf.stalkSpecializes hsp a ∈ IsLocalRing.maximalIdeal _
    rw [← IsLocalRing.ker_eq_maximalIdeal _ (j.stalkMap_surjective (genericPoint T)),
      RingHom.mem_ker, hcompat]
    exact ⟨fun h0 => by rw [h0, map_zero], fun h0 => hTinj (h0.trans (map_zero _).symm)⟩
  letI : Algebra (Y.presheaf.stalk (j Q.genericPoint)) (Y.presheaf.stalk (j (genericPoint T))) :=
    (Y.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (Y.presheaf.stalk (j (genericPoint T)))
      (primeOfSpecializes hsp) := isLocalization_stalkSpecializes hsp
  have hpne : primeOfSpecializes hsp ≠ ⊥ := by
    intro hb
    have hm := IsLocalization.AtPrime.map_eq_maximalIdeal (primeOfSpecializes hsp)
      (Y.presheaf.stalk (j (genericPoint T)))
    rw [hb, Ideal.map_bot] at hm
    exact IsDiscreteValuationRing.not_a_field _ hm.symm
  obtain ⟨t', ht'p, ht'⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hpne
  have hz1 := coheight_fromSpecStalk_span_eq_one ht'
  set q' : PrimeSpectrum (Y.presheaf.stalk (j Q.genericPoint)) :=
    ⟨Ideal.span {t'}, (Ideal.span_singleton_prime ht'.ne_zero).mpr ht'⟩ with hq'
  have hz' : Y.fromSpecStalk _ q' ⤳ j Q.genericPoint := fromSpecStalk_specializes _ q'
  have hpz' : primeOfSpecializes hz' = Ideal.span {t'} :=
    comap_maximalIdeal_stalkSpecializes_fromSpecStalk _ q'
  have hz'y : Y.fromSpecStalk _ q' = j (genericPoint T) := by
    apply eq_of_specializes_of_coheight_eq_one _ hz1 hy
    apply specializes_of_primeOfSpecializes_le hz' hsp
    rwa [hpz', Ideal.span_le, Set.singleton_subset_iff]
  have hp_eq : primeOfSpecializes hsp = Ideal.span {t'} :=
    (primeOfSpecializes_congr hz'y.symm hsp hz').trans hpz'
  have hker : RingHom.ker (j.stalkMap Q.genericPoint).hom = Ideal.span {t'} := hkerψ.trans hp_eq
  -- coordinates at `y'`
  let := stalkAlgebra sY (j Q.genericPoint)
  let := stalkAlgebra (j ≫ sY) Q.genericPoint
  letI : Algebra (Y.presheaf.stalk (j Q.genericPoint)) (T.presheaf.stalk Q.genericPoint) :=
    (j.stalkMap Q.genericPoint).hom.toAlgebra
  have := isScalarTower_stalkMap sY j Q.genericPoint
  obtain ⟨hfsR, -, hefR⟩ := MMP.Flips.ResolutionInputs.stalk_facts sY (j Q.genericPoint)
  obtain ⟨hfsC, -, hefC⟩ := MMP.Flips.ResolutionInputs.stalk_facts (j ≫ sY) Q.genericPoint
  have : Module.Free (Y.presheaf.stalk (j Q.genericPoint))
      Ω[Y.presheaf.stalk (j Q.genericPoint)⁄k] := Module.free_of_flat_of_isLocalRing
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (j Q.genericPoint)
  have hrank : Module.finrank (Y.presheaf.stalk (j Q.genericPoint))
      Ω[Y.presheaf.stalk (j Q.genericPoint)⁄k] = n + 1 :=
    (MMP.Mori.finrank_kaehlerDifferential_eq_of_isFractionRing (k := k)
      (A := Y.presheaf.stalk (j Q.genericPoint)) (K := Y.functionField)).symm.trans hKrank
  obtain ⟨x', hspanR, hliC, hspanC⟩ := exists_coordinates_local (k := k)
    (A := Y.presheaf.stalk (j Q.genericPoint)) (C := T.presheaf.stalk Q.genericPoint)
    (j.stalkMap_surjective _) ht'.ne_zero hker hrank
  -- coordinates at the generic point of `T`
  let := stalkAlgebra sY (j (genericPoint T))
  have := isScalarTower_stalkSpecializes sY hsp
  have hspanR' := hspanR
  rw [cons_D_eq] at hspanR'
  have hspan_y := span_map_D_eq_top (k := k) (A := Y.presheaf.stalk (j Q.genericPoint))
    (B := Y.presheaf.stalk (j (genericPoint T))) (primeOfSpecializes hsp).primeCompl _ hspanR'
  set ϖ := Y.presheaf.stalkSpecializes hsp t' with hϖdef
  set x0 : Fin n → Y.presheaf.stalk (j (genericPoint T)) :=
    fun i => Y.presheaf.stalkSpecializes hsp (x' i) with hx0def
  have hspan_y' : Submodule.span (Y.presheaf.stalk (j (genericPoint T))) (Set.range
      (Fin.cons (D k _ ϖ) fun i => D k _ (x0 i) :
        Fin (n + 1) → Ω[Y.presheaf.stalk (j (genericPoint T))⁄k])) = ⊤ := by
    rw [cons_D_eq]
    convert hspan_y using 3
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have hϖ : Irreducible ϖ := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (primeOfSpecializes hsp)
        (Y.presheaf.stalk (j (genericPoint T))), hp_eq, Ideal.map_span, Set.image_singleton]
    rfl
  have hτy := (ordForm_eq_ordAt sY P τ _ hP).symm.trans hτ
  obtain ⟨a0, ha0, hne, hτE⟩ := exists_unit_presentation sY _ hy τ hτ0 hτy ϖ x0 hϖ hspan_y'
  have hρE := residue_eq_of_isPoincareResidue sY j hy τ h ϖ a0 x0 hϖ hspan_y' hne hτE
  -- write `a₀ = a / b`
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (primeOfSpecializes hsp).primeCompl a0
  have hab' : a0 * Y.presheaf.stalkSpecializes hsp b = Y.presheaf.stalkSpecializes hsp a := by
    rw [← hab]
    exact IsLocalization.mk'_spec _ a b
  have hbunit : IsUnit (Y.presheaf.stalkSpecializes hsp b) := IsLocalization.map_units _ b
  have hap : a ∉ primeOfSpecializes hsp := by
    intro hm
    have hu : IsUnit (Y.presheaf.stalkSpecializes hsp a) := hab' ▸ ha0.mul hbunit
    exact (IsLocalRing.mem_maximalIdeal _).mp hm hu
  have hbp : (b : Y.presheaf.stalk (j Q.genericPoint)) ∉ primeOfSpecializes hsp := b.2
  have hψa : (j.stalkMap Q.genericPoint).hom a ≠ 0 := fun h0 =>
    hap (hkerψ.le (RingHom.mem_ker.mpr h0))
  have hψb : (j.stalkMap Q.genericPoint).hom b ≠ 0 := fun h0 =>
    hbp (hkerψ.le (RingHom.mem_ker.mpr h0))
  -- `a₀ = a / b` on `T`
  have hspT : ∀ c : T.presheaf.stalk Q.genericPoint,
      T.presheaf.stalkSpecializes hTsp c = algebraMap _ T.functionField c := fun c => rfl
  have hCa : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
      ((j.stalkMap Q.genericPoint).hom a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hψa
  have hCb : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
      ((j.stalkMap Q.genericPoint).hom b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hψb
  have hφa0 : (j.stalkMap (genericPoint T)).hom a0 =
      algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom a) *
        (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom b))⁻¹ := by
    have h1 := congrArg (j.stalkMap (genericPoint T)).hom hab'
    rw [map_mul, hcompat, hcompat, hspT, hspT] at h1
    rw [← h1, mul_assoc, mul_inv_cancel₀ hCb, mul_one]
  refine ⟨a, b, hψa, hψb, ?_, ?_⟩
  · let := functionFieldAlgebra (j ≫ sY)
    have := isScalarTower_stalk_functionField (j ≫ sY) Q.genericPoint
    set σC := exteriorPower.ιMulti (T.presheaf.stalk Q.genericPoint) n
      (fun i => D k (T.presheaf.stalk Q.genericPoint) ((j.stalkMap Q.genericPoint).hom (x' i)))
    have hgenC := span_ιMulti_eq_top _ hspanC
    have himgC : topFormsMap k _ T.functionField n σC = exteriorPower.ιMulti T.functionField n
        (fun i => D k T.functionField (algebraMap _ T.functionField
          ((j.stalkMap Q.genericPoint).hom (x' i)))) := by
      rw [topFormsMap_ιMulti]
      congr 1
      funext i
      simp
    have hliK : LinearIndependent T.functionField (fun i => D k T.functionField
        (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom (x' i)))) := by
      let bC := Module.Basis.mk hliC hspanC.ge
      let bK := bC.ofIsLocalizedModule T.functionField (nonZeroDivisors _)
        (KaehlerDifferential.map k k (T.presheaf.stalk Q.genericPoint) T.functionField)
      have hfun : (fun i => D k T.functionField
          (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom (x' i)))) = ⇑bK := by
        funext i
        simp [bK, bC, Module.Basis.ofIsLocalizedModule_apply]
        rfl
      rw [hfun]
      exact bK.linearIndependent
    have h0C : topFormsMap k _ T.functionField n σC ≠ 0 :=
      himgC ▸ ιMulti_ne_zero_of_linearIndependent hliK
    have hρE' : PiTensorProduct.subsingletonEquiv (R := T.functionField)
        (s := fun _ : Fin 1 => ⋀[T.functionField]^n Ω[T.functionField⁄k]) 0 ρ =
        (j.stalkMap (genericPoint T)).hom a0 • topFormsMap k _ T.functionField n σC := by
      rw [hρE, himgC]
      congr 2
      funext i
      rw [hx0def]
      simp only
      rw [hcompat, hspT]
    rw [MMP.Mori.PrimeDivisor.ordForm_eq Q ρ hgenC h0C,
      formCoeff_eq_of_subsingletonEquiv hgenC h0C ρ _ hρE', hφa0, ord_mul_inv hCa hCb]
  · intro E hE
    have hEsp := genericPoint_specializes_of_mem_support E hE
    have hE1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
    let := stalkAlgebra sY E.genericPoint
    letI : Algebra (Y.presheaf.stalk (j Q.genericPoint)) (Y.presheaf.stalk E.genericPoint) :=
      (Y.presheaf.stalkSpecializes hEsp).hom.toAlgebra
    have := isScalarTower_stalkSpecializes sY hEsp
    have : IsLocalization.AtPrime (Y.presheaf.stalk E.genericPoint) (primeOfSpecializes hEsp) :=
      isLocalization_stalkSpecializes hEsp
    have := isScalarTower_stalk_functionField sY E.genericPoint
    have hspanE := span_map_D_eq_top (k := k) (A := Y.presheaf.stalk (j Q.genericPoint))
      (B := Y.presheaf.stalk E.genericPoint) (primeOfSpecializes hEsp).primeCompl _ hspanR'
    set eE : Fin (n + 1) → Ω[Y.presheaf.stalk E.genericPoint⁄k] := fun i =>
      D k _ (algebraMap _ (Y.presheaf.stalk E.genericPoint)
        ((Fin.cons t' x' : Fin (n + 1) → Y.presheaf.stalk (j Q.genericPoint)) i))
    have hgenE := span_ιMulti_eq_top eE hspanE
    have himgE : topFormsMap k _ Y.functionField (n + 1) (exteriorPower.ιMulti _ (n + 1) eE) =
        exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) := by
      rw [topFormsMap_ιMulti]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [eE, KaehlerDifferential.map_D, Fin.cons_zero, hϖdef]
        exact congrArg _ ((algebraMap_stalkSpecializes hEsp t').trans
          (algebraMap_stalkSpecializes hsp t').symm)
      · simp only [eE, KaehlerDifferential.map_D, Fin.cons_succ, hx0def]
        exact congrArg _ ((algebraMap_stalkSpecializes hEsp (x' i)).trans
          (algebraMap_stalkSpecializes hsp (x' i)).symm)
    have h0E : topFormsMap k _ Y.functionField (n + 1) (exteriorPower.ιMulti _ (n + 1) eE) ≠ 0 :=
      himgE ▸ hne
    have hcoef := formCoeff_eq_of_subsingletonEquiv hgenE h0E τ _ (hτE.trans (by rw [himgE]))
    have hDE : (MMP.Mori.divisorOfForm τ + Finsupp.single P (1 : ℤ) : MMP.Mori.Divisor Y) E =
        E.ordForm τ + if E = P then 1 else 0 := by
      rw [Finsupp.add_apply, Finsupp.single_apply]
      congr 1
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    rw [hDE, E.ordForm_eq τ hgenE h0E, hcoef]
    -- the coefficient `a₀ / ϖ` is `a / (b t')`
    have hRa : algebraMap _ Y.functionField a ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]
      rintro rfl; exact hap (Ideal.zero_mem _)
    have hRb : algebraMap _ Y.functionField (b : Y.presheaf.stalk (j Q.genericPoint)) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]
      intro h0; apply hbp; rw [h0]; exact Ideal.zero_mem _
    have hRt : algebraMap _ Y.functionField t' ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]; exact ht'.ne_zero
    have ha0' : algebraMap _ Y.functionField a0 = algebraMap _ Y.functionField a *
        (algebraMap _ Y.functionField (b : Y.presheaf.stalk (j Q.genericPoint)))⁻¹ := by
      have h1 := congrArg (algebraMap _ Y.functionField) hab'
      rw [map_mul, algebraMap_stalkSpecializes, algebraMap_stalkSpecializes] at h1
      rw [← h1, mul_assoc, mul_inv_cancel₀ hRb, mul_one]
    have hϖK : algebraMap _ Y.functionField ϖ = algebraMap _ Y.functionField t' :=
      algebraMap_stalkSpecializes hsp t'
    rw [ha0', hϖK, ord_mul_inv (mul_ne_zero hRa (inv_ne_zero hRb)) hRt,
      ord_mul_inv hRa hRb]
    -- the order of `t'` along `E`
    have ht'E := ord_prime_eq_ite ht' hz' hpz' hz1 E hE
    rw [hz'y, hP] at ht'E
    rw [ht'E]
    have hiff : E.genericPoint = P.genericPoint ↔ E = P :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.eq_iff
    by_cases hEP : E = P
    · rw [if_pos (hiff.mpr hEP), if_pos hEP]; ring
    · rw [if_neg (fun h => hEP (hiff.mp h)), if_neg hEP]; ring

/-- **The local computation of the divisor of the residue.** At a prime divisor `Q` of `T`,
with `y' = j(η_Q)`, choose local coordinates `t', x'` of `𝒪_{Y,y'}` adapted to `T` and write
`τ = F · dt'/t' ∧ dx'`; then `ord_Q(Res τ) = v_Q(F|_T)`, while `div_Y τ + T` agrees with
`div F` along the prime divisors through `y'`, and restricting the principal divisor `div F`
to `T` gives `v_Q(F|_T)`. -/
private theorem ordForm_eq_sum_intersectionLength
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) (Q : MMP.Mori.PrimeDivisor T) :
    Q.ordForm ρ = (MMP.Mori.divisorOfForm τ + Finsupp.single P 1).sum
      fun E d => E.intersectionLength j Q • d := by
  classical
  obtain ⟨a, b, ha, hb, hQ, hD⟩ := exists_local_presentation_at sY hY j P hP τ hτ0 hτ h Q
  obtain ⟨Sa, hSa, hfa⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sY j a ha
  obtain ⟨Sb, hSb, hfb⟩ := Q.ord_stalkMap_eq_sum_intersectionLength_mul_ord sY j b hb
  set D := MMP.Mori.divisorOfForm τ + Finsupp.single P (1 : ℤ) with hDdef
  set S := D.support ∪ Sa ∪ Sb
  have h1 : D.sum (fun E d => E.intersectionLength j Q • d) =
      ∑ E ∈ S, if j Q.genericPoint ∈ E.support then
          (E.intersectionLength j Q : ℤ) * D E else 0 := by
    rw [Finsupp.sum]
    rw [Finset.sum_subset (s₁ := D.support) (s₂ := S) (by
      intro E hE; simp [S, hE]) (by
      intro E _ hE
      rw [Finsupp.notMem_support_iff] at hE
      simp [hE])]
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs with hE
    · rw [nsmul_eq_mul]
    · rw [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem j E hE, zero_smul]
  have h2 : ∀ E ∈ S, (if j Q.genericPoint ∈ E.support then
      (E.intersectionLength j Q : ℤ) * D E else 0) =
      (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
        Y.ord (algebraMap _ Y.functionField a) E.genericPoint else 0) -
      (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
        Y.ord (algebraMap _ Y.functionField b) E.genericPoint else 0) := by
    intro E _
    split_ifs with hE
    · rw [hD E hE, mul_sub]
    · rw [sub_zero]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib,
    ← hfa S (by intro E hE; simp [S, hE]), ← hfb S (by intro E hE; simp [S, hE]), hQ]

/-- The divisor of the residue is `(div_Y τ + T)|_T`. -/
private theorem divisorOfForm_eq_restrict_of_isPoincareResidue
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) :
    MMP.Mori.divisorOfForm ρ =
      (MMP.Mori.divisorOfForm τ + Finsupp.single P 1).restrict j := by
  classical
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  set D := MMP.Mori.divisorOfForm τ + Finsupp.single P (1 : ℤ) with hDdef
  have hDP : D P = 0 := by
    simp only [D, Finsupp.add_apply, Finsupp.single_eq_same]
    change P.ordForm τ + 1 = 0
    rw [hτ]; rfl
  have : AlgebraicGeometry.IsNoetherian T := ⟨⟩
  have hgen : ∀ s : T, Order.coheight s = 0 → s = genericPoint T := fun s hs => by
    have hle : s ≤ genericPoint T := genericPoint_specializes s
    exact (Specializes.antisymm (Order.coheight_eq_zero.mp hs hle) hle).eq
  have hpure : ∀ s : T, Order.coheight s = 0 → Order.coheight (j s) = 1 := fun s hs => by
    rw [hgen s hs]; exact hy
  have hD : ∀ E ∈ D.support, ∀ s : T, Order.coheight s = 0 → j s ≠ E.genericPoint := by
    intro E hE s hs hjs
    rw [hgen s hs, hP] at hjs
    have : P = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hjs
    rw [Finsupp.mem_support_iff, ← this] at hE
    exact hE hDP
  ext Q
  change Q.ordForm ρ = (D.restrict j).coeff Q
  rw [MMP.Mori.DivisorWithCoeffs.coeff_restrict_of_pure j D hpure hD Q]
  exact ordForm_eq_sum_intersectionLength sY hY j P hP τ hτ0 hτ h Q

/-- Residues commute with pull-back to the strict transform. -/
private theorem isPoincareResidue_pullback
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (hρ : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ)
    {Y₁ T₁ : Scheme.{u}} (g : Y₁ ⟶ Y) [IsIntegral Y₁] [IsLocallyNoetherian Y₁]
    [Smooth (g ≫ sY)] [IsProper g] [IsDominant g]
    (_hg : MMP.Mori.IsBirationalMorphism g) (U : Y.Opens) (_hU : P.genericPoint ∈ U)
    [IsIso (morphismRestrict g U)]
    (j₁ : T₁ ⟶ Y₁) [IsClosedImmersion j₁] [IsIntegral T₁]
    (h : T₁ ⟶ T) [IsDominant h] (hh : h ≫ j = j₁ ≫ g) :
    MMP.Fourfold.IsPoincareResidue (g ≫ sY) j₁ n 1
      (MMP.Mori.pullbackRationalPluriForms sY g τ)
      (cast (by rw [← Category.assoc, hh, Category.assoc]; rfl)
        (MMP.Mori.pullbackRationalPluriForms (j ≫ sY) h ρ)) := by
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  have := isDiscreteValuationRing_stalk sY _ hy
  obtain ⟨_, _, _, -, -, -, hli, hspanB, -, -, hKrank, hKfin⟩ :=
    exists_residue_data sY j P hP τ hτ0 hτ
  have hy₁U : g (j₁ (genericPoint T₁)) ∈ U := by
    rw [map_genericPoint_eq g j j₁ h hh, hP]; exact _hU
  have := isIso_stalkMap_of_isIso_morphismRestrict g U _ hy₁U
  let := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  let bT := Module.Basis.mk hli hspanB.ge
  exact isPoincareResidue_pullback_of_finrank g j₁ h hh hy ⟨hKrank, hKfin⟩
    ⟨by rw [Module.finrank_eq_card_basis bT, Fintype.card_fin], Module.Finite.of_basis bT⟩ hρ

end Obligations

end MMP.Mori.SmoothDivisorResidue

open MMP.Mori.SmoothDivisorResidue in
/-- **The residue of a rational top form along a smooth prime divisor.** Let `Y` be a smooth
variety of dimension `n + 1` over `k`, `j : T ⟶ Y` a smooth integral closed subscheme whose
generic point is that of the prime divisor `P`, and `τ ≠ 0` a rational top form on `Y` with
`ord_P τ = -1`. Then there is exactly one residue `ρ = Res_T τ`
(`MMP.Fourfold.IsPoincareResidue`); it is nonzero, `div_T ρ = (div_Y τ + P)|_T`, and for every
proper birational morphism `g : Y₁ ⟶ Y` of smooth varieties which is an isomorphism over an open
`U ∋ η_P`, and every integral closed `j₁ : T₁ ⟶ Y₁` mapping dominantly onto `T` (the strict
transform), `h^*ρ` is the residue of `g^*τ` along `T₁`. -/
@[mmp "lem_mmp_smooth_divisor_residue"]
public theorem MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one {k : Type u} [Field k]
    {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [Smooth sY] {n : ℕ} (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [CompactSpace T] [IsLocallyNoetherian T]
    [Smooth (j ≫ sY)] (P : PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    (τ : RationalPluriForms sY (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1) :
    ∃ ρ : RationalPluriForms (j ≫ sY) n 1,
      (∀ ρ', MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ' ↔ ρ' = ρ) ∧ ρ ≠ 0 ∧
      divisorOfForm ρ = (divisorOfForm τ + Finsupp.single P 1).restrict j ∧
      ∀ {Y₁ T₁ : Scheme.{u}} (g : Y₁ ⟶ Y) [IsIntegral Y₁] [IsLocallyNoetherian Y₁]
        [Smooth (g ≫ sY)] [IsProper g] [IsDominant g] (_hg : IsBirationalMorphism g)
        (U : Y.Opens) (_hU : P.genericPoint ∈ U) [IsIso (morphismRestrict g U)]
        (j₁ : T₁ ⟶ Y₁) [IsClosedImmersion j₁] [IsIntegral T₁] (h : T₁ ⟶ T) [IsDominant h]
        (hh : h ≫ j = j₁ ≫ g),
        MMP.Fourfold.IsPoincareResidue (g ≫ sY) j₁ n 1 (pullbackRationalPluriForms sY g τ)
          (cast (by rw [← Category.assoc, hh, Category.assoc]; rfl)
            (pullbackRationalPluriForms (j ≫ sY) h ρ)) := by
  obtain ⟨ρ, hρ⟩ := exists_isPoincareResidue sY hY j P hP τ hτ0 hτ
  refine ⟨ρ, fun ρ' => ⟨fun h' =>
    isPoincareResidue_unique_of_ordForm_eq_neg_one sY hY j P hP τ hτ0 hτ h' hρ,
    fun e => e ▸ hρ⟩, ne_zero_of_isPoincareResidue sY hY j P hP τ hτ0 hτ hρ,
    divisorOfForm_eq_restrict_of_isPoincareResidue sY hY j P hP τ hτ0 hτ hρ, ?_⟩
  intro Y₁ T₁ g _ _ _ _ _ hg U hU _ j₁ _ _ h _ hh
  exact isPoincareResidue_pullback sY hY j P hP τ hτ0 hτ hρ g hg U hU j₁ h hh

/-!
## The Poincaré residue sequence and its rational extension

Let `Y` be a smooth variety of dimension `n + 1` over a field `k` and `ι : T ⟶ Y` a smooth prime
divisor, with generic point `y = ι(η_T)`. The Poincaré residue `Res_T` is defined on the rational
top forms `σ` with `ord_T σ ≥ -1`: writing `σ = g · dt/t ∧ dx₁ ∧ ⋯ ∧ dx_n` with `t` a uniformizer
of the discrete valuation ring `𝒪_{Y,y}` and `g, x_i ∈ 𝒪_{Y,y}`, one puts
`Res_T σ = ḡ · dx̄₁ ∧ ⋯ ∧ dx̄_n`, a rational `n`-form on `T`. It is additive,
`Res_T (φσ) = φ̄ · Res_T σ` for `φ ∈ 𝒪_{Y,y}`, and on sections it gives an `𝒪_Y`-linear
surjection `ω_Y(T) → ι_* ω_T` whose kernel is `ω_Y`.
-/

namespace MMP.Mori.PoincareResidue

open KaehlerDifferential IsLocalRing TensorProduct

section Algebra

variable {k A L : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A] [Field L]
  [Algebra k L] [Algebra A L] [IsScalarTower k A L]

private theorem linearIndependent_tmul_D [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k L]
    (hsurj : Function.Surjective (algebraMap A L))
    {n : ℕ} {t : A} (htk : algebraMap A L t = 0) (ht2 : t ∉ maximalIdeal A ^ 2)
    (hker : RingHom.ker (algebraMap A L) = maximalIdeal A)
    (x : Fin n → A) (hx : LinearIndependent L fun i => D k L (algebraMap A L (x i))) :
    LinearIndependent L (Fin.cons ((1 : L) ⊗ₜ[A] D k A t)
      fun i => (1 : L) ⊗ₜ[A] D k A (x i) : Fin (n + 1) → L ⊗[A] Ω[A⁄k]) := by
  have hφ : ∀ a : A, mapBaseChange k A L ((1 : L) ⊗ₜ[A] D k A a) = D k L (algebraMap A L a) := by
    intro a
    rw [mapBaseChange_tmul, one_smul, map_D]
  have htail : LinearIndependent L fun i => (1 : L) ⊗ₜ[A] D k A (x i) := by
    refine LinearIndependent.of_comp (mapBaseChange k A L) ?_
    convert hx using 1
    funext i
    exact hφ (x i)
  have ht0 : (1 : L) ⊗ₜ[A] D k A t ≠ 0 := by
    have hinj : Function.Injective (kerCotangentToTensor k A L) := by
      refine (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hsurj).mpr ?_
      exact ((Algebra.formallySmooth_iff k L).mp inferInstance).2
    have htI : t ∈ RingHom.ker (algebraMap A L) := htk
    intro h0
    have : (RingHom.ker (algebraMap A L)).toCotangent ⟨t, htI⟩ = 0 :=
      hinj (by rwa [kerCotangentToTensor_toCotangent, map_zero])
    rw [Ideal.toCotangent_eq_zero] at this
    exact ht2 (hker ▸ this)
  refine linearIndependent_fin_cons.mpr ⟨htail, fun hmem => ht0 ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hmem
  have hc0 : ∀ i, c i = 0 := by
    have := congrArg (mapBaseChange k A L) hc
    rw [map_sum, hφ, htk, Derivation.map_zero] at this
    simp only [map_smul, hφ] at this
    exact fun i => (Fintype.linearIndependent_iff.mp hx) c this i
  rw [← hc]
  simp [hc0]

private theorem exists_basis_cons_D [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k L]
    [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    (hsurj : Function.Surjective (algebraMap A L))
    {n : ℕ} (hn : Module.finrank A Ω[A⁄k] = n + 1) {t : A} (htk : algebraMap A L t = 0)
    (ht2 : t ∉ maximalIdeal A ^ 2) (hker : RingHom.ker (algebraMap A L) = maximalIdeal A)
    (x : Fin n → A) (hx : LinearIndependent L fun i => D k L (algebraMap A L (x i))) :
    ∃ b : Module.Basis (Fin (n + 1)) A Ω[A⁄k],
      ⇑b = (Fin.cons (D k A t) fun i => D k A (x i) : Fin (n + 1) → Ω[A⁄k]) := by
  set w : Fin (n + 1) → Ω[A⁄k] := Fin.cons (D k A t) fun i => D k A (x i) with hw
  have hw' : (fun i => (1 : L) ⊗ₜ[A] w i) = (Fin.cons ((1 : L) ⊗ₜ[A] D k A t)
      fun i => (1 : L) ⊗ₜ[A] D k A (x i) : Fin (n + 1) → L ⊗[A] Ω[A⁄k]) := by
    funext i
    refine Fin.cases rfl (fun i => rfl) i
  have hli : LinearIndependent L fun i => (1 : L) ⊗ₜ[A] w i := by
    rw [hw']
    exact linearIndependent_tmul_D hsurj htk ht2 hker x hx
  let bL := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Module.finrank_baseChange, hn, Fintype.card_fin])
  have hspL : Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[A] w i) = ⊤ := by
    simpa [bL] using bL.span_eq
  have hsp := SmoothDivisorResidue.span_eq_top_of_isBasis_tmul hsurj hn w hli hspL
  exact ⟨basisOfTopLeSpanOfCardEqFinrank w hsp.ge (by rw [hn, Fintype.card_fin]),
    coe_basisOfTopLeSpanOfCardEqFinrank _ _ _⟩

private theorem span_ιMulti_cons_D_eq_top [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k L]
    [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    (hsurj : Function.Surjective (algebraMap A L))
    {n : ℕ} (hn : Module.finrank A Ω[A⁄k] = n + 1) {t : A} (htk : algebraMap A L t = 0)
    (ht2 : t ∉ maximalIdeal A ^ 2) (hker : RingHom.ker (algebraMap A L) = maximalIdeal A)
    (x : Fin n → A) (hx : LinearIndependent L fun i => D k L (algebraMap A L (x i))) :
    Submodule.span A {(exteriorPower.ιMulti A (n + 1)
      (Fin.cons (D k A t) fun i => D k A (x i) : Fin (n + 1) → Ω[A⁄k]))} = ⊤ := by
  obtain ⟨b, hb⟩ := exists_basis_cons_D hsurj hn htk ht2 hker x hx
  have hbij := MMP.Intersection.bijective_smul_ιMulti_basis b
  rw [hb] at hbij
  refine eq_top_iff.mpr fun w _ => ?_
  obtain ⟨r, rfl⟩ := hbij.2 w
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Algebra

section Setup

variable {k : Type u} [Field k] {Y T : Scheme.{u}}

variable [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

private theorem isDiscreteValuationRing_stalk_of_genericPoint_eq (P : MMP.Mori.PrimeDivisor Y)
    {y : Y} (hy : P.genericPoint = y) :
    IsDiscreteValuationRing (Y.presheaf.stalk y) := by
  subst hy
  exact P.isDiscreteValuationRing_localRing

private theorem ord_nonneg (P : MMP.Mori.PrimeDivisor Y) {y : Y} (hy : P.genericPoint = y)
    (a : Y.presheaf.stalk y) : 0 ≤ Y.ord (algebraMap _ Y.functionField a) y := by
  subst hy
  by_cases ha : algebraMap _ Y.functionField a = 0
  · rw [ha, Scheme.ord_zero]; rfl
  have h := (P.divisorialValuation_le_one_iff _).mpr ⟨a, rfl⟩
  rw [P.divisorialValuation_eq_exp_neg_ord ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

private theorem ord_pos_iff (P : MMP.Mori.PrimeDivisor Y) {y : Y} (hy : P.genericPoint = y)
    {a : Y.presheaf.stalk y} (ha : algebraMap _ Y.functionField a ≠ 0) :
    0 < Y.ord (algebraMap _ Y.functionField a) y ↔ a ∈ maximalIdeal (Y.presheaf.stalk y) := by
  subst hy
  rw [← P.divisorialValuation_algebraMap_lt_one_iff, P.divisorialValuation_eq_exp_neg_ord ha,
    ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem exists_eq_of_ord_nonneg (P : MMP.Mori.PrimeDivisor Y) {y : Y}
    (hy : P.genericPoint = y)
    {f : Y.functionField} (h : f = 0 ∨ 0 ≤ Y.ord f y) :
    ∃ a : Y.presheaf.stalk y, algebraMap _ Y.functionField a = f := by
  subst hy
  rcases h with rfl | h
  · exact ⟨0, map_zero _⟩
  by_cases hf : f = 0
  · exact ⟨0, hf ▸ map_zero _⟩
  have hv : P.divisorialValuation f ≤ 1 := by
    rw [P.divisorialValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨a, ha⟩ := (P.divisorialValuation_le_one_iff f).mp hv
  exact ⟨a, ha⟩

private theorem exists_ord_eq_one (P : MMP.Mori.PrimeDivisor Y) {y : Y} (hy : P.genericPoint = y) :
    ∃ t : Y.presheaf.stalk y, Y.ord (algebraMap _ Y.functionField t) y = 1 := by
  have := isDiscreteValuationRing_stalk_of_genericPoint_eq P hy
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y)
  exact ⟨ϖ, SmoothDivisorResidue.ord_algebraMap_irreducible y (hy ▸ P.coheight_genericPoint) hϖ⟩

omit [IsNormal Y] in
private theorem ne_zero_of_ord_eq_one {f : Y.functionField} {y : Y} (h : Y.ord f y = 1) :
    f ≠ 0 := by
  rintro rfl
  simp at h

private theorem mem_maximalIdeal_and_notMem_sq_of_ord_eq_one (P : MMP.Mori.PrimeDivisor Y)
    {y : Y} (hy : P.genericPoint = y)
    {t : Y.presheaf.stalk y} (ht : Y.ord (algebraMap _ Y.functionField t) y = 1) :
    t ∈ maximalIdeal (Y.presheaf.stalk y) ∧ t ∉ maximalIdeal (Y.presheaf.stalk y) ^ 2 := by
  have ht0 := ne_zero_of_ord_eq_one ht
  refine ⟨(ord_pos_iff P hy ht0).mp (by omega), fun hsq => ?_⟩
  have := isDiscreteValuationRing_stalk_of_genericPoint_eq P hy
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y)
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hsq
  obtain ⟨c, rfl⟩ := hsq
  have hϖ1 := SmoothDivisorResidue.ord_algebraMap_irreducible y (hy ▸ P.coheight_genericPoint) hϖ
  have hϖ0 := ne_zero_of_ord_eq_one hϖ1
  have hc0 : algebraMap _ Y.functionField c ≠ 0 := by
    intro h; apply ht0; rw [map_mul, h, mul_zero]
  rw [map_mul, map_pow, Scheme.ord_mul (pow_ne_zero 2 hϖ0) hc0, pow_two,
    Scheme.ord_mul hϖ0 hϖ0, hϖ1] at ht
  have := ord_nonneg P hy c
  omega

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- On a smooth integral scheme of dimension `d` over `k`, the function field has
`dim Ω_{k(Y)/k} = d`, and at every point `Ω_{𝒪_{Y,y}/k}` is free of rank `d`. -/
private theorem finrank_kaehler (sY : Y ⟶ Spec (.of k)) [Smooth sY] {d : ℕ}
    (hY : topologicalKrullDim Y = d) (y : Y) :
    letI := MMP.Mori.stalkAlgebra sY y
    letI := MMP.Mori.functionFieldAlgebra sY
    Module.Free (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] ∧
      Module.Finite (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] ∧
      Module.finrank (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] = d ∧
      Module.finrank Y.functionField Ω[Y.functionField⁄k] = d := by
  letI := MMP.Mori.stalkAlgebra sY y
  letI := MMP.Mori.functionFieldAlgebra sY
  haveI := MMP.Mori.isScalarTower_stalk_functionField sY y
  obtain ⟨h1, h2, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts sY y
  have : Module.Finite (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] :=
    KaehlerDifferential.finite k _
  have : Module.Free (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] :=
    Module.free_of_flat_of_isLocalRing
  have : Algebra.FormallySmooth (Y.presheaf.stalk y) Y.functionField :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors (Y.presheaf.stalk y))
  have : Algebra.FormallySmooth k Y.functionField :=
    Algebra.FormallySmooth.comp k (Y.presheaf.stalk y) Y.functionField
  have := MMP.Mori.essFiniteType_functionField (sX := sY)
  have hK : Module.finrank Y.functionField Ω[Y.functionField⁄k] = d := by
    have h := (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k
      Y.functionField).2.2
    rw [Module.finrank_zero_of_subsingleton (M := Algebra.H1Cotangent k Y.functionField),
      Nat.cast_zero, sub_zero] at h
    rw [← MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hY]
    exact_mod_cast h.symm
  refine ⟨inferInstance, inferInstance, ?_, hK⟩
  rw [← MMP.Mori.finrank_kaehlerDifferential_eq_of_isFractionRing (K := Y.functionField), hK]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The residue map `𝒪_{Y,j(η_T)} → k(T)` along an integral closed subscheme. -/
private theorem residue_facts (sY : Y ⟶ Spec (.of k)) (j : T ⟶ Y) [IsClosedImmersion j]
    [IsIntegral T] [Smooth (j ≫ sY)] :
    letI := MMP.Mori.stalkAlgebra sY (j (genericPoint T))
    letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk (j (genericPoint T))) T.functionField ∧
      Algebra.FormallySmooth k T.functionField ∧
      Function.Surjective (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) ∧
      RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) =
        maximalIdeal _ := by
  letI := MMP.Mori.stalkAlgebra sY (j (genericPoint T))
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have hsurj : Function.Surjective
      (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) :=
    SurjectiveOnStalks.stalkMap_surjective (f := j) _
  exact ⟨SmoothDivisorResidue.isScalarTower_stalkMap sY j _,
    (MMP.Flips.ResolutionInputs.stalk_facts (j ≫ sY) (genericPoint T)).1, hsurj,
    IsLocalRing.ker_eq_maximalIdeal _ hsurj⟩

/-- The order along `P` of a form, computed from any generator of the top forms of the local ring
at the generic point `y` of `P`. -/
private theorem ordForm_eq_ord_formCoeff (sY : Y ⟶ Spec (.of k)) (P : MMP.Mori.PrimeDivisor Y)
    {y : Y}
    (hy : P.genericPoint = y) {d : ℕ} :
    letI := MMP.Mori.stalkAlgebra sY y
    letI := MMP.Mori.functionFieldAlgebra sY
    haveI := MMP.Mori.isScalarTower_stalk_functionField sY y
    ∀ {ω : ⋀[Y.presheaf.stalk y]^d Ω[Y.presheaf.stalk y⁄k]}
      (hω : Submodule.span (Y.presheaf.stalk y) {ω} = ⊤)
      (h0 : MMP.Mori.topFormsMap k (Y.presheaf.stalk y) Y.functionField d ω ≠ 0)
      (τ : MMP.Mori.RationalPluriForms sY d 1),
      P.ordForm τ = Y.ord (MMP.Mori.formCoeff (k := k) (m := 1)
          (Y.presheaf.stalk y) hω h0 τ) y := by
  subst hy
  intro ω hω h0 τ
  exact P.ordForm_eq τ hω h0

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The coordinate of `g · (dt/t ∧ dx₁ ∧ ⋯ ∧ dx_n)` along the generator `dt ∧ dx₁ ∧ ⋯ ∧ dx_n`
is `g / t`. -/
private theorem formCoeff_presentation (sY : Y ⟶ Spec (.of k)) {y : Y} {n : ℕ}
    (t g : Y.presheaf.stalk y) (x : Fin n → Y.presheaf.stalk y)
    (τ : MMP.Mori.RationalPluriForms sY (n + 1) 1) :
    letI := MMP.Mori.stalkAlgebra sY y
    letI := MMP.Mori.functionFieldAlgebra sY
    haveI := MMP.Mori.isScalarTower_stalk_functionField sY y
    ∀ (hω : Submodule.span (Y.presheaf.stalk y) {(exteriorPower.ιMulti _ (n + 1)
        (Fin.cons (D k _ t) fun i => D k _ (x i) : Fin (n + 1) → Ω[Y.presheaf.stalk y⁄k]))} = ⊤)
      (h0 : MMP.Mori.topFormsMap k (Y.presheaf.stalk y) Y.functionField (n + 1)
        (exteriorPower.ιMulti _ (n + 1)
          (Fin.cons (D k _ t) fun i => D k _ (x i) : Fin (n + 1) → Ω[Y.presheaf.stalk y⁄k])) ≠ 0),
      τ = (algebraMap _ Y.functionField g • PiTensorProduct.tprod Y.functionField
          (fun _ : Fin 1 => (algebraMap _ Y.functionField t)⁻¹ •
            exteriorPower.ιMulti Y.functionField (n + 1)
              (Fin.cons (KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
                fun i => KaehlerDifferential.D k Y.functionField (algebraMap _ _ (x i)))) :
          TensorPower Y.functionField 1 (⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k])) →
      MMP.Mori.formCoeff (k := k) (m := 1) (Y.presheaf.stalk y) hω h0 τ =
        algebraMap _ Y.functionField g * (algebraMap _ Y.functionField t)⁻¹ := by
  letI := MMP.Mori.stalkAlgebra sY y
  letI := MMP.Mori.functionFieldAlgebra sY
  haveI := MMP.Mori.isScalarTower_stalk_functionField sY y
  intro hω h0 hτ
  have hW : MMP.Mori.topFormsMap k (Y.presheaf.stalk y) Y.functionField (n + 1)
      (exteriorPower.ιMulti _ (n + 1)
        (Fin.cons (D k _ t) fun i => D k _ (x i) : Fin (n + 1) → Ω[Y.presheaf.stalk y⁄k])) =
      exteriorPower.ιMulti Y.functionField (n + 1)
        (Fin.cons (KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
          fun i => KaehlerDifferential.D k Y.functionField (algebraMap _ _ (x i))) := by
    rw [MMP.Mori.topFormsMap_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [KaehlerDifferential.map_D]
  have key : τ = (algebraMap _ Y.functionField g * (algebraMap _ Y.functionField t)⁻¹) •
      (MMP.Mori.ZTensorPower.basis (MMP.Mori.topFormsBasis _ hω h0) 1 () :
        MMP.Mori.ZTensorPower Y.functionField _ 1) := by
    rw [hτ]
    show _ = _ • (MMP.Mori.ZTensorPower.basis (MMP.Mori.topFormsBasis _ hω h0) (.ofNat 1) () :
      ⨂[Y.functionField]^1 _)
    rw [MMP.Mori.ZTensorPower.basis_ofNat, MMP.Mori.topFormsBasis_apply, hW,
      MMP.Mori.tprod_const_smul, pow_one, smul_smul]
    rfl
  rw [key, MMP.Mori.formCoeff_smul]
  simp [MMP.Mori.formCoeff]

/-- **Coordinates along `T`.** If `t` is a uniformizer of `𝒪_{Y,y}`, `y = j(η_T)`, and
`x₁, …, x_n ∈ 𝒪_{Y,y}` have linearly independent differentials `dx̄ᵢ` in `Ω_{k(T)/k}`, then
`dt ∧ dx₁ ∧ ⋯ ∧ dx_n` generates `Ω^{n+1}_{𝒪_{Y,y}/k}`, with nonzero image in `Ω^{n+1}_{k(Y)/k}`. -/
private theorem generator_of_linearIndependent (sY : Y ⟶ Spec (.of k)) [Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1) (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T]
    [Smooth (j ≫ sY)] (P : MMP.Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {t : Y.presheaf.stalk (j (genericPoint T))}
    (ht : Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1)
    (x : Fin n → Y.presheaf.stalk (j (genericPoint T))) :
    letI := MMP.Mori.stalkAlgebra sY (j (genericPoint T))
    letI := MMP.Mori.functionFieldAlgebra sY
    letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
    haveI := MMP.Mori.isScalarTower_stalk_functionField sY (j (genericPoint T))
    LinearIndependent T.functionField
        (fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x i))) →
      Submodule.span (Y.presheaf.stalk (j (genericPoint T))) {(exteriorPower.ιMulti
          (Y.presheaf.stalk (j (genericPoint T))) (n + 1)
        (Fin.cons (D k (Y.presheaf.stalk (j (genericPoint T))) t)
          fun i => D k (Y.presheaf.stalk (j (genericPoint T))) (x i) :
          Fin (n + 1) → Ω[Y.presheaf.stalk (j (genericPoint T))⁄k]))} = ⊤ ∧
      MMP.Mori.topFormsMap k (Y.presheaf.stalk (j (genericPoint T))) Y.functionField (n + 1)
        (exteriorPower.ιMulti (Y.presheaf.stalk (j (genericPoint T))) (n + 1)
          (Fin.cons (D k (Y.presheaf.stalk (j (genericPoint T))) t)
          fun i => D k (Y.presheaf.stalk (j (genericPoint T))) (x i) :
            Fin (n + 1) → Ω[Y.presheaf.stalk (j (genericPoint T))⁄k])) ≠ 0 := by
  letI := MMP.Mori.stalkAlgebra sY (j (genericPoint T))
  letI := MMP.Mori.functionFieldAlgebra sY
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  haveI := MMP.Mori.isScalarTower_stalk_functionField sY (j (genericPoint T))
  intro hx
  letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨_, _, hsurj, hker⟩ := residue_facts sY j
  obtain ⟨_, _, _⟩ := MMP.Flips.ResolutionInputs.stalk_facts sY (j (genericPoint T))
  obtain ⟨_, _, hn, hK⟩ := finrank_kaehler sY (d := n + 1) (by rw [hY]; norm_cast)
    (j (genericPoint T))
  obtain ⟨htm, ht2⟩ := mem_maximalIdeal_and_notMem_sq_of_ord_eq_one P hP.symm ht
  have htk : algebraMap _ T.functionField t = 0 := by
    rw [← RingHom.mem_ker, hker]; exact htm
  have hspan := span_ιMulti_cons_D_eq_top hsurj hn htk ht2 hker x hx
  have : FiniteDimensional Y.functionField Ω[Y.functionField⁄k] :=
    Module.finite_of_finrank_pos (by rw [hK]; omega)
  have := MMP.Mori.nontrivial_exteriorPower_of_finrank_eq k Y.functionField hK
  exact ⟨hspan, MMP.Mori.topFormsMap_ne_zero_of_span_eq_top hspan⟩

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- On a smooth integral scheme over `k`, `Ω_{𝒪_{Y,y}/k}` is finite free of the rank of
`Ω_{k(Y)/k}`. -/
private theorem free_kaehler (sY : Y ⟶ Spec (.of k)) [Smooth sY] (y : Y) :
    letI := MMP.Mori.stalkAlgebra sY y
    letI := MMP.Mori.functionFieldAlgebra sY
    Module.Free (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] ∧
      Module.Finite (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] ∧
      Module.finrank (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] =
        Module.finrank Y.functionField Ω[Y.functionField⁄k] := by
  letI := MMP.Mori.stalkAlgebra sY y
  letI := MMP.Mori.functionFieldAlgebra sY
  haveI := MMP.Mori.isScalarTower_stalk_functionField sY y
  obtain ⟨h1, h2, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts sY y
  have : Module.Finite (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] :=
    KaehlerDifferential.finite k _
  have : Module.Free (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] :=
    Module.free_of_flat_of_isLocalRing
  exact ⟨inferInstance, inferInstance,
    (MMP.Mori.finrank_kaehlerDifferential_eq_of_isFractionRing (K := Y.functionField)).symm⟩

/-- On a smooth normal integral scheme, `ord_Γ(f • τ) = v_Γ(f) + ord_Γ(τ)` for forms of degree
`dim Ω_{k(Y)/k}`. -/
private theorem ordForm_smul_of_smooth (sY : Y ⟶ Spec (.of k)) [Smooth sY]
    (Γ : MMP.Mori.PrimeDivisor Y) {d : ℕ}
    (hd : letI := MMP.Mori.functionFieldAlgebra sY
      Module.finrank Y.functionField Ω[Y.functionField⁄k] = d) {m : ℤ}
    {f : Y.functionField} (hf : f ≠ 0) {τ : MMP.Mori.RationalPluriForms sY d m} (hτ : τ ≠ 0) :
    Γ.ordForm (f • τ) = Y.ord f Γ.genericPoint + Γ.ordForm τ := by
  letI := MMP.Mori.stalkAlgebra sY Γ.genericPoint
  letI := MMP.Mori.functionFieldAlgebra sY
  haveI := MMP.Mori.isScalarTower_stalk_functionField sY Γ.genericPoint
  obtain ⟨_, _, hr⟩ := free_kaehler sY Γ.genericPoint
  exact MMP.Mori.ordAt_smul (k := k) Γ.ord_mul_of_ne_zero
    (fun _ ha => Γ.ord_algebraMap_of_isUnit ha)
    (MMP.Mori.exists_topForms_generator_of_free (K := Y.functionField) (hr.trans hd)) hf hτ

open Classical in
/-- **Local equations of a prime divisor on a smooth scheme.** If `η_P ⤳ z`, there is
`π ∈ 𝒪_{Y,z}` with `ord_Γ π = 1` for `Γ = P` and `ord_Γ π = 0` for every other prime divisor
`Γ` through `z`: `𝒪_{Y,z}` is factorial, a prime element `π` of the prime of `P` generates the
prime of every prime divisor through `z` containing it, and these primes determine the divisor. -/
private theorem exists_localEquation (sY : Y ⟶ Spec (.of k)) [Smooth sY]
    (P : MMP.Mori.PrimeDivisor Y) {z : Y} (hz : P.genericPoint ⤳ z) :
    ∃ π : Y.presheaf.stalk z, algebraMap _ Y.functionField π ≠ 0 ∧
      ∀ (Γ : MMP.Mori.PrimeDivisor Y), Γ.genericPoint ⤳ z →
        Y.ord (algebraMap _ Y.functionField π) Γ.genericPoint = if Γ = P then 1 else 0 := by
  classical
  haveI := AlgebraicGeometry.uniqueFactorizationMonoid_stalk_of_smooth sY z
  -- for a prime element `π` in the prime of `Γ`, that prime is `(π)` and `π` is a uniformizer
  have key : ∀ (Γ : MMP.Mori.PrimeDivisor Y) (h : Γ.genericPoint ⤳ z) {π : Y.presheaf.stalk z},
      Prime π → π ∈ MMP.Intersection.primeOfSpecializes h →
      MMP.Intersection.primeOfSpecializes h = Ideal.span {π} ∧
        Irreducible ((Y.presheaf.stalkSpecializes h).hom π) := by
    intro Γ h π hπ hmem
    letI := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
    haveI := MMP.Intersection.isLocalization_stalkSpecializes h
    haveI := isDiscreteValuationRing_stalk_of_genericPoint_eq Γ rfl
    set q := MMP.Intersection.primeOfSpecializes h
    have hle : Ideal.span {π} ≤ q := (Ideal.span_singleton_le_iff_mem _).mpr hmem
    have hpr : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
    have hd : Disjoint (q.primeCompl : Set (Y.presheaf.stalk z)) ↑(Ideal.span {π}) :=
      Set.disjoint_left.mpr fun a ha hb => ha (hle hb)
    have hI := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl
      (Y.presheaf.stalk Γ.genericPoint) _ hpr hd
    have hinj : Function.Injective (algebraMap (Y.presheaf.stalk z)
        (Y.presheaf.stalk Γ.genericPoint)) :=
      IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors q)
    have hne : Ideal.map (algebraMap _ (Y.presheaf.stalk Γ.genericPoint)) (Ideal.span {π}) ≠ ⊥ := by
      rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
      exact fun h0 => hπ.ne_zero (hinj (h0.trans (map_zero _).symm))
    have hmax := IsLocalRing.eq_maximalIdeal (hI.isMaximal hne)
    have hcomap := IsLocalization.under_map_of_isPrime_disjoint q.primeCompl
      (Y.presheaf.stalk Γ.genericPoint) hpr hd
    refine ⟨?_, ?_⟩
    · rw [← hcomap, hmax]
      rfl
    · rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmax, Ideal.map_span,
        Set.image_singleton]
      rfl
  set p := MMP.Intersection.primeOfSpecializes hz
  have hp0 : p ≠ ⊥ := by
    letI := (Y.presheaf.stalkSpecializes hz).hom.toAlgebra
    haveI := MMP.Intersection.isLocalization_stalkSpecializes hz
    haveI := isDiscreteValuationRing_stalk_of_genericPoint_eq P rfl
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl ϖ
    change IsLocalization.mk' _ a s = ϖ at has
    intro hp
    have hs := IsLocalization.mk'_spec P.localRing a s
    rw [has] at hs
    have ha : a ∈ p := by
      change (Y.presheaf.stalkSpecializes hz).hom a ∈ IsLocalRing.maximalIdeal _
      change ϖ * algebraMap _ P.localRing (s : Y.presheaf.stalk z) = _ at hs
      rw [← RingHom.algebraMap_toAlgebra (Y.presheaf.stalkSpecializes hz).hom, ← hs]
      exact Ideal.mul_mem_right _ _
        (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
    rw [hp, Ideal.mem_bot] at ha
    rw [ha, IsLocalization.mk'_zero] at has
    exact hϖ.ne_zero has.symm
  obtain ⟨π, hπp, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (inferInstance : p.IsPrime) hp0
  obtain ⟨hpπ, hirrP⟩ := key P hz hπ hπp
  have hπ0 : algebraMap _ Y.functionField π ≠ 0 := by
    rw [← MMP.Mori.algebraMap_stalkSpecializes hz]
    intro h0
    exact hirrP.ne_zero (IsFractionRing.injective _ Y.functionField (h0.trans (map_zero _).symm))
  refine ⟨π, hπ0, fun Γ hΓ => ?_⟩
  rw [← MMP.Mori.algebraMap_stalkSpecializes hΓ]
  by_cases hmem : π ∈ MMP.Intersection.primeOfSpecializes hΓ
  · obtain ⟨hqπ, hirr⟩ := key Γ hΓ hπ hmem
    have hΓP : Γ = P := by
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      have h1 := MMP.Intersection.fromSpecStalk_primeOfSpecializes hΓ
      have h2 := MMP.Intersection.fromSpecStalk_primeOfSpecializes hz
      have hPS : (⟨MMP.Intersection.primeOfSpecializes hΓ, inferInstance⟩ :
          PrimeSpectrum (Y.presheaf.stalk z)) =
          ⟨MMP.Intersection.primeOfSpecializes hz, inferInstance⟩ :=
        PrimeSpectrum.ext (hqπ.trans hpπ.symm)
      exact h1.symm.trans ((congrArg _ hPS).trans h2)
    rw [if_pos hΓP]
    haveI := isDiscreteValuationRing_stalk_of_genericPoint_eq Γ rfl
    exact SmoothDivisorResidue.ord_algebraMap_irreducible _ Γ.coheight_genericPoint hirr
  · have hΓP : Γ ≠ P := by
      rintro rfl
      exact hmem hπp
    rw [if_neg hΓP]
    exact SmoothDivisorResidue.ord_algebraMap_of_isUnit _ Γ.coheight_genericPoint
      (notMem_maximalIdeal.mp hmem)

/-- **Local generators of `ω_Y`.** Near every point `z` of a smooth integral scheme of dimension
`d` there are local coordinates `x₁, …, x_d` on an open `U`, and `dx₁ ∧ ⋯ ∧ dx_d` generates the
top forms of `𝒪_{Y,y}` at every `y ∈ U`; so it is a nonzero form of order zero along every prime
divisor meeting `U`. -/
private theorem exists_canonical_generator (sY : Y ⟶ Spec (.of k)) [Smooth sY] {d : ℕ}
    (hY : topologicalKrullDim Y = d) (z : Y) :
    ∃ U : Y.Opens, z ∈ U ∧ ∃ ω : MMP.Mori.RationalPluriForms sY d 1, ω ≠ 0 ∧
      ∀ Γ : MMP.Mori.PrimeDivisor Y, Γ.genericPoint ∈ U → Γ.ordForm ω = 0 := by
  letI := MMP.Mori.functionFieldAlgebra sY
  obtain ⟨U, hzU, m, x, hx, hrank, -⟩ := MMP.Flips.ResolutionInputs.exists_isLocalCoordinatesOn sY z
  have hmd : m = d := by
    obtain ⟨_, _, hd, -⟩ := finrank_kaehler sY hY z
    exact hrank.symm.trans hd
  subst hmd
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨_, _, _, hK⟩ := finrank_kaehler sY hY z
  have : FiniteDimensional Y.functionField Ω[Y.functionField⁄k] := by
    obtain ⟨_, _, _⟩ := free_kaehler sY z
    letI := MMP.Mori.stalkAlgebra sY z
    haveI := MMP.Mori.isScalarTower_stalk_functionField sY z
    exact Module.Finite.of_basis ((Module.Free.chooseBasis (Y.presheaf.stalk z)
      Ω[Y.presheaf.stalk z⁄k]).ofIsLocalizedModule Y.functionField
      (nonZeroDivisors (Y.presheaf.stalk z)) (KaehlerDifferential.map k k _ Y.functionField))
  have := MMP.Mori.nontrivial_exteriorPower_of_finrank_eq k Y.functionField hK
  set W0 : ⋀[Y.functionField]^m Ω[Y.functionField⁄k] := exteriorPower.ιMulti Y.functionField m
    (fun i => D k Y.functionField (Y.germToFunctionField U (x i))) with hW0
  -- at every point of `U`, `dx₁ ∧ ⋯ ∧ dx_m` generates the top forms of the local ring
  have hloc : ∀ y ∈ U,
      letI := MMP.Mori.stalkAlgebra sY y
      haveI := MMP.Mori.isScalarTower_stalk_functionField sY y
      ∃ gen : ⋀[Y.presheaf.stalk y]^m Ω[Y.presheaf.stalk y⁄k],
        Submodule.span (Y.presheaf.stalk y) {gen} = ⊤ ∧
          MMP.Mori.topFormsMap k (Y.presheaf.stalk y) Y.functionField m gen = W0 := by
    intro y hyU
    letI := MMP.Mori.stalkAlgebra sY y
    haveI := MMP.Mori.isScalarTower_stalk_functionField sY y
    obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset hyU
    obtain ⟨b, hb⟩ := hx ⟨W, hW⟩ hWU
    letI := MMP.Mori.sectionAlgebra sY W
    letI : Algebra Γ(Y, W) (Y.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hyW⟩
    haveI := MMP.Mori.isScalarTower_section_stalk sY W ⟨y, hyW⟩
    haveI := hW.isLocalization_stalk ⟨y, hyW⟩
    haveI := MMP.Flips.ResolutionInputs.isLocalizedModule_kaehlerMap (k := k)
      (hW.primeIdealOf ⟨y, hyW⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
    let b' := b.ofIsLocalizedModule (Y.presheaf.stalk y)
        (hW.primeIdealOf ⟨y, hyW⟩).asIdeal.primeCompl
      (KaehlerDifferential.map k k Γ(Y, W) (Y.presheaf.stalk y))
    refine ⟨exteriorPower.ιMulti _ m b', ?_, ?_⟩
    · refine eq_top_iff.mpr fun w _ => ?_
      obtain ⟨r, rfl⟩ := (MMP.Intersection.bijective_smul_ιMulti_basis b').2 w
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [MMP.Mori.topFormsMap_ιMulti, hW0]
      congr 1
      funext i
      rw [Module.Basis.ofIsLocalizedModule_apply, hb, KaehlerDifferential.map_D,
        KaehlerDifferential.map_D]
      congr 1
      haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
      change algebraMap (Y.presheaf.stalk y) Y.functionField
        ((Y.presheaf.germ W y hyW).hom ((Y.presheaf.map (homOfLE hWU).op).hom (x i))) = _
      rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hyW]
      simp only [Scheme.germToFunctionField, ← CommRingCat.comp_apply]
      have hg := TopCat.Presheaf.germ_res Y.presheaf (homOfLE hWU) (genericPoint Y)
        ((genericPoint_spec Y).mem_open_set_iff W.isOpen |>.mpr ⟨y, trivial, hyW⟩)
      exact congrArg (fun f => (ConcreteCategory.hom f) (x i)) hg
  set ω : MMP.Mori.RationalPluriForms sY m 1 :=
    (PiTensorProduct.tprod Y.functionField (fun _ : Fin 1 => W0) :
      TensorPower Y.functionField 1 (⋀[Y.functionField]^m Ω[Y.functionField⁄k])) with hω
  have hcoeff : ∀ y ∈ U,
      letI := MMP.Mori.stalkAlgebra sY y
      haveI := MMP.Mori.isScalarTower_stalk_functionField sY y
      ∀ (gen : ⋀[Y.presheaf.stalk y]^m Ω[Y.presheaf.stalk y⁄k])
        (hgen : Submodule.span (Y.presheaf.stalk y) {gen} = ⊤)
        (h0 : MMP.Mori.topFormsMap k (Y.presheaf.stalk y) Y.functionField m gen ≠ 0),
        MMP.Mori.topFormsMap k (Y.presheaf.stalk y) Y.functionField m gen = W0 →
        MMP.Mori.formCoeff (k := k) (m := 1) (Y.presheaf.stalk y) hgen h0 ω = 1 := by
    intro y _ gen hgen h0 hgW
    letI := MMP.Mori.stalkAlgebra sY y
    haveI := MMP.Mori.isScalarTower_stalk_functionField sY y
    have hb : ω = (MMP.Mori.ZTensorPower.basis (MMP.Mori.topFormsBasis _ hgen h0) 1 () :
        MMP.Mori.ZTensorPower Y.functionField _ 1) := by
      show _ = (MMP.Mori.ZTensorPower.basis (MMP.Mori.topFormsBasis _ hgen h0) (.ofNat 1) () :
        ⨂[Y.functionField]^1 _)
      rw [MMP.Mori.ZTensorPower.basis_ofNat, MMP.Mori.topFormsBasis_apply, hgW]
    rw [hb]
    simp [MMP.Mori.formCoeff]
  refine ⟨U, hzU, ω, ?_, fun Γ hΓ => ?_⟩
  · letI := MMP.Mori.stalkAlgebra sY z
    haveI := MMP.Mori.isScalarTower_stalk_functionField sY z
    obtain ⟨gen, hgen, hgW⟩ := hloc z hzU
    have h0 := MMP.Mori.topFormsMap_ne_zero_of_span_eq_top (K := Y.functionField) hgen
    intro hω0
    have h1 := (MMP.Mori.formCoeff_eq_zero_iff (m := 1) hgen h0 ω).mpr hω0
    rw [hcoeff z hzU gen hgen h0 hgW] at h1
    exact one_ne_zero h1
  · letI := MMP.Mori.stalkAlgebra sY Γ.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField sY Γ.genericPoint
    obtain ⟨gen, hgen, hgW⟩ := hloc Γ.genericPoint hΓ
    have h0 := MMP.Mori.topFormsMap_ne_zero_of_span_eq_top (K := Y.functionField) hgen
    rw [ordForm_eq_ord_formCoeff sY Γ rfl hgen h0 ω, hcoeff _ hΓ gen hgen h0 hgW]
    exact Scheme.ord_one _

end Setup

variable {k : Type u} [Field k] {Y T : AlgebraicGeometry.Scheme.{u}}
  (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
      [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsIntegral T] (j : T ⟶ Y)

/-- The residue of a chosen presentation, and `0` if there is none. -/
private noncomputable def res (n : ℕ) (σ : MMP.Mori.RationalPluriForms sY (n + 1) 1) :
    MMP.Mori.RationalPluriForms (j ≫ sY) n 1 :=
  open Classical in
  if h : ∃ ρ, MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ then h.choose else 0

/-- Multiplying a presentation by `φ ∈ 𝒪_{Y,y}` multiplies its residue by `φ̄`. -/
private theorem isPoincareResidue_smul {n : ℕ} {σ : MMP.Mori.RationalPluriForms sY (n + 1) 1}
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ)
    (φ : Y.presheaf.stalk (j (genericPoint T))) :
    MMP.Fourfold.IsPoincareResidue sY j n 1 (algebraMap _ Y.functionField φ • σ)
      ((j.stalkMap (genericPoint T)).hom φ • ρ) := by
  obtain ⟨t, g, x, ht, hσ, hρ⟩ := h
  refine ⟨t, φ * g, x, ht, ?_, ?_⟩
  · rw [hσ, map_mul, mul_smul]
    rfl
  · rw [hρ, map_mul, mul_smul]
    rfl

/-- A presentation whose restricted differentials `dx̄ᵢ` are linearly dependent has residue `0`. -/
private theorem residue_eq_zero_of_not_linearIndependent {n : ℕ}
    (g : Y.presheaf.stalk (j (genericPoint T))) (x : Fin n → Y.presheaf.stalk (j (genericPoint T)))
    (hx : letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
      ¬ LinearIndependent T.functionField
        (fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x i)))) :
    letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
    ((j.stalkMap (genericPoint T)).hom g • PiTensorProduct.tprod T.functionField
        (fun _ : Fin 1 => exteriorPower.ιMulti T.functionField n
          fun i => KaehlerDifferential.D k T.functionField
            ((j.stalkMap (genericPoint T)).hom (x i))) :
        TensorPower T.functionField 1 (⋀[T.functionField]^n Ω[T.functionField⁄k])) = 0 := by
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  rw [(exteriorPower.ιMulti T.functionField n).map_linearDependent _ hx,
    (PiTensorProduct.tprod T.functionField).map_coord_zero (0 : Fin 1) rfl, smul_zero]

/-- A form with a presentation that is zero, or does not have order exactly `-1`, has residue
`0`: a presentation `g · dt/t ∧ dx` with `ḡ ≠ 0` and `dx̄₁ ∧ ⋯ ∧ dx̄_n ≠ 0` has `dt ∧ dx` a
generator of the top forms of `𝒪_{Y,y}` and `g` a unit, so the form is nonzero of order `-1`. -/
private theorem isPoincareResidue_eq_zero {k : Type u} [Field k]
    {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    {σ : MMP.Mori.RationalPluriForms sY (n + 1) 1}
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ) (hσ : σ = 0 ∨ P.ordForm σ ≠ -1) :
    ρ = 0 := by
  letI := MMP.Mori.stalkAlgebra sY (j (genericPoint T))
  letI := MMP.Mori.functionFieldAlgebra sY
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  haveI := MMP.Mori.isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨t, g, x, ht, hσe, hρe⟩ := h
  by_contra hρ0
  have hg : (j.stalkMap (genericPoint T)).hom g ≠ 0 := by
    intro h0; apply hρ0; rw [hρe, h0, zero_smul]; rfl
  have hli : LinearIndependent T.functionField
      (fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x i))) := by
    by_contra hli
    exact hρ0 (by rw [hρe]; exact residue_eq_zero_of_not_linearIndependent sY j g x hli)
  letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨_, _, _, hker⟩ := residue_facts sY j
  have hgm : g ∉ maximalIdeal _ := by
    rw [← hker, RingHom.mem_ker]; exact hg
  have hy : Order.coheight (j (genericPoint T)) = 1 := hP ▸ P.coheight_genericPoint
  have hg0 : algebraMap _ Y.functionField g ≠ 0 := ((notMem_maximalIdeal.mp hgm).map _).ne_zero
  have hgo := SmoothDivisorResidue.ord_algebraMap_of_isUnit _ hy (notMem_maximalIdeal.mp hgm)
  obtain ⟨hω, h0⟩ := generator_of_linearIndependent sY hY j P hP ht x hli
  have hc := formCoeff_presentation sY t g x σ hω h0 hσe
  have hord := ordForm_eq_ord_formCoeff sY P hP.symm hω h0 σ
  have ht0 := ne_zero_of_ord_eq_one ht
  rw [hc, Scheme.ord_mul hg0 (inv_ne_zero ht0), hgo,
    SmoothDivisorResidue.ord_inv ht0, ht] at hord
  have hσ0 : σ ≠ 0 := by
    intro h0'
    have h1 := (MMP.Mori.formCoeff_eq_zero_iff (m := 1) hω h0 σ).mpr h0'
    rw [hc] at h1
    exact mul_ne_zero hg0 (inv_ne_zero ht0) h1
  rcases hσ with h | h
  · exact hσ0 h
  · exact h (by rw [hord]; rfl)

/-- The residue does not depend on the presentation. -/
private theorem isPoincareResidue_unique {k : Type u} [Field k] {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    {σ : MMP.Mori.RationalPluriForms sY (n + 1) 1}
    {ρ ρ' : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ)
    (h' : MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ') : ρ = ρ' := by
  by_cases hσ : σ ≠ 0 ∧ P.ordForm σ = -1
  · obtain ⟨ρ₀, hρ₀, -⟩ :=
      MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one sY hY j P hP σ hσ.1 hσ.2
    exact ((hρ₀ ρ).1 h).trans ((hρ₀ ρ').1 h').symm
  · have hσ' : σ = 0 ∨ P.ordForm σ ≠ -1 := by tauto
    exact (isPoincareResidue_eq_zero sY hY j P hP h hσ').trans
      (isPoincareResidue_eq_zero sY hY j P hP h' hσ').symm

/-- **Coordinates along `T`** exist: a uniformizer `t` of `𝒪_{Y,y}` and `x₁, …, x_n ∈ 𝒪_{Y,y}`
whose restrictions have linearly independent differentials on `T`. They are read off a
presentation of a form with a simple pole along `T`, whose residue is nonzero. -/
private theorem exists_coordinates {k : Type u} [Field k] {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) :
    letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
    ∃ (t : Y.presheaf.stalk (j (genericPoint T))) (x : Fin n → Y.presheaf.stalk (j
        (genericPoint T))),
      Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 ∧
      LinearIndependent T.functionField
        (fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x i))) := by
  letI := MMP.Mori.stalkAlgebra sY (j (genericPoint T))
  letI := MMP.Mori.functionFieldAlgebra sY
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  haveI := MMP.Mori.isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨t₀, ht₀⟩ := exists_ord_eq_one P hP.symm
  obtain ⟨_, _, hn, -⟩ := finrank_kaehler sY (d := n + 1) (by rw [hY]; norm_cast)
    (j (genericPoint T))
  obtain ⟨ω, hω, h0⟩ := MMP.Mori.exists_topForms_generator_of_free (K := Y.functionField) hn
  have ht0 := ne_zero_of_ord_eq_one ht₀
  let τ : MMP.Mori.RationalPluriForms sY (n + 1) 1 := (algebraMap _ Y.functionField t₀)⁻¹ •
    (MMP.Mori.ZTensorPower.basis (MMP.Mori.topFormsBasis _ hω h0) 1
        () : MMP.Mori.ZTensorPower _ _ 1)
  have hc : MMP.Mori.formCoeff (k := k) (m := 1) (Y.presheaf.stalk (j (genericPoint T))) hω h0 τ =
      (algebraMap _ Y.functionField t₀)⁻¹ := by
    simp [τ, MMP.Mori.formCoeff]
  have hτ0 : τ ≠ 0 := by
    intro h0'
    have h1 := (MMP.Mori.formCoeff_eq_zero_iff (m := 1) hω h0 τ).mpr h0'
    rw [hc] at h1
    exact inv_ne_zero ht0 h1
  have hτ : P.ordForm τ = -1 := by
    rw [ordForm_eq_ord_formCoeff sY P hP.symm hω h0 τ, hc,
      SmoothDivisorResidue.ord_inv ht0, ht₀]
  obtain ⟨ρ, hρ, hρ0, -⟩ :=
    MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one sY hY j P hP τ hτ0 hτ
  obtain ⟨t, g, x, ht, -, hρe⟩ := (hρ ρ).2 rfl
  refine ⟨t, x, ht, ?_⟩
  by_contra hli
  exact hρ0 (by rw [hρe]; exact residue_eq_zero_of_not_linearIndependent sY j g x hli)

/-- **Presentations along fixed coordinates.** For coordinates `t, x` along `T`, every rational
top form of order at least `-1` along `T` is `g · dt/t ∧ dx₁ ∧ ⋯ ∧ dx_n` with `g ∈ 𝒪_{Y,y}`. -/
private theorem exists_coeff_of_neg_one_le {k : Type u} [Field k]
    {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    {t : Y.presheaf.stalk (j (genericPoint T))} {x : Fin n → Y.presheaf.stalk (j (genericPoint T))}
    (ht : Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1)
    (hx : letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
      LinearIndependent T.functionField
        (fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x i))))
    (σ : MMP.Mori.RationalPluriForms sY (n + 1) 1) (hσ : -1 ≤ P.ordForm σ) :
    letI := MMP.Mori.functionFieldAlgebra sY
    ∃ g : Y.presheaf.stalk (j (genericPoint T)),
      σ = (algebraMap _ Y.functionField g • PiTensorProduct.tprod Y.functionField
          (fun _ : Fin 1 => (algebraMap _ Y.functionField t)⁻¹ •
            exteriorPower.ιMulti Y.functionField (n + 1)
              (Fin.cons (KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
                fun i => KaehlerDifferential.D k Y.functionField (algebraMap _ _ (x i)))) :
          TensorPower Y.functionField 1 (⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k])) := by
  letI := MMP.Mori.stalkAlgebra sY (j (genericPoint T))
  letI := MMP.Mori.functionFieldAlgebra sY
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  haveI := MMP.Mori.isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hω, h0⟩ := generator_of_linearIndependent sY hY j P hP ht x hx
  have ht0 := ne_zero_of_ord_eq_one ht
  set c := MMP.Mori.formCoeff (k := k) (m := 1) (Y.presheaf.stalk (j (genericPoint T))) hω h0 σ
    with hc
  have hord : c = 0 ∨ 0 ≤ Y.ord (c * algebraMap _ Y.functionField t) (j (genericPoint T)) := by
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    refine Or.inr ?_
    rw [Scheme.ord_mul hc0 ht0, ht, hc, ← ordForm_eq_ord_formCoeff sY P hP.symm hω h0 σ]
    omega
  obtain ⟨g, hg⟩ := exists_eq_of_ord_nonneg P hP.symm (f := c * algebraMap _ Y.functionField t)
    (hord.imp (fun h => by rw [h, zero_mul]) id)
  refine ⟨g, ?_⟩
  set E : MMP.Mori.RationalPluriForms sY (n + 1) 1 :=
    (algebraMap _ Y.functionField g • PiTensorProduct.tprod Y.functionField
          (fun _ : Fin 1 => (algebraMap _ Y.functionField t)⁻¹ •
            exteriorPower.ιMulti Y.functionField (n + 1)
              (Fin.cons (KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
                fun i => KaehlerDifferential.D k Y.functionField (algebraMap _ _ (x i)))) :
          TensorPower Y.functionField 1 (⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]))
    with hE
  have hcE := formCoeff_presentation sY t g x E hω h0 hE
  rw [hg, mul_assoc, mul_inv_cancel₀ ht0, mul_one] at hcE
  rw [← MMP.Mori.formCoeff_smul_basis (m := 1) hω h0 σ,
    ← MMP.Mori.formCoeff_smul_basis (m := 1) hω h0 E, hcE]

/-- Every rational top form of order at least `-1` along `T` has a presentation
`g · dt/t ∧ dx₁ ∧ ⋯ ∧ dx_n`: `Ω^{n+1}_{𝒪_{Y,y}/k}` is free on `dt ∧ dx₁ ∧ ⋯ ∧ dx_n`. -/
private theorem exists_isPoincareResidue_of_neg_one_le {k : Type u} [Field k]
    {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    (σ : MMP.Mori.RationalPluriForms sY (n + 1) 1) (hσ : -1 ≤ P.ordForm σ) :
    ∃ ρ, MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ := by
  letI := MMP.Mori.functionFieldAlgebra sY
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  obtain ⟨t, x, ht, hx⟩ := exists_coordinates sY hY j P hP
  obtain ⟨g, hg⟩ := exists_coeff_of_neg_one_le sY hY j P hP ht hx σ hσ
  exact ⟨_, t, g, x, ht, hg, rfl⟩

/-- Two forms of order at least `-1` with presentations have a presentation of their sum, with
the sum of the residues: both are presented along the same coordinates. -/
private theorem isPoincareResidue_add {k : Type u} [Field k] {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    {σ σ' : MMP.Mori.RationalPluriForms sY (n + 1) 1}
    {ρ ρ' : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (hσ : -1 ≤ P.ordForm σ) (hσ' : -1 ≤ P.ordForm σ')
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ)
    (h' : MMP.Fourfold.IsPoincareResidue sY j n 1 σ' ρ') :
    MMP.Fourfold.IsPoincareResidue sY j n 1 (σ + σ') (ρ + ρ') := by
  letI := MMP.Mori.functionFieldAlgebra sY
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  obtain ⟨t, x, ht, hx⟩ := exists_coordinates sY hY j P hP
  obtain ⟨g, hg⟩ := exists_coeff_of_neg_one_le sY hY j P hP ht hx σ hσ
  obtain ⟨g', hg'⟩ := exists_coeff_of_neg_one_le sY hY j P hP ht hx σ' hσ'
  have hρ := isPoincareResidue_unique sY hY j P hP h ⟨t, g, x, ht, hg, rfl⟩
  have hρ' := isPoincareResidue_unique sY hY j P hP h' ⟨t, g', x, ht, hg', rfl⟩
  refine ⟨t, g + g', x, ht, ?_, ?_⟩
  · rw [hg, hg', map_add, add_smul]
    rfl
  · rw [hρ, hρ', map_add, add_smul]
    rfl

private theorem mem_of_genericPoint_mem {X : Scheme.{u}} (Γ : MMP.Mori.PrimeDivisor X) {U : X.Opens}
    (h : (Γ.support ∩ U).Nonempty) : Γ.genericPoint ∈ U := by
  obtain ⟨z, hz, hzU⟩ := h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hz
  exact hz.mem_open U.isOpen hzU

/-- The restriction to `T` of a divisor which is effective on `U` is effective on `j⁻¹U`. -/
private theorem coeff_restrict_nonneg {Y T : Scheme.{u}} (j : T ⟶ Y) (D : MMP.Mori.Divisor Y)
    {U : Y.Opens} (hD : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ U).Nonempty → 0 ≤ D.coeff E)
    (Γ' : MMP.Mori.PrimeDivisor T) (hΓ' : (Γ'.support ∩ j ⁻¹ᵁ U).Nonempty) :
    0 ≤ (D.restrict j).coeff Γ' := by
  classical
  by_cases h : (Function.support (MMP.Mori.DivisorWithCoeffs.restrictCoeff j D)).Finite
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_restrict j h]
    refine Finset.sum_nonneg fun E _ => ?_
    by_cases hl : E.intersectionLength j Γ' = 0
    · simp [hl]
    have hmem : j Γ'.genericPoint ∈ E.support := by
      by_contra hn
      exact hl (MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem j E hn)
    exact smul_nonneg (Nat.zero_le _) (hD E ⟨_, hmem, mem_of_genericPoint_mem Γ' hΓ'⟩)
  · rw [MMP.Mori.DivisorWithCoeffs.restrict, dif_neg h]
    rfl

/-- Every point of `j(T)` lies on the prime divisor with generic point `j(η_T)`. -/
private theorem map_mem_support {Y T : Scheme.{u}} [IsIntegral T] (j : T ⟶ Y)
    (P : MMP.Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) (x : T) :
    j x ∈ P.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
  have := (genericPoint_specializes x).map j.continuous
  rw [hP] at this
  exact this

private theorem support_inter_nonempty {Y T : Scheme.{u}} [IsIntegral T] (j : T ⟶ Y)
    (P : MMP.Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) {U : Y.Opens}
    (hU : j ⁻¹ᵁ U ≠ ⊥) : (P.support ∩ U).Nonempty := by
  obtain ⟨z, hz⟩ : ∃ z, z ∈ j ⁻¹ᵁ U := by
    by_contra hn
    exact hU (eq_bot_iff.mpr fun z hz => (hn ⟨z, hz⟩).elim)
  exact ⟨j z, map_mem_support j P hP z, hz⟩

/-- **The residue on sections.** A map `r` on forms which vanishes exactly off the forms with a
simple pole, and has `div(r σ) = (div σ + T)|_T` on them, sends `ω_Y(T)(U)` into `ω_T(j⁻¹U)` with
kernel `ω_Y(U)`. -/
private theorem mem_pluricanonicalSections_of_residue {k : Type u} [Field k]
    {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    (r : MMP.Mori.RationalPluriForms sY (n + 1) 1 →
      MMP.Mori.RationalPluriForms (j ≫ sY) n 1)
    (hr0 : ∀ σ, -1 ≤ P.ordForm σ → (σ = 0 ∨ P.ordForm σ ≠ -1) → r σ = 0)
    (hr1 : ∀ σ, σ ≠ 0 → P.ordForm σ = -1 → r σ ≠ 0 ∧
      MMP.Mori.divisorOfForm (r σ) =
        (MMP.Mori.divisorOfForm σ + Finsupp.single P 1).restrict j)
    (U : Y.Opens) (hU : j ⁻¹ᵁ U ≠ ⊥) :
    ∀ σ ∈ MMP.Mori.pluricanonicalSections sY (n + 1) 1 (Finsupp.single P 1) U,
      r σ ∈ MMP.Mori.pluricanonicalSections (j ≫ sY) n 1 0
        (j ⁻¹ᵁ U) ∧
      (r σ = 0 ↔ σ ∈ MMP.Mori.pluricanonicalSections sY (n + 1) 1 0 U) := by
  intro σ hσ
  have hPU := support_inter_nonempty j P hP hU
  have hU' : U ≠ ⊥ := by
    rintro rfl
    exact hU (by simp)
  have hcoeff : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ U).Nonempty → σ ≠ 0 →
      0 ≤ P.ordForm σ + 1 ∧ (E ≠ P → 0 ≤ E.ordForm σ) := by
    intro E hE hσ0
    have h1 := hσ.2 P hPU hσ0
    have h2 := hσ.2 E hE hσ0
    simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.single_eq_same] at h1
    refine ⟨h1, fun hEP => ?_⟩
    simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.single_eq_of_ne hEP, add_zero] at h2
    exact h2
  have hord : σ ≠ 0 → -1 ≤ P.ordForm σ := fun hσ0 => by
    have := (hcoeff P hPU hσ0).1; omega
  refine ⟨?_, ?_, ?_⟩
  · refine (MMP.Mori.mem_pluricanonicalSections_of_ne_bot hU).mpr fun Γ' hΓ' hr => ?_
    have hσ0 : σ ≠ 0 := fun h => hr (hr0 σ (by rw [h]; simp) (Or.inl h))
    have hσ1 : P.ordForm σ = -1 := by
      by_contra h
      exact hr (hr0 σ (hord hσ0) (Or.inr h))
    have hdiv := (hr1 σ hσ0 hσ1).2
    have := congrArg (fun D => MMP.Mori.DivisorWithCoeffs.coeff D Γ') hdiv
    simp only [MMP.Mori.coeff_divisorOfForm] at this
    rw [this]
    simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.coe_zero, Pi.zero_apply, add_zero]
    refine coeff_restrict_nonneg j _ (fun E hE => ?_) Γ' hΓ'
    simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.coe_add, Pi.add_apply]
    by_cases hEP : E = P
    · subst hEP
      rw [Finsupp.single_eq_same]
      exact (hcoeff E hE hσ0).1
    · rw [Finsupp.single_eq_of_ne hEP, add_zero]
      exact (hcoeff E hE hσ0).2 hEP
  · intro hr
    refine (MMP.Mori.mem_pluricanonicalSections_of_ne_bot hU').mpr fun E hE hσ0 => ?_
    simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.coe_zero, Pi.zero_apply, add_zero]
    by_cases hEP : E = P
    · subst hEP
      have h1 := (hcoeff E hE hσ0).1
      by_contra h
      exact (hr1 σ hσ0 (by omega)).1 hr
    · exact (hcoeff E hE hσ0).2 hEP
  · intro h0
    by_cases hσ0 : σ = 0
    · exact hr0 σ (by rw [hσ0]; simp) (Or.inl hσ0)
    have := h0.2 P hPU hσ0
    simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.coe_zero, Pi.zero_apply, add_zero] at this
    exact hr0 σ (by omega) (Or.inr (by omega))

/-- The differentials `dx̄₁, …, dx̄_n` of coordinates along `T` are a basis of `Ω_{k(T)/k}`:
`Ω_{k(T)/k}` is spanned by the images of `dt, dx₁, …, dx_n`, and `dt̄ = 0`. -/
private theorem exists_basis_kaehler_functionField {k : Type u} [Field k]
    {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) :
    letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
    Nonempty (Module.Basis (Fin n) T.functionField Ω[T.functionField⁄k]) := by
  letI := MMP.Mori.stalkAlgebra sY (j (genericPoint T))
  letI := MMP.Mori.functionFieldAlgebra sY
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  haveI := MMP.Mori.isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨t, x, ht, hx⟩ := exists_coordinates sY hY j P hP
  letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨_, _, hsurj, hker⟩ := residue_facts sY j
  obtain ⟨_, _, _⟩ := MMP.Flips.ResolutionInputs.stalk_facts sY (j (genericPoint T))
  obtain ⟨_, _, hn, -⟩ := finrank_kaehler sY (d := n + 1) (by rw [hY]; norm_cast)
    (j (genericPoint T))
  obtain ⟨htm, ht2⟩ := mem_maximalIdeal_and_notMem_sq_of_ord_eq_one P hP.symm ht
  have htk : algebraMap _ T.functionField t = 0 := by
    rw [← RingHom.mem_ker, hker]; exact htm
  obtain ⟨b, hb⟩ := exists_basis_cons_D hsurj hn htk ht2 hker x hx
  have hspan : Submodule.span T.functionField
      (Set.range fun i => D k T.functionField (algebraMap _ T.functionField (x i))) = ⊤ := by
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation k T.functionField,
      Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    obtain ⟨a, rfl⟩ := hsurj l
    have h1 : ∀ a, D k T.functionField (algebraMap _ T.functionField a) =
        KaehlerDifferential.mapBaseChange k _ T.functionField
          ((1 : T.functionField) ⊗ₜ[Y.presheaf.stalk (j (genericPoint T))] D k _ a) := by
      intro a
      rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    rw [h1, ← b.sum_repr (D k _ a), TensorProduct.tmul_sum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul T.functionField]
    refine Submodule.smul_mem _ _ ?_
    have hbi : b i = (Fin.cons (D k _ t) fun i => D k _ (x i) :
        Fin (n + 1) → Ω[Y.presheaf.stalk (j (genericPoint T))⁄k]) i := by rw [hb]
    rw [hbi]
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero, ← h1, htk, Derivation.map_zero]
      exact zero_mem _
    · rw [Fin.cons_succ, ← h1]
      exact Submodule.subset_span ⟨i, rfl⟩
  exact ⟨Module.Basis.mk hx hspan.ge⟩

/-- The rational `n`-forms on `T` are a line. -/
private theorem exists_smul_eq_of_ne_zero {k : Type u} [Field k]
    {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    {ρ₀ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1} (h0 : ρ₀ ≠ 0)
    (ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1) :
    ∃ f : T.functionField, ρ = f • ρ₀ := by
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  obtain ⟨b⟩ := exists_basis_kaehler_functionField sY hY j P hP
  have : Module.Finite T.functionField Ω[T.functionField⁄k] := Module.Finite.of_basis b
  have h1 : Module.finrank T.functionField (⋀[T.functionField]^n Ω[T.functionField⁄k]) = 1 := by
    rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b, Fintype.card_fin,
      Nat.choose_self]
  let b1 : Module.Basis Unit T.functionField (⋀[T.functionField]^n Ω[T.functionField⁄k]) :=
    (Module.finBasisOfFinrankEq _ _ h1).reindex (Equiv.ofUnique _ _)
  let B : Module.Basis Unit T.functionField
      (MMP.Mori.RationalPluriForms (j ≫ sY) n 1) :=
    MMP.Mori.ZTensorPower.basis b1 1
  have hB : Module.finrank T.functionField
      (MMP.Mori.RationalPluriForms (j ≫ sY) n 1) = 1 := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_unit]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ρ₀ h0).mp hB ρ
  exact ⟨c, hc.symm⟩

/-- The restriction to `T` of a divisor which vanishes on `W` vanishes on `j⁻¹W`. -/
private theorem coeff_restrict_eq_zero {Y T : Scheme.{u}} (j : T ⟶ Y) (D : MMP.Mori.Divisor Y)
    {W : Y.Opens} (hD : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ W).Nonempty → D.coeff E = 0)
    (Γ' : MMP.Mori.PrimeDivisor T) (hΓ' : (Γ'.support ∩ j ⁻¹ᵁ W).Nonempty) :
    (D.restrict j).coeff Γ' = 0 := by
  classical
  by_cases h : (Function.support (MMP.Mori.DivisorWithCoeffs.restrictCoeff j D)).Finite
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_restrict j h]
    refine Finset.sum_eq_zero fun E _ => ?_
    by_cases hl : E.intersectionLength j Γ' = 0
    · simp [hl]
    have hmem : j Γ'.genericPoint ∈ E.support := by
      by_contra hn
      exact hl (MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem j E hn)
    have := hD E ⟨_, hmem, mem_of_genericPoint_mem Γ' hΓ'⟩
    simp only [MMP.Mori.DivisorWithCoeffs.coeff] at this
    rw [this]
    simp
  · rw [MMP.Mori.DivisorWithCoeffs.restrict, dif_neg h]
    rfl

/-- **Local generators of `ω_Y(T)`.** Near every point of `T` there is a form `σ₀` generating
`ω_Y(T)`: `ord_Γ σ₀ = -coeff_Γ(T)` for every prime divisor `Γ` meeting a neighbourhood `W`. -/
private theorem exists_generatesOn_twisted {k : Type u} [Field k]
    {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) (x : T) :
    ∃ W : Y.Opens, j x ∈ W ∧ ∃ σ₀ : MMP.Mori.RationalPluriForms sY (n + 1) 1, σ₀ ≠ 0 ∧
      ∀ Γ : MMP.Mori.PrimeDivisor Y, (Γ.support ∩ W).Nonempty →
        Γ.ordForm σ₀ + MMP.Mori.DivisorWithCoeffs.coeff (Finsupp.single P 1) Γ = 0 := by
  classical
  letI := MMP.Mori.functionFieldAlgebra sY
  have hz : P.genericPoint ⤳ j x := hP ▸ (genericPoint_specializes x).map j.continuous
  have hd : topologicalKrullDim Y = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hY]; push_cast; rfl
  obtain ⟨U₁, hzU₁, ω₁, hω₁0, hω₁⟩ := exists_canonical_generator sY hd (j x)
  obtain ⟨π, hπ0, hπ⟩ := exists_localEquation sY P hz
  obtain ⟨-, -, -, hK⟩ := finrank_kaehler sY hd (j x)
  set σ₀ : MMP.Mori.RationalPluriForms sY (n + 1) 1 :=
    (algebraMap _ Y.functionField π)⁻¹ • ω₁ with hσ₀
  have hσ₀0 : σ₀ ≠ 0 := smul_ne_zero (inv_ne_zero hπ0) hω₁0
  have hthrough : ∀ Γ : MMP.Mori.PrimeDivisor Y, j x ∈ Γ.support →
      Γ.ordForm σ₀ + MMP.Mori.DivisorWithCoeffs.coeff (Finsupp.single P 1) Γ = 0 := by
    intro Γ hΓ
    have hΓz : Γ.genericPoint ⤳ j x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hΓ
      exact hΓ
    have hΓU : Γ.genericPoint ∈ U₁ := hΓz.mem_open U₁.isOpen hzU₁
    rw [hσ₀, ordForm_smul_of_smooth sY Γ hK (inv_ne_zero hπ0) hω₁0, hω₁ Γ hΓU, add_zero]
    rw [SmoothDivisorResidue.ord_inv hπ0, hπ Γ hΓz]
    by_cases h : Γ = P
    · subst h
      simp [MMP.Mori.DivisorWithCoeffs.coeff]
    · simp [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.single_eq_of_ne h, h]
  set E : Set (MMP.Mori.PrimeDivisor Y) := {Γ | Γ.ordForm σ₀ +
    MMP.Mori.DivisorWithCoeffs.coeff (Finsupp.single P 1) Γ ≠ 0} with hEdef
  have hE : E.Finite := by
    refine ((MMP.Mori.finite_ordForm_ne_zero σ₀).union (Set.finite_singleton P)).subset ?_
    intro Γ hΓ
    by_cases h : Γ = P
    · exact Or.inr h
    · refine Or.inl fun h0 => hΓ ?_
      simp [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.single_eq_of_ne h, h0]
  have hC : IsClosed (⋃ Γ ∈ E, Γ.support) :=
    hE.isClosed_biUnion fun Γ _ => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isClosed_closure
  refine ⟨U₁ ⊓ ⟨(⋃ Γ ∈ E, Γ.support)ᶜ, hC.isOpen_compl⟩, ⟨hzU₁, ?_⟩, σ₀, hσ₀0, ?_⟩
  · intro hmem
    obtain ⟨Γ, hΓE, hzΓ⟩ := Set.mem_iUnion₂.mp hmem
    exact hΓE (hthrough Γ hzΓ)
  · rintro Γ ⟨w, hwΓ, -, hwC⟩
    by_contra hne
    exact hwC (Set.mem_iUnion₂.mpr ⟨Γ, hne, hwΓ⟩)

private theorem isPoincareResidue_res {n : ℕ} {σ : MMP.Mori.RationalPluriForms sY (n + 1) 1}
    (h : ∃ ρ, MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ) :
    MMP.Fourfold.IsPoincareResidue sY j n 1 σ (res sY j n σ) := by
  rw [res, dif_pos h]; exact h.choose_spec

private theorem isPoincareResidue_res_of_neg_one_le {k : Type u} [Field k]
    {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    {σ : MMP.Mori.RationalPluriForms sY (n + 1) 1} (hσ : -1 ≤ P.ordForm σ) :
    MMP.Fourfold.IsPoincareResidue sY j n 1 σ (res sY j n σ) :=
  isPoincareResidue_res sY j (exists_isPoincareResidue_of_neg_one_le sY hY j P hP σ hσ)

/-- `res` computes the residue of every form that has a presentation. -/
private theorem res_eq_of_isPoincareResidue {k : Type u} [Field k]
    {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    {σ : MMP.Mori.RationalPluriForms sY (n + 1) 1}
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ) : res sY j n σ = ρ :=
  isPoincareResidue_unique sY hY j P hP (isPoincareResidue_res sY j ⟨ρ, h⟩) h

/-- **Local surjectivity of the residue.** Every section of `ω_T` over `j⁻¹U` is, near each
point of `j⁻¹U`, the residue of a section of `ω_Y(T)`. -/
private theorem exists_mem_res_eq {k : Type u} [Field k] {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) (U : Y.Opens) (hU : j ⁻¹ᵁ U ≠ ⊥) :
    ∀ ρ ∈ MMP.Mori.pluricanonicalSections (j ≫ sY) n 1 0
        (j ⁻¹ᵁ U), ∀ x ∈ j ⁻¹ᵁ U, ∃ V : Y.Opens, j x ∈ V ∧ V ≤ U ∧
      ∃ σ ∈ MMP.Mori.pluricanonicalSections sY (n + 1) 1 (Finsupp.single P 1) V,
        res sY j n σ = ρ := by
  letI := MMP.Mori.functionFieldAlgebra sY
  letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  intro ρ hρ x hx
  have hres0 : res sY j n 0 = 0 :=
    isPoincareResidue_eq_zero sY hY j P hP (isPoincareResidue_res_of_neg_one_le sY hY j P hP
      (σ := 0) (by simp)) (Or.inl rfl)
  by_cases hρ0 : ρ = 0
  · exact ⟨U, hx, le_rfl, 0, zero_mem _, by rw [hres0, hρ0]⟩
  obtain ⟨W, hxW, σ₀, hσ₀0, hσ₀⟩ := exists_generatesOn_twisted sY hY j P hP x
  have hjx := map_mem_support j P hP x
  have hσ₀P : P.ordForm σ₀ = -1 := by
    have := hσ₀ P ⟨j x, hjx, hxW⟩
    simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.single_eq_same] at this
    omega
  obtain ⟨ρ₀, hρ₀, hρ₀0, hdiv, -⟩ :=
    MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one sY hY j P hP σ₀ hσ₀0 hσ₀P
  have hres₀ : res sY j n σ₀ = ρ₀ :=
    (hρ₀ _).1 (isPoincareResidue_res_of_neg_one_le sY hY j P hP hσ₀P.ge)
  have hρ₀ord : ∀ Γ' : MMP.Mori.PrimeDivisor T, (Γ'.support ∩ j ⁻¹ᵁ W).Nonempty →
      Γ'.ordForm ρ₀ = 0 := by
    intro Γ' hΓ'
    have := congrArg (fun D => MMP.Mori.DivisorWithCoeffs.coeff D Γ') hdiv
    simp only [MMP.Mori.coeff_divisorOfForm] at this
    rw [this]
    refine coeff_restrict_eq_zero j _ (fun E hE => ?_) Γ' hΓ'
    have := hσ₀ E hE
    simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.coe_add, Pi.add_apply] at this ⊢
    exact this
  obtain ⟨f, hf⟩ := exists_smul_eq_of_ne_zero sY hY j P hP hρ₀0 ρ
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hρ0 (by rw [hf, zero_smul])
  obtain ⟨bT⟩ := exists_basis_kaehler_functionField sY hY j P hP
  have hL : Module.finrank T.functionField Ω[T.functionField⁄k] = n := by
    rw [Module.finrank_eq_card_basis bT, Fintype.card_fin]
  have hfx : ∀ Γ' : MMP.Mori.PrimeDivisor T, x ∈ Γ'.support →
      0 ≤ T.ord f Γ'.genericPoint := by
    intro Γ' hxΓ'
    have h1 := hρ.2 Γ' ⟨x, hxΓ', hx⟩ hρ0
    rw [hf, ordForm_smul_of_smooth (j ≫ sY) Γ' hL hf0 hρ₀0, hρ₀ord Γ' ⟨x, hxΓ', hxW⟩] at h1
    simpa [MMP.Mori.DivisorWithCoeffs.coeff] using h1
  obtain ⟨r, hr⟩ :=
    MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg x hf0 hfx
  obtain ⟨r', hr'⟩ := SurjectiveOnStalks.stalkMap_surjective (f := j) x r
  obtain ⟨V', hjxV', s, hs⟩ := Y.presheaf.exists_germ_eq r'
  have : Nonempty V' := ⟨⟨j x, hjxV'⟩⟩
  set a : Y.functionField := algebraMap (Y.presheaf.stalk (j x)) Y.functionField r' with ha
  have ha' : a = Y.germToFunctionField V' s := by
    rw [ha, ← hs, Scheme.algebraMap_germ_eq_germToFunctionField]
  have ha0 : a ≠ 0 := by
    intro h0
    apply hf0
    have hr'0 : r' = 0 := IsFractionRing.injective _ Y.functionField (h0.trans (map_zero _).symm)
    rw [← hr, ← hr', hr'0, map_zero, map_zero]
  obtain ⟨-, -, -, hK⟩ := finrank_kaehler sY (d := n + 1) (by rw [hY]; norm_cast) (j x)
  refine ⟨W ⊓ V' ⊓ U, ⟨⟨hxW, hjxV'⟩, hx⟩, inf_le_right, a • σ₀, ?_, ?_⟩
  · have hV : W ⊓ V' ⊓ U ≠ ⊥ := by
      intro h
      have : j x ∈ W ⊓ V' ⊓ U := ⟨⟨hxW, hjxV'⟩, hx⟩
      rw [h] at this
      exact this
    refine (MMP.Mori.mem_pluricanonicalSections_of_ne_bot hV).mpr fun Γ hΓ _ => ?_
    have hΓW : (Γ.support ∩ W).Nonempty := hΓ.mono fun z hz => ⟨hz.1, hz.2.1.1⟩
    have hΓV' : Γ.genericPoint ∈ V' :=
      mem_of_genericPoint_mem Γ (hΓ.mono fun z hz => ⟨hz.1, hz.2.1.2⟩)
    rw [ordForm_smul_of_smooth sY Γ hK ha0 hσ₀0]
    have h1 := hσ₀ Γ hΓW
    have h2 : 0 ≤ Y.ord a Γ.genericPoint := by
      rw [ha', ← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hΓV']
      exact ord_nonneg Γ rfl _
    omega
  · have hsp : j (genericPoint T) ⤳ j x := (genericPoint_specializes x).map j.continuous
    set φ := (Y.presheaf.stalkSpecializes hsp).hom r' with hφ
    have hφa : algebraMap _ Y.functionField φ = a := by
      rw [hφ, ha]
      exact MMP.Mori.algebraMap_stalkSpecializes hsp r'
    have hφf : (j.stalkMap (genericPoint T)).hom φ = f := by
      rw [hφ, Scheme.Hom.stalkSpecializes_stalkMap_apply, hr', ← hr,
        RingHom.algebraMap_toAlgebra]
    have hI := isPoincareResidue_smul sY j
      (isPoincareResidue_res_of_neg_one_le sY hY j P hP hσ₀P.ge) φ
    rw [hφa, hφf, hres₀, ← hf] at hI
    exact res_eq_of_isPoincareResidue sY hY j P hP hI

/-- The residue sequence `0 → ω_Y → ω_Y(T) → ι_* ω_T → 0` on sections over opens meeting `T`. -/
private theorem res_sections {k : Type u} [Field k] {Y T : AlgebraicGeometry.Scheme.{u}}
    (sY : Y ⟶ AlgebraicGeometry.Spec (.of k)) [AlgebraicGeometry.IsIntegral Y]
    [CompactSpace Y] [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsNormal Y]
    [AlgebraicGeometry.Smooth sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [AlgebraicGeometry.IsClosedImmersion j] [AlgebraicGeometry.IsIntegral T]
    [CompactSpace T] [AlgebraicGeometry.IsLocallyNoetherian T] [AlgebraicGeometry.IsNormal T]
    [AlgebraicGeometry.Smooth (j ≫ sY)]
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) :
    ∀ U : Y.Opens, j ⁻¹ᵁ U ≠ ⊥ →
        (∀ σ ∈ MMP.Mori.pluricanonicalSections sY (n + 1) 1 (Finsupp.single P 1) U,
          res sY j n σ ∈ MMP.Mori.pluricanonicalSections
            (j ≫ sY) n 1 0 (j ⁻¹ᵁ U) ∧
          (res sY j n σ = 0 ↔ σ ∈ MMP.Mori.pluricanonicalSections sY (n + 1) 1 0 U)) ∧
        ∀ ρ ∈ MMP.Mori.pluricanonicalSections (j ≫ sY) n 1 0
            (j ⁻¹ᵁ U), ∀ x ∈ j ⁻¹ᵁ U, ∃ V : Y.Opens, j x ∈ V ∧ V ≤ U ∧
          ∃ σ ∈ MMP.Mori.pluricanonicalSections sY (n + 1) 1 (Finsupp.single P 1) V,
            res sY j n σ = ρ := by
  intro U hU
  refine ⟨mem_pluricanonicalSections_of_residue sY j P hP (res sY j n) (fun σ hσ h => ?_)
    (fun σ hσ0 hσ => ?_) U hU, exists_mem_res_eq sY hY j P hP U hU⟩
  · exact isPoincareResidue_eq_zero sY hY j P hP
      (isPoincareResidue_res_of_neg_one_le sY hY j P hP hσ) h
  · obtain ⟨ρ, hρ, hρ0, hdiv, -⟩ :=
      MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one sY hY j P hP σ hσ0 hσ
    rw [(hρ _).1 (isPoincareResidue_res_of_neg_one_le sY hY j P hP hσ.ge)]
    exact ⟨hρ0, hdiv⟩

end MMP.Mori.PoincareResidue

open MMP.Mori.PoincareResidue in
/-- **The Poincaré residue.** Let `Y` be a smooth variety of dimension `n + 1` over `k`,
`j : T ⟶ Y` a smooth integral closed subscheme whose generic point is that of the prime divisor
`P`, and `y = j(η_T)`. There is a map `res` from rational `(n+1)`-forms on `Y` to rational
`n`-forms on `T` such that, on the forms `σ` with `ord_P σ ≥ -1`:
* `res σ` is the Poincaré residue of `σ` for every presentation
  (`MMP.Fourfold.IsPoincareResidue`), and nothing else is;
* `res` is additive, and `res (φ • σ) = φ̄ • res σ` for `φ ∈ 𝒪_{Y,y}`;
and on every open `U` of `Y` meeting `T`, `res` maps `ω_Y(P)(U)` into `ω_T(j⁻¹U)`, with kernel
`ω_Y(U)`, and locally onto: every section of `ω_T` over `j⁻¹U` is, near each point of `j⁻¹U`,
the residue of a section of `ω_Y(P)`. -/
@[mmp "lem_mmp_foundation_km5b_full_poincare_residue"]
public theorem MMP.Mori.exists_poincareResidue {k : Type u} [Field k] {Y T : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [Smooth sY] {n : ℕ} (hY : topologicalKrullDim Y = n + 1) (j : T ⟶ Y) [IsClosedImmersion j]
    [IsIntegral T] [CompactSpace T] [IsLocallyNoetherian T] [IsNormal T] [Smooth (j ≫ sY)]
    (P : PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) :
    ∃ res : RationalPluriForms sY (n + 1) 1 → RationalPluriForms (j ≫ sY) n 1,
      (∀ σ, -1 ≤ P.ordForm σ →
        ∀ ρ, MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ ↔ ρ = res σ) ∧
      (∀ σ σ', -1 ≤ P.ordForm σ → -1 ≤ P.ordForm σ' → res (σ + σ') = res σ + res σ') ∧
      (∀ σ, -1 ≤ P.ordForm σ → ∀ φ : Y.presheaf.stalk (j (genericPoint T)),
        res (algebraMap _ Y.functionField φ • σ) =
          (j.stalkMap (genericPoint T)).hom φ • res σ) ∧
      ∀ U : Y.Opens, j ⁻¹ᵁ U ≠ ⊥ →
        (∀ σ ∈ pluricanonicalSections sY (n + 1) 1 (Finsupp.single P 1) U,
          res σ ∈ pluricanonicalSections (j ≫ sY) n 1 0 (j ⁻¹ᵁ U) ∧
          (res σ = 0 ↔ σ ∈ pluricanonicalSections sY (n + 1) 1 0 U)) ∧
        ∀ ρ ∈ pluricanonicalSections (j ≫ sY) n 1 0 (j ⁻¹ᵁ U), ∀ x ∈ j ⁻¹ᵁ U,
          ∃ V : Y.Opens, j x ∈ V ∧ V ≤ U ∧
          ∃ σ ∈ pluricanonicalSections sY (n + 1) 1 (Finsupp.single P 1) V,
            res σ = ρ :=
  ⟨res sY j n, fun σ hσ ρ => ⟨fun h => (res_eq_of_isPoincareResidue sY hY j P hP h).symm,
      fun h => h ▸ isPoincareResidue_res_of_neg_one_le sY hY j P hP hσ⟩,
    fun σ σ' hσ hσ' => res_eq_of_isPoincareResidue sY hY j P hP
      (isPoincareResidue_add sY hY j P hP hσ hσ'
        (isPoincareResidue_res_of_neg_one_le sY hY j P hP hσ)
        (isPoincareResidue_res_of_neg_one_le sY hY j P hP hσ')),
    fun σ hσ φ => res_eq_of_isPoincareResidue sY hY j P hP
      (isPoincareResidue_smul sY j (isPoincareResidue_res_of_neg_one_le sY hY j P hP hσ) φ),
    res_sections sY hY j P hP⟩

